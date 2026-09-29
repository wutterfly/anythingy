//! A store that hands out small, copyable tokens instead of references.
//!
//! See [`TokenStore`] for details.

use alloc::vec::{self, Vec};
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::{Enumerate, FusedIterator};
use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop};
use core::num::NonZeroU32;
use core::ops::{Index, IndexMut};
use core::slice;

/// Marks the end of the free list. Also caps the store at `u32::MAX` slots.
const NONE: u32 = u32::MAX;

/// Converts a slot position into the `u32` a token stores.
///
/// Positions always fit: the store refuses to grow past `u32::MAX` slots.
#[inline]
#[allow(clippy::cast_possible_truncation)]
const fn slot_index(position: usize) -> u32 {
    debug_assert!(position < NONE as usize);
    position as u32
}

/// The version of a slot while it holds a value.
///
/// **Always odd.** A slot's own version is odd exactly while it is occupied
/// and even while it is vacant, and `Version` can only be constructed odd
/// (see [`Version::from_raw`]). So a token's version can never equal the
/// version of a vacant slot, which is what lets [`Slot::value_if`] trust a
/// matching version without looking at anything else.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Version(NonZeroU32);

impl Version {
    /// The version of a slot's first value.
    const FIRST: Self = Self(NonZeroU32::MIN);

    /// Turns any number into a valid (odd) version by setting the low bit.
    /// A number that is already odd is unchanged.
    fn from_raw(raw: u32) -> Self {
        // `MIN` is 1, so this is `1 | raw`: odd, hence non-zero.
        Self(NonZeroU32::MIN | raw)
    }

    const fn get(self) -> u32 {
        self.0.get()
    }
}

/// An opaque handle to a value in a [`TokenStore`].
///
/// A token reveals nothing about where or how the value is stored; all you
/// can do with it is hand it back to the store that issued it, compare it for
/// equality, hash it, and order it (in an arbitrary but consistent order).
///
/// Tokens are 8 bytes, `Copy`, and cheap to compare and hash. A token is
/// tied to the type `T` of the store that issued it, so a token for a
/// texture cannot be used to look up a mesh. It stays `Copy`, `Send` and
/// `Sync` whatever `T` is, since it holds no `T`.
///
/// A token stays valid until the value it refers to is removed. After that
/// every lookup with it returns `None`, even when the space is reused for a
/// new value.
///
/// `Option<Token<T>>` is also 8 bytes.
pub struct Token<T> {
    index: u32,
    version: Version,
    _marker: PhantomData<fn() -> T>,
}

impl<T> Token<T> {
    fn new(index: u32, version: Version) -> Self {
        Self {
            index,
            version,
            _marker: PhantomData,
        }
    }

    // The accessors below exist for the tests only: users of the crate only
    // ever see an opaque token.

    /// The slot index.
    #[cfg(test)]
    pub(crate) const fn index(self) -> u32 {
        self.index
    }

    /// How many values the slot has held when this token was issued,
    /// counting from 1.
    #[cfg(test)]
    pub(crate) const fn generation(self) -> u32 {
        self.version.get() / 2 + 1
    }

    /// Packs the token into a `u64`, to build forged tokens in tests.
    #[cfg(test)]
    pub(crate) fn to_bits(self) -> u64 {
        (u64::from(self.version.get()) << 32) | u64::from(self.index)
    }

    /// Rebuilds a token from [`to_bits`](Self::to_bits), or from made-up bits.
    /// Returns `None` if the generation half is zero.
    #[cfg(test)]
    #[allow(clippy::cast_possible_truncation)] // deliberate: the low half is the index
    pub(crate) fn from_bits(bits: u64) -> Option<Self> {
        let raw = (bits >> 32) as u32;
        if raw == 0 {
            return None;
        }
        Some(Self::new(bits as u32, Version::from_raw(raw)))
    }
}

// Implemented by hand: deriving would require `T: Clone`, `T: Eq`, ...
// even though a token never holds a `T`.
impl<T> Clone for Token<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Token<T> {}

impl<T> PartialEq for Token<T> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.version == other.version
    }
}

impl<T> Eq for Token<T> {}

impl<T> Hash for Token<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.version.hash(state);
    }
}

impl<T> PartialOrd for Token<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// An arbitrary but consistent order, so tokens can be keys of ordered
/// collections. It says nothing about when the values were inserted.
impl<T> Ord for Token<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.index, self.version).cmp(&(other.index, other.version))
    }
}

impl<T> fmt::Debug for Token<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Opaque on purpose: nothing about the slot is shown.
        f.debug_struct("Token").finish_non_exhaustive()
    }
}

/// A store that keeps values and returns a [`Token`] for each one.
///
/// Insert a value to get a token, then use the token to read, modify or
/// remove the value later. Tokens are small `Copy` values you can keep in
/// other data structures freely, unlike references, which would tie those
/// structures to the store's borrow.
///
/// A token is only valid for the value it was issued for. Once that value is
/// removed the token is detected as stale, even after the space is reused for
/// a new value, instead of silently reaching that new value (the "ABA
/// problem" of plain indices).
///
/// Removed slots are reused, so the store does not grow while values come and
/// go. The memory overhead is 4 bytes per slot (rounded up to the value's
/// alignment).
///
/// All operations are O(1) except iteration, [`clear`](Self::clear) and
/// [`retain`](Self::retain), which are O(slots). Iteration order is
/// unspecified, and unrelated to insertion order once space has been reused.
///
/// # Limits
///
/// The store holds at most `u32::MAX - 1` slots; [`insert`](Self::insert)
/// panics beyond that.
///
/// A token is never issued twice by the same store, so a stale token can never
/// become valid again: a slot that has been reused about 2.1 billion times is
/// retired instead of reused, which costs one slot of memory.
///
/// # Examples
///
/// A renderer that hands out texture tokens instead of the textures:
///
/// ```
/// use anythingy::TokenStore;
///
/// struct Texture {
///     width: u32,
///     height: u32,
/// }
///
/// let mut textures = TokenStore::new();
/// let grass = textures.insert(Texture { width: 256, height: 256 });
/// let rock = textures.insert(Texture { width: 512, height: 512 });
///
/// assert_eq!(textures[grass].width, 256);
///
/// // Unload a texture: its token is now stale, everything else is unaffected.
/// let removed = textures.remove(grass).unwrap();
/// assert_eq!(removed.height, 256);
/// assert!(textures.get(grass).is_none());
/// assert_eq!(textures[rock].height, 512);
///
/// // The space is reused for a new value, but the old token is still stale.
/// let sand = textures.insert(Texture { width: 64, height: 64 });
/// assert_ne!(sand, grass);
/// assert!(textures.get(grass).is_none());
/// assert_eq!(textures[sand].width, 64);
/// ```
pub struct TokenStore<T> {
    slots: Vec<Slot<T>>,
    /// Index of the most recently freed slot, or [`NONE`].
    free_head: u32,
    len: usize,
}

/// What a slot holds: the value while occupied, the link to the next free
/// slot while vacant.
union SlotData<T> {
    value: ManuallyDrop<T>,
    next_free: u32,
}

/// One slot of a [`TokenStore`].
///
/// # Invariants
///
/// * `version` is **odd if and only if the slot is occupied**, and then
///   `data.value` holds an initialized `T` that this slot owns.
/// * While the slot is vacant (`version` even), `data.next_free` was the
///   last field written, so it is initialized.
///
/// Everything that reads the union goes through the small set of methods
/// below, which is where all of this module's `unsafe` code lives.
struct Slot<T> {
    data: SlotData<T>,
    version: u32,
}

impl<T> Slot<T> {
    /// A new slot holding `value`.
    const fn occupied(value: T, version: Version) -> Self {
        Self {
            data: SlotData {
                value: ManuallyDrop::new(value),
            },
            version: version.get(),
        }
    }

    const fn is_occupied(&self) -> bool {
        self.version & 1 == 1
    }

    /// The value and its version, if the slot is occupied.
    fn get(&self) -> Option<(Version, &T)> {
        if self.is_occupied() {
            // SAFETY: an odd version means `data.value` is initialized.
            let value = unsafe { &*self.data.value };
            Some((Version::from_raw(self.version), value))
        } else {
            None
        }
    }

    /// Like [`get`](Self::get), mutably.
    fn get_mut(&mut self) -> Option<(Version, &mut T)> {
        if self.is_occupied() {
            let version = Version::from_raw(self.version);
            // SAFETY: an odd version means `data.value` is initialized.
            let value = unsafe { &mut *self.data.value };
            Some((version, value))
        } else {
            None
        }
    }

    /// The value, if the slot currently has exactly this version.
    fn value_if(&self, version: Version) -> Option<&T> {
        if self.version == version.get() {
            // SAFETY: `Version` is always odd, so the slot is odd, so it is
            // occupied and `data.value` is initialized.
            Some(unsafe { &*self.data.value })
        } else {
            None
        }
    }

    /// Like [`value_if`](Self::value_if), mutably.
    fn value_mut_if(&mut self, version: Version) -> Option<&mut T> {
        if self.version == version.get() {
            // SAFETY: as in `value_if`.
            Some(unsafe { &mut *self.data.value })
        } else {
            None
        }
    }

    /// The next free slot's index, if this slot is vacant.
    const fn next_free(&self) -> Option<u32> {
        if self.is_occupied() {
            None
        } else {
            // SAFETY: a vacant slot's `next_free` is always initialized.
            Some(unsafe { self.data.next_free })
        }
    }

    /// Moves the value out and leaves the slot vacant, with the given even
    /// `vacant_version` and free-list link. Returns `None`, changing nothing,
    /// if the slot is already vacant.
    fn vacate(&mut self, vacant_version: u32, next_free: u32) -> Option<T> {
        debug_assert_eq!(vacant_version & 1, 0);
        if !self.is_occupied() {
            return None;
        }
        // SAFETY: the slot is occupied, so `data.value` is initialized. The
        // union and `version` are overwritten below before anything else can
        // look at the slot, so the value is never read or dropped again.
        let value = unsafe { ManuallyDrop::take(&mut self.data.value) };
        self.data.next_free = next_free;
        self.version = vacant_version;
        Some(value)
    }

    /// Puts `value` into this vacant slot.
    fn fill(&mut self, value: T, version: Version) {
        debug_assert!(!self.is_occupied());
        self.data.value = ManuallyDrop::new(value);
        self.version = version.get();
    }

    /// Moves the value out, for consuming iteration. The slot is left
    /// vacant (and never reused, since it is being consumed).
    fn take(&mut self) -> Option<(Version, T)> {
        let version = Version::from_raw(self.version);
        let value = self.vacate(0, NONE)?;
        Some((version, value))
    }
}

impl<T> Drop for Slot<T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() && self.is_occupied() {
            // SAFETY: occupied, so `data.value` is initialized, and this is
            // the only place that drops it: `vacate` clears the occupied
            // bit before handing the value out.
            unsafe { ManuallyDrop::drop(&mut self.data.value) };
        }
    }
}

impl<T: Clone> Clone for Slot<T> {
    fn clone(&self) -> Self {
        match self.get() {
            Some((version, value)) => Self::occupied(value.clone(), version),
            None => Self {
                data: SlotData {
                    // SAFETY: a vacant slot's `next_free` is initialized.
                    next_free: unsafe { self.data.next_free },
                },
                version: self.version,
            },
        }
    }
}

impl<T> TokenStore<T> {
    /// Creates an empty store. Does not allocate.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: Vec::new(),
            free_head: NONE,
            len: 0,
        }
    }

    /// Creates an empty store with room for `capacity` slots.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            slots: Vec::with_capacity(capacity),
            free_head: NONE,
            len: 0,
        }
    }

    /// Returns the number of slots (used or free) the store can hold without
    /// reallocating.
    #[must_use]
    pub const fn capacity(&self) -> usize {
        self.slots.capacity()
    }

    /// Reserves room for at least `additional` more slots. May reserve more
    /// than needed, since freed slots are reused before new ones are added.
    pub fn reserve(&mut self, additional: usize) {
        self.slots.reserve(additional);
    }

    /// Returns the number of values stored.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the store holds no values.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Stores a value and returns the token for it.
    ///
    /// # Panics
    ///
    /// Panics if the store is full (`u32::MAX - 1` slots).
    pub fn insert(&mut self, value: T) -> Token<T> {
        self.insert_with(|_| value)
    }

    /// Stores the value built by `f`, which is given the token the value
    /// will be reachable by. Useful for values that need to know their own
    /// token, such as an object that registers itself elsewhere.
    ///
    /// If `f` panics, the store is left unchanged.
    ///
    /// # Panics
    ///
    /// Panics if the store is full (`u32::MAX - 1` slots).
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::{Token, TokenStore};
    ///
    /// struct Node {
    ///     me: Token<Node>,
    /// }
    ///
    /// let mut nodes = TokenStore::new();
    /// let token = nodes.insert_with(|me| Node { me });
    /// assert_eq!(nodes[token].me, token);
    /// ```
    pub fn insert_with<F: FnOnce(Token<T>) -> T>(&mut self, f: F) -> Token<T> {
        // Work out which slot the value will go into, and build the value,
        // before changing anything, so a panic in `f` leaves the store as
        // it was.
        let token = if self.free_head == NONE {
            let index = u32::try_from(self.slots.len())
                .ok()
                .filter(|&index| index != NONE)
                .expect("TokenStore is full");
            Token::new(index, Version::FIRST)
        } else {
            // A vacant slot's version is even; the next value gets the odd
            // number after it.
            let vacant = self.slots[self.free_head as usize].version;
            Token::new(self.free_head, Version::from_raw(vacant))
        };
        let value = f(token);

        if self.free_head == NONE {
            self.slots.push(Slot::occupied(value, token.version));
        } else {
            let slot = &mut self.slots[token.index as usize];
            let next = slot
                .next_free()
                .expect("free list points at an occupied slot");
            slot.fill(value, token.version);
            self.free_head = next;
        }
        self.len += 1;
        token
    }

    /// Returns a reference to the value for `token`, or `None` if the token
    /// is stale (its value was removed) or was not issued by this store.
    #[must_use]
    pub fn get(&self, token: Token<T>) -> Option<&T> {
        self.slots
            .get(token.index as usize)?
            .value_if(token.version)
    }

    /// Returns a mutable reference to the value for `token`, or `None` if
    /// the token is stale.
    pub fn get_mut(&mut self, token: Token<T>) -> Option<&mut T> {
        self.slots
            .get_mut(token.index as usize)?
            .value_mut_if(token.version)
    }

    /// Returns mutable references to the values for `N` tokens at once, in
    /// the order the tokens are given.
    ///
    /// Useful when two values have to be modified together, for example
    /// copying from one texture into another.
    ///
    /// # Errors
    ///
    /// Returns [`GetDisjointMutError::StaleToken`] if any token is stale, and
    /// [`GetDisjointMutError::OverlappingTokens`] if two tokens refer to the
    /// same value, since that would hand out two `&mut` to it. Nothing is
    /// modified either way.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::TokenStore;
    ///
    /// let mut store = TokenStore::new();
    /// let a = store.insert(1);
    /// let b = store.insert(2);
    ///
    /// let [x, y] = store.get_disjoint_mut([a, b]).unwrap();
    /// std::mem::swap(x, y);
    /// assert_eq!((store[a], store[b]), (2, 1));
    ///
    /// assert!(store.get_disjoint_mut([a, a]).is_err());
    /// ```
    pub fn get_disjoint_mut<const N: usize>(
        &mut self,
        tokens: [Token<T>; N],
    ) -> Result<[&mut T; N], GetDisjointMutError> {
        // Check every token first, so that stale tokens are reported as such
        // before the slice is asked about overlapping indices.
        if tokens.iter().any(|&token| !self.contains(token)) {
            return Err(GetDisjointMutError::StaleToken);
        }
        let slots = self
            .slots
            .get_disjoint_mut(tokens.map(|token| token.index as usize))
            .map_err(|error| match error {
                slice::GetDisjointMutError::OverlappingIndices => {
                    GetDisjointMutError::OverlappingTokens
                }
                // Every token was just checked to be in range.
                slice::GetDisjointMutError::IndexOutOfBounds => GetDisjointMutError::StaleToken,
            })?;
        Ok(slots.map(|slot| match slot.get_mut() {
            Some((_, value)) => value,
            None => unreachable!("token was checked to refer to a live value"),
        }))
    }

    /// Returns `true` if `token` still refers to a value in the store.
    #[must_use]
    pub fn contains(&self, token: Token<T>) -> bool {
        self.get(token).is_some()
    }

    /// Removes and returns the value for `token`, or `None` if the token is
    /// stale. The token, and every copy of it, becomes stale.
    pub fn remove(&mut self, token: Token<T>) -> Option<T> {
        match self.slots.get(token.index as usize) {
            Some(slot) if slot.version == token.version.get() => {
                self.remove_at(token.index as usize)
            }
            _ => None,
        }
    }

    /// Removes the value in slot `index`, if there is one, regardless of
    /// which token it was issued under.
    fn remove_at(&mut self, index: usize) -> Option<T> {
        let slot = self.slots.get_mut(index)?;
        if !slot.is_occupied() {
            return None;
        }

        // Invalidate the slot's tokens by moving to the even version after
        // the current one; the next value will get the odd version after
        // that. Only the very last version, `u32::MAX`, has no successor:
        // then the slot is retired instead of reused (version 0, off the
        // free list), so it is never handed out again and no token can ever
        // be issued twice.
        let (vacant_version, next_free, relink) = match slot.version.checked_add(1) {
            Some(vacant_version) => (vacant_version, self.free_head, true),
            None => (0, NONE, false),
        };
        let value = slot.vacate(vacant_version, next_free)?;
        if relink {
            self.free_head = slot_index(index);
        }
        self.len -= 1;
        Some(value)
    }

    /// Removes every value. All tokens issued so far become stale, and stay
    /// stale when the slots are reused.
    pub fn clear(&mut self) {
        for index in 0..self.slots.len() {
            drop(self.remove_at(index));
        }
    }

    /// Keeps only the values for which `f` returns `true`. Removed values
    /// invalidate their tokens. `f` may mutate the values it keeps.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(Token<T>, &mut T) -> bool,
    {
        for index in 0..self.slots.len() {
            let keep = match self.slots[index].get_mut() {
                Some((version, value)) => f(Token::new(slot_index(index), version), value),
                None => continue,
            };
            if !keep {
                drop(self.remove_at(index));
            }
        }
    }

    /// Iterates over `(token, &value)` pairs in an unspecified order.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.slots.iter().enumerate(),
            remaining: self.len,
        }
    }

    /// Iterates over `(token, &mut value)` pairs in an unspecified order.
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            remaining: self.len,
            inner: self.slots.iter_mut().enumerate(),
        }
    }

    /// Iterates over the tokens of all stored values, in an unspecified order.
    #[must_use]
    pub fn tokens(&self) -> Tokens<'_, T> {
        Tokens { inner: self.iter() }
    }

    /// Iterates over the stored values in an unspecified order.
    #[must_use]
    pub fn values(&self) -> Values<'_, T> {
        Values { inner: self.iter() }
    }

    /// Iterates over mutable references to the stored values in an unspecified order.
    pub fn values_mut(&mut self) -> ValuesMut<'_, T> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// Removes and yields every `(token, value)` pair, in an unspecified order. The
    /// store is empty afterwards, even if the iterator is dropped before
    /// it is exhausted. All tokens issued so far become stale.
    pub const fn drain(&mut self) -> Drain<'_, T> {
        Drain {
            store: self,
            index: 0,
        }
    }
}

/// The error returned by [`TokenStore::get_disjoint_mut`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GetDisjointMutError {
    /// A token is stale: its value was removed, or it was not issued by this
    /// store.
    StaleToken,
    /// Two tokens refer to the same value.
    OverlappingTokens,
}

impl fmt::Display for GetDisjointMutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StaleToken => f.write_str("a token is stale"),
            Self::OverlappingTokens => f.write_str("two tokens refer to the same value"),
        }
    }
}

impl core::error::Error for GetDisjointMutError {}

impl<T> Default for TokenStore<T> {
    fn default() -> Self {
        Self::new()
    }
}

// Cloning keeps the slots' generations, so a token issued by the original
// also works on the clone (and refers to the clone's copy of its value).
impl<T: Clone> Clone for TokenStore<T> {
    fn clone(&self) -> Self {
        Self {
            slots: self.slots.clone(),
            free_head: self.free_head,
            len: self.len,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for TokenStore<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<T> Index<Token<T>> for TokenStore<T> {
    type Output = T;

    /// # Panics
    ///
    /// Panics if the token is stale.
    fn index(&self, token: Token<T>) -> &T {
        self.get(token).expect("invalid or stale token")
    }
}

impl<T> IndexMut<Token<T>> for TokenStore<T> {
    /// # Panics
    ///
    /// Panics if the token is stale.
    fn index_mut(&mut self, token: Token<T>) -> &mut T {
        self.get_mut(token).expect("invalid or stale token")
    }
}

/// Inserts every value, discarding the tokens. Use
/// [`insert`](TokenStore::insert) when you need them.
impl<T> Extend<T> for TokenStore<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.insert(value);
        }
    }
}

impl<T> IntoIterator for TokenStore<T> {
    type Item = (Token<T>, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            remaining: self.len,
            inner: self.slots.into_iter().enumerate(),
        }
    }
}

impl<'a, T> IntoIterator for &'a TokenStore<T> {
    type Item = (Token<T>, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut TokenStore<T> {
    type Item = (Token<T>, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

/// An iterator over the `(token, &value)` pairs of a [`TokenStore`]. Created
/// by [`TokenStore::iter`].
pub struct Iter<'a, T> {
    inner: Enumerate<slice::Iter<'a, Slot<T>>>,
    remaining: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Token<T>, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        for (index, slot) in self.inner.by_ref() {
            if let Some((version, value)) = slot.get() {
                self.remaining -= 1;
                return Some((Token::new(slot_index(index), version), value));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        while let Some((index, slot)) = self.inner.next_back() {
            if let Some((version, value)) = slot.get() {
                self.remaining -= 1;
                return Some((Token::new(slot_index(index), version), value));
            }
        }
        None
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}
impl<T> FusedIterator for Iter<'_, T> {}

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone(),
            remaining: self.remaining,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over the `(token, &mut value)` pairs of a
/// [`TokenStore`]. Created by [`TokenStore::iter_mut`].
pub struct IterMut<'a, T> {
    inner: Enumerate<slice::IterMut<'a, Slot<T>>>,
    remaining: usize,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (Token<T>, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        for (index, slot) in self.inner.by_ref() {
            if let Some((version, value)) = slot.get_mut() {
                self.remaining -= 1;
                return Some((Token::new(slot_index(index), version), value));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T> DoubleEndedIterator for IterMut<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        while let Some((index, slot)) = self.inner.next_back() {
            if let Some((version, value)) = slot.get_mut() {
                self.remaining -= 1;
                return Some((Token::new(slot_index(index), version), value));
            }
        }
        None
    }
}

impl<T> ExactSizeIterator for IterMut<'_, T> {}
impl<T> FusedIterator for IterMut<'_, T> {}

/// An owning iterator over the `(token, value)` pairs of a [`TokenStore`].
/// Created by [`TokenStore::into_iter`].
pub struct IntoIter<T> {
    inner: Enumerate<vec::IntoIter<Slot<T>>>,
    remaining: usize,
}

impl<T> Iterator for IntoIter<T> {
    type Item = (Token<T>, T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        for (index, mut slot) in self.inner.by_ref() {
            if let Some((version, value)) = slot.take() {
                self.remaining -= 1;
                return Some((Token::new(slot_index(index), version), value));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        while let Some((index, mut slot)) = self.inner.next_back() {
            if let Some((version, value)) = slot.take() {
                self.remaining -= 1;
                return Some((Token::new(slot_index(index), version), value));
            }
        }
        None
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}
impl<T> FusedIterator for IntoIter<T> {}

/// A draining iterator over the `(token, value)` pairs of a [`TokenStore`].
/// Created by [`TokenStore::drain`].
///
/// Values not yet yielded when the iterator is dropped are dropped with it.
pub struct Drain<'a, T> {
    store: &'a mut TokenStore<T>,
    index: usize,
}

impl<T> Iterator for Drain<'_, T> {
    type Item = (Token<T>, T);

    fn next(&mut self) -> Option<Self::Item> {
        while self.index < self.store.slots.len() {
            let index = self.index;
            self.index += 1;
            // The token must carry the version from before the removal.
            let version = self.store.slots[index].version;
            if let Some(value) = self.store.remove_at(index) {
                return Some((
                    Token::new(slot_index(index), Version::from_raw(version)),
                    value,
                ));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.store.len, Some(self.store.len))
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {}
impl<T> FusedIterator for Drain<'_, T> {}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        for _ in self.by_ref() {}
    }
}

/// Implements the iterator traits for a wrapper around one of the pair
/// iterators above, in its `inner` field, mapping each pair with `$map`.
macro_rules! forward_iterator {
    ({$($generics:tt)*} $name:ty, $item:ty, $map:expr) => {
        impl<$($generics)*> Iterator for $name {
            type Item = $item;

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.inner.next().map($map)
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.inner.size_hint()
            }
        }

        impl<$($generics)*> DoubleEndedIterator for $name {
            #[inline]
            fn next_back(&mut self) -> Option<Self::Item> {
                self.inner.next_back().map($map)
            }
        }

        impl<$($generics)*> ExactSizeIterator for $name {}
        impl<$($generics)*> FusedIterator for $name {}
    };
}

/// Debug output for iterators that cannot show their remaining items
/// without consuming them: just how many are left.
macro_rules! debug_remaining {
    ({$($generics:tt)*} $name:ident $ty:ty) => {
        impl<$($generics)*> fmt::Debug for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct(stringify!($name)).field("remaining", &self.len()).finish()
            }
        }
    };
}

debug_remaining!({'a, T} IterMut IterMut<'a, T>);
debug_remaining!({T} IntoIter IntoIter<T>);
debug_remaining!({'a, T} Drain Drain<'a, T>);

/// An iterator over the tokens of a [`TokenStore`]. Created by
/// [`TokenStore::tokens`].
pub struct Tokens<'a, T> {
    inner: Iter<'a, T>,
}
forward_iterator!({'a, T} Tokens<'a, T>, Token<T>, |(token, _)| token);
debug_remaining!({'a, T} Tokens Tokens<'a, T>);

impl<T> Clone for Tokens<'_, T> {
    fn clone(&self) -> Self {
        Tokens {
            inner: self.inner.clone(),
        }
    }
}

/// An iterator over the values of a [`TokenStore`]. Created by
/// [`TokenStore::values`].
pub struct Values<'a, T> {
    inner: Iter<'a, T>,
}
forward_iterator!({'a, T} Values<'a, T>, &'a T, |(_, value)| value);

impl<T> Clone for Values<'_, T> {
    fn clone(&self) -> Self {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Values<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over the values of a [`TokenStore`]. Created by
/// [`TokenStore::values_mut`].
pub struct ValuesMut<'a, T> {
    inner: IterMut<'a, T>,
}
forward_iterator!({'a, T} ValuesMut<'a, T>, &'a mut T, |(_, value)| value);
debug_remaining!({'a, T} ValuesMut ValuesMut<'a, T>);

#[cfg(test)]
mod tests {
    // Test values are small and narrowed on purpose.
    #![allow(clippy::cast_possible_truncation)]
    use super::*;
    use std::collections::HashMap;
    use std::rc::Rc;

    // ---- basics ----

    #[test]
    fn insert_get_and_len() {
        let mut store = TokenStore::new();
        assert!(store.is_empty());
        let a = store.insert("a");
        let b = store.insert("b");
        assert_eq!(store.len(), 2);
        assert_eq!(store.get(a), Some(&"a"));
        assert_eq!(store.get(b), Some(&"b"));
        assert!(store.contains(a));
        assert_ne!(a, b);
    }

    #[test]
    fn get_mut_and_index() {
        let mut store = TokenStore::new();
        let t = store.insert(1);
        *store.get_mut(t).unwrap() += 10;
        assert_eq!(store[t], 11);
        store[t] += 1;
        assert_eq!(store.get(t), Some(&12));
    }

    #[test]
    #[should_panic(expected = "invalid or stale token")]
    fn index_with_stale_token_panics() {
        let mut store = TokenStore::new();
        let t = store.insert(1);
        store.remove(t);
        let _ = store[t];
    }

    #[test]
    #[should_panic(expected = "invalid or stale token")]
    fn index_mut_with_stale_token_panics() {
        let mut store = TokenStore::new();
        let t = store.insert(1);
        store.remove(t);
        store[t] = 2;
    }

    #[test]
    fn remove_returns_value_and_stales_the_token() {
        let mut store = TokenStore::new();
        let t = store.insert(String::from("x"));
        assert_eq!(store.remove(t), Some(String::from("x")));
        assert_eq!(store.remove(t), None); // already gone
        assert_eq!(store.get(t), None);
        assert!(store.get_mut(t).is_none());
        assert!(!store.contains(t));
        assert_eq!(store.len(), 0);
    }

    #[test]
    fn slot_is_reused_but_old_token_stays_stale() {
        let mut store = TokenStore::new();
        let old = store.insert("old");
        store.remove(old);
        let new = store.insert("new");

        assert_eq!(new.index(), old.index()); // slot reused
        assert!(new.generation() > old.generation());
        assert_eq!(store.get(old), None);
        assert_eq!(store.remove(old), None);
        assert_eq!(store.get(new), Some(&"new")); // unaffected by stale calls
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn free_list_reuses_most_recently_freed_first() {
        let mut store = TokenStore::new();
        let tokens: Vec<_> = (0..4).map(|i| store.insert(i)).collect();
        store.remove(tokens[1]);
        store.remove(tokens[3]);
        assert_eq!(store.insert(10).index(), tokens[3].index());
        assert_eq!(store.insert(11).index(), tokens[1].index());
        assert_eq!(store.insert(12).index(), 4); // free list empty: grows
    }

    #[test]
    fn store_does_not_grow_under_churn() {
        let mut store = TokenStore::new();
        let mut live = Vec::new();
        for i in 0..8 {
            live.push(store.insert(i));
        }
        for round in 0..1000 {
            let t = live.remove(round % live.len());
            store.remove(t);
            live.push(store.insert(round));
        }
        assert_eq!(store.len(), 8);
        assert_eq!(store.slots.len(), 8);
    }

    #[test]
    fn token_from_another_store_of_same_type_is_treated_as_untrusted() {
        // Tokens carry no store identity, so a token from a different store
        // just looks up whatever is at that slot and generation. It must
        // never panic or misbehave.
        let mut a = TokenStore::new();
        let b: TokenStore<i32> = TokenStore::new();
        let t = a.insert(1);
        assert_eq!(b.get(t), None); // out of range in the empty store
    }

    #[test]
    fn insert_with_gives_the_final_token() {
        struct Node {
            me: Token<Self>,
        }
        let mut store = TokenStore::new();
        let first = store.insert_with(|me| Node { me });
        assert_eq!(store[first].me, first);

        store.remove(first);
        let reused = store.insert_with(|me| Node { me });
        assert_eq!(reused.index(), first.index());
        assert_eq!(store[reused].me, reused);
        assert_ne!(store[reused].me, first);
    }

    #[test]
    fn insert_with_panic_leaves_the_store_unchanged() {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        let mut store = TokenStore::new();
        let a = store.insert(1);
        let b = store.insert(2);
        store.remove(a); // so the next insert would reuse a's slot

        let result = catch_unwind(AssertUnwindSafe(|| {
            store.insert_with(|_| panic!("boom"));
        }));
        assert!(result.is_err());
        assert_eq!(store.len(), 1);
        assert_eq!(store.get(b), Some(&2));

        // The free slot is still available and still valid.
        let c = store.insert(3);
        assert_eq!(c.index(), a.index());
        assert_eq!(store[c], 3);
        assert_eq!(store.get(a), None);
    }

    // ---- token type ----

    #[test]
    fn token_is_small_and_has_a_niche() {
        assert_eq!(std::mem::size_of::<Token<String>>(), 8);
        assert_eq!(std::mem::size_of::<Option<Token<String>>>(), 8);
    }

    #[test]
    fn token_is_copy_send_sync_regardless_of_t() {
        fn assert_traits<X: Copy + Send + Sync + Eq + Hash + Ord>() {}
        assert_traits::<Token<Rc<()>>>();
        assert_traits::<Token<std::cell::RefCell<String>>>();
    }

    #[test]
    fn token_ordering_hash_and_debug() {
        let mut store = TokenStore::new();
        let a = store.insert(());
        let b = store.insert(());
        assert!(a < b);
        assert_eq!(a.cmp(&a), Ordering::Equal);
        // Debug output is opaque: it must not reveal the slot or generation.
        assert_eq!(format!("{a:?}"), "Token { .. }");
        assert_eq!(format!("{b:?}"), "Token { .. }");

        let mut set = std::collections::HashSet::new();
        set.insert(a);
        set.insert(b);
        set.insert(a);
        assert_eq!(set.len(), 2);

        // Newer generation of the same slot sorts after the older one.
        store.remove(a);
        let a2 = store.insert(());
        assert!(a < a2);
        assert_ne!(a, a2);
    }

    #[test]
    fn token_bits_round_trip() {
        let mut store = TokenStore::new();
        let t = store.insert(5);
        store.remove(t);
        let t = store.insert(6);
        assert_eq!(t.generation(), 2);

        let bits = t.to_bits();
        let back = Token::<i32>::from_bits(bits).unwrap();
        assert_eq!(back, t);
        assert_eq!(store[back], 6);

        // Generation zero can never come from a token.
        assert_eq!(Token::<i32>::from_bits(7), None);
    }

    #[test]
    fn forged_tokens_are_safe() {
        let mut store = TokenStore::new();
        let t = store.insert(1);
        for bits in [
            u64::MAX,
            0x1_0000_0007, // generation 1, index out of range
            0x1_0000_3039,
            (0x63 << 32) | u64::from(t.index()), // generation 99
        ] {
            if let Some(forged) = Token::<i32>::from_bits(bits) {
                assert_eq!(store.get(forged), None);
                assert_eq!(store.remove(forged), None);
            }
        }
        assert_eq!(store.get(t), Some(&1));
    }

    // ---- get_disjoint_mut ----

    #[test]
    fn get_disjoint_mut_returns_references_in_token_order() {
        let mut store = TokenStore::new();
        let first = store.insert(10);
        let second = store.insert(20);
        let third = store.insert(30);

        // Requested out of slot order.
        let [third_ref, first_ref, second_ref] =
            store.get_disjoint_mut([third, first, second]).unwrap();
        assert_eq!((*third_ref, *first_ref, *second_ref), (30, 10, 20));
        *third_ref += 1;
        *first_ref += 2;
        *second_ref += 3;
        assert_eq!((store[first], store[second], store[third]), (12, 23, 31));
    }

    #[test]
    fn get_disjoint_mut_can_swap_two_values() {
        let mut store = TokenStore::new();
        let a = store.insert(String::from("a"));
        let b = store.insert(String::from("b"));
        let [x, y] = store.get_disjoint_mut([a, b]).unwrap();
        std::mem::swap(x, y);
        assert_eq!((store[a].as_str(), store[b].as_str()), ("b", "a"));
    }

    #[test]
    fn get_disjoint_mut_rejects_stale_tokens_without_side_effects() {
        let mut store = TokenStore::new();
        let a = store.insert(1);
        let b = store.insert(2);
        store.remove(b);

        assert_eq!(
            store.get_disjoint_mut([a, b]).err(),
            Some(GetDisjointMutError::StaleToken)
        );
        assert_eq!(
            store.get_disjoint_mut([b, a]).err(),
            Some(GetDisjointMutError::StaleToken)
        );
        assert_eq!(store[a], 1);

        // A token for a reused slot is stale too.
        let b2 = store.insert(3);
        assert_eq!(b2.index(), b.index());
        assert_eq!(
            store.get_disjoint_mut([a, b]).err(),
            Some(GetDisjointMutError::StaleToken)
        );
        assert!(store.get_disjoint_mut([a, b2]).is_ok());
    }

    #[test]
    fn get_disjoint_mut_rejects_overlapping_tokens() {
        let mut store = TokenStore::new();
        let a = store.insert(1);
        let b = store.insert(2);
        assert_eq!(
            store.get_disjoint_mut([a, a]).err(),
            Some(GetDisjointMutError::OverlappingTokens)
        );
        assert_eq!(
            store.get_disjoint_mut([a, b, a]).err(),
            Some(GetDisjointMutError::OverlappingTokens)
        );
        assert_eq!((store[a], store[b]), (1, 2));
    }

    #[test]
    fn get_disjoint_mut_same_slot_old_generation_is_stale_not_overlapping() {
        let mut store = TokenStore::new();
        let old = store.insert(1);
        store.remove(old);
        let new = store.insert(2);
        assert_eq!(old.index(), new.index());
        assert_eq!(
            store.get_disjoint_mut([new, old]).err(),
            Some(GetDisjointMutError::StaleToken)
        );
    }

    #[test]
    fn get_disjoint_mut_with_zero_and_one_token() {
        let mut store = TokenStore::new();
        let a = store.insert(5);
        let [] = store.get_disjoint_mut([]).unwrap();
        let [x] = store.get_disjoint_mut([a]).unwrap();
        *x += 1;
        assert_eq!(store[a], 6);
    }

    #[test]
    fn get_disjoint_mut_error_display_and_traits() {
        assert_eq!(
            GetDisjointMutError::StaleToken.to_string(),
            "a token is stale"
        );
        assert_eq!(
            GetDisjointMutError::OverlappingTokens.to_string(),
            "two tokens refer to the same value"
        );
        let boxed: Box<dyn std::error::Error> = Box::new(GetDisjointMutError::StaleToken);
        assert_eq!(boxed.to_string(), "a token is stale");
    }

    // ---- generation exhaustion ----

    #[test]
    fn slot_with_exhausted_generation_is_retired_not_reused() {
        let mut store = TokenStore::new();
        let t = store.insert("x");
        // Age the slot to its last generation.
        store.slots[0].version = u32::MAX;
        let last = Token::new(0, Version::from_raw(u32::MAX));
        assert_eq!(store.get(t), None); // the old token no longer matches
        assert_eq!(store.get(last), Some(&"x"));

        assert_eq!(store.remove(last), Some("x"));
        // Retired: not on the free list, and the old token stays dead.
        assert_eq!(store.free_head, NONE);
        assert_eq!(store.get(last), None);
        assert_eq!(store.remove(last), None);
        assert!(store.get_mut(last).is_none());
        assert!(store.get_disjoint_mut([last]).is_err());

        // The next value gets a fresh slot instead.
        let next = store.insert("y");
        assert_eq!(next.index(), 1);
        assert_eq!(store.len(), 1);
        assert_eq!(store.slots.len(), 2);
        assert_eq!(store.get(last), None);
        assert_eq!(store.get(t), None);
    }

    #[test]
    fn tokens_are_never_issued_twice_as_a_slot_runs_out_of_generations() {
        use std::collections::HashSet;

        let mut store = TokenStore::new();
        let mut issued = HashSet::new();
        let first = store.insert(0);
        issued.insert(first);

        // Put slot 0 a few generations from the end and keep cycling it,
        // which retires it and moves on to fresh slots.
        let near_end = u32::MAX - 4; // odd, so two cycles from the end
        store.slots[0].version = near_end;
        let mut token = Token::new(0, Version::from_raw(near_end));
        assert!(issued.insert(token));
        for _ in 0..10 {
            store.remove(token);
            token = store.insert(0);
            assert!(issued.insert(token), "token {token:?} was issued twice");
        }
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn generations_advance_one_per_removal() {
        let mut store = TokenStore::new();
        let mut token = store.insert(0);
        for expected in 1..=5 {
            assert_eq!(token.generation(), expected);
            store.remove(token);
            token = store.insert(0);
        }
    }

    // ---- slot layout (union) ----

    /// Checks everything the `unsafe` code relies on about the slots.
    fn check_invariants<T>(store: &TokenStore<T>) {
        use std::collections::HashSet;

        // The version's low bit says occupied, and the count matches `len`.
        let occupied = store.slots.iter().filter(|s| s.is_occupied()).count();
        assert_eq!(occupied, store.len, "len disagrees with occupied slots");

        // The free list only visits vacant slots, each at most once...
        let mut on_list = HashSet::new();
        let mut index = store.free_head;
        while index != NONE {
            assert!(on_list.insert(index), "free list loops at {index}");
            let slot = &store.slots[index as usize];
            assert!(
                !slot.is_occupied(),
                "free list reaches occupied slot {index}"
            );
            assert_ne!(slot.version, 0, "retired slot {index} is on the free list");
            index = slot.next_free().expect("vacant slot must have a link");
        }
        // ...and every vacant slot that is not retired (version 0) is on it.
        let reusable = store
            .slots
            .iter()
            .filter(|s| !s.is_occupied() && s.version != 0)
            .count();
        assert_eq!(
            on_list.len(),
            reusable,
            "a reusable slot is off the free list"
        );
    }

    #[test]
    fn slots_are_compact() {
        assert_eq!(std::mem::size_of::<Slot<u64>>(), 16);
        assert_eq!(std::mem::size_of::<Slot<u32>>(), 8);
        assert_eq!(std::mem::size_of::<Slot<u8>>(), 8);
        assert_eq!(std::mem::size_of::<Slot<()>>(), 8);
        assert_eq!(std::mem::size_of::<Slot<[u64; 3]>>(), 32);
    }

    #[test]
    fn version_is_always_odd() {
        for raw in [0, 1, 2, 3, 4, u32::MAX - 1, u32::MAX] {
            let version = Version::from_raw(raw);
            assert_eq!(version.get() & 1, 1, "raw {raw}");
            assert!(version.get() >= raw.min(u32::MAX - 1));
        }
        assert_eq!(Version::from_raw(7).get(), 7); // odd stays as it is
        assert_eq!(Version::FIRST.get(), 1);
    }

    #[test]
    fn slot_versions_track_occupancy() {
        let mut store = TokenStore::new();
        let t = store.insert('a');
        assert_eq!(store.slots[0].version, 1); // occupied: odd
        store.remove(t);
        assert_eq!(store.slots[0].version, 2); // vacant: even
        assert_eq!(store.slots[0].next_free(), Some(NONE));
        let t = store.insert('b');
        assert_eq!(store.slots[0].version, 3);
        assert_eq!(t.generation(), 2);
        check_invariants(&store);
    }

    #[test]
    fn forged_even_version_cannot_reach_a_vacant_slot() {
        // A vacant slot's version is even. If a token could carry an even
        // version equal to it, `get` would read the free-list link as a `T`.
        let mut store = TokenStore::new();
        let t = store.insert(String::from("x"));
        store.remove(t);
        assert_eq!(store.slots[0].version, 2);

        let forged = Token::<String>::from_bits(2u64 << 32).unwrap();
        assert_eq!(forged.version.get() & 1, 1); // forced odd
        assert_eq!(store.get(forged), None);
        assert_eq!(store.remove(forged), None);
        assert!(store.get_mut(forged).is_none());
        assert!(store.get_disjoint_mut([forged]).is_err());
        check_invariants(&store);
    }

    #[test]
    fn retired_slot_drops_its_value_exactly_once() {
        let token = Rc::new(());
        let mut store = TokenStore::new();
        let first = store.insert(Rc::clone(&token));
        store.slots[0].version = u32::MAX;
        let last = Token::new(0, Version::from_raw(u32::MAX));
        assert_eq!(store.get(first), None);

        assert_eq!(live(&token), 1);
        drop(store.remove(last)); // retires the slot
        assert_eq!(live(&token), 0);
        assert_eq!(store.slots[0].version, 0);
        check_invariants(&store);

        // Dropping the store must not touch the retired slot's stale bytes.
        drop(store);
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn clone_with_vacant_and_occupied_slots_drops_correctly() {
        let token = Rc::new(());
        let mut store = TokenStore::new();
        let tokens: Vec<_> = (0..6).map(|_| store.insert(Rc::clone(&token))).collect();
        store.remove(tokens[1]);
        store.remove(tokens[4]);
        assert_eq!(live(&token), 4);

        let copy = store.clone();
        assert_eq!(live(&token), 8);
        check_invariants(&copy);
        assert_eq!(copy.len(), 4);
        assert_eq!(copy.free_head, store.free_head);

        drop(copy);
        assert_eq!(live(&token), 4);
        drop(store);
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn clone_panic_does_not_leak_or_double_drop() {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        struct PanicOnClone {
            token: Rc<()>,
            panic: bool,
        }
        impl Clone for PanicOnClone {
            fn clone(&self) -> Self {
                assert!(!self.panic, "clone failed");
                Self {
                    token: Rc::clone(&self.token),
                    panic: false,
                }
            }
        }

        let token = Rc::new(());
        let mut store = TokenStore::new();
        for i in 0..5 {
            store.insert(PanicOnClone {
                token: Rc::clone(&token),
                panic: i == 3,
            });
        }
        assert_eq!(live(&token), 5);
        let result = catch_unwind(AssertUnwindSafe(|| store.clone()));
        assert!(result.is_err());
        // Slots cloned before the panic were dropped again.
        assert_eq!(live(&token), 5);
        drop(store);
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn zero_sized_and_large_values_work() {
        let mut units = TokenStore::new();
        let a = units.insert(());
        let b = units.insert(());
        assert_eq!(units.remove(a), Some(()));
        assert_eq!(units.get(a), None);
        assert_eq!(units.get(b), Some(&()));
        check_invariants(&units);

        let mut big = TokenStore::new();
        let t = big.insert([7u64; 64]);
        big[t][63] = 9;
        assert_eq!(big.remove(t).unwrap()[63], 9);
        check_invariants(&big);
    }

    #[test]
    fn values_with_alignment_above_the_link_work() {
        #[repr(align(32))]
        #[derive(Debug, PartialEq)]
        struct Aligned(u8);

        let mut store = TokenStore::new();
        let a = store.insert(Aligned(1));
        let b = store.insert(Aligned(2));
        store.remove(a);
        let c = store.insert(Aligned(3));
        assert_eq!(store[b], Aligned(2));
        assert_eq!(store[c], Aligned(3));
        assert_eq!(&raw const store[c] as usize % 32, 0);
        check_invariants(&store);
    }

    // ---- clear / retain / drain ----

    #[test]
    fn clear_invalidates_all_tokens_permanently() {
        let mut store = TokenStore::new();
        let old: Vec<_> = (0..5).map(|i| store.insert(i)).collect();
        store.clear();
        assert!(store.is_empty());
        assert!(old.iter().all(|t| store.get(*t).is_none()));

        // Refill the same slots: old tokens must not match.
        let new: Vec<_> = (0..5).map(|i| store.insert(i + 100)).collect();
        assert_eq!(store.slots.len(), 5);
        for t in &old {
            assert_eq!(store.get(*t), None);
        }
        for (i, t) in new.iter().enumerate() {
            assert_eq!(store[*t], i32::try_from(i).unwrap() + 100);
        }
    }

    #[test]
    fn retain_keeps_matching_and_stales_the_rest() {
        let mut store = TokenStore::new();
        let tokens: Vec<_> = (0..10).map(|i| store.insert(i)).collect();
        store.retain(|_, v| {
            *v += 100;
            *v % 2 == 0
        });
        assert_eq!(store.len(), 5);
        for (i, t) in tokens.iter().enumerate() {
            if i % 2 == 0 {
                assert_eq!(store[*t], i32::try_from(i).unwrap() + 100);
            } else {
                assert_eq!(store.get(*t), None);
            }
        }
    }

    #[test]
    fn retain_receives_the_right_tokens() {
        let mut store = TokenStore::new();
        let a = store.insert("a");
        let b = store.insert("b");
        store.remove(a);
        let a2 = store.insert("a2"); // reuses slot 0 with generation 2
        let mut seen = Vec::new();
        store.retain(|token, v| {
            seen.push((token, *v));
            true
        });
        assert_eq!(seen, vec![(a2, "a2"), (b, "b")]);
    }

    #[test]
    fn drain_yields_tokens_valid_before_removal() {
        let mut store = TokenStore::new();
        let tokens: Vec<_> = (0..4).map(|i| store.insert(i * 10)).collect();
        store.remove(tokens[1]);

        let drained: Vec<_> = store.drain().collect();
        assert_eq!(
            drained,
            vec![(tokens[0], 0), (tokens[2], 20), (tokens[3], 30)]
        );
        assert!(store.is_empty());
        assert!(tokens.iter().all(|t| store.get(*t).is_none()));
        // Usable afterwards.
        let t = store.insert(1);
        assert_eq!(store[t], 1);
    }

    #[test]
    fn drain_is_exact_size_and_drop_finishes_the_job() {
        let mut store = TokenStore::new();
        (0..5).for_each(|i| {
            store.insert(i);
        });
        let mut drain = store.drain();
        assert_eq!(drain.len(), 5);
        drain.next();
        assert_eq!(drain.len(), 4);
        drop(drain);
        assert!(store.is_empty());

        // Leaking the drain leaves a consistent store.
        (0..5).for_each(|i| {
            store.insert(i);
        });
        let mut drain = store.drain();
        drain.next();
        std::mem::forget(drain);
        assert_eq!(store.len(), store.iter().count());
        let t = store.insert(99);
        assert_eq!(store[t], 99);
    }

    // ---- iteration ----

    fn sample() -> (TokenStore<i32>, Vec<Token<i32>>) {
        let mut store = TokenStore::new();
        let tokens: Vec<_> = (0..6).map(|i| store.insert(i * 10)).collect();
        store.remove(tokens[1]);
        store.remove(tokens[4]);
        (store, tokens)
    }

    #[test]
    fn iter_visits_live_values_in_slot_order_with_valid_tokens() {
        let (store, tokens) = sample();
        let items: Vec<_> = store.iter().map(|(t, v)| (t, *v)).collect();
        assert_eq!(
            items,
            vec![
                (tokens[0], 0),
                (tokens[2], 20),
                (tokens[3], 30),
                (tokens[5], 50)
            ]
        );
        for (t, v) in &store {
            assert_eq!(store[t], *v);
        }
    }

    #[test]
    fn iterators_are_exact_size_double_ended_and_fused() {
        let (mut store, tokens) = sample();

        let mut iter = store.iter();
        assert_eq!(iter.len(), 4);
        assert_eq!(iter.next_back().map(|(t, _)| t), Some(tokens[5]));
        assert_eq!(iter.next().map(|(t, _)| t), Some(tokens[0]));
        assert_eq!(iter.len(), 2);
        assert_eq!(iter.by_ref().count(), 2);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        assert_eq!(store.tokens().next_back(), Some(tokens[5]));
        assert_eq!(store.tokens().len(), 4);
        assert_eq!(
            store.values().rev().copied().collect::<Vec<_>>(),
            vec![50, 30, 20, 0]
        );
        assert_eq!(store.values_mut().len(), 4);
        assert_eq!(store.iter_mut().len(), 4);
        assert_eq!(store.clone().into_iter().len(), 4);
        assert_eq!(store.clone().into_iter().next_back(), Some((tokens[5], 50)));
    }

    #[test]
    fn iter_mut_and_values_mut_modify_in_place() {
        let (mut store, tokens) = sample();
        for (_, v) in &mut store {
            *v += 1;
        }
        for v in store.values_mut() {
            *v *= 2;
        }
        for (_, v) in &mut store {
            *v += 1;
        }
        assert_eq!(store[tokens[0]], 3);
        assert_eq!(store[tokens[5]], 103);
        assert_eq!(store.get(tokens[1]), None);
    }

    #[test]
    fn iter_stops_early_once_everything_was_seen() {
        // A long run of free slots at the end must not be scanned.
        let mut store = TokenStore::new();
        let tokens: Vec<_> = (0..100).map(|i| store.insert(i)).collect();
        for t in &tokens[1..] {
            store.remove(*t);
        }
        let mut iter = store.iter();
        assert!(iter.next().is_some());
        assert_eq!(iter.remaining, 0);
        assert!(iter.next().is_none());
    }

    #[test]
    fn into_iter_by_value() {
        let (store, tokens) = sample();
        let items: Vec<_> = store.into_iter().collect();
        assert_eq!(
            items,
            vec![
                (tokens[0], 0),
                (tokens[2], 20),
                (tokens[3], 30),
                (tokens[5], 50)
            ]
        );
    }

    #[test]
    fn iterator_clone_and_debug() {
        let mut store = TokenStore::new();
        let a = store.insert("a");
        store.insert("b");
        let iter = store.iter();
        assert_eq!(iter.clone().count(), 2);
        assert_eq!(iter.count(), 2);
        assert_eq!(
            format!("{:?}", store.iter()),
            "[(Token { .. }, \"a\"), (Token { .. }, \"b\")]"
        );
        assert_eq!(format!("{:?}", store.values()), "[\"a\", \"b\"]");
        assert_eq!(format!("{:?}", store.tokens()), "Tokens { remaining: 2 }");
        assert_eq!(
            format!("{:?}", store.iter_mut()),
            "IterMut { remaining: 2 }"
        );
        assert_eq!(
            format!("{:?}", store.clone().into_iter()),
            "IntoIter { remaining: 2 }"
        );
        assert_eq!(
            format!("{store:?}"),
            "{Token { .. }: \"a\", Token { .. }: \"b\"}"
        );
        let _ = a;
    }

    #[test]
    fn iterator_types_are_nameable() {
        type Nameable<'a> = (
            Option<super::Iter<'a, i32>>,
            Option<super::IterMut<'a, i32>>,
            Option<super::IntoIter<i32>>,
            Option<super::Drain<'a, i32>>,
            Option<super::Tokens<'a, i32>>,
            Option<super::Values<'a, i32>>,
            Option<super::ValuesMut<'a, i32>>,
        );
        let none: Nameable<'_> = Default::default();
        assert!(none.0.is_none());
    }

    // ---- other trait impls ----

    #[test]
    fn extend_default_clone_and_capacity() {
        let mut store: TokenStore<i32> = TokenStore::default();
        store.extend([1, 2, 3]);
        assert_eq!(store.len(), 3);
        assert_eq!(store.values().copied().collect::<Vec<_>>(), vec![1, 2, 3]);

        let with_cap: TokenStore<i32> = TokenStore::with_capacity(10);
        assert!(with_cap.capacity() >= 10);
        let mut reserved: TokenStore<i32> = TokenStore::new();
        reserved.reserve(10);
        assert!(reserved.capacity() >= 10);
    }

    #[test]
    fn clone_keeps_tokens_valid_and_is_independent() {
        let mut store = TokenStore::new();
        let a = store.insert(String::from("a"));
        let b = store.insert(String::from("b"));
        store.remove(a);

        let mut copy = store.clone();
        assert_eq!(copy.get(b).map(String::as_str), Some("b"));
        assert_eq!(copy.get(a), None);
        copy.get_mut(b).unwrap().push('!');
        assert_eq!(store[b], "b"); // original unaffected

        // The free list was cloned as well.
        assert_eq!(copy.insert(String::new()).index(), a.index());
    }

    // ---- drop accounting ----

    fn live(token: &Rc<()>) -> usize {
        Rc::strong_count(token) - 1
    }

    fn filled(token: &Rc<()>, n: usize) -> (TokenStore<Rc<()>>, Vec<Token<Rc<()>>>) {
        let mut store = TokenStore::new();
        let tokens = (0..n).map(|_| store.insert(Rc::clone(token))).collect();
        (store, tokens)
    }

    #[test]
    fn dropping_the_store_drops_everything() {
        let token = Rc::new(());
        let (store, _) = filled(&token, 5);
        assert_eq!(live(&token), 5);
        drop(store);
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn remove_clear_and_retain_drop_values() {
        let token = Rc::new(());
        let (mut store, tokens) = filled(&token, 6);
        drop(store.remove(tokens[0]));
        assert_eq!(live(&token), 5);
        store.retain(|t, _| t.index() % 2 == 0);
        assert_eq!(live(&token), 2); // slots 2 and 4
        store.clear();
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn drain_and_into_iter_drop_unconsumed_values() {
        let token = Rc::new(());
        let (mut store, _) = filled(&token, 5);
        let mut drain = store.drain();
        drop(drain.next());
        assert_eq!(live(&token), 4);
        drop(drain);
        assert_eq!(live(&token), 0);

        let (store, _) = filled(&token, 5);
        let mut iter = store.into_iter();
        drop(iter.next());
        assert_eq!(live(&token), 4);
        drop(iter);
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn retain_panic_leaves_a_consistent_store() {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        let token = Rc::new(());
        let (mut store, tokens) = filled(&token, 8);
        let result = catch_unwind(AssertUnwindSafe(|| {
            store.retain(|t, _| {
                assert!(t.index() != 5, "boom");
                t.index() % 2 == 0
            });
        }));
        assert!(result.is_err());

        // Slots 0..5 were processed (odd ones removed), 5.. untouched.
        assert_eq!(store.len(), store.iter().count());
        assert_eq!(live(&token), store.len());
        for t in &tokens {
            assert_eq!(store.contains(*t), t.index() % 2 == 0 || t.index() >= 5);
        }
        // Still fully usable.
        let fresh = store.insert(Rc::clone(&token));
        assert!(store.contains(fresh));
        drop(store);
        assert_eq!(live(&token), 0);
    }

    // ---- randomized model check ----

    /// Every token ever issued must agree with a model that only tracks
    /// which tokens are live -- including all the dead ones, which is what
    /// catches a slot reuse mistake (ABA).
    #[test]
    fn matches_a_model_under_random_operations() {
        struct Lcg(u64);
        impl Lcg {
            fn next(&mut self) -> u64 {
                self.0 = self
                    .0
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                self.0 >> 33
            }
        }

        let steps = if cfg!(miri) { 400 } else { 40_000 };
        let mut rng = Lcg(0xABCD_1234);
        let mut store: TokenStore<u64> = TokenStore::new();
        let mut model: HashMap<Token<u64>, u64> = HashMap::new();
        let mut issued: Vec<Token<u64>> = Vec::new();

        for step in 0..steps {
            let pick = |rng: &mut Lcg, issued: &Vec<Token<u64>>| -> Option<Token<u64>> {
                if issued.is_empty() {
                    None
                } else {
                    Some(issued[(rng.next() as usize) % issued.len()])
                }
            };
            match rng.next() % 10 {
                0..=3 => {
                    let value = rng.next();
                    let t = store.insert(value);
                    assert!(!model.contains_key(&t), "issued a live token twice");
                    model.insert(t, value);
                    issued.push(t);
                }
                4..=6 => {
                    if let Some(t) = pick(&mut rng, &issued) {
                        assert_eq!(store.remove(t), model.remove(&t));
                    }
                }
                7 => {
                    if let Some(t) = pick(&mut rng, &issued) {
                        let delta = rng.next();
                        if let (Some(a), Some(b)) = (store.get_mut(t), model.get_mut(&t)) {
                            *a = a.wrapping_add(delta);
                            *b = b.wrapping_add(delta);
                        }
                    }
                }
                8 => {
                    let modulus = 2 + rng.next() % 3;
                    store.retain(|t, v| {
                        let keep = !(*v + u64::from(t.index())).is_multiple_of(modulus);
                        if !keep {
                            model.remove(&t);
                        }
                        keep
                    });
                }
                _ => {
                    if step % 200 == 0 {
                        store.clear();
                        model.clear();
                    }
                }
            }

            assert_eq!(store.len(), model.len());
            check_invariants(&store);
            if step % 50 == 0 {
                for t in &issued {
                    assert_eq!(store.get(*t), model.get(t), "token {t:?} disagrees");
                }
            }
        }
        for t in &issued {
            assert_eq!(store.get(*t), model.get(t));
        }
        let mut from_iter: Vec<_> = store.iter().map(|(t, v)| (t, *v)).collect();
        let mut from_model: Vec<_> = model.iter().map(|(t, v)| (*t, *v)).collect();
        from_iter.sort();
        from_model.sort();
        assert_eq!(from_iter, from_model);
    }
}
