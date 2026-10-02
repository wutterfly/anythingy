//! A hash map that keeps its first few entries inline.
//!
//! See [`InlineMap`] for details.

use std::{
    borrow::Borrow,
    collections::{
        HashMap,
        hash_map::{self, RandomState},
    },
    fmt,
    hash::{BuildHasher, Hash},
    iter::{FusedIterator, Zip},
    mem::{self, ManuallyDrop, MaybeUninit},
    num::NonZeroUsize,
    ops::Index,
    ptr, slice,
};

use crate::heap_size::HeapSize;

/// A hash map that stores up to `N` entries inline, without allocating, and moves to the heap ("spills") when it
/// grows beyond that.
///
/// It behaves like a [`HashMap`], and has the same API (`get`, `insert`, `remove`, `entry`, `iter`, `retain`, ...).
/// The difference is where the entries live, and how they are found:
///
/// * While there are at most `N` entries, they are stored inside the `InlineMap` itself, and a key is found by
///   comparing it to the keys, which are next to each other. That is faster than hashing for a few keys, and
///   nothing is allocated, nothing has to be hashed, and there is no pointer to follow.
/// * The first entry beyond `N` moves all entries into a [`HashMap`]. From then on it is a plain hash map, and a key
///   is found by hashing it, no matter how many entries there are.
/// * Once spilled it stays a hash map, even if it shrinks back to `N` entries or fewer. Check with
///   [`spilled`](Self::spilled).
///
/// Pick `N` so that the inline part covers the typical number of entries: a large `N` makes every `InlineMap` (and
/// anything containing one) large, since the inline entries are part of it, and moving it around copies all `N`
/// slots. The cost of a lookup grows with `N` as well, up to the size where hashing is cheaper than comparing.
///
/// The order of the entries is as unspecified as for a [`HashMap`]. Removing an entry from an inline map moves the
/// last one into its place.
///
/// Like [`HashMap`], it takes the hasher as a type parameter. Use [`InlineMap::with_hasher`] for a cheaper hasher
/// than the default one if the keys are already well distributed.
///
/// # Examples
///
/// ```
/// use anythingy::InlineMap;
///
/// let mut map: InlineMap<&str, u32, 2> = InlineMap::new();
/// map.insert("a", 1);
/// map.insert("b", 2);
/// assert!(!map.spilled()); // both are inline
///
/// map.insert("c", 3); // one past the inline capacity
/// assert!(map.spilled());
///
/// assert_eq!(map.get("a"), Some(&1));
/// assert_eq!(map.get("c"), Some(&3));
/// assert_eq!(map.len(), 3);
/// ```
pub struct InlineMap<K, V, const N: usize, S = RandomState> {
    repr: Repr<K, V, N, S>,
}

/// Where the entries are.
enum Repr<K, V, const N: usize, S> {
    Inline(Inline<K, V, N, S>),
    Heap(HashMap<K, V, S>),
}

/// The inline entries of a map that did not spill.
///
/// # Invariants
///
/// - `len <= N`.
/// - Exactly `keys[..len]` and `values[..len]` are initialized, and owned by this struct. `values[i]` belongs to
///   `keys[i]`.
/// - No key is in the map twice.
/// - `hasher` is initialized, and owned by this struct, unless it was moved out to a hash map: that only happens
///   when the whole `Inline` is thrown away without dropping it (see [`InlineMap::spill`]).
// `repr(C)` keeps the length right in front of the keys, so the first keys a lookup compares are in the cache line
// that the length was just read from.
#[repr(C)]
struct Inline<K, V, const N: usize, S> {
    len: Len,

    /// Kept apart from the values, so that finding a key only reads keys, which are small, and not the (possibly
    /// large) values next to them.
    keys: [MaybeUninit<K>; N],
    values: [MaybeUninit<V>; N],

    /// Only to be given to the hash map, if the map spills.
    hasher: ManuallyDrop<S>,
}

/// The number of entries of an [`Inline`], stored as one more than it is, which makes it a number that is never zero.
///
/// That is all it is for: the compiler can then use the value zero of this field to tell that a map spilled, and store
/// both kinds of map in the same space, instead of adding a tag that tells them apart. That saves 8 bytes for most sizes
/// of `N`.
#[derive(Clone, Copy)]
struct Len(NonZeroUsize);

impl Len {
    /// No entries.
    const ZERO: Self = Self(NonZeroUsize::MIN);

    /// A number of entries, which is the number of the entries that are in an array, so it is far below `usize::MAX`
    /// in any map that can exist. If it was not, this panics, and does not produce a length that is wrong.
    #[inline]
    const fn new(len: usize) -> Self {
        match NonZeroUsize::new(len.wrapping_add(1)) {
            Some(stored) => Self(stored),
            None => panic!("too many entries"),
        }
    }

    #[inline]
    const fn get(self) -> usize {
        self.0.get() - 1
    }
}

/// The smallest number of entries for which the keys are searched block by block. Below this, stopping at the first match
/// is faster.
const BLOCK_SEARCH_MIN_LEN: usize = 16;

/// The number of keys that the block-wise search compares in one step.
const BLOCK: usize = 8;

/// The index of the key among `keys`, comparing [`BLOCK`] keys per step without stopping early inside a block, so that
/// the compiler can turn the comparison into a vector operation. Only worth it for cheap keys, see
/// `Inline::CHEAP_KEYS`.
///
/// Kept out of line on purpose: inlined, it makes `position` big enough that the plain scan used for few entries is no
/// longer inlined into its callers, which makes small maps slower.
#[inline(never)]
fn block_position<K, Q>(keys: &[K], key: &Q) -> Option<usize>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    let (blocks, rest) = keys.as_chunks::<BLOCK>();

    for (i, block) in blocks.iter().enumerate() {
        let mut found = false;
        for k in block {
            found |= k.borrow() == key;
        }

        if found {
            return block
                .iter()
                .position(|k| k.borrow() == key)
                .map(|offset| i * BLOCK + offset);
        }
    }

    rest.iter()
        .position(|k| k.borrow() == key)
        .map(|i| blocks.len() * BLOCK + i)
}

/// Drops `len` keys and `len` values, and all of them, even if dropping one panics (the panic goes on afterwards).
///
/// # Safety
///
/// `keys[..len]` and `values[..len]` have to be initialized, owned by the caller, and not used again.
unsafe fn drop_entries<K, V>(keys: *mut K, values: *mut V, len: usize) {
    /// Drops the values when it goes out of scope, which also happens if dropping a key panics.
    struct DropValues<V>(*mut V, usize);

    impl<V> Drop for DropValues<V> {
        fn drop(&mut self) {
            // SAFETY: guaranteed by the caller of `drop_entries`.
            unsafe { ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.0, self.1)) };
        }
    }

    let _values = DropValues(values, len);

    // SAFETY: guaranteed by the caller.
    unsafe { ptr::drop_in_place(ptr::slice_from_raw_parts_mut(keys, len)) };
}

impl<K, V, const N: usize, S> Inline<K, V, N, S> {
    #[inline]
    const fn new(hasher: S) -> Self {
        Self {
            len: Len::ZERO,
            keys: [const { MaybeUninit::uninit() }; N],
            values: [const { MaybeUninit::uninit() }; N],
            hasher: ManuallyDrop::new(hasher),
        }
    }

    /// The number of entries.
    #[inline]
    const fn len(&self) -> usize {
        self.len.get()
    }

    #[inline]
    const fn set_len(&mut self, len: usize) {
        self.len = Len::new(len);
    }

    #[inline]
    const fn keys(&self) -> &[K] {
        // SAFETY: `keys[..len]` is initialized (see the invariants), and `MaybeUninit<K>` has the layout of `K`.
        unsafe { slice::from_raw_parts(self.keys.as_ptr().cast::<K>(), self.len()) }
    }

    #[inline]
    const fn values(&self) -> &[V] {
        // SAFETY: `values[..len]` is initialized (see the invariants), and `MaybeUninit<V>` has the layout of `V`.
        unsafe { slice::from_raw_parts(self.values.as_ptr().cast::<V>(), self.len()) }
    }

    #[inline]
    const fn values_mut(&mut self) -> &mut [V] {
        // SAFETY: as in `values`, and `&mut self` makes this the only reference to them.
        unsafe { slice::from_raw_parts_mut(self.values.as_mut_ptr().cast::<V>(), self.len()) }
    }

    /// The keys, and the values (which can be changed) at the same time.
    #[inline]
    const fn entries_mut(&mut self) -> (&[K], &mut [V]) {
        let len = self.len();

        // SAFETY: as in `keys` and `values_mut`. They are different fields, so the two slices do not overlap.
        unsafe {
            (
                slice::from_raw_parts(self.keys.as_ptr().cast::<K>(), len),
                slice::from_raw_parts_mut(self.values.as_mut_ptr().cast::<V>(), len),
            )
        }
    }

    /// Whether keys of this type are cheap enough to compare that checking a whole block of them at once beats
    /// stopping at the first match: small plain-data keys (integers, `char`, small enums, ...), and not anything that
    /// owns data or is wider than a pointer, where the extra comparisons cost more than the vectorization saves.
    const CHEAP_KEYS: bool = !mem::needs_drop::<K>() && mem::size_of::<K>() <= 8;

    /// The index of the key, if it is in the map.
    #[inline]
    fn position<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        let keys = self.keys();

        if Self::CHEAP_KEYS && keys.len() >= BLOCK_SEARCH_MIN_LEN {
            return block_position(keys, key);
        }

        keys.iter().position(|k| k.borrow() == key)
    }

    /// Adds an entry. The key must not be in the map yet, and there has to be room.
    #[inline]
    fn push(&mut self, key: K, value: V) -> &mut V {
        debug_assert!(self.len() < N, "there has to be room");

        let i = self.len();

        // SAFETY: `i < N`, as the caller made sure there is room.
        let (key_slot, value_slot) = unsafe {
            (
                self.keys.get_unchecked_mut(i),
                self.values.get_unchecked_mut(i),
            )
        };
        key_slot.write(key);
        let value = value_slot.write(value);

        // Only now, so that an entry that is half written is never counted. Neither `write` can panic.
        self.len = Len::new(i + 1);

        value
    }

    /// Removes the entry at the index, and moves the last entry into its place.
    #[inline]
    fn remove_at(&mut self, index: usize) -> (K, V) {
        let len = self.len();
        assert!(index < len, "index out of bounds");

        let last = len - 1;
        let keys = self.keys.as_mut_ptr().cast::<K>();
        let values = self.values.as_mut_ptr().cast::<V>();

        // SAFETY: `index <= last < len`, so the entries at both are initialized. The entry at `index` is moved out,
        // and its place is filled with the last one (which is not the same slot then, so they do not overlap), or
        // is just given up, if it was the last one. Either way, `len` is lowered afterwards, so no entry is owned
        // twice, and the one that was moved out is not owned by the map any more.
        unsafe {
            let entry = (ptr::read(keys.add(index)), ptr::read(values.add(index)));

            if index != last {
                ptr::copy_nonoverlapping(keys.add(last), keys.add(index), 1);
                ptr::copy_nonoverlapping(values.add(last), values.add(index), 1);
            }

            self.set_len(last);
            entry
        }
    }

    /// Drops all entries.
    fn clear(&mut self) {
        // set first, so that nothing is dropped twice if dropping an entry panics: the others are leaked then
        let len = self.len();
        self.set_len(0);

        // SAFETY: `keys[..len]` and `values[..len]` are initialized and owned (see the invariants), and nothing
        // looks at them again, since `len` is `0` now.
        unsafe {
            drop_entries(
                self.keys.as_mut_ptr().cast::<K>(),
                self.values.as_mut_ptr().cast::<V>(),
                len,
            );
        }
    }
}

impl<K, V, const N: usize, S> Drop for Inline<K, V, N, S> {
    fn drop(&mut self) {
        // SAFETY: the hasher is initialized and owned (see the invariants), and not used again.
        unsafe { ManuallyDrop::drop(&mut self.hasher) };

        self.clear();
    }
}

impl<K, V, const N: usize> InlineMap<K, V, N, RandomState> {
    /// Creates an empty map, which uses the default hasher. It does not allocate.
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::with_hasher(RandomState::new())
    }

    /// Creates an empty map with room for at least `capacity` entries, which uses the default hasher. It only
    /// allocates if `capacity` is more than `N`.
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, RandomState::new())
    }
}

impl<K, V, const N: usize, S> InlineMap<K, V, N, S> {
    /// Creates an empty map, which uses the given hasher. It does not allocate.
    #[inline]
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            repr: Repr::Inline(Inline::new(hash_builder)),
        }
    }

    /// Creates an empty map with room for at least `capacity` entries, which uses the given hasher. It only
    /// allocates if `capacity` is more than `N`.
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        if capacity <= N {
            Self::with_hasher(hash_builder)
        } else {
            Self {
                repr: Repr::Heap(HashMap::with_capacity_and_hasher(capacity, hash_builder)),
            }
        }
    }

    /// Returns the number of entries the map can hold without allocating, or without allocating more, once it
    /// spilled.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        match &self.repr {
            Repr::Inline(_) => N,
            Repr::Heap(map) => map.capacity(),
        }
    }

    /// Returns the number of entries.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        match &self.repr {
            Repr::Inline(inline) => inline.len(),
            Repr::Heap(map) => map.len(),
        }
    }

    /// Returns `true` if there are no entries.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the entries are in a hash map, which is the case once there were more than `N`.
    #[inline]
    #[must_use]
    pub const fn spilled(&self) -> bool {
        matches!(self.repr, Repr::Heap(_))
    }

    /// Returns the hasher.
    #[inline]
    #[must_use]
    pub fn hasher(&self) -> &S {
        match &self.repr {
            Repr::Inline(inline) => &inline.hasher,
            Repr::Heap(map) => map.hasher(),
        }
    }

    /// Iterates over the entries, in no particular order.
    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter(match &self.repr {
            Repr::Inline(inline) => IterRepr::Inline(inline.keys().iter().zip(inline.values())),
            Repr::Heap(map) => IterRepr::Heap(map.iter()),
        })
    }

    /// Iterates over the entries, in no particular order, and lets the values be changed.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut(match &mut self.repr {
            Repr::Inline(inline) => {
                let (keys, values) = inline.entries_mut();
                IterMutRepr::Inline(keys.iter().zip(values.iter_mut()))
            }
            Repr::Heap(map) => IterMutRepr::Heap(map.iter_mut()),
        })
    }

    /// Iterates over the keys, in no particular order.
    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys(match &self.repr {
            Repr::Inline(inline) => KeysRepr::Inline(inline.keys().iter()),
            Repr::Heap(map) => KeysRepr::Heap(map.keys()),
        })
    }

    /// Iterates over the values, in no particular order.
    #[inline]
    pub fn values(&self) -> Values<'_, K, V> {
        Values(match &self.repr {
            Repr::Inline(inline) => ValuesRepr::Inline(inline.values().iter()),
            Repr::Heap(map) => ValuesRepr::Heap(map.values()),
        })
    }

    /// Iterates over the values, in no particular order, and lets them be changed.
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut(match &mut self.repr {
            Repr::Inline(inline) => ValuesMutRepr::Inline(inline.values_mut().iter_mut()),
            Repr::Heap(map) => ValuesMutRepr::Heap(map.values_mut()),
        })
    }

    /// Creates an iterator over the keys, which takes them out of the map.
    #[inline]
    #[must_use]
    pub fn into_keys(self) -> IntoKeys<K, V, N> {
        IntoKeys(self.into_iter())
    }

    /// Creates an iterator over the values, which takes them out of the map.
    #[inline]
    #[must_use]
    pub fn into_values(self) -> IntoValues<K, V, N> {
        IntoValues(self.into_iter())
    }

    /// Removes all entries. A map that spilled keeps its allocation, and stays a hash map.
    pub fn clear(&mut self) {
        match &mut self.repr {
            Repr::Inline(inline) => inline.clear(),
            Repr::Heap(map) => map.clear(),
        }
    }

    /// Keeps only the entries for which the function returns `true`, and removes the others.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        match &mut self.repr {
            Repr::Inline(inline) => {
                let mut i = 0;

                while i < inline.len() {
                    let keep = {
                        let (keys, values) = inline.entries_mut();
                        f(&keys[i], &mut values[i])
                    };

                    if keep {
                        i += 1;
                    } else {
                        // The last entry is moved to `i`, so it is the next one to look at. The map is consistent
                        // at every point where user code runs (`f`, and the drop of the entry that was removed).
                        drop(inline.remove_at(i));
                    }
                }
            }
            Repr::Heap(map) => map.retain(f),
        }
    }

    /// The inline part of a map that did not spill.
    #[inline]
    fn inline_ref(&self) -> &Inline<K, V, N, S> {
        match &self.repr {
            Repr::Inline(inline) => inline,
            Repr::Heap(_) => unreachable!("the map spilled"),
        }
    }

    #[inline]
    fn inline_mut(&mut self) -> &mut Inline<K, V, N, S> {
        match &mut self.repr {
            Repr::Inline(inline) => inline,
            Repr::Heap(_) => unreachable!("the map spilled"),
        }
    }

    /// The hash map of a map that spilled.
    #[inline]
    fn heap_mut(&mut self) -> &mut HashMap<K, V, S> {
        match &mut self.repr {
            Repr::Heap(map) => map,
            Repr::Inline(_) => unreachable!("the map did not spill"),
        }
    }
}

impl<K: Eq + Hash, V, const N: usize, S: BuildHasher> InlineMap<K, V, N, S> {
    /// Moves all entries into a hash map, with room for at least `capacity` entries. Does nothing if the map
    /// spilled already.
    #[cold]
    fn spill(&mut self, capacity: usize) {
        let Repr::Inline(inline) = &mut self.repr else {
            return;
        };

        let len = inline.len();

        // SAFETY: the hasher is moved to the hash map, and `inline` is never dropped (see below), so it is not
        // dropped twice. Nothing can panic between here and where `inline` is wrapped in `ManuallyDrop`.
        let hasher = unsafe { ManuallyDrop::into_inner(ptr::read(&raw const inline.hasher)) };
        let map = HashMap::with_capacity_and_hasher(capacity.max(len), hasher);

        // SAFETY: the inline part is replaced by the (empty) hash map, and what was in it is wrapped in
        // `ManuallyDrop`: the entries are moved out below, so they must not be dropped with it (and if hashing one
        // of the keys panics, the ones that were not moved yet are leaked, and not dropped twice), and the hasher
        // was moved out above.
        let old = ManuallyDrop::new(unsafe { ptr::replace(&raw mut self.repr, Repr::Heap(map)) });

        let (Repr::Inline(old), Repr::Heap(map)) = (&*old, &mut self.repr) else {
            unreachable!("the map was inline, and is a hash map now");
        };

        let keys = old.keys.as_ptr().cast::<K>();
        let values = old.values.as_ptr().cast::<V>();

        for i in 0..len {
            // SAFETY: `i < len`, so both are initialized, and each entry is only read once.
            let (key, value) = unsafe { (ptr::read(keys.add(i)), ptr::read(values.add(i))) };
            map.insert(key, value);
        }
    }

    /// Reserves room for at least `additional` more entries. This spills the map if it does not fit inline.
    pub fn reserve(&mut self, additional: usize) {
        match &mut self.repr {
            Repr::Inline(inline) => {
                let needed = inline.len().saturating_add(additional);

                if needed > N {
                    self.spill(needed);
                }
            }
            Repr::Heap(map) => map.reserve(additional),
        }
    }

    /// Shrinks the allocation of a map that spilled as much as possible. It stays a hash map.
    pub fn shrink_to_fit(&mut self) {
        if let Repr::Heap(map) = &mut self.repr {
            map.shrink_to_fit();
        }
    }

    /// Returns the value of the key, if there is one.
    #[inline]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match &self.repr {
            Repr::Inline(inline) => inline.position(key).map(|i| {
                // SAFETY: `position` only returns indices below `len`, and there are as many values as keys.
                unsafe { inline.values().get_unchecked(i) }
            }),
            Repr::Heap(map) => map.get(key),
        }
    }

    /// Returns the key and the value of the key, if there is one.
    #[inline]
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match &self.repr {
            Repr::Inline(inline) => inline.position(key).map(|i| {
                // SAFETY: as in `get`.
                unsafe {
                    (
                        inline.keys().get_unchecked(i),
                        inline.values().get_unchecked(i),
                    )
                }
            }),
            Repr::Heap(map) => map.get_key_value(key),
        }
    }

    /// Returns the value of the key, if there is one, and lets it be changed.
    #[inline]
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match &mut self.repr {
            Repr::Inline(inline) => {
                let i = inline.position(key)?;

                // SAFETY: as in `get`.
                Some(unsafe { inline.values_mut().get_unchecked_mut(i) })
            }
            Repr::Heap(map) => map.get_mut(key),
        }
    }

    /// Returns `true` if there is a value for the key.
    #[inline]
    #[must_use]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match &self.repr {
            Repr::Inline(inline) => inline.position(key).is_some(),
            Repr::Heap(map) => map.contains_key(key),
        }
    }

    /// Inserts a value for the key, and returns the value it had before, if there was one. A key that is already
    /// in the map is not replaced, only its value.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if let Repr::Inline(inline) = &mut self.repr {
            if let Some(i) = inline.position(&key) {
                // SAFETY: as in `get`.
                let old = unsafe { inline.values_mut().get_unchecked_mut(i) };
                return Some(mem::replace(old, value));
            }

            if inline.len() < N {
                inline.push(key, value);
                return None;
            }

            self.spill(N + 1);
        }

        self.heap_mut().insert(key, value)
    }

    /// Removes the key from the map, and returns its value, if there was one.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.remove_entry(key).map(|(_, value)| value)
    }

    /// Removes the key from the map, and returns the key and its value, if there was one.
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match &mut self.repr {
            Repr::Inline(inline) => {
                let i = inline.position(key)?;
                Some(inline.remove_at(i))
            }
            Repr::Heap(map) => map.remove_entry(key),
        }
    }

    /// Gets the entry of the key, to inspect it, or to insert a value for it if there is none.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, N, S> {
        // Looked at first, with a shared borrow that has ended before `self` is
        // handed to the entry. Older compilers do not accept the same thing
        // written as one `match` on `&mut self.repr`.
        if let Repr::Inline(inline) = &self.repr {
            let position = inline.position(&key);
            let has_room = inline.len() < N;

            return match position {
                Some(index) => {
                    Entry::Occupied(OccupiedEntry(OccupiedRepr::Inline { map: self, index }))
                }
                None if has_room => Entry::Vacant(VacantEntry(VacantRepr::Room(self, key))),
                None => Entry::Vacant(VacantEntry(VacantRepr::Full(self, key))),
            };
        }

        match self.heap_mut().entry(key) {
            hash_map::Entry::Occupied(entry) => {
                Entry::Occupied(OccupiedEntry(OccupiedRepr::Heap(entry)))
            }
            hash_map::Entry::Vacant(entry) => Entry::Vacant(VacantEntry(VacantRepr::Heap(entry))),
        }
    }
}

// ############################
// Entry
// ############################

/// The entry of a key in an [`InlineMap`], see [`InlineMap::entry`].
pub enum Entry<'a, K, V, const N: usize, S> {
    /// The key is in the map.
    Occupied(OccupiedEntry<'a, K, V, N, S>),
    /// The key is not in the map.
    Vacant(VacantEntry<'a, K, V, N, S>),
}

/// An entry of a key that is in the map.
pub struct OccupiedEntry<'a, K, V, const N: usize, S>(OccupiedRepr<'a, K, V, N, S>);

enum OccupiedRepr<'a, K, V, const N: usize, S> {
    /// `index` is the index of the key in the inline part of `map`, which did not change since.
    Inline {
        map: &'a mut InlineMap<K, V, N, S>,
        index: usize,
    },
    Heap(hash_map::OccupiedEntry<'a, K, V>),
}

/// An entry of a key that is not in the map.
pub struct VacantEntry<'a, K, V, const N: usize, S>(VacantRepr<'a, K, V, N, S>);

enum VacantRepr<'a, K, V, const N: usize, S> {
    /// The map is inline, and there is room for another entry.
    Room(&'a mut InlineMap<K, V, N, S>, K),
    /// The map is inline, and full: inserting spills it.
    Full(&'a mut InlineMap<K, V, N, S>, K),
    Heap(hash_map::VacantEntry<'a, K, V>),
}

impl<'a, K: Eq + Hash, V, const N: usize, S: BuildHasher> Entry<'a, K, V, N, S> {
    /// Returns the value of the entry, after inserting the given one if it was vacant.
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        self.or_insert_with(|| default)
    }

    /// Returns the value of the entry, after inserting the one that `make` creates if it was vacant. `make` is
    /// only called if it was, and if it panics, the map is left as it was.
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, make: F) -> &'a mut V {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => entry.insert(make()),
        }
    }

    /// Like [`Entry::or_insert_with`], but `make` gets the key.
    #[inline]
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, make: F) -> &'a mut V {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => {
                let value = make(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Returns the value of the entry, after inserting the default one if it was vacant.
    #[inline]
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }

    /// Changes the value of the entry, if it is occupied, before anything else is done with it.
    #[inline]
    #[must_use]
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Self::Occupied(mut entry) => {
                f(entry.get_mut());
                Self::Occupied(entry)
            }
            Self::Vacant(entry) => Self::Vacant(entry),
        }
    }

    /// Returns the key of the entry.
    #[inline]
    #[must_use]
    pub fn key(&self) -> &K {
        match self {
            Self::Occupied(entry) => entry.key(),
            Self::Vacant(entry) => entry.key(),
        }
    }
}

impl<'a, K, V, const N: usize, S> OccupiedEntry<'a, K, V, N, S> {
    /// Returns the key of the entry.
    #[inline]
    #[must_use]
    pub fn key(&self) -> &K {
        match &self.0 {
            // SAFETY: `index` is the index of a key in the map (see `OccupiedRepr`).
            OccupiedRepr::Inline { map, index } => unsafe {
                map.inline_ref().keys().get_unchecked(*index)
            },
            OccupiedRepr::Heap(entry) => entry.key(),
        }
    }

    /// Returns the value of the entry.
    #[inline]
    #[must_use]
    pub fn get(&self) -> &V {
        match &self.0 {
            // SAFETY: as in `key`.
            OccupiedRepr::Inline { map, index } => unsafe {
                map.inline_ref().values().get_unchecked(*index)
            },
            OccupiedRepr::Heap(entry) => entry.get(),
        }
    }

    /// Returns the value of the entry, and lets it be changed.
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        match &mut self.0 {
            // SAFETY: as in `key`.
            OccupiedRepr::Inline { map, index } => unsafe {
                map.inline_mut().values_mut().get_unchecked_mut(*index)
            },
            OccupiedRepr::Heap(entry) => entry.get_mut(),
        }
    }

    /// Returns the value of the entry, and lets it be changed for as long as the map is borrowed.
    #[inline]
    #[must_use]
    pub fn into_mut(self) -> &'a mut V {
        match self.0 {
            // SAFETY: as in `key`.
            OccupiedRepr::Inline { map, index } => unsafe {
                map.inline_mut().values_mut().get_unchecked_mut(index)
            },
            OccupiedRepr::Heap(entry) => entry.into_mut(),
        }
    }

    /// Replaces the value of the entry, and returns the old one.
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Removes the entry from the map, and returns its value.
    #[inline]
    #[must_use]
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Removes the entry from the map, and returns its key and value.
    #[inline]
    #[must_use]
    pub fn remove_entry(self) -> (K, V) {
        match self.0 {
            OccupiedRepr::Inline { map, index } => map.inline_mut().remove_at(index),
            OccupiedRepr::Heap(entry) => entry.remove_entry(),
        }
    }
}

impl<'a, K: Eq + Hash, V, const N: usize, S: BuildHasher> VacantEntry<'a, K, V, N, S> {
    /// Inserts the value for the key of the entry, and returns it.
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        match self.0 {
            VacantRepr::Room(map, key) => map.inline_mut().push(key, value),
            VacantRepr::Full(map, key) => {
                map.spill(N + 1);

                match map.heap_mut().entry(key) {
                    hash_map::Entry::Vacant(entry) => entry.insert(value),
                    hash_map::Entry::Occupied(_) => unreachable!("the key was not in the map"),
                }
            }
            VacantRepr::Heap(entry) => entry.insert(value),
        }
    }
}

impl<K, V, const N: usize, S> VacantEntry<'_, K, V, N, S> {
    /// Returns the key of the entry.
    #[inline]
    #[must_use]
    pub fn key(&self) -> &K {
        match &self.0 {
            VacantRepr::Room(_, key) | VacantRepr::Full(_, key) => key,
            VacantRepr::Heap(entry) => entry.key(),
        }
    }

    /// Takes the key of the entry.
    #[inline]
    #[must_use]
    pub fn into_key(self) -> K {
        match self.0 {
            VacantRepr::Room(_, key) | VacantRepr::Full(_, key) => key,
            VacantRepr::Heap(entry) => entry.into_key(),
        }
    }
}

// ############################
// Iterators
// ############################

/// An iterator over the entries of an [`InlineMap`], see [`InlineMap::iter`].
pub struct Iter<'a, K, V>(IterRepr<'a, K, V>);

enum IterRepr<'a, K, V> {
    Inline(Zip<slice::Iter<'a, K>, slice::Iter<'a, V>>),
    Heap(hash_map::Iter<'a, K, V>),
}

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Self(match &self.0 {
            IterRepr::Inline(iter) => IterRepr::Inline(iter.clone()),
            IterRepr::Heap(iter) => IterRepr::Heap(iter.clone()),
        })
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IterRepr::Inline(iter) => iter.next(),
            IterRepr::Heap(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            IterRepr::Inline(iter) => iter.size_hint(),
            IterRepr::Heap(iter) => iter.size_hint(),
        }
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {}
impl<K, V> FusedIterator for Iter<'_, K, V> {}

/// An iterator over the entries of an [`InlineMap`], which lets the values be changed, see [`InlineMap::iter_mut`].
pub struct IterMut<'a, K, V>(IterMutRepr<'a, K, V>);

enum IterMutRepr<'a, K, V> {
    Inline(Zip<slice::Iter<'a, K>, slice::IterMut<'a, V>>),
    Heap(hash_map::IterMut<'a, K, V>),
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IterMutRepr::Inline(iter) => iter.next(),
            IterMutRepr::Heap(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            IterMutRepr::Inline(iter) => iter.size_hint(),
            IterMutRepr::Heap(iter) => iter.size_hint(),
        }
    }
}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {}
impl<K, V> FusedIterator for IterMut<'_, K, V> {}

/// An iterator over the keys of an [`InlineMap`], see [`InlineMap::keys`].
pub struct Keys<'a, K, V>(KeysRepr<'a, K, V>);

enum KeysRepr<'a, K, V> {
    Inline(slice::Iter<'a, K>),
    Heap(hash_map::Keys<'a, K, V>),
}

impl<K, V> Clone for Keys<'_, K, V> {
    fn clone(&self) -> Self {
        Self(match &self.0 {
            KeysRepr::Inline(iter) => KeysRepr::Inline(iter.clone()),
            KeysRepr::Heap(iter) => KeysRepr::Heap(iter.clone()),
        })
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            KeysRepr::Inline(iter) => iter.next(),
            KeysRepr::Heap(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            KeysRepr::Inline(iter) => iter.size_hint(),
            KeysRepr::Heap(iter) => iter.size_hint(),
        }
    }
}

impl<K, V> ExactSizeIterator for Keys<'_, K, V> {}
impl<K, V> FusedIterator for Keys<'_, K, V> {}

/// An iterator over the values of an [`InlineMap`], see [`InlineMap::values`].
pub struct Values<'a, K, V>(ValuesRepr<'a, K, V>);

enum ValuesRepr<'a, K, V> {
    Inline(slice::Iter<'a, V>),
    Heap(hash_map::Values<'a, K, V>),
}

impl<K, V> Clone for Values<'_, K, V> {
    fn clone(&self) -> Self {
        Self(match &self.0 {
            ValuesRepr::Inline(iter) => ValuesRepr::Inline(iter.clone()),
            ValuesRepr::Heap(iter) => ValuesRepr::Heap(iter.clone()),
        })
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            ValuesRepr::Inline(iter) => iter.next(),
            ValuesRepr::Heap(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            ValuesRepr::Inline(iter) => iter.size_hint(),
            ValuesRepr::Heap(iter) => iter.size_hint(),
        }
    }
}

impl<K, V> ExactSizeIterator for Values<'_, K, V> {}
impl<K, V> FusedIterator for Values<'_, K, V> {}

/// An iterator over the values of an [`InlineMap`], which lets them be changed, see [`InlineMap::values_mut`].
pub struct ValuesMut<'a, K, V>(ValuesMutRepr<'a, K, V>);

enum ValuesMutRepr<'a, K, V> {
    Inline(slice::IterMut<'a, V>),
    Heap(hash_map::ValuesMut<'a, K, V>),
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            ValuesMutRepr::Inline(iter) => iter.next(),
            ValuesMutRepr::Heap(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            ValuesMutRepr::Inline(iter) => iter.size_hint(),
            ValuesMutRepr::Heap(iter) => iter.size_hint(),
        }
    }
}

impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {}
impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

/// An iterator over the entries of an [`InlineMap`], which takes them out of it, see [`IntoIterator`].
pub struct IntoIter<K, V, const N: usize>(IntoIterRepr<K, V, N>);

enum IntoIterRepr<K, V, const N: usize> {
    Inline(InlineIntoIter<K, V, N>),
    Heap(hash_map::IntoIter<K, V>),
}

/// The entries of a map that did not spill, which were moved out of it.
///
/// # Invariants
///
/// Exactly `keys[pos..len]` and `values[pos..len]` are initialized, and owned by this struct.
struct InlineIntoIter<K, V, const N: usize> {
    keys: [MaybeUninit<K>; N],
    values: [MaybeUninit<V>; N],
    pos: usize,
    len: usize,
}

impl<K, V, const N: usize> Drop for InlineIntoIter<K, V, N> {
    fn drop(&mut self) {
        let (pos, len) = (self.pos, self.len);
        self.pos = len;

        // SAFETY: `keys[pos..len]` and `values[pos..len]` are initialized and owned (see the invariants), and
        // nothing looks at them again, since `pos == len` now.
        unsafe {
            drop_entries(
                self.keys.as_mut_ptr().cast::<K>().add(pos),
                self.values.as_mut_ptr().cast::<V>().add(pos),
                len - pos,
            );
        }
    }
}

impl<K, V, const N: usize> Iterator for IntoIter<K, V, N> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IntoIterRepr::Inline(iter) => {
                if iter.pos == iter.len {
                    return None;
                }

                let i = iter.pos;
                iter.pos += 1;

                // SAFETY: `i` was in `pos..len`, so both are initialized, and `pos` is past them now: each entry
                // is only read once.
                Some(unsafe {
                    (
                        iter.keys.get_unchecked(i).assume_init_read(),
                        iter.values.get_unchecked(i).assume_init_read(),
                    )
                })
            }
            IntoIterRepr::Heap(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            IntoIterRepr::Inline(iter) => {
                let left = iter.len - iter.pos;
                (left, Some(left))
            }
            IntoIterRepr::Heap(iter) => iter.size_hint(),
        }
    }
}

impl<K, V, const N: usize> ExactSizeIterator for IntoIter<K, V, N> {}
impl<K, V, const N: usize> FusedIterator for IntoIter<K, V, N> {}

/// An iterator over the keys of an [`InlineMap`], which takes them out of it, see [`InlineMap::into_keys`].
pub struct IntoKeys<K, V, const N: usize>(IntoIter<K, V, N>);

impl<K, V, const N: usize> Iterator for IntoKeys<K, V, N> {
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(key, _)| key)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V, const N: usize> ExactSizeIterator for IntoKeys<K, V, N> {}
impl<K, V, const N: usize> FusedIterator for IntoKeys<K, V, N> {}

/// An iterator over the values of an [`InlineMap`], which takes them out of it, see [`InlineMap::into_values`].
pub struct IntoValues<K, V, const N: usize>(IntoIter<K, V, N>);

impl<K, V, const N: usize> Iterator for IntoValues<K, V, N> {
    type Item = V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, value)| value)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V, const N: usize> ExactSizeIterator for IntoValues<K, V, N> {}
impl<K, V, const N: usize> FusedIterator for IntoValues<K, V, N> {}

impl<'a, K, V, const N: usize, S> IntoIterator for &'a InlineMap<K, V, N, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V, const N: usize, S> IntoIterator for &'a mut InlineMap<K, V, N, S> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K, V, const N: usize, S> IntoIterator for InlineMap<K, V, N, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, N>;

    fn into_iter(self) -> Self::IntoIter {
        // the map is taken apart below, so it must not be dropped as a whole
        let map = ManuallyDrop::new(self);

        // SAFETY: `map` is never used or dropped again, so `repr` is only owned by the copy.
        match unsafe { ptr::read(&raw const map.repr) } {
            Repr::Inline(inline) => {
                // the same goes for this: it is taken apart, not dropped
                let mut inline = ManuallyDrop::new(inline);

                // SAFETY: the hasher is initialized and owned (see the invariants), and not used again.
                unsafe { ManuallyDrop::drop(&mut inline.hasher) };

                // SAFETY: the entries are moved to the iterator, and `inline` is never dropped, so it does not own
                // them any more.
                let (keys, values) = unsafe {
                    (
                        ptr::read(&raw const inline.keys),
                        ptr::read(&raw const inline.values),
                    )
                };

                IntoIter(IntoIterRepr::Inline(InlineIntoIter {
                    keys,
                    values,
                    pos: 0,
                    len: inline.len(),
                }))
            }
            Repr::Heap(map) => IntoIter(IntoIterRepr::Heap(map.into_iter())),
        }
    }
}

// ############################
// Traits
// ############################

impl<K, V, const N: usize, S: Default> Default for InlineMap<K, V, N, S> {
    #[inline]
    fn default() -> Self {
        Self::with_hasher(S::default())
    }
}

impl<K: Clone, V: Clone, const N: usize, S: Clone> Clone for InlineMap<K, V, N, S> {
    fn clone(&self) -> Self {
        match &self.repr {
            Repr::Inline(inline) => {
                let mut clone = Inline::new(S::clone(&inline.hasher));

                // one at a time, so a clone that panics leaves a map that is dropped correctly
                for (key, value) in inline.keys().iter().zip(inline.values()) {
                    clone.push(key.clone(), value.clone());
                }

                Self {
                    repr: Repr::Inline(clone),
                }
            }
            Repr::Heap(map) => Self {
                repr: Repr::Heap(map.clone()),
            },
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug, const N: usize, S> fmt::Debug for InlineMap<K, V, N, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, const N: usize, S> PartialEq for InlineMap<K, V, N, S>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .all(|(key, value)| other.get(key).is_some_and(|v| value == v))
    }
}

impl<K: Eq + Hash, V: Eq, const N: usize, S: BuildHasher> Eq for InlineMap<K, V, N, S> {}

impl<K, Q, V, const N: usize, S> Index<&Q> for InlineMap<K, V, N, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash + ?Sized,
    S: BuildHasher,
{
    type Output = V;

    /// Returns the value of the key.
    ///
    /// # Panics
    /// Panics if there is no value for the key.
    #[inline]
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<K: Eq + Hash, V, const N: usize, S: BuildHasher> Extend<(K, V)> for InlineMap<K, V, N, S> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        let iter = iter.into_iter();

        // like `HashMap`: room for the entries that the iterator knows there will be
        self.reserve(iter.size_hint().0);

        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<K: Eq + Hash, V, const N: usize, S: BuildHasher + Default> FromIterator<(K, V)>
    for InlineMap<K, V, N, S>
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut map = Self::default();
        map.extend(iter);
        map
    }
}

impl<K: Eq + Hash, V, const N: usize, const M: usize, S: BuildHasher + Default> From<[(K, V); M]>
    for InlineMap<K, V, N, S>
{
    fn from(entries: [(K, V); M]) -> Self {
        Self::from_iter(entries)
    }
}

impl<K, V, const N: usize, S> HeapSize for InlineMap<K, V, N, S> {
    /// Counts what the map itself allocated: nothing, while the entries are inline, and the table of the hash map
    /// once they are not. What the keys and values own is not counted.
    #[inline]
    fn heap_size(&self) -> usize {
        match &self.repr {
            Repr::Inline(_) => 0,
            Repr::Heap(map) => map.heap_size(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        hash::{BuildHasherDefault, Hasher},
        panic::{AssertUnwindSafe, catch_unwind},
        sync::{
            Arc,
            atomic::{AtomicBool, AtomicIsize, AtomicUsize, Ordering},
        },
    };

    use super::{Entry, InlineMap};
    use crate::heap_size::HeapSize;

    type Map<const N: usize> = InlineMap<u32, String, N>;

    /// A hasher that gives every key the same hash: the hash map is slow with it, but has to stay correct.
    #[derive(Default)]
    struct SameHash;

    impl Hasher for SameHash {
        fn finish(&self) -> u64 {
            0
        }

        fn write(&mut self, _: &[u8]) {}
    }

    fn map_of<const N: usize>(entries: u32) -> Map<N> {
        let mut map = Map::<N>::new();
        for i in 0..entries {
            map.insert(i, i.to_string());
        }
        map
    }

    #[test]
    fn is_empty_at_first() {
        let map = Map::<4>::new();

        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
        assert!(!map.spilled());
        assert_eq!(map.capacity(), 4);
        assert_eq!(map.get(&1), None);
        assert!(!map.contains_key(&1));
        assert_eq!(map.iter().count(), 0);
        assert_eq!(map.heap_size(), 0);
    }

    #[test]
    fn keeps_the_first_entries_inline() {
        let map = map_of::<3>(3);

        assert_eq!(map.len(), 3);
        assert!(!map.spilled());
        assert_eq!(map.heap_size(), 0, "nothing was allocated by the map");

        for i in 0..3 {
            assert_eq!(map.get(&i), Some(&i.to_string()));
        }
    }

    #[test]
    fn moves_all_entries_into_a_hash_map_when_it_spills() {
        let mut map = map_of::<3>(3);
        assert!(!map.spilled());

        // one past the inline capacity
        assert_eq!(map.insert(3, "3".into()), None);
        assert!(map.spilled());
        assert!(map.heap_size() > 0);
        assert_eq!(map.len(), 4);

        // the entries that were inline came along
        for i in 0..4 {
            assert_eq!(map.get(&i), Some(&i.to_string()));
        }
        assert_eq!(map.get(&4), None);

        // and it is a plain hash map from now on
        for i in 4..100 {
            map.insert(i, i.to_string());
        }
        assert_eq!(map.len(), 100);
        for i in 0..100 {
            assert_eq!(map.get(&i), Some(&i.to_string()));
        }
    }

    #[test]
    fn insert_replaces_the_value_of_a_key() {
        let mut map = Map::<2>::new();

        // inline
        map.insert(0, "a".into());
        assert_eq!(map.insert(0, "b".into()), Some("a".into()));
        assert_eq!(map.get(&0), Some(&"b".into()));

        // after it spilled
        for i in 1..5 {
            map.insert(i, i.to_string());
        }
        assert!(map.spilled());
        assert_eq!(map.insert(4, "x".into()), Some("4".into()));
        assert_eq!(map.insert(0, "y".into()), Some("b".into()));

        // replacing never adds an entry
        assert_eq!(map.len(), 5);
        assert_eq!(map.get(&4), Some(&"x".into()));
        assert_eq!(map.get(&0), Some(&"y".into()));
    }

    #[test]
    fn get_key_value_and_index() {
        for entries in [3, 10] {
            let map = map_of::<4>(entries);

            assert_eq!(map.get_key_value(&2), Some((&2, &"2".into())));
            assert_eq!(map.get_key_value(&99), None);
            assert_eq!(map[&2], "2");
        }
    }

    #[test]
    #[should_panic(expected = "no entry found for key")]
    fn index_panics_without_an_entry() {
        let map = map_of::<4>(2);
        let _ = &map[&99];
    }

    #[test]
    fn get_mut_changes_the_value() {
        for entries in [3, 10] {
            let mut map = map_of::<4>(entries);

            map.get_mut(&1).unwrap().push('!');
            map.get_mut(&2).unwrap().push('?');

            assert_eq!(map.get(&1), Some(&"1!".into()));
            assert_eq!(map.get(&2), Some(&"2?".into()));
            assert_eq!(map.get_mut(&99), None);
        }
    }

    #[test]
    fn remove() {
        for entries in [4, 10] {
            let mut map = map_of::<4>(entries);

            assert_eq!(map.remove(&1), Some("1".into()));
            assert_eq!(map.remove(&1), None);
            assert_eq!(map.remove_entry(&0), Some((0, "0".into())));
            assert_eq!(map.remove_entry(&99), None);

            assert_eq!(map.len(), entries as usize - 2);
            assert!(!map.contains_key(&0));
            assert!(!map.contains_key(&1));

            // everything else is still there, whichever entry was moved into the place of the removed ones
            for i in 2..entries {
                assert_eq!(map.get(&i), Some(&i.to_string()), "key {i}");
            }
        }
    }

    #[test]
    fn remove_every_entry_in_every_order() {
        // removing from the front, the middle and the end of an inline map moves different entries around
        for order in [
            [0, 1, 2],
            [2, 1, 0],
            [1, 0, 2],
            [1, 2, 0],
            [0, 2, 1],
            [2, 0, 1],
        ] {
            let mut map = map_of::<4>(3);

            for (removed, key) in order.iter().enumerate() {
                assert_eq!(map.remove(key), Some(key.to_string()));

                for left in order.iter().skip(removed + 1) {
                    assert_eq!(map.get(left), Some(&left.to_string()), "{order:?}");
                }
            }

            assert!(map.is_empty());
            assert!(!map.spilled());
        }
    }

    #[test]
    fn stays_a_hash_map_once_it_spilled() {
        let mut map = map_of::<2>(5);
        assert!(map.spilled());

        map.clear();
        assert!(map.spilled(), "it does not move back inline");
        assert!(map.is_empty());

        map.insert(1, "1".into());
        assert_eq!(map.get(&1), Some(&"1".into()));
    }

    #[test]
    fn clear_drops_everything() {
        let probe = Arc::new(());

        for entries in [3, 10] {
            let mut map = InlineMap::<u32, Arc<()>, 4>::new();
            for i in 0..entries {
                map.insert(i, probe.clone());
            }
            assert_eq!(Arc::strong_count(&probe), entries as usize + 1);

            map.clear();
            assert_eq!(Arc::strong_count(&probe), 1);
            assert!(map.is_empty());
        }
    }

    #[test]
    fn retain() {
        for entries in [4, 10] {
            let mut map = map_of::<4>(entries);

            map.retain(|key, value| {
                value.push('!');
                key % 2 == 0
            });

            assert_eq!(map.len(), entries as usize / 2);
            for i in 0..entries {
                if i % 2 == 0 {
                    assert_eq!(map.get(&i), Some(&format!("{i}!")), "key {i}");
                } else {
                    assert!(!map.contains_key(&i), "key {i}");
                }
            }
        }
    }

    #[test]
    fn retain_nothing_and_everything() {
        let mut map = map_of::<8>(6);
        map.retain(|_, _| true);
        assert_eq!(map.len(), 6);

        map.retain(|_, _| false);
        assert!(map.is_empty());
    }

    #[test]
    fn retain_drops_what_it_removes() {
        let probe = Arc::new(());
        let mut map = InlineMap::<u32, Arc<()>, 8>::new();
        for i in 0..6 {
            map.insert(i, probe.clone());
        }

        map.retain(|key, _| *key < 2);
        assert_eq!(Arc::strong_count(&probe), 3);
    }

    #[test]
    fn retain_that_panics_leaves_a_consistent_map() {
        let probe = Arc::new(());
        let mut map = InlineMap::<u32, Arc<()>, 8>::new();
        for i in 0..6 {
            map.insert(i, probe.clone());
        }

        let result = catch_unwind(AssertUnwindSafe(|| {
            map.retain(|key, _| match key {
                0 | 1 => false,
                3 => panic!("no more"),
                _ => true,
            });
        }));
        assert!(result.is_err());

        // whatever was done is done: every entry that is left is whole, and counted once
        assert_eq!(Arc::strong_count(&probe), map.len() + 1);

        drop(map);
        assert_eq!(Arc::strong_count(&probe), 1);
    }

    #[test]
    fn entry_inserts_only_when_vacant() {
        for entries in [2, 10] {
            let mut map = map_of::<4>(entries);

            // occupied
            assert_eq!(*map.entry(1).or_insert("new".into()), "1");
            // vacant
            assert_eq!(*map.entry(entries + 1).or_insert("new".into()), "new");

            assert_eq!(map.len(), entries as usize + 1);
        }
    }

    #[test]
    fn entry_spills_when_it_inserts_into_a_full_map() {
        let mut map = map_of::<2>(2);
        assert!(!map.spilled());

        *map.entry(2).or_insert_with(|| "two".into()) += "!";

        assert!(map.spilled());
        assert_eq!(map.get(&2), Some(&"two!".into()));
        assert_eq!(map.get(&0), Some(&"0".into()));
        assert_eq!(map.get(&1), Some(&"1".into()));
    }

    #[test]
    fn entry_or_insert_with_creates_once() {
        let mut map = Map::<2>::new();
        let mut made = 0;

        // inline, inline, and spilled
        for key in [0, 1, 2] {
            for _ in 0..3 {
                map.entry(key)
                    .or_insert_with(|| {
                        made += 1;
                        key.to_string()
                    })
                    .push('.');
            }
        }

        assert_eq!(made, 3);
        for key in [0, 1, 2] {
            assert_eq!(map.get(&key), Some(&format!("{key}...")));
        }
    }

    #[test]
    fn entry_or_insert_with_that_panics_leaves_the_map_as_it_was() {
        let probe = Arc::new(());
        let mut map = InlineMap::<u32, Arc<()>, 2>::new();
        map.insert(0, probe.clone());

        // inline, with room left
        let result = catch_unwind(AssertUnwindSafe(|| {
            map.entry(1).or_insert_with(|| panic!("no value"));
        }));
        assert!(result.is_err());
        assert_eq!(map.len(), 1);
        assert!(!map.contains_key(&1));

        map.insert(1, probe.clone());

        // inline, full: it must not have spilled either
        let result = catch_unwind(AssertUnwindSafe(|| {
            map.entry(2).or_insert_with(|| panic!("no value"));
        }));
        assert!(result.is_err());
        assert_eq!(map.len(), 2);
        assert!(!map.spilled());

        drop(map);
        assert_eq!(Arc::strong_count(&probe), 1);
    }

    #[test]
    fn entry_helpers() {
        for entries in [1, 10] {
            let mut map = map_of::<4>(entries);

            // `or_default`
            assert_eq!(*map.entry(50).or_default(), "");
            // `or_insert_with_key`
            assert_eq!(
                *map.entry(51).or_insert_with_key(|key| format!("key {key}")),
                "key 51"
            );
            // `and_modify`, occupied and vacant
            map.entry(0)
                .and_modify(|v| v.push('!'))
                .or_insert("x".into());
            map.entry(52)
                .and_modify(|v| v.push('!'))
                .or_insert("x".into());

            assert_eq!(map.get(&0), Some(&"0!".into()));
            assert_eq!(map.get(&52), Some(&"x".into()));
            assert_eq!(map.entry(0).key(), &0);
            assert_eq!(map.entry(99).key(), &99);
        }
    }

    #[test]
    fn occupied_entry() {
        for entries in [3, 10] {
            let mut map = map_of::<4>(entries);

            let Entry::Occupied(mut entry) = map.entry(1) else {
                panic!("1 is in the map");
            };
            assert_eq!(entry.key(), &1);
            assert_eq!(entry.get(), "1");
            entry.get_mut().push('+');
            assert_eq!(entry.insert("new".into()), "1+");
            assert_eq!(entry.get(), "new");
            assert_eq!(entry.into_mut(), "new");

            let Entry::Occupied(entry) = map.entry(2) else {
                panic!("2 is in the map");
            };
            assert_eq!(entry.remove_entry(), (2, "2".into()));

            let Entry::Occupied(entry) = map.entry(0) else {
                panic!("0 is in the map");
            };
            assert_eq!(entry.remove(), "0");

            assert_eq!(map.len(), entries as usize - 2);
            assert_eq!(map.get(&1), Some(&"new".into()));
            for i in 3..entries {
                assert_eq!(map.get(&i), Some(&i.to_string()));
            }
        }
    }

    #[test]
    fn vacant_entry() {
        for entries in [3, 10] {
            let mut map = map_of::<4>(entries);

            let Entry::Vacant(entry) = map.entry(99) else {
                panic!("99 is not in the map");
            };
            assert_eq!(entry.key(), &99);
            assert_eq!(entry.into_key(), 99);
            assert!(!map.contains_key(&99), "taking the key does not insert");

            let Entry::Vacant(entry) = map.entry(99) else {
                panic!("99 is not in the map");
            };
            entry.insert("ninety-nine".into()).push('!');
            assert_eq!(map.get(&99), Some(&"ninety-nine!".into()));
        }
    }

    #[test]
    fn iterates_over_all_entries() {
        for entries in [0, 3, 4, 5, 20] {
            let mut map = map_of::<4>(entries);
            let expected = (0..entries).collect::<Vec<_>>();

            let mut keys = map.keys().copied().collect::<Vec<_>>();
            keys.sort_unstable();
            assert_eq!(keys, expected);

            let mut values = map.values().cloned().collect::<Vec<_>>();
            values.sort_unstable();
            let mut expected_values = expected.iter().map(u32::to_string).collect::<Vec<_>>();
            expected_values.sort_unstable();
            assert_eq!(values, expected_values);

            let mut pairs = map.iter().map(|(k, v)| (*k, v.clone())).collect::<Vec<_>>();
            pairs.sort_unstable();
            assert_eq!(pairs.len(), entries as usize);
            for (key, value) in &pairs {
                assert_eq!(*value, key.to_string());
            }

            // the same through `for`
            let mut count = 0;
            for (key, value) in &map {
                assert_eq!(*value, key.to_string());
                count += 1;
            }
            assert_eq!(count, entries);

            // and they know how many there are, and how many are left
            assert_eq!(map.iter().len(), entries as usize);
            assert_eq!(map.keys().len(), entries as usize);
            assert_eq!(map.values().len(), entries as usize);
            let mut iter = map.iter();
            iter.next();
            assert_eq!(iter.len(), (entries as usize).saturating_sub(1));
            assert_eq!(iter.clone().count(), iter.len());

            assert_eq!(map.iter_mut().len(), entries as usize);
            assert_eq!(map.values_mut().len(), entries as usize);
        }
    }

    #[test]
    fn iter_mut_and_values_mut_change_every_value() {
        for entries in [3, 10] {
            let mut map = map_of::<4>(entries);

            for (key, value) in &mut map {
                value.push('+');
                value.push_str(&key.to_string());
            }
            for value in map.values_mut() {
                value.push('!');
            }
            map.iter_mut().for_each(|(_, value)| value.push('?'));

            for i in 0..entries {
                assert_eq!(map.get(&i), Some(&format!("{i}+{i}!?")));
            }
        }
    }

    #[test]
    fn into_iterators_take_everything_out() {
        for entries in [0, 3, 4, 10] {
            let expected = (0..entries).map(|i| (i, i.to_string())).collect::<Vec<_>>();

            let mut owned = map_of::<4>(entries).into_iter().collect::<Vec<_>>();
            owned.sort_unstable();
            assert_eq!(owned, expected);

            let mut keys = map_of::<4>(entries).into_keys().collect::<Vec<_>>();
            keys.sort_unstable();
            assert_eq!(keys, (0..entries).collect::<Vec<_>>());

            let mut values = map_of::<4>(entries).into_values().collect::<Vec<_>>();
            values.sort_unstable();
            let mut expected_values = expected.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>();
            expected_values.sort_unstable();
            assert_eq!(values, expected_values);

            assert_eq!(map_of::<4>(entries).into_iter().len(), entries as usize);
        }
    }

    #[test]
    fn into_iter_drops_what_was_not_taken() {
        let probe = Arc::new(());

        for entries in [3, 10] {
            let mut map = InlineMap::<u32, Arc<()>, 4>::new();
            for i in 0..entries {
                map.insert(i, probe.clone());
            }

            let mut iter = map.into_iter();
            drop(iter.next());
            drop(iter.next());
            assert_eq!(Arc::strong_count(&probe), entries as usize - 1);

            drop(iter);
            assert_eq!(Arc::strong_count(&probe), 1);
        }
    }

    #[test]
    fn drops_the_hasher_once() {
        // The `Arc` is only held, so that its count shows when the hasher is dropped.
        #[derive(Clone)]
        struct CountedHasher(#[allow(dead_code)] Arc<()>);

        impl std::hash::BuildHasher for CountedHasher {
            type Hasher = std::collections::hash_map::DefaultHasher;

            fn build_hasher(&self) -> Self::Hasher {
                std::collections::hash_map::DefaultHasher::new()
            }
        }

        let probe = Arc::new(());

        // inline, taken apart
        let mut map = InlineMap::<u32, u32, 4, _>::with_hasher(CountedHasher(probe.clone()));
        map.insert(1, 1);
        assert_eq!(Arc::strong_count(&probe), 2);
        let iter = map.into_iter();
        assert_eq!(
            Arc::strong_count(&probe),
            1,
            "the hasher is dropped when the map is taken apart"
        );
        drop(iter);

        // spilled, with the hasher moved into the hash map
        let mut map = InlineMap::<u32, u32, 1, _>::with_hasher(CountedHasher(probe.clone()));
        map.insert(1, 1);
        map.insert(2, 2);
        assert!(map.spilled());
        assert_eq!(Arc::strong_count(&probe), 2, "moved, not copied");
        drop(map);
        assert_eq!(Arc::strong_count(&probe), 1);

        // inline, dropped
        let map = InlineMap::<u32, u32, 4, _>::with_hasher(CountedHasher(probe.clone()));
        assert_eq!(Arc::strong_count(&probe), 2);
        drop(map);
        assert_eq!(Arc::strong_count(&probe), 1);
    }

    #[test]
    fn reserve_and_capacity() {
        let mut map = Map::<4>::new();
        assert_eq!(map.capacity(), 4);

        // fits inline
        map.reserve(4);
        assert!(!map.spilled());

        map.insert(1, "1".into());
        map.reserve(3);
        assert!(!map.spilled());

        // does not fit inline
        map.reserve(4);
        assert!(map.spilled());
        assert!(map.capacity() >= 5);
        assert_eq!(map.get(&1), Some(&"1".into()));

        map.shrink_to_fit();
        assert_eq!(map.get(&1), Some(&"1".into()));
    }

    #[test]
    fn with_capacity_only_allocates_when_it_has_to() {
        let map = Map::<4>::with_capacity(4);
        assert!(!map.spilled());
        assert_eq!(map.heap_size(), 0);

        let map = Map::<4>::with_capacity(5);
        assert!(map.spilled());
        assert!(map.capacity() >= 5);
        assert!(map.is_empty());
    }

    #[test]
    fn without_inline_capacity_is_a_hash_map() {
        let mut map = InlineMap::<u32, u32, 0>::new();

        for i in 0..100 {
            map.insert(i, i * 2);
        }

        assert!(map.spilled());
        for i in 0..100 {
            assert_eq!(map.get(&i), Some(&(i * 2)));
        }
    }

    #[test]
    fn works_with_colliding_hashes() {
        let mut map: InlineMap<u32, u32, 2, BuildHasherDefault<SameHash>> =
            InlineMap::with_hasher(BuildHasherDefault::default());

        for i in 0..50 {
            map.insert(i, i + 1);
        }

        for i in 0..50 {
            assert_eq!(map.get(&i), Some(&(i + 1)));
        }
        assert_eq!(map.remove(&10), Some(11));
        assert_eq!(map.get(&10), None);
    }

    #[test]
    fn looks_up_borrowed_keys() {
        for entries in [1, 3] {
            let mut map = InlineMap::<String, u32, 2>::new();
            for i in 0..entries {
                map.insert(format!("key{i}"), i);
            }

            // `&str` instead of `&String`
            assert_eq!(map.get("key0"), Some(&0));
            assert!(map.contains_key("key0"));
            assert!(!map.contains_key("other"));
            assert_eq!(map["key0"], 0);
            assert_eq!(map.remove("key0"), Some(0));
        }
    }

    #[test]
    fn drops_every_key_and_value_once() {
        let key_probe = Arc::new(());
        let value_probe = Arc::new(());

        for entries in [3usize, 10] {
            {
                let mut map = InlineMap::<(usize, Arc<()>), Arc<()>, 4>::new();
                // `Arc<()>` is equal to every other one, so only the number tells the keys apart
                let insert = |i: usize, map: &mut InlineMap<(usize, Arc<()>), Arc<()>, 4>| {
                    map.insert((i, key_probe.clone()), value_probe.clone())
                };

                for i in 0..entries {
                    insert(i, &mut map);
                }
                assert_eq!(Arc::strong_count(&key_probe), entries + 1);
                assert_eq!(Arc::strong_count(&value_probe), entries + 1);

                // replacing drops the old value, and the key that was passed in
                insert(0, &mut map);
                insert(entries - 1, &mut map);
                assert_eq!(Arc::strong_count(&key_probe), entries + 1);
                assert_eq!(Arc::strong_count(&value_probe), entries + 1);

                // removing hands both back
                drop(map.remove_entry(&(0, key_probe.clone())));
                assert_eq!(Arc::strong_count(&key_probe), entries);
                assert_eq!(Arc::strong_count(&value_probe), entries);
            }

            assert_eq!(Arc::strong_count(&key_probe), 1);
            assert_eq!(Arc::strong_count(&value_probe), 1);
        }
    }

    #[test]
    fn drops_what_is_inline_when_it_is_not_full() {
        let probe = Arc::new(());

        {
            let mut map = InlineMap::<u32, Arc<()>, 8>::new();
            for i in 0..3 {
                map.insert(i, probe.clone());
            }
            assert_eq!(Arc::strong_count(&probe), 4);
        }

        assert_eq!(Arc::strong_count(&probe), 1);
    }

    /// A key that panics when it is hashed, once told to.
    #[derive(PartialEq, Eq)]
    struct PanicsWhenHashed(u32);

    static PANIC_WHEN_HASHED: AtomicBool = AtomicBool::new(false);
    static VALUES_DROPPED: AtomicUsize = AtomicUsize::new(0);

    impl std::hash::Hash for PanicsWhenHashed {
        fn hash<H: Hasher>(&self, state: &mut H) {
            assert!(
                !PANIC_WHEN_HASHED.load(Ordering::SeqCst),
                "the key was hashed"
            );
            self.0.hash(state);
        }
    }

    struct CountedValue;

    impl Drop for CountedValue {
        fn drop(&mut self) {
            VALUES_DROPPED.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn spill_that_panics_while_hashing_drops_nothing_twice() {
        let mut map = InlineMap::<PanicsWhenHashed, CountedValue, 3>::new();
        for i in 0..3 {
            map.insert(PanicsWhenHashed(i), CountedValue);
        }
        assert!(!map.spilled());

        // spilling hashes every key
        PANIC_WHEN_HASHED.store(true, Ordering::SeqCst);
        let result = catch_unwind(AssertUnwindSafe(|| {
            map.insert(PanicsWhenHashed(3), CountedValue);
        }));
        PANIC_WHEN_HASHED.store(false, Ordering::SeqCst);
        assert!(result.is_err());

        // The map is a (possibly smaller) hash map now, and works. The entries that were not moved are leaked, and
        // nothing is dropped twice, which Miri would catch, and the count here as well.
        assert!(map.spilled());
        assert!(map.len() <= 3);
        let before = VALUES_DROPPED.load(Ordering::SeqCst);
        map.insert(PanicsWhenHashed(10), CountedValue);

        let len = map.len();
        drop(map);
        assert!(VALUES_DROPPED.load(Ordering::SeqCst) - before <= len);
    }

    #[test]
    fn works_with_zero_sized_keys_and_values() {
        let mut map = InlineMap::<(), (), 2>::new();
        assert_eq!(map.insert((), ()), None);
        assert_eq!(map.insert((), ()), Some(()));
        assert_eq!(map.len(), 1);
        assert_eq!(map.get(&()), Some(&()));
        assert_eq!(map.remove(&()), Some(()));
        assert!(map.is_empty());
    }

    #[test]
    fn is_a_const_with_a_const_hasher() {
        const fn new() -> InlineMap<u32, u32, 2, BuildHasherDefault<SameHash>> {
            InlineMap::with_hasher(BuildHasherDefault::new())
        }

        let mut map = new();
        map.insert(1, 2);
        assert_eq!(map.get(&1), Some(&2));
    }

    #[test]
    fn clone_and_eq() {
        for entries in [0, 3, 10] {
            let map = map_of::<4>(entries);
            let clone = map.clone();

            assert_eq!(map, clone);
            assert_eq!(clone.spilled(), map.spilled());
            assert_eq!(clone.len(), map.len());

            let mut changed = clone;
            changed.insert(1000, "x".into());
            assert_ne!(map, changed);
            assert_ne!(changed, map);
        }

        // the same entries, inserted in another order
        let mut a = Map::<4>::new();
        let mut b = Map::<4>::new();
        a.insert(1, "1".into());
        a.insert(2, "2".into());
        b.insert(2, "2".into());
        b.insert(1, "1".into());
        assert_eq!(a, b);

        // a different value
        b.insert(1, "other".into());
        assert_ne!(a, b);
    }

    #[test]
    fn clone_that_panics_drops_what_it_cloned() {
        static CLONES_LEFT: AtomicIsize = AtomicIsize::new(0);

        struct PanicsWhenCloned(Arc<()>);

        impl Clone for PanicsWhenCloned {
            fn clone(&self) -> Self {
                assert!(
                    CLONES_LEFT.fetch_sub(1, Ordering::SeqCst) > 0,
                    "no more clones"
                );
                Self(self.0.clone())
            }
        }

        let probe = Arc::new(());
        let mut map = InlineMap::<u32, PanicsWhenCloned, 4>::new();
        for i in 0..3 {
            map.insert(i, PanicsWhenCloned(probe.clone()));
        }

        CLONES_LEFT.store(2, Ordering::SeqCst);
        let result = catch_unwind(AssertUnwindSafe(|| map.clone()));
        assert!(result.is_err());

        // the two values that were cloned were dropped with the unfinished clone
        assert_eq!(Arc::strong_count(&probe), 4);

        drop(map);
        assert_eq!(Arc::strong_count(&probe), 1);
    }

    #[test]
    fn extend_from_iterator_and_from_array() {
        for entries in [2u32, 10] {
            let map: InlineMap<u32, u32, 4> = (0..entries).map(|i| (i, i * 2)).collect();
            assert_eq!(map.len(), entries as usize);
            assert_eq!(map.spilled(), entries > 4);

            let mut other = InlineMap::<u32, u32, 4>::new();
            other.extend((0..entries).map(|i| (i, i * 2)));
            assert_eq!(map, other);
        }

        let map = InlineMap::<&str, u32, 4>::from([("a", 1), ("b", 2)]);
        assert_eq!(map["a"], 1);
        assert_eq!(map["b"], 2);
        assert!(!map.spilled());

        // `extend` with an iterator that says how many there will be reserves room up front
        let mut map = InlineMap::<u32, u32, 2>::new();
        map.extend((0..50).map(|i| (i, i)));
        assert_eq!(map.len(), 50);
    }

    #[test]
    fn hasher() {
        let map = InlineMap::<u32, u32, 2, BuildHasherDefault<SameHash>>::default();
        let _: &BuildHasherDefault<SameHash> = map.hasher();

        // the same one after it spilled
        let mut map = map;
        for i in 0..5 {
            map.insert(i, i);
        }
        assert!(map.spilled());
        let _: &BuildHasherDefault<SameHash> = map.hasher();
    }

    #[test]
    fn debug() {
        let mut map = InlineMap::<u32, u32, 1>::new();
        map.insert(1, 10);
        assert_eq!(format!("{map:?}"), "{1: 10}");

        map.insert(2, 20);
        let debug = format!("{map:?}");
        assert!(
            debug == "{1: 10, 2: 20}" || debug == "{2: 20, 1: 10}",
            "{debug}"
        );
    }

    #[test]
    fn default() {
        let map = InlineMap::<u32, u32, 4>::default();
        assert!(map.is_empty());
    }

    #[test]
    fn can_be_sent_and_shared_between_threads() {
        const fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<InlineMap<u32, String, 4>>();

        let map = map_of::<4>(10);
        std::thread::scope(|s| {
            for _ in 0..4 {
                s.spawn(|| {
                    for i in 0..10 {
                        assert_eq!(map.get(&i), Some(&i.to_string()));
                    }
                });
            }
        });
    }

    #[test]
    fn finds_cheap_keys_block_by_block_in_a_big_inline_map() {
        // 16 or more entries: the keys are compared eight at a time, and the
        // sizes cover a whole number of blocks, and a rest after the last one.
        for entries in [16_u32, 17, 23, 24, 25, 31, 40, 63, 64] {
            let mut map = InlineMap::<u32, u32, 64>::new();
            for i in 0..entries {
                map.insert(i * 3, i);
            }
            assert!(!map.spilled());
            assert_eq!(map.len(), entries as usize);

            for i in 0..entries {
                assert_eq!(
                    map.get(&(i * 3)),
                    Some(&i),
                    "{entries} entries, key {}",
                    i * 3
                );
                assert!(!map.contains_key(&(i * 3 + 1)));
            }
            assert_eq!(map.get(&u32::MAX), None);

            // Replacing a value keeps the entry where it is.
            assert_eq!(map.insert(3, 1000), Some(1));
            assert_eq!(map.get(&3), Some(&1000));
            assert_eq!(map.len(), entries as usize);

            // Removing moves the last entry into the hole, which has to be found
            // at its new place, in the first block as well as in the rest.
            assert_eq!(map.remove(&0), Some(0));
            assert_eq!(map.get(&0), None);
            let last = (entries - 1) * 3;
            assert_eq!(map.get(&last), Some(&(entries - 1)), "{entries} entries");
            assert_eq!(map.remove(&last), Some(entries - 1));
            assert_eq!(map.get(&last), None);

            for i in 1..entries - 1 {
                let expected = if i == 1 { 1000 } else { i };
                assert_eq!(map.get(&(i * 3)), Some(&expected), "{entries} entries");
            }
        }
    }

    #[test]
    fn block_search_works_for_other_cheap_key_types() {
        let mut chars = InlineMap::<char, usize, 32>::new();
        let mut bytes = InlineMap::<u8, usize, 32>::new();
        let mut pairs = InlineMap::<(u8, u8), usize, 32>::new();
        for i in 0..30_u8 {
            chars.insert(char::from(b'a' + i), usize::from(i));
            bytes.insert(i.wrapping_mul(7), usize::from(i));
            pairs.insert((i, i ^ 5), usize::from(i));
        }

        for i in 0..30_u8 {
            assert_eq!(chars.get(&char::from(b'a' + i)), Some(&usize::from(i)));
            assert_eq!(bytes.get(&i.wrapping_mul(7)), Some(&usize::from(i)));
            assert_eq!(pairs.get(&(i, i ^ 5)), Some(&usize::from(i)));
        }
        assert_eq!(chars.get(&'#'), None);
        assert_eq!(pairs.get(&(0, 0)), None);
    }

    #[test]
    fn keys_that_are_not_cheap_to_compare_work_with_many_entries() {
        // Owned and wide keys use the plain scan, which has to give the same
        // answers, also for a lookup through a borrowed form of the key.
        let mut map = InlineMap::<String, u32, 32>::new();
        for i in 0..30_u32 {
            map.insert(format!("key {i}"), i);
        }
        assert!(!map.spilled());

        for i in 0..30_u32 {
            assert_eq!(map.get(format!("key {i}").as_str()), Some(&i));
        }
        assert_eq!(map.get("key 30"), None);

        let mut wide = InlineMap::<u128, u32, 32>::new();
        for i in 0..30_u32 {
            wide.insert(u128::from(i) << 70, i);
        }
        for i in 0..30_u32 {
            assert_eq!(wide.get(&(u128::from(i) << 70)), Some(&i));
        }
        assert_eq!(wide.get(&1), None);
    }

    /// A map does not store a tag that tells whether it spilled. The length of the inline part is never zero (see
    /// `Len`), so the compiler uses that value to mark a map that spilled. That makes the map exactly as big as its
    /// inline part, when that is the bigger one of the two, and 8 bytes smaller than with a tag.
    #[cfg(target_pointer_width = "64")]
    #[test]
    fn the_spilled_state_takes_no_extra_space() {
        use super::{Inline, Repr};
        use std::collections::hash_map::RandomState;
        use std::mem::size_of;

        fn check<K, V, const N: usize>() {
            let inline = size_of::<Inline<K, V, N, RandomState>>();
            assert_eq!(size_of::<Repr<K, V, N, RandomState>>(), inline, "N = {N}");
            assert_eq!(size_of::<InlineMap<K, V, N>>(), inline, "N = {N}");
        }

        check::<u32, u32, 4>();
        check::<u32, u32, 8>();
        check::<u64, u64, 2>();
        check::<u64, u64, 4>();
        check::<String, u64, 1>();
        check::<String, u64, 4>();
        check::<u128, u128, 1>();
        check::<u8, u8, 16>();
    }
}
