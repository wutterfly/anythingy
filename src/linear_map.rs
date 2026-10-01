//! A map backed by a flat vector of pairs, searched linearly.
//!
//! See [`LinearMap`] for details and when to prefer it over `HashMap`.

use crate::heap_size::HeapSize;
use alloc::vec::{self, Vec};
use core::borrow::Borrow;
use core::fmt;
use core::iter::{FromIterator, FusedIterator};
use core::mem;
use core::ops::Index;
use core::slice;

/// A map backed by a `Vec<(K, V)>`, searched linearly.
///
/// Unlike `HashMap`, keys only need `Eq` (no `Hash`, no `Ord`). Lookups are
/// O(n), but for small maps the contiguous storage is more cache-friendly
/// than a hash table's scattered buckets, so this can outperform `HashMap`
/// when the number of entries is small (roughly up to a few dozen).
///
/// Maps with small plain-data keys, such as integers, are searched
/// particularly fast.
///
/// Iteration follows storage order, which is insertion order until
/// [`remove`](Self::remove) is used: removal swaps the last entry into the
/// vacated slot instead of shifting everything down, so it does not
/// preserve order. [`retain`](Self::retain) does.
///
/// # Examples
///
/// ```
/// use anythingy::LinearMap;
///
/// let mut ages = LinearMap::new();
/// ages.insert("alice", 30);
/// ages.insert("bob", 25);
///
/// assert_eq!(ages.get("alice"), Some(&30));
/// *ages.entry("bob").or_insert(0) += 1;
/// assert_eq!(ages["bob"], 26);
/// ```
#[derive(Clone)]
pub struct LinearMap<K, V> {
    storage: Vec<(K, V)>,
}

impl<K, V> LinearMap<K, V> {
    /// Creates an empty map. Does not allocate.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            storage: Vec::new(),
        }
    }

    /// Creates an empty map with room for at least `capacity` entries.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            storage: Vec::with_capacity(capacity),
        }
    }

    /// Returns the number of entries the map can hold without reallocating.
    #[must_use]
    pub const fn capacity(&self) -> usize {
        self.storage.capacity()
    }

    /// Reserves room for at least `additional` more entries.
    pub fn reserve(&mut self, additional: usize) {
        self.storage.reserve(additional);
    }

    /// Shrinks the capacity as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.storage.shrink_to_fit();
    }

    /// Shrinks the capacity to `min_capacity` or the current length,
    /// whichever is larger.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.storage.shrink_to(min_capacity);
    }

    /// Returns the number of entries.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.storage.len()
    }

    /// Returns `true` if the map holds no entries.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.storage.is_empty()
    }

    /// Removes every entry, keeping the allocated capacity.
    pub fn clear(&mut self) {
        self.storage.clear();
    }

    /// Iterates over `(&key, &value)` pairs in storage order.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            inner: self.storage.iter(),
        }
    }

    /// Iterates over `(&key, &mut value)` pairs in storage order.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            inner: self.storage.iter_mut(),
        }
    }

    /// Iterates over the keys in storage order.
    #[must_use]
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys {
            inner: self.storage.iter(),
        }
    }

    /// Iterates over the values in storage order.
    #[must_use]
    pub fn values(&self) -> Values<'_, K, V> {
        Values {
            inner: self.storage.iter(),
        }
    }

    /// Iterates over mutable references to the values in storage order.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.storage.iter_mut(),
        }
    }

    /// Consumes the map, yielding its keys and dropping the values.
    #[must_use]
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys {
            inner: self.storage.into_iter(),
        }
    }

    /// Consumes the map, yielding its values and dropping the keys.
    #[must_use]
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues {
            inner: self.storage.into_iter(),
        }
    }

    /// Removes and yields every entry, keeping the allocated capacity.
    ///
    /// The map is empty afterwards, even if the iterator is dropped before
    /// it is exhausted or leaked.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::LinearMap;
    ///
    /// let mut map: LinearMap<_, _> = [(1, "a"), (2, "b")].into();
    /// let drained: Vec<_> = map.drain().collect();
    /// assert_eq!(drained, vec![(1, "a"), (2, "b")]);
    /// assert!(map.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain {
            inner: self.storage.drain(..),
        }
    }

    /// Keeps only the entries for which `f` returns `true`, preserving the
    /// order of the ones that stay. `f` may mutate the values.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.storage.retain_mut(|(k, v)| f(k, v));
    }

    /// Appends an entry without checking for an existing key, returning
    /// its index.
    fn push_entry(&mut self, key: K, value: V) -> usize {
        self.storage.push((key, value));
        self.storage.len() - 1
    }

    fn swap_remove_entry(&mut self, index: usize) -> (K, V) {
        self.storage.swap_remove(index)
    }
}

/// The smallest map (in entries) for which the block-wise search is used.
/// Below this the plain early-exit scan is faster.
const BLOCK_SEARCH_MIN_LEN: usize = 32;

/// Number of keys compared per step by the block-wise search.
const BLOCK: usize = 8;

impl<K: Eq, V> LinearMap<K, V> {
    /// Whether keys of this type are cheap enough to compare that checking
    /// a whole block at once beats stopping at the first match. True for
    /// small plain-data keys (integers, `char`, small enums, ...), false
    /// for anything that owns data or is wider than a pointer, where the
    /// extra comparisons would cost more than the vectorization saves.
    const CHEAP_KEYS: bool = !mem::needs_drop::<K>() && mem::size_of::<K>() <= 8;

    fn position<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        if Self::CHEAP_KEYS && self.storage.len() >= BLOCK_SEARCH_MIN_LEN {
            return block_position(&self.storage, key);
        }
        self.storage.iter().position(|(k, _)| k.borrow() == key)
    }

    /// Returns `true` if the map contains `key`.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.position(key).is_some()
    }

    /// Returns a reference to the value stored for `key`.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.position(key).map(|idx| &self.storage[idx].1)
    }

    /// Returns a mutable reference to the value stored for `key`.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.position(key).map(move |idx| &mut self.storage[idx].1)
    }

    /// Returns the stored key and value for `key`.
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.position(key).map(|idx| {
            let (k, v) = &self.storage[idx];
            (k, v)
        })
    }

    /// Inserts a key-value pair, returning the previous value if the key
    /// was already present. An existing key is kept as it is; only its
    /// value is replaced.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if let Some(idx) = self.position(&key) {
            Some(mem::replace(&mut self.storage[idx].1, value))
        } else {
            self.push_entry(key, value);
            None
        }
    }

    /// Like [`insert`](Self::insert), but also swaps in the given key for the
    /// stored one and returns the old key and value. For `LinearSet::replace`.
    pub(crate) fn replace_entry(&mut self, key: K, value: V) -> Option<(K, V)> {
        if let Some(idx) = self.position(&key) {
            Some(mem::replace(&mut self.storage[idx], (key, value)))
        } else {
            self.push_entry(key, value);
            None
        }
    }

    /// Removes a key, returning its value if present.
    ///
    /// This is O(1) beyond the initial linear scan: it swaps the removed
    /// entry with the last one instead of shifting the rest, so it does
    /// not preserve insertion order.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.position(key).map(|idx| self.swap_remove_entry(idx).1)
    }

    /// Removes a key, returning the stored key and value if present. Does
    /// not preserve insertion order; see [`remove`](Self::remove).
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.position(key).map(|idx| self.swap_remove_entry(idx))
    }

    /// Gets the given key's entry, for in-place insertion or update with a
    /// single search.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::LinearMap;
    ///
    /// let mut counts = LinearMap::new();
    /// for word in ["a", "b", "a", "a"] {
    ///     *counts.entry(word).or_insert(0) += 1;
    /// }
    /// assert_eq!(counts["a"], 3);
    /// assert_eq!(counts["b"], 1);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        match self.position(&key) {
            Some(index) => Entry::Occupied(OccupiedEntry { map: self, index }),
            None => Entry::Vacant(VacantEntry { map: self, key }),
        }
    }
}

/// Position of `key` among the pairs' keys, comparing [`BLOCK`] keys per
/// step without stopping early inside a block, so the compiler can turn the
/// comparison into a vector operation. Only worth it for cheap-to-compare
/// keys; see `LinearMap::CHEAP_KEYS`.
///
/// Kept out of line on purpose: inlining it makes `position` big enough
/// that the plain early-exit scan used for small maps stops being inlined
/// into callers, which costs small maps around 30% per lookup.
#[inline(never)]
fn block_position<K, V, Q>(pairs: &[(K, V)], key: &Q) -> Option<usize>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    let (blocks, rest) = pairs.as_chunks::<BLOCK>();
    for (i, block) in blocks.iter().enumerate() {
        let mut found = false;
        for (k, _) in block {
            found |= k.borrow() == key;
        }
        if found {
            return block
                .iter()
                .position(|(k, _)| k.borrow() == key)
                .map(|offset| i * BLOCK + offset);
        }
    }
    rest.iter()
        .position(|(k, _)| k.borrow() == key)
        .map(|i| blocks.len() * BLOCK + i)
}

/// A view into a single entry of a [`LinearMap`], which is either vacant or
/// occupied. Created by [`LinearMap::entry`].
pub enum Entry<'a, K, V> {
    /// The key is present.
    Occupied(OccupiedEntry<'a, K, V>),
    /// The key is absent.
    Vacant(VacantEntry<'a, K, V>),
}

/// A view into an occupied entry of a [`LinearMap`].
pub struct OccupiedEntry<'a, K, V> {
    map: &'a mut LinearMap<K, V>,
    index: usize,
}

/// A view into a vacant entry of a [`LinearMap`].
pub struct VacantEntry<'a, K, V> {
    map: &'a mut LinearMap<K, V>,
    key: K,
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Returns the entry's key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(e) => e.key(),
            Entry::Vacant(e) => e.key(),
        }
    }

    /// Inserts `default` if the entry is vacant, and returns a mutable
    /// reference to the value.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default),
        }
    }

    /// Inserts the result of `default` if the entry is vacant, and returns
    /// a mutable reference to the value.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default()),
        }
    }

    /// Like [`or_insert_with`](Self::or_insert_with), but `default`
    /// receives the key.
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => {
                let value = default(e.key());
                e.insert(value)
            }
        }
    }

    /// Inserts `V::default()` if the entry is vacant, and returns a mutable
    /// reference to the value.
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }

    /// Applies `f` to the value if the entry is occupied, then returns the
    /// entry for further chaining.
    #[must_use]
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut e) => {
                f(e.get_mut());
                Entry::Occupied(e)
            }
            Entry::Vacant(e) => Entry::Vacant(e),
        }
    }
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    /// Returns the entry's key.
    #[must_use]
    pub fn key(&self) -> &K {
        &self.map.storage[self.index].0
    }

    /// Returns a reference to the value.
    #[must_use]
    pub fn get(&self) -> &V {
        &self.map.storage[self.index].1
    }

    /// Returns a mutable reference to the value.
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.map.storage[self.index].1
    }

    /// Converts the entry into a mutable reference to the value, with the
    /// lifetime of the map.
    #[must_use]
    pub fn into_mut(self) -> &'a mut V {
        &mut self.map.storage[self.index].1
    }

    /// Replaces the value, returning the old one.
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Removes the entry, returning its value. Does not preserve insertion
    /// order; see [`LinearMap::remove`].
    #[must_use]
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Removes the entry, returning its key and value. Does not preserve
    /// insertion order; see [`LinearMap::remove`].
    #[must_use]
    pub fn remove_entry(self) -> (K, V) {
        self.map.swap_remove_entry(self.index)
    }
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    /// Returns the key that would be inserted.
    pub const fn key(&self) -> &K {
        &self.key
    }

    /// Takes ownership of the key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Inserts the value and returns a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        let index = self.map.push_entry(self.key, value);
        &mut self.map.storage[index].1
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Entry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Entry::Occupied(e) => f.debug_tuple("Entry").field(e).finish(),
            Entry::Vacant(e) => f.debug_tuple("Entry").field(e).finish(),
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for OccupiedEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

impl<K: fmt::Debug, V> fmt::Debug for VacantEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}

impl<K, V> Default for LinearMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for LinearMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// Two maps are equal if they hold the same keys with equal values,
/// regardless of storage order.
impl<K: Eq, V: PartialEq> PartialEq for LinearMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().all(|(k, v)| other.get(k) == Some(v))
    }
}

impl<K: Eq, V: Eq> Eq for LinearMap<K, V> {}

impl<K, Q, V> Index<&Q> for LinearMap<K, V>
where
    K: Eq + Borrow<Q>,
    Q: Eq + ?Sized,
{
    type Output = V;

    /// # Panics
    ///
    /// Panics if the key is not present.
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

/// Builds a map from an iterator. Later duplicates overwrite earlier ones.
/// Every insert searches the map so far, so this is O(n²): meant for the
/// small maps this type is designed for.
impl<K: Eq, V> FromIterator<(K, V)> for LinearMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = Self::new();
        map.extend(iter);
        map
    }
}

impl<K: Eq, V, const N: usize> From<[(K, V); N]> for LinearMap<K, V> {
    fn from(entries: [(K, V); N]) -> Self {
        entries.into_iter().collect()
    }
}

impl<K: Eq, V> Extend<(K, V)> for LinearMap<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        // Same policy as `HashMap`: the hint is a lower bound on items but
        // says nothing about duplicates, so only reserve half of it once
        // the map already has entries.
        let (lower, _) = iter.size_hint();
        self.reserve(if self.is_empty() {
            lower
        } else {
            lower.div_ceil(2)
        });
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K: Eq + Copy + 'a, V: Copy + 'a> Extend<(&'a K, &'a V)> for LinearMap<K, V> {
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|(k, v)| (*k, *v)));
    }
}

impl<K, V> IntoIterator for LinearMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter {
            inner: self.storage.into_iter(),
        }
    }
}

impl<'a, K, V> IntoIterator for &'a LinearMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut LinearMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

/// Implements `Iterator`, `DoubleEndedIterator`, `ExactSizeIterator` and
/// `FusedIterator` for a wrapper around a slice or vector iterator of
/// `(K, V)` pairs in its `inner` field, turning each pair into the wrapper's
/// item with `$map`.
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

            #[inline]
            fn count(self) -> usize {
                self.inner.len()
            }
        }

        impl<$($generics)*> DoubleEndedIterator for $name {
            #[inline]
            fn next_back(&mut self) -> Option<Self::Item> {
                self.inner.next_back().map($map)
            }
        }

        impl<$($generics)*> ExactSizeIterator for $name {
            #[inline]
            fn len(&self) -> usize {
                self.inner.len()
            }
        }

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

/// An iterator over the entries of a [`LinearMap`]. Created by
/// [`LinearMap::iter`].
pub struct Iter<'a, K, V> {
    inner: slice::Iter<'a, (K, V)>,
}
forward_iterator!({'a, K, V} Iter<'a, K, V>, (&'a K, &'a V), |(k, v)| (k, v));

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone(),
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over the entries of a [`LinearMap`]. Created by
/// [`LinearMap::iter_mut`].
pub struct IterMut<'a, K, V> {
    inner: slice::IterMut<'a, (K, V)>,
}
forward_iterator!(
    {'a, K, V} IterMut<'a, K, V>,
    (&'a K, &'a mut V),
    |(k, v): &'a mut (K, V)| (&*k, v)
);
debug_remaining!({'a, K, V} IterMut IterMut<'a, K, V>);

/// An owning iterator over the entries of a [`LinearMap`]. Created by
/// [`LinearMap::into_iter`].
pub struct IntoIter<K, V> {
    inner: vec::IntoIter<(K, V)>,
}
forward_iterator!({K, V} IntoIter<K, V>, (K, V), |pair| pair);
debug_remaining!({K, V} IntoIter IntoIter<K, V>);

/// A draining iterator over the entries of a [`LinearMap`]. Created by
/// [`LinearMap::drain`].
pub struct Drain<'a, K, V> {
    inner: vec::Drain<'a, (K, V)>,
}
forward_iterator!({'a, K, V} Drain<'a, K, V>, (K, V), |pair| pair);
debug_remaining!({'a, K, V} Drain Drain<'a, K, V>);

/// An iterator over the keys of a [`LinearMap`]. Created by
/// [`LinearMap::keys`].
pub struct Keys<'a, K, V> {
    inner: slice::Iter<'a, (K, V)>,
}
forward_iterator!({'a, K, V} Keys<'a, K, V>, &'a K, |(k, _)| k);

impl<K, V> Clone for Keys<'_, K, V> {
    fn clone(&self) -> Self {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<K: fmt::Debug, V> fmt::Debug for Keys<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An iterator over the values of a [`LinearMap`]. Created by
/// [`LinearMap::values`].
pub struct Values<'a, K, V> {
    inner: slice::Iter<'a, (K, V)>,
}
forward_iterator!({'a, K, V} Values<'a, K, V>, &'a V, |(_, v)| v);

impl<K, V> Clone for Values<'_, K, V> {
    fn clone(&self) -> Self {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<K, V: fmt::Debug> fmt::Debug for Values<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over the values of a [`LinearMap`]. Created by
/// [`LinearMap::values_mut`].
pub struct ValuesMut<'a, K, V> {
    inner: slice::IterMut<'a, (K, V)>,
}
forward_iterator!({'a, K, V} ValuesMut<'a, K, V>, &'a mut V, |(_, v): &'a mut (K, V)| v);
debug_remaining!({'a, K, V} ValuesMut ValuesMut<'a, K, V>);

/// An owning iterator over the keys of a [`LinearMap`]. Created by
/// [`LinearMap::into_keys`]. Each value is dropped as its key is yielded.
pub struct IntoKeys<K, V> {
    inner: vec::IntoIter<(K, V)>,
}
forward_iterator!({K, V} IntoKeys<K, V>, K, |(k, _)| k);
debug_remaining!({K, V} IntoKeys IntoKeys<K, V>);

/// An owning iterator over the values of a [`LinearMap`]. Created by
/// [`LinearMap::into_values`]. Each key is dropped as its value is yielded.
pub struct IntoValues<K, V> {
    inner: vec::IntoIter<(K, V)>,
}
forward_iterator!({K, V} IntoValues<K, V>, V, |(_, v)| v);
debug_remaining!({K, V} IntoValues IntoValues<K, V>);

/// Counts the buffer of key-value pairs, which is `0` for a map that has not
/// allocated yet.
impl<K, V> HeapSize for LinearMap<K, V> {
    fn heap_size(&self) -> usize {
        self.storage.capacity() * size_of::<(K, V)>()
    }
}

#[cfg(test)]
mod tests {
    // Test values are small and narrowed on purpose.
    #![allow(clippy::cast_possible_truncation)]
    use super::*;

    #[test]
    fn insert_and_get() {
        let mut map = LinearMap::new();
        assert_eq!(map.insert("a", 1), None);
        assert_eq!(map.insert("b", 2), None);
        assert_eq!(map.get("a"), Some(&1));
        assert_eq!(map.get("b"), Some(&2));
        assert_eq!(map.get("c"), None);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn insert_overwrites_existing_key() {
        let mut map = LinearMap::new();
        map.insert("a", 1);
        assert_eq!(map.insert("a", 2), Some(1));
        assert_eq!(map.get("a"), Some(&2));
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn remove_swaps_last_element_in() {
        let mut map = LinearMap::new();
        map.insert("a", 1);
        map.insert("b", 2);
        map.insert("c", 3);
        assert_eq!(map.remove("a"), Some(1));
        assert_eq!(map.len(), 2);
        assert!(!map.contains_key("a"));
        assert!(map.contains_key("b"));
        assert!(map.contains_key("c"));
    }

    #[test]
    fn get_mut_updates_value() {
        let mut map = LinearMap::new();
        map.insert("a", 1);
        *map.get_mut("a").unwrap() += 10;
        assert_eq!(map.get("a"), Some(&11));
    }

    #[test]
    fn iter_yields_all_pairs() {
        let mut map = LinearMap::new();
        map.insert(1, "one");
        map.insert(2, "two");
        let mut pairs: Vec<_> = map.iter().collect();
        pairs.sort();
        assert_eq!(pairs, vec![(&1, &"one"), (&2, &"two")]);
    }

    #[test]
    fn from_iterator_and_extend() {
        let map: LinearMap<_, _> = vec![(1, "a"), (2, "b")].into_iter().collect();
        assert_eq!(map.len(), 2);

        let mut map2 = LinearMap::new();
        map2.extend(vec![(1, "a"), (1, "override")]);
        assert_eq!(map2.get(&1), Some(&"override"));
        assert_eq!(map2.len(), 1);
    }

    #[test]
    fn index_operator() {
        let mut map = LinearMap::new();
        map.insert("a", 1);
        assert_eq!(map["a"], 1);
    }

    #[test]
    fn equality() {
        let mut a = LinearMap::new();
        a.insert(1, "x");
        a.insert(2, "y");
        let mut b = LinearMap::new();
        b.insert(2, "y");
        b.insert(1, "x");
        assert_eq!(a, b);
    }

    #[test]
    fn debug_format() {
        let mut map = LinearMap::new();
        map.insert("a", 1);
        assert_eq!(format!("{map:?}"), "{\"a\": 1}");
    }

    #[test]
    fn empty_map_basics() {
        let mut map: LinearMap<i32, i32> = LinearMap::default();
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
        assert_eq!(map.get(&1), None);
        assert_eq!(map.remove(&1), None);
        assert_eq!(map.remove_entry(&1), None);
        assert_eq!(map.iter().count(), 0);
        assert_eq!(map, LinearMap::new());
        map.clear();
        assert!(map.is_empty());
    }

    #[test]
    fn clear_keeps_capacity_and_empties() {
        let mut map = LinearMap::with_capacity(16);
        assert!(map.capacity() >= 16);
        map.insert(1, 1);
        map.clear();
        assert!(map.is_empty());
        assert!(map.capacity() >= 16);
        assert_eq!(map.get(&1), None);
    }

    #[test]
    fn get_key_value_and_remove_entry() {
        let mut map = LinearMap::new();
        map.insert(String::from("a"), 1);
        map.insert(String::from("b"), 2);
        assert_eq!(map.get_key_value("b"), Some((&String::from("b"), &2)));
        assert_eq!(map.remove_entry("a"), Some((String::from("a"), 1)));
        assert_eq!(map.remove_entry("a"), None);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn borrowed_key_lookups() {
        let mut map: LinearMap<String, i32> = LinearMap::new();
        map.insert("key".to_string(), 1);
        assert!(map.contains_key("key"));
        assert_eq!(map.get("key"), Some(&1));
        assert_eq!(map.get(&"key".to_string()), Some(&1));
        assert_eq!(map["key"], 1);
        assert_eq!(map.remove("key"), Some(1));
    }

    #[test]
    #[should_panic(expected = "no entry found for key")]
    fn index_missing_key_panics() {
        let map: LinearMap<i32, i32> = LinearMap::new();
        let _ = map[&1];
    }

    #[test]
    fn iter_mut_keys_values_and_values_mut() {
        let mut map: LinearMap<i32, i32> = (0..4).map(|i| (i, i)).collect();
        for (_, v) in &mut map {
            *v += 10;
        }
        for v in map.values_mut() {
            *v *= 2;
        }
        for (_, v) in &mut map {
            *v += 1;
        }
        let mut values: Vec<_> = map.values().copied().collect();
        values.sort_unstable();
        assert_eq!(values, vec![21, 23, 25, 27]);
        let mut keys: Vec<_> = map.keys().copied().collect();
        keys.sort_unstable();
        assert_eq!(keys, vec![0, 1, 2, 3]);
    }

    #[test]
    fn into_iter_by_value_and_exact_size() {
        let map: LinearMap<i32, &str> = [(1, "a"), (2, "b"), (3, "c")].into_iter().collect();
        assert_eq!(map.iter().len(), 3);
        let mut iter = map.into_iter();
        assert_eq!(iter.len(), 3);
        iter.next();
        assert_eq!(iter.len(), 2);
        assert_eq!(iter.size_hint(), (2, Some(2)));
        let mut rest: Vec<_> = iter.collect();
        rest.sort_unstable();
        assert_eq!(rest.len(), 2);
    }

    #[test]
    fn equality_distinguishes_different_maps() {
        let a: LinearMap<i32, i32> = [(1, 1), (2, 2)].into_iter().collect();
        let different_value: LinearMap<i32, i32> = [(1, 1), (2, 3)].into_iter().collect();
        let different_key: LinearMap<i32, i32> = [(1, 1), (3, 2)].into_iter().collect();
        let shorter = LinearMap::from([(1, 1)]);
        assert_ne!(a, different_value);
        assert_ne!(a, different_key);
        assert_ne!(a, shorter);
        assert_ne!(shorter, a);
    }

    #[test]
    fn clone_is_independent() {
        let mut a: LinearMap<i32, String> = LinearMap::new();
        a.insert(1, "x".to_string());
        let mut b = a.clone();
        b.get_mut(&1).unwrap().push('y');
        b.insert(2, "z".to_string());
        assert_eq!(a.get(&1).unwrap(), "x");
        assert_eq!(a.len(), 1);
        assert_eq!(b.get(&1).unwrap(), "xy");
    }

    #[test]
    fn zero_sized_keys_and_values() {
        let mut map: LinearMap<(), ()> = LinearMap::new();
        assert_eq!(map.insert((), ()), None);
        assert_eq!(map.insert((), ()), Some(()));
        assert_eq!(map.len(), 1);
        assert_eq!(map.remove(&()), Some(()));
        assert!(map.is_empty());
    }

    /// Counts how many `Tracked` values are alive via an `Rc` token.
    mod drops {
        use super::*;
        use std::rc::Rc;

        struct Tracked(#[allow(dead_code)] Rc<()>);

        fn live(token: &Rc<()>) -> usize {
            Rc::strong_count(token) - 1
        }

        fn filled(token: &Rc<()>, n: u32) -> LinearMap<u32, Tracked> {
            (0..n).map(|i| (i, Tracked(Rc::clone(token)))).collect()
        }

        #[test]
        fn dropping_map_drops_everything() {
            let token = Rc::new(());
            let map = filled(&token, 5);
            assert_eq!(live(&token), 5);
            drop(map);
            assert_eq!(live(&token), 0);
        }

        #[test]
        fn overwritten_value_is_returned_not_leaked() {
            let token = Rc::new(());
            let mut map = filled(&token, 3);
            let old = map.insert(1, Tracked(Rc::clone(&token)));
            assert!(old.is_some());
            assert_eq!(live(&token), 4);
            drop(old);
            assert_eq!(live(&token), 3);
        }

        #[test]
        fn remove_clear_and_retain_drop_values() {
            let token = Rc::new(());
            let mut map = filled(&token, 6);
            drop(map.remove(&0));
            assert_eq!(live(&token), 5);
            map.retain(|k, _| k % 2 == 0);
            assert_eq!(live(&token), 2); // 2 and 4 remain
            map.clear();
            assert_eq!(live(&token), 0);
        }

        #[test]
        fn partially_consumed_into_iter_drops_the_rest() {
            let token = Rc::new(());
            let map = filled(&token, 5);
            let mut iter = map.into_iter();
            drop(iter.next());
            assert_eq!(live(&token), 4);
            drop(iter);
            assert_eq!(live(&token), 0);
        }
    }

    /// Random operations checked against `std::collections::HashMap`.
    #[test]
    fn matches_hashmap_under_random_operations() {
        use std::collections::HashMap;

        // Small deterministic PRNG so the test needs no dependencies.
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

        let steps = if cfg!(miri) { 300 } else { 20_000 };
        let mut rng = Lcg(0x5EED);
        let mut map: LinearMap<u8, u32> = LinearMap::new();
        let mut model: HashMap<u8, u32> = HashMap::new();

        for step in 0..steps {
            let key = (rng.next() % 24) as u8; // few keys => many collisions
            let value = rng.next() as u32;
            match rng.next() % 9 {
                0..=2 => assert_eq!(map.insert(key, value), model.insert(key, value)),
                3 | 4 => assert_eq!(map.remove(&key), model.remove(&key)),
                5 => assert_eq!(map.get(&key), model.get(&key)),
                6 => {
                    if let (Some(a), Some(b)) = (map.get_mut(&key), model.get_mut(&key)) {
                        *a = a.wrapping_add(value);
                        *b = b.wrapping_add(value);
                    }
                    assert_eq!(map.contains_key(&key), model.contains_key(&key));
                }
                7 => {
                    let keep = |k: &u8| k % 3 != (value % 3) as u8;
                    map.retain(|k, _| keep(k));
                    model.retain(|k, _| keep(k));
                }
                _ => {
                    if step % 50 == 0 {
                        map.clear();
                        model.clear();
                    }
                }
            }
            assert_eq!(map.len(), model.len());
        }

        let as_model: HashMap<u8, u32> = map.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(as_model, model);
        assert_eq!(map.iter().count(), model.len()); // no duplicate keys stored
    }

    #[test]
    fn retain_removes_matching() {
        let mut map: LinearMap<i32, i32> = (0..5).map(|i| (i, i * i)).collect();
        map.retain(|k, _| k % 2 == 0);
        let mut keys: Vec<_> = map.keys().copied().collect();
        keys.sort_unstable();
        assert_eq!(keys, vec![0, 2, 4]);
    }

    // ---- entry API ----

    #[test]
    fn entry_or_insert_and_counting() {
        let mut counts: LinearMap<&str, i32> = LinearMap::new();
        for word in ["a", "b", "a", "c", "a", "b"] {
            *counts.entry(word).or_insert(0) += 1;
        }
        assert_eq!(counts["a"], 3);
        assert_eq!(counts["b"], 2);
        assert_eq!(counts["c"], 1);
        assert_eq!(counts.len(), 3);
    }

    #[test]
    fn entry_or_insert_keeps_existing_value() {
        let mut map = LinearMap::new();
        map.insert("k", 1);
        assert_eq!(*map.entry("k").or_insert(99), 1);
        assert_eq!(*map.entry("k").or_insert_with(|| 98), 1);
        assert_eq!(*map.entry("k").or_default(), 1);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn entry_or_insert_with_variants() {
        let mut map: LinearMap<String, usize> = LinearMap::new();
        assert_eq!(
            *map.entry("abc".to_string())
                .or_insert_with_key(std::string::String::len),
            3
        );
        let mut calls = 0;
        map.entry("abc".to_string()).or_insert_with(|| {
            calls += 1;
            0
        });
        assert_eq!(calls, 0); // occupied: closure not called
        let mut lists: LinearMap<i32, Vec<i32>> = LinearMap::new();
        lists.entry(1).or_default().push(1);
        lists.entry(1).or_default().push(2);
        assert_eq!(lists[&1], vec![1, 2]);
    }

    #[test]
    fn entry_and_modify_then_or_insert() {
        let mut map: LinearMap<&str, i32> = LinearMap::new();
        map.entry("a").and_modify(|v| *v += 1).or_insert(10);
        assert_eq!(map["a"], 10); // vacant: modify skipped, inserted
        map.entry("a").and_modify(|v| *v += 1).or_insert(10);
        assert_eq!(map["a"], 11); // occupied: modified
    }

    #[test]
    fn entry_key_and_occupied_vacant_variants() {
        let mut map: LinearMap<String, i32> = LinearMap::new();
        map.insert("here".to_string(), 1);

        match map.entry("here".to_string()) {
            Entry::Occupied(mut e) => {
                assert_eq!(e.key(), "here");
                assert_eq!(*e.get(), 1);
                *e.get_mut() += 1;
                assert_eq!(e.insert(10), 2);
                assert_eq!(*e.into_mut(), 10);
            }
            Entry::Vacant(_) => panic!("expected occupied"),
        }

        match map.entry("gone".to_string()) {
            Entry::Vacant(e) => {
                assert_eq!(e.key(), "gone");
                assert_eq!(e.into_key(), "gone");
            }
            Entry::Occupied(_) => panic!("expected vacant"),
        }
        assert_eq!(map.len(), 1); // into_key inserted nothing
        assert_eq!(map.entry("x".to_string()).key(), "x");
    }

    #[test]
    fn occupied_entry_remove() {
        let mut map: LinearMap<i32, &str> = [(1, "a"), (2, "b"), (3, "c")].into();
        match map.entry(1) {
            Entry::Occupied(e) => assert_eq!(e.remove(), "a"),
            Entry::Vacant(_) => panic!(),
        }
        match map.entry(2) {
            Entry::Occupied(e) => assert_eq!(e.remove_entry(), (2, "b")),
            Entry::Vacant(_) => panic!(),
        }
        assert_eq!(map.len(), 1);
        assert_eq!(map[&3], "c");
    }

    #[test]
    fn entry_debug_output() {
        let mut map: LinearMap<i32, i32> = LinearMap::new();
        map.insert(1, 2);
        assert_eq!(
            format!("{:?}", map.entry(1)),
            "Entry(OccupiedEntry { key: 1, value: 2 })"
        );
        assert_eq!(format!("{:?}", map.entry(5)), "Entry(VacantEntry(5))");
    }

    // ---- new collection API ----

    #[test]
    fn from_array_and_extend_by_reference() {
        let mut map = LinearMap::from([(1, 10), (2, 20), (1, 11)]);
        assert_eq!(map.len(), 2);
        assert_eq!(map[&1], 11); // later duplicate wins

        let other = LinearMap::from([(2, 21), (3, 30)]);
        map.extend(&other); // `&LinearMap` yields `(&K, &V)`
        assert_eq!(map[&2], 21);
        assert_eq!(map[&3], 30);
        assert_eq!(map.len(), 3);
    }

    #[test]
    fn reserve_and_shrink() {
        let mut map: LinearMap<u32, u32> = LinearMap::new();
        assert_eq!(map.capacity(), 0);
        map.reserve(50);
        assert!(map.capacity() >= 50);
        map.insert(1, 1);
        map.shrink_to(10);
        assert!(map.capacity() >= 10);
        map.shrink_to_fit();
        assert!(map.capacity() >= 1 && map.capacity() < 50);
    }

    #[test]
    fn extend_reserves_from_size_hint() {
        let mut map: LinearMap<u32, u32> = LinearMap::new();
        map.extend((0..100).map(|i| (i, i)));
        assert_eq!(map.len(), 100);
        // One up-front reservation, not repeated doubling from zero.
        assert!(map.capacity() >= 100);
    }

    #[test]
    fn drain_yields_everything_and_empties_the_map() {
        let mut map: LinearMap<i32, i32> = (0..5).map(|i| (i, i * 2)).collect();
        let cap = map.capacity();
        let mut drained: Vec<_> = map.drain().collect();
        drained.sort_unstable();
        assert_eq!(drained, vec![(0, 0), (1, 2), (2, 4), (3, 6), (4, 8)]);
        assert!(map.is_empty());
        assert_eq!(map.capacity(), cap);
        map.insert(1, 1); // still usable
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn dropping_or_leaking_a_drain_still_empties_the_map() {
        let mut map: LinearMap<i32, i32> = (0..5).map(|i| (i, i)).collect();
        let mut drain = map.drain();
        drain.next();
        drop(drain);
        assert!(map.is_empty());

        let mut map: LinearMap<i32, i32> = (0..5).map(|i| (i, i)).collect();
        std::mem::forget(map.drain());
        assert_eq!(map.len(), map.iter().count());
        assert!(map.is_empty());
        map.insert(7, 7);
        assert_eq!(map.get(&7), Some(&7));
    }

    #[test]
    fn into_keys_and_into_values() {
        let map: LinearMap<i32, &str> = [(1, "a"), (2, "b"), (3, "c")].into();
        let mut keys: Vec<_> = map.clone().into_keys().collect();
        keys.sort_unstable();
        assert_eq!(keys, vec![1, 2, 3]);
        let mut values: Vec<_> = map.into_values().collect();
        values.sort_unstable();
        assert_eq!(values, vec!["a", "b", "c"]);
    }

    // ---- iterator traits ----

    #[test]
    fn iterators_are_double_ended_exact_size_and_fused() {
        let mut map: LinearMap<i32, i32> = (0..4).map(|i| (i, i * 10)).collect();

        let mut iter = map.iter();
        assert_eq!(iter.len(), 4);
        assert_eq!(iter.next_back(), Some((&3, &30)));
        assert_eq!(iter.next(), Some((&0, &0)));
        assert_eq!(iter.len(), 2);
        assert_eq!(iter.by_ref().count(), 2);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None); // fused

        assert_eq!(
            map.keys().rev().copied().collect::<Vec<_>>(),
            vec![3, 2, 1, 0]
        );
        assert_eq!(map.values().len(), 4);
        assert_eq!(
            map.values_mut().rev().map(|v| *v).collect::<Vec<_>>(),
            vec![30, 20, 10, 0]
        );
        assert_eq!(map.iter_mut().len(), 4);
        assert_eq!(map.clone().into_iter().next_back(), Some((3, 30)));
        assert_eq!(map.clone().into_keys().len(), 4);
        assert_eq!(map.clone().into_values().next_back(), Some(30));
        assert_eq!(map.drain().len(), 4);
    }

    #[test]
    fn iterator_clone_and_debug() {
        let map: LinearMap<i32, &str> = [(1, "a"), (2, "b")].into();
        let iter = map.iter();
        let copy = iter.clone();
        assert_eq!(iter.count(), 2);
        assert_eq!(copy.count(), 2);

        assert_eq!(format!("{:?}", map.iter()), "[(1, \"a\"), (2, \"b\")]");
        assert_eq!(format!("{:?}", map.keys()), "[1, 2]");
        assert_eq!(format!("{:?}", map.values()), "[\"a\", \"b\"]");
        assert_eq!(map.keys().clone().count(), 2);
        assert_eq!(map.values().clone().count(), 2);

        let mut map = map;
        assert_eq!(format!("{:?}", map.iter_mut()), "IterMut { remaining: 2 }");
        assert_eq!(
            format!("{:?}", map.clone().into_iter()),
            "IntoIter { remaining: 2 }"
        );
    }

    #[test]
    fn iterator_types_are_nameable() {
        // Compile-time check that the iterator types are public.
        type Nameable<'a> = (
            Option<super::Iter<'a, i32, i32>>,
            Option<super::IterMut<'a, i32, i32>>,
            Option<super::IntoIter<i32, i32>>,
            Option<super::Keys<'a, i32, i32>>,
            Option<super::Values<'a, i32, i32>>,
            Option<super::ValuesMut<'a, i32, i32>>,
            Option<super::IntoKeys<i32, i32>>,
            Option<super::IntoValues<i32, i32>>,
            Option<super::Drain<'a, i32, i32>>,
            Option<super::Entry<'a, i32, i32>>,
            Option<super::OccupiedEntry<'a, i32, i32>>,
            Option<super::VacantEntry<'a, i32, i32>>,
        );
        let none: Nameable<'_> = Default::default();
        assert!(none.0.is_none());
    }

    // ---- block search (large maps of small plain keys) ----

    #[test]
    fn block_search_finds_every_key_at_every_length() {
        // Straddles the threshold and several block boundaries, including
        // lengths that are not a multiple of the block size.
        for n in 0..=(BLOCK_SEARCH_MIN_LEN * 3 + 5) as u32 {
            let map: LinearMap<u32, u32> = (0..n).map(|i| (i, i + 1000)).collect();
            for i in 0..n {
                assert_eq!(map.get(&i), Some(&(i + 1000)), "n={n} key={i}");
            }
            assert_eq!(map.get(&n), None, "n={n} miss");
            assert_eq!(map.get(&u32::MAX), None);
        }
    }

    #[test]
    fn block_search_agrees_with_plain_search() {
        for n in [0usize, 1, 7, 8, 9, 31, 32, 33, 63, 64, 65, 200] {
            let pairs: Vec<(u16, ())> = (0..n as u16).map(|i| (i.wrapping_mul(37), ())).collect();
            for probe in 0..300u16 {
                let plain = pairs.iter().position(|(k, ())| *k == probe);
                assert_eq!(block_position(&pairs, &probe), plain, "n={n} probe={probe}");
            }
        }
    }

    #[test]
    fn block_search_used_only_for_cheap_keys() {
        const {
            assert!(LinearMap::<u64, ()>::CHEAP_KEYS);
            assert!(LinearMap::<char, ()>::CHEAP_KEYS);
            assert!(!LinearMap::<String, ()>::CHEAP_KEYS);
            assert!(!LinearMap::<&str, ()>::CHEAP_KEYS); // 16 bytes
            assert!(!LinearMap::<[u64; 2], ()>::CHEAP_KEYS);
        }
    }

    #[test]
    fn large_map_matches_hashmap_under_random_operations() {
        use std::collections::HashMap;

        let mut state = 0x1234_5678_9abc_def0u64;
        let mut next = move || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            state >> 33
        };

        let steps = if cfg!(miri) { 400 } else { 30_000 };
        let mut map: LinearMap<u16, u32> = LinearMap::new();
        let mut model: HashMap<u16, u32> = HashMap::new();

        for _ in 0..steps {
            // ~150 distinct keys: the map regularly holds well over 32
            // entries, so the block search runs.
            let key = (next() % 150) as u16;
            let value = next() as u32;
            match next() % 6 {
                0 | 1 => assert_eq!(map.insert(key, value), model.insert(key, value)),
                2 => assert_eq!(map.remove(&key), model.remove(&key)),
                3 => assert_eq!(map.get(&key), model.get(&key)),
                4 => {
                    *map.entry(key).or_insert(0) += 1;
                    *model.entry(key).or_insert(0) += 1;
                }
                _ => assert_eq!(map.contains_key(&key), model.contains_key(&key)),
            }
            assert_eq!(map.len(), model.len());
        }
        let as_model: HashMap<u16, u32> = map.into_iter().collect();
        assert_eq!(as_model, model);
    }

    // ---- retain semantics and panic safety ----

    #[test]
    fn retain_preserves_order_and_can_mutate() {
        let mut map: LinearMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        map.retain(|k, v| {
            *v += 100;
            k % 3 != 0
        });
        let entries: Vec<_> = map.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(
            entries,
            vec![(1, 101), (2, 102), (4, 104), (5, 105), (7, 107), (8, 108)]
        );
    }

    #[test]
    fn retain_visits_each_entry_exactly_once() {
        let mut map: LinearMap<i32, ()> = (0..20).map(|i| (i, ())).collect();
        let mut seen = Vec::new();
        map.retain(|k, ()| {
            seen.push(*k);
            k % 2 == 0
        });
        seen.sort_unstable();
        assert_eq!(seen, (0..20).collect::<Vec<_>>());
        assert_eq!(map.len(), 10);
    }

    #[test]
    fn retain_panic_leaves_a_consistent_map() {
        use std::panic::{AssertUnwindSafe, catch_unwind};
        use std::rc::Rc;

        let token = Rc::new(());
        let mut map: LinearMap<i32, Rc<()>> = (0..8).map(|i| (i, Rc::clone(&token))).collect();
        let result = catch_unwind(AssertUnwindSafe(|| {
            map.retain(|k, _| {
                assert!(*k != 5, "boom");
                k % 2 == 0
            });
        }));
        assert!(result.is_err());

        // Still a valid map: keys and values in step, no duplicates, nothing
        // lost or double-dropped.
        assert_eq!(map.keys().count(), map.values().count());
        let mut keys: Vec<_> = map.keys().copied().collect();
        keys.sort_unstable();
        keys.dedup();
        assert_eq!(keys.len(), map.len());
        assert_eq!(Rc::strong_count(&token) - 1, map.len());
        for k in 0..8 {
            assert_eq!(map.contains_key(&k), keys.contains(&k));
        }
        drop(map);
        assert_eq!(Rc::strong_count(&token), 1);
    }

    // ---- drop accounting for the new consuming APIs ----

    mod new_drops {
        use super::*;
        use std::rc::Rc;

        fn filled(token: &Rc<()>, n: u32) -> LinearMap<u32, Rc<()>> {
            (0..n).map(|i| (i, Rc::clone(token))).collect()
        }

        fn live(token: &Rc<()>) -> usize {
            Rc::strong_count(token) - 1
        }

        #[test]
        fn drain_partially_consumed_drops_the_rest() {
            let token = Rc::new(());
            let mut map = filled(&token, 5);
            let mut drain = map.drain();
            drop(drain.next());
            assert_eq!(live(&token), 4);
            drop(drain);
            assert_eq!(live(&token), 0);
            assert!(map.is_empty());
        }

        #[test]
        fn into_keys_drops_each_value_and_the_rest_on_drop() {
            let token = Rc::new(());
            let map = filled(&token, 4);
            let mut keys = map.into_keys();
            assert_eq!(keys.next(), Some(0));
            assert_eq!(live(&token), 3); // the yielded pair's value is dropped
            drop(keys);
            assert_eq!(live(&token), 0);
        }

        #[test]
        fn into_values_yields_owned_values_and_drops_keys() {
            let token = Rc::new(());
            let map = filled(&token, 4);
            let mut values = map.into_values();
            let first = values.next();
            assert_eq!(live(&token), 4);
            drop(values);
            assert_eq!(live(&token), 1); // only `first` is left
            drop(first);
            assert_eq!(live(&token), 0);
        }

        #[test]
        fn entry_operations_drop_correctly() {
            let token = Rc::new(());
            let mut map = filled(&token, 3);
            if let Entry::Occupied(mut e) = map.entry(1) {
                drop(e.insert(Rc::clone(&token))); // old value dropped
            }
            assert_eq!(live(&token), 3);
            if let Entry::Occupied(e) = map.entry(2) {
                drop(e.remove());
            }
            assert_eq!(live(&token), 2);
            map.entry(9).or_insert_with(|| Rc::clone(&token));
            assert_eq!(live(&token), 3);
            drop(map);
            assert_eq!(live(&token), 0);
        }
    }

    #[test]
    fn heap_size_is_the_buffer_of_pairs() {
        let mut map = LinearMap::<u32, u64>::new();
        assert_eq!(map.heap_size(), 0);

        map.insert(1, 1);
        assert_eq!(map.heap_size(), map.capacity() * size_of::<(u32, u64)>());
        assert!(map.heap_size() >= size_of::<(u32, u64)>());

        let reserved = LinearMap::<u32, u64>::with_capacity(100);
        assert_eq!(reserved.heap_size(), reserved.capacity() * 16);
        assert!(reserved.heap_size() >= 100 * 16);
    }
}
