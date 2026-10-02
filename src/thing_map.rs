//! A map with one value per type.
//!
//! See [`ThingMap`] for details.

use crate::heap_size::HeapSize;
use std::any::TypeId;
use std::collections::hash_map;
use std::collections::{HashMap, TryReserveError};
use std::fmt;
use std::hash::BuildHasher;
use std::marker::PhantomData;

use crate::thing::{DEFAULT_THING_SIZE, RawThing, Thing};

pub use crate::type_id_hasher::{TypeIdBuildHasher, TypeIdHasher};

/// A map that holds at most one value of each type, looked up by the type.
///
/// It works like a `HashMap` whose keys are types: the type is a generic
/// argument of the method (`map.get::<Config>()`) instead of a value, and the
/// method names and behavior follow [`std::collections::HashMap`] as closely
/// as that allows. Typical uses are shared resources, per-type registries and
/// caches: one place to keep a `Config`, a `Cache`, and so on.
///
/// Values up to `SIZE` bytes (24 by default, enough for a `Vec` or `String`)
/// are stored inline in the map; larger ones are boxed. See [`Thing`] for the
/// rules, and [`fits`](Self::fits) to check whether a type can be stored.
///
/// Lookups are fast: keys are hashed with a cheap pass-through hasher by
/// default ([`TypeIdBuildHasher`]), and a lookup does no further type check.
///
/// # Differences from `HashMap`
///
/// * Methods that take a key take a type instead: `get::<T>()`,
///   `insert::<T>(value)`, `entry::<T>()`.
/// * There is no iteration (`iter`, `keys`, `values`, `drain`, `retain`,
///   `into_iter`): the values are erased, so there is nothing useful to do
///   with them without naming their types. Use `len`, `is_empty`,
///   `contains_key` and `clear` for what remains.
/// * There is no `Extend`, `FromIterator`, `Clone`, `PartialEq` or `Index`:
///   the values are erased, so the map cannot clone or compare them.
///
/// # Thread safety
///
/// Like `Thing`, a `ThingMap` is neither `Send` nor `Sync`, since the values
/// it holds are not required to be. For a map that is, whose values must all
/// be `Send + Sync`, see [`SThingMap`](crate::SThingMap).
///
/// ```compile_fail,E0277
/// fn assert_send<T: Send>() {}
/// assert_send::<anythingy::ThingMap<24>>();
/// ```
///
/// # Examples
///
/// ```
/// use anythingy::ThingMap;
///
/// struct Config {
///     verbose: bool,
/// }
/// struct Counter(u32);
///
/// let mut resources = ThingMap::<24>::new();
/// resources.insert(Config { verbose: true });
/// resources.insert(Counter(0));
///
/// resources.get_mut::<Counter>().unwrap().0 += 1;
/// assert_eq!(resources.get::<Counter>().unwrap().0, 1);
/// assert!(resources.get::<Config>().unwrap().verbose);
/// assert!(resources.get::<String>().is_none()); // nothing of that type
///
/// // Like `HashMap`, `entry` inserts on first use.
/// resources.entry::<Vec<i32>>().or_default().push(1);
/// resources.entry::<Vec<i32>>().or_default().push(2);
/// assert_eq!(resources.get::<Vec<i32>>().unwrap(), &[1, 2]);
/// ```
pub struct ThingMap<const SIZE: usize = DEFAULT_THING_SIZE, S = TypeIdBuildHasher> {
    /// Invariant: the erased value stored under a `TypeId` is a value of
    /// exactly that type. Only [`insert`](Self::insert) and the entry types
    /// add values, and they always use the `TypeId` of the value's own type
    /// as the key.
    map: HashMap<TypeId, RawThing<SIZE>, S>,
}

impl<const SIZE: usize> ThingMap<SIZE, TypeIdBuildHasher> {
    /// Creates an empty map. Does not allocate.
    #[must_use]
    pub fn new() -> Self {
        Self::with_hasher(TypeIdBuildHasher::default())
    }

    /// Creates an empty map with room for at least `capacity` types.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, TypeIdBuildHasher::default())
    }
}

impl<const SIZE: usize, S> ThingMap<SIZE, S> {
    /// Creates an empty map that hashes its keys with `hash_builder`.
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            map: HashMap::with_hasher(hash_builder),
        }
    }

    /// Creates an empty map with room for at least `capacity` types, hashing
    /// its keys with `hash_builder`.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            map: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    /// Returns a reference to the map's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        self.map.hasher()
    }

    /// Returns `true` if a value of type `T` can be stored in this map: `SIZE`
    /// is large enough to hold it, or a `Box` of it. See
    /// [`Thing::fitting`].
    #[must_use]
    pub const fn fits<T: 'static>() -> bool {
        Thing::<SIZE>::fitting::<T>()
    }

    /// Returns the number of types the map holds a value for.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the map holds nothing.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns how many types the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Removes every value, dropping them. Keeps the allocated capacity.
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl<const SIZE: usize, S: BuildHasher> ThingMap<SIZE, S> {
    /// Reserves room for at least `additional` more types.
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional);
    }

    /// Tries to reserve room for at least `additional` more types.
    ///
    /// # Errors
    ///
    /// Returns an error if the new capacity overflows or the allocator fails.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.map.try_reserve(additional)
    }

    /// Shrinks the capacity as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
    }

    /// Shrinks the capacity to `min_capacity` or the current length,
    /// whichever is larger.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.map.shrink_to(min_capacity);
    }

    /// Returns `true` if the map holds a value of type `T`.
    pub fn contains_key<T: 'static>(&self) -> bool {
        self.map.contains_key(&TypeId::of::<T>())
    }

    /// Stores `value`, replacing and returning the previous value of the same
    /// type, if any.
    ///
    /// # Panics
    ///
    /// Panics if `SIZE` is too small to hold a `Box<T>`; see [`Thing::new`].
    /// [`fits`](Self::fits) tells whether that is the case.
    pub fn insert<T: 'static>(&mut self, value: T) -> Option<T> {
        let old = self.map.insert(TypeId::of::<T>(), RawThing::new(value))?;
        // SAFETY: `old` was stored under `TypeId::of::<T>()`, so by the type
        // invariant of `map` it holds a `T`.
        Some(unsafe { old.get_unchecked::<T>() })
    }

    /// Returns a reference to the value of type `T`, if there is one.
    pub fn get<T: 'static>(&self) -> Option<&T> {
        let thing = self.map.get(&TypeId::of::<T>())?;
        // SAFETY: found under `TypeId::of::<T>()`, so it holds a `T` (type
        // invariant of `map`).
        Some(unsafe { thing.get_ref_unchecked::<T>() })
    }

    /// Returns the stored key and a reference to the value of type `T`, if
    /// there is one.
    pub fn get_key_value<T: 'static>(&self) -> Option<(&TypeId, &T)> {
        let (id, thing) = self.map.get_key_value(&TypeId::of::<T>())?;
        // SAFETY: as in `get`.
        Some((id, unsafe { thing.get_ref_unchecked::<T>() }))
    }

    /// Returns a mutable reference to the value of type `T`, if there is one.
    pub fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
        let thing = self.map.get_mut(&TypeId::of::<T>())?;
        // SAFETY: as in `get`.
        Some(unsafe { thing.get_mut_unchecked::<T>() })
    }

    /// Removes and returns the value of type `T`, if there is one.
    pub fn remove<T: 'static>(&mut self) -> Option<T> {
        let thing = self.map.remove(&TypeId::of::<T>())?;
        // SAFETY: as in `get`.
        Some(unsafe { thing.get_unchecked::<T>() })
    }

    /// Removes and returns the stored key and the value of type `T`, if there
    /// is one.
    pub fn remove_entry<T: 'static>(&mut self) -> Option<(TypeId, T)> {
        let (id, thing) = self.map.remove_entry(&TypeId::of::<T>())?;
        // SAFETY: as in `get`.
        Some((id, unsafe { thing.get_unchecked::<T>() }))
    }

    /// Gets the entry for type `T`, for in-place insertion or update with a
    /// single lookup.
    ///
    /// # Panics
    ///
    /// Inserting through the entry panics if `SIZE` is too small to hold a
    /// `Box<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::ThingMap;
    ///
    /// let mut map = ThingMap::<24>::new();
    /// *map.entry::<u32>().or_insert(0) += 5;
    /// map.entry::<u32>().and_modify(|n| *n *= 2).or_insert(0);
    /// assert_eq!(map.get::<u32>(), Some(&10));
    /// ```
    pub fn entry<T: 'static>(&mut self) -> Entry<'_, T, SIZE> {
        match self.map.entry(TypeId::of::<T>()) {
            hash_map::Entry::Occupied(inner) => Entry::Occupied(OccupiedEntry {
                inner,
                _marker: PhantomData,
            }),
            hash_map::Entry::Vacant(inner) => Entry::Vacant(VacantEntry {
                inner,
                _marker: PhantomData,
            }),
        }
    }
}

impl<const SIZE: usize, S: Default> Default for ThingMap<SIZE, S> {
    fn default() -> Self {
        Self::with_hasher(S::default())
    }
}

impl<const SIZE: usize, S> fmt::Debug for ThingMap<SIZE, S> {
    /// Lists the `TypeId`s of the stored values.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.map.keys()).finish()
    }
}

/// A view into the entry for type `T` in a [`ThingMap`], which is either
/// vacant or occupied. Created by [`ThingMap::entry`].
pub enum Entry<'a, T: 'static, const SIZE: usize = DEFAULT_THING_SIZE> {
    /// A value of type `T` is present.
    Occupied(OccupiedEntry<'a, T, SIZE>),
    /// There is no value of type `T`.
    Vacant(VacantEntry<'a, T, SIZE>),
}

/// A view into an occupied entry of a [`ThingMap`].
pub struct OccupiedEntry<'a, T: 'static, const SIZE: usize = DEFAULT_THING_SIZE> {
    /// Invariant: its key is `TypeId::of::<T>()`, so its value is a `T`.
    inner: hash_map::OccupiedEntry<'a, TypeId, RawThing<SIZE>>,
    _marker: PhantomData<fn() -> T>,
}

/// A view into a vacant entry of a [`ThingMap`].
pub struct VacantEntry<'a, T: 'static, const SIZE: usize = DEFAULT_THING_SIZE> {
    /// Invariant: its key is `TypeId::of::<T>()`.
    inner: hash_map::VacantEntry<'a, TypeId, RawThing<SIZE>>,
    _marker: PhantomData<fn() -> T>,
}

impl<'a, T: 'static, const SIZE: usize> Entry<'a, T, SIZE> {
    /// Returns the entry's key, the `TypeId` of `T`.
    #[must_use]
    pub fn key(&self) -> &TypeId {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    /// Inserts `default` if the entry is vacant, and returns a mutable
    /// reference to the value.
    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Inserts the result of `default` if the entry is vacant, and returns a
    /// mutable reference to the value. If `default` panics, the map is left
    /// unchanged.
    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Like [`or_insert_with`](Self::or_insert_with), but `default` receives
    /// the key.
    pub fn or_insert_with_key<F: FnOnce(&TypeId) -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Inserts `T::default()` if the entry is vacant, and returns a mutable
    /// reference to the value.
    pub fn or_default(self) -> &'a mut T
    where
        T: Default,
    {
        self.or_insert_with(T::default)
    }

    /// Applies `f` to the value if the entry is occupied, then returns the
    /// entry for further chaining.
    #[must_use]
    pub fn and_modify<F: FnOnce(&mut T)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }

    /// Stores `value` (replacing the old one if occupied) and returns the
    /// now-occupied entry.
    pub fn insert_entry(self, value: T) -> OccupiedEntry<'a, T, SIZE> {
        match self {
            Entry::Occupied(mut entry) => {
                entry.insert(value);
                entry
            }
            Entry::Vacant(entry) => entry.insert_entry(value),
        }
    }
}

impl<'a, T: 'static, const SIZE: usize> OccupiedEntry<'a, T, SIZE> {
    /// Returns the entry's key, the `TypeId` of `T`.
    #[must_use]
    pub fn key(&self) -> &TypeId {
        self.inner.key()
    }

    /// Returns a reference to the value.
    #[must_use]
    pub fn get(&self) -> &T {
        // SAFETY: the entry's key is `TypeId::of::<T>()` (field invariant),
        // so the value is a `T`.
        unsafe { self.inner.get().get_ref_unchecked::<T>() }
    }

    /// Returns a mutable reference to the value.
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: as in `get`.
        unsafe { self.inner.get_mut().get_mut_unchecked::<T>() }
    }

    /// Converts the entry into a mutable reference to the value, with the
    /// lifetime of the map.
    #[must_use]
    pub fn into_mut(self) -> &'a mut T {
        // SAFETY: as in `get`.
        unsafe { self.inner.into_mut().get_mut_unchecked::<T>() }
    }

    /// Replaces the value, returning the old one.
    ///
    /// # Panics
    ///
    /// Panics if `SIZE` is too small to hold a `Box<T>`.
    pub fn insert(&mut self, value: T) -> T {
        let old = self.inner.insert(RawThing::new(value));
        // SAFETY: as in `get`.
        unsafe { old.get_unchecked::<T>() }
    }

    /// Removes the value from the map and returns it.
    #[must_use]
    pub fn remove(self) -> T {
        // SAFETY: as in `get`.
        unsafe { self.inner.remove().get_unchecked::<T>() }
    }

    /// Removes the value from the map and returns the key and the value.
    #[must_use]
    pub fn remove_entry(self) -> (TypeId, T) {
        let (id, thing) = self.inner.remove_entry();
        // SAFETY: as in `get`.
        (id, unsafe { thing.get_unchecked::<T>() })
    }
}

impl<'a, T: 'static, const SIZE: usize> VacantEntry<'a, T, SIZE> {
    /// Returns the key that would be used, the `TypeId` of `T`.
    #[must_use]
    pub fn key(&self) -> &TypeId {
        self.inner.key()
    }

    /// Takes ownership of the key.
    #[must_use]
    pub fn into_key(self) -> TypeId {
        self.inner.into_key()
    }

    /// Stores `value` and returns a mutable reference to it.
    ///
    /// # Panics
    ///
    /// Panics if `SIZE` is too small to hold a `Box<T>`.
    pub fn insert(self, value: T) -> &'a mut T {
        let thing = self.inner.insert(RawThing::new(value));
        // SAFETY: the value was just created from a `T`.
        unsafe { thing.get_mut_unchecked::<T>() }
    }

    /// Stores `value` and returns the now-occupied entry.
    ///
    /// # Panics
    ///
    /// Panics if `SIZE` is too small to hold a `Box<T>`.
    pub fn insert_entry(self, value: T) -> OccupiedEntry<'a, T, SIZE> {
        OccupiedEntry {
            inner: self.inner.insert_entry(RawThing::new(value)),
            _marker: PhantomData,
        }
    }
}

impl<T: 'static, const SIZE: usize> fmt::Debug for Entry<'_, T, SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Entry::Occupied(entry) => f.debug_tuple("Entry").field(entry).finish(),
            Entry::Vacant(entry) => f.debug_tuple("Entry").field(entry).finish(),
        }
    }
}

impl<T: 'static, const SIZE: usize> fmt::Debug for OccupiedEntry<'_, T, SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("type", &core::any::type_name::<T>())
            .finish()
    }
}

impl<T: 'static, const SIZE: usize> fmt::Debug for VacantEntry<'_, T, SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VacantEntry")
            .field("type", &core::any::type_name::<T>())
            .finish()
    }
}

/// A lower bound: room for as many values as the map can hold without growing,
/// plus the allocation of each value that is boxed, see [`Thing`]'s
/// implementation. What the values own is not included.
///
/// The standard library does not expose how a hash table is laid out, so the
/// control data that it keeps for each bucket, and the buckets beyond the
/// capacity, are left out.
impl<const SIZE: usize, S> HeapSize for ThingMap<SIZE, S> {
    fn heap_size(&self) -> usize {
        let table = self.map.capacity() * size_of::<(TypeId, RawThing<SIZE>)>();
        let boxes: usize = self.map.values().map(RawThing::heap_size).sum();
        table + boxes
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::RandomState;
    use std::rc::Rc;

    #[derive(Debug, PartialEq)]
    struct Config {
        verbose: bool,
    }

    #[derive(Debug, PartialEq)]
    struct Counter(u32);

    #[derive(Debug, PartialEq, Default)]
    struct Marker;

    type Map = ThingMap<24>;

    // ---- basics ----

    #[test]
    fn insert_get_and_get_mut() {
        let mut map = Map::new();
        assert!(map.is_empty());
        assert_eq!(map.insert(Config { verbose: true }), None);
        assert_eq!(map.insert(Counter(1)), None);
        assert_eq!(map.len(), 2);

        assert_eq!(map.get::<Config>(), Some(&Config { verbose: true }));
        map.get_mut::<Counter>().unwrap().0 += 41;
        assert_eq!(map.get::<Counter>(), Some(&Counter(42)));
        assert!(map.contains_key::<Config>());
    }

    #[test]
    fn a_missing_type_is_none_even_if_others_exist() {
        let mut map = Map::new();
        map.insert(1u32);
        assert!(map.get::<u64>().is_none());
        assert!(map.get_mut::<i32>().is_none());
        assert!(map.get::<String>().is_none());
        assert!(!map.contains_key::<u64>());
        assert_eq!(map.remove::<u64>(), None);
        assert!(map.get_key_value::<u64>().is_none());
        assert!(map.remove_entry::<u64>().is_none());
        assert_eq!(map.get::<u32>(), Some(&1));
    }

    #[test]
    fn insert_replaces_and_returns_the_old_value() {
        let mut map = Map::new();
        assert_eq!(map.insert(String::from("first")), None);
        assert_eq!(
            map.insert(String::from("second")),
            Some(String::from("first"))
        );
        assert_eq!(map.len(), 1);
        assert_eq!(map.get::<String>().unwrap(), "second");
    }

    #[test]
    fn remove_get_key_value_and_remove_entry() {
        let mut map = Map::new();
        map.insert(Counter(7));
        map.insert(1u8);

        let (id, value) = map.get_key_value::<Counter>().unwrap();
        assert_eq!(*id, TypeId::of::<Counter>());
        assert_eq!(value, &Counter(7));

        assert_eq!(
            map.remove_entry::<Counter>(),
            Some((TypeId::of::<Counter>(), Counter(7)))
        );
        assert_eq!(map.remove::<Counter>(), None);
        assert!(!map.contains_key::<Counter>());
        assert_eq!(map.remove::<u8>(), Some(1));
        assert!(map.is_empty());
    }

    #[test]
    fn similar_looking_types_do_not_get_mixed_up() {
        struct Meters(i64);
        struct Seconds(i64);
        let mut map = Map::new();
        map.insert(Meters(1));
        map.insert(Seconds(2));
        map.insert(3u32);
        map.insert(4i32);
        map.insert(5u64);
        map.insert(6i64);
        assert_eq!(map.get::<Meters>().unwrap().0, 1);
        assert_eq!(map.get::<Seconds>().unwrap().0, 2);
        assert_eq!(map.get::<u32>(), Some(&3));
        assert_eq!(map.get::<i32>(), Some(&4));
        assert_eq!(map.get::<u64>(), Some(&5));
        assert_eq!(map.get::<i64>(), Some(&6));
        assert_eq!(map.len(), 6);
    }

    #[test]
    fn references_and_generic_instances_are_distinct_types() {
        let mut map = Map::new();
        map.insert(vec![1u8]);
        map.insert(vec![1u16]);
        map.insert(Some(1u8));
        map.insert("static text");
        assert_eq!(map.get::<Vec<u8>>().unwrap(), &vec![1u8]);
        assert_eq!(map.get::<Vec<u16>>().unwrap(), &vec![1u16]);
        assert_eq!(map.get::<Option<u8>>(), Some(&Some(1)));
        assert_eq!(map.get::<&'static str>(), Some(&"static text"));
        assert!(map.get::<Option<u16>>().is_none());
    }

    // ---- storage sizes ----

    #[test]
    fn inline_boxed_and_zero_sized_values_all_work() {
        let mut map = Map::new();
        map.insert(7u8); // inline
        map.insert([9u64; 16]); // 128 bytes: boxed
        map.insert(Marker); // zero-sized

        assert_eq!(map.get::<u8>(), Some(&7));
        assert_eq!(map.get::<[u64; 16]>().unwrap()[15], 9);
        assert_eq!(map.get::<Marker>(), Some(&Marker));
        map.get_mut::<[u64; 16]>().unwrap()[0] = 1;
        assert_eq!(map.remove::<[u64; 16]>().unwrap()[0], 1);
        assert_eq!(map.remove::<Marker>(), Some(Marker));
    }

    #[test]
    fn over_aligned_values_are_boxed_and_work() {
        #[repr(align(64))]
        #[derive(Debug, PartialEq)]
        struct Aligned(u8);

        let mut map = ThingMap::<32>::new();
        assert_eq!(map.insert(Aligned(1)), None);
        assert_eq!(map.get::<Aligned>(), Some(&Aligned(1)));
        assert_eq!(
            std::ptr::from_ref::<Aligned>(map.get::<Aligned>().unwrap()) as usize % 64,
            0
        );
        assert_eq!(map.insert(Aligned(2)), Some(Aligned(1)));
    }

    #[test]
    fn a_small_size_boxes_what_does_not_fit() {
        let mut map = ThingMap::<8>::new();
        assert!(ThingMap::<8>::fits::<String>()); // boxed: a Box fits in 8 bytes
        map.insert(String::from("boxed"));
        map.insert(1u32);
        assert_eq!(map.get::<String>().unwrap(), "boxed");
        assert_eq!(map.remove::<String>().as_deref(), Some("boxed"));
    }

    #[test]
    #[should_panic(expected = "too small")]
    fn insert_panics_when_size_cannot_even_hold_a_box() {
        assert!(!ThingMap::<4>::fits::<String>());
        let mut map = ThingMap::<4>::new();
        map.insert(String::from("x"));
    }

    // ---- entry API ----

    #[test]
    fn entry_or_insert_and_counting() {
        let mut map = Map::new();
        for _ in 0..3 {
            *map.entry::<u32>().or_insert(0) += 1;
        }
        assert_eq!(map.get::<u32>(), Some(&3));
        // An existing value is kept.
        assert_eq!(*map.entry::<u32>().or_insert(99), 3);
        assert_eq!(map.len(), 1);
    }

    #[test]
    #[allow(clippy::unwrap_or_default)]
    fn entry_or_insert_with_variants() {
        let mut map = Map::new();
        map.entry::<Vec<i32>>().or_insert_with(Vec::new).push(1);
        map.entry::<Vec<i32>>()
            .or_insert_with(|| unreachable!("value exists"))
            .push(2);
        assert_eq!(map.get::<Vec<i32>>().unwrap(), &[1, 2]);

        let mut seen = None;
        map.entry::<String>().or_insert_with_key(|id| {
            seen = Some(*id);
            String::from("made")
        });
        assert_eq!(seen, Some(TypeId::of::<String>()));
        map.entry::<String>()
            .or_insert_with_key(|_| unreachable!("value exists"));

        assert_eq!(map.entry::<Marker>().or_default(), &mut Marker);
        *map.entry::<u8>().or_default() += 3;
        *map.entry::<u8>().or_default() += 4;
        assert_eq!(map.get::<u8>(), Some(&7));
    }

    #[test]
    fn entry_and_modify_then_or_insert() {
        let mut map = Map::new();
        map.entry::<Counter>()
            .and_modify(|c| c.0 += 1)
            .or_insert(Counter(10));
        assert_eq!(map.get::<Counter>(), Some(&Counter(10))); // vacant: not modified
        map.entry::<Counter>()
            .and_modify(|c| c.0 += 1)
            .or_insert(Counter(10));
        assert_eq!(map.get::<Counter>(), Some(&Counter(11)));
    }

    #[test]
    fn entry_key_and_occupied_vacant_variants() {
        let mut map = Map::new();
        map.insert(String::from("here"));

        assert_eq!(*map.entry::<String>().key(), TypeId::of::<String>());
        match map.entry::<String>() {
            Entry::Occupied(mut entry) => {
                assert_eq!(*entry.key(), TypeId::of::<String>());
                assert_eq!(entry.get(), "here");
                entry.get_mut().push('!');
                assert_eq!(entry.insert(String::from("new")), "here!");
                assert_eq!(entry.into_mut(), "new");
            }
            Entry::Vacant(_) => panic!("expected occupied"),
        }

        match map.entry::<u8>() {
            Entry::Vacant(entry) => {
                assert_eq!(*entry.key(), TypeId::of::<u8>());
                assert_eq!(entry.into_key(), TypeId::of::<u8>());
            }
            Entry::Occupied(_) => panic!("expected vacant"),
        }
        assert!(!map.contains_key::<u8>()); // into_key inserted nothing
    }

    #[test]
    fn occupied_entry_remove_and_remove_entry() {
        let mut map = Map::new();
        map.insert(1u8);
        map.insert(2u16);
        match map.entry::<u8>() {
            Entry::Occupied(entry) => assert_eq!(entry.remove(), 1),
            Entry::Vacant(_) => panic!(),
        }
        match map.entry::<u16>() {
            Entry::Occupied(entry) => {
                assert_eq!(entry.remove_entry(), (TypeId::of::<u16>(), 2));
            }
            Entry::Vacant(_) => panic!(),
        }
        assert!(map.is_empty());
    }

    #[test]
    fn insert_entry_variants() {
        let mut map = Map::new();
        let entry = map.entry::<u32>().insert_entry(1); // vacant
        assert_eq!(*entry.get(), 1);
        let entry = map.entry::<u32>().insert_entry(2); // occupied: replaced
        assert_eq!(*entry.get(), 2);
        assert_eq!(map.len(), 1);

        match map.entry::<u64>() {
            Entry::Vacant(vacant) => assert_eq!(*vacant.insert_entry(5).get(), 5),
            Entry::Occupied(_) => panic!(),
        }
        assert_eq!(map.get::<u64>(), Some(&5));
    }

    #[test]
    fn entry_debug_output() {
        let mut map = Map::new();
        map.insert(1u8);
        assert_eq!(
            format!("{:?}", map.entry::<u8>()),
            "Entry(OccupiedEntry { type: \"u8\" })"
        );
        assert_eq!(
            format!("{:?}", map.entry::<u16>()),
            "Entry(VacantEntry { type: \"u16\" })"
        );
    }

    #[test]
    fn a_panicking_initializer_leaves_the_map_unchanged() {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        let mut map = Map::new();
        map.insert(1u8);
        let result = catch_unwind(AssertUnwindSafe(|| {
            map.entry::<String>().or_insert_with(|| panic!("no value"));
        }));
        assert!(result.is_err());
        assert_eq!(map.len(), 1);
        assert!(!map.contains_key::<String>());
        map.insert(String::from("fine"));
        assert_eq!(map.get::<String>().unwrap(), "fine");
    }

    // ---- housekeeping ----

    #[test]
    fn capacity_reserve_shrink_and_clear() {
        let mut map = ThingMap::<24>::with_capacity(8);
        assert!(map.capacity() >= 8);
        map.reserve(32);
        assert!(map.capacity() >= 32);
        map.try_reserve(64).unwrap();
        assert!(map.capacity() >= 64);

        map.insert(1u8);
        map.insert(2u16);
        map.clear();
        assert!(map.is_empty());
        assert!(map.capacity() >= 64); // clear keeps the capacity
        assert!(map.get::<u8>().is_none());
        map.shrink_to(16);
        assert!(map.capacity() >= 16 && map.capacity() < 64);
        map.shrink_to_fit();
        assert!(map.capacity() < 16);
    }

    #[test]
    fn default_and_debug() {
        let mut map: ThingMap = ThingMap::default();
        assert!(map.is_empty());
        map.insert(1u8);
        let debug = format!("{map:?}");
        assert!(debug.starts_with("{TypeId("), "{debug}");
        assert_eq!(debug.matches("TypeId").count(), 1);
    }

    #[test]
    fn custom_hasher_and_hasher_accessor() {
        let mut map = ThingMap::<24, RandomState>::with_hasher(RandomState::new());
        map.insert(1u8);
        map.insert(String::from("s"));
        assert_eq!(map.get::<u8>(), Some(&1));
        let _: &RandomState = map.hasher();

        let map = ThingMap::<24, RandomState>::with_capacity_and_hasher(4, RandomState::new());
        assert!(map.capacity() >= 4);
        let map: ThingMap<24, RandomState> = ThingMap::default();
        assert!(map.is_empty());
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn entries_store_the_type_id_once_in_release_builds() {
        assert_eq!(core::mem::size_of::<(TypeId, RawThing<24>)>(), 48);
        assert!(
            core::mem::size_of::<(TypeId, RawThing<24>)>()
                < core::mem::size_of::<(TypeId, Thing<24>)>()
        );
    }

    #[test]
    fn entry_types_are_nameable() {
        type Nameable<'a> = (
            Option<super::Entry<'a, u8>>,
            Option<super::OccupiedEntry<'a, u8>>,
            Option<super::VacantEntry<'a, u8>>,
        );
        let none: Nameable<'_> = Default::default();
        assert!(none.0.is_none());
    }

    // ---- drop accounting ----

    fn live(token: &Rc<()>) -> usize {
        Rc::strong_count(token) - 1
    }

    #[test]
    fn values_are_dropped_exactly_once() {
        let token = Rc::new(());
        let mut map = Map::new();
        map.insert(Rc::clone(&token)); // inline
        map.insert((Rc::clone(&token), [0u64; 8])); // boxed
        assert_eq!(live(&token), 2);

        // Replacing returns the old value, which is dropped here.
        drop(map.insert(Rc::clone(&token)));
        assert_eq!(live(&token), 2);

        drop(map.remove::<Rc<()>>());
        assert_eq!(live(&token), 1);
        map.clear();
        assert_eq!(live(&token), 0);

        map.insert(Rc::clone(&token));
        map.insert((Rc::clone(&token), [0u64; 8]));
        drop(map);
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn entry_operations_drop_correctly() {
        let token = Rc::new(());
        let mut map = Map::new();
        map.entry::<Rc<()>>().or_insert(Rc::clone(&token));
        assert_eq!(live(&token), 1);
        // A default that is not needed is never even created.
        map.entry::<Rc<()>>().or_insert_with(|| Rc::clone(&token));
        assert_eq!(live(&token), 1);
        // An unused `or_insert` argument is dropped.
        map.entry::<Rc<()>>().or_insert(Rc::clone(&token));
        assert_eq!(live(&token), 1);
        match map.entry::<Rc<()>>() {
            Entry::Occupied(mut entry) => drop(entry.insert(Rc::clone(&token))),
            Entry::Vacant(_) => panic!(),
        }
        assert_eq!(live(&token), 1);
        match map.entry::<Rc<()>>() {
            Entry::Occupied(entry) => drop(entry.remove()),
            Entry::Vacant(_) => panic!(),
        }
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn many_types_in_one_map() {
        struct Marked<const N: usize>(usize);
        let mut map = Map::new();

        macro_rules! insert_all {
            ($($n:literal)*) => {
                $( map.insert(Marked::<$n>($n)); )*
            };
        }
        macro_rules! check_all {
            ($($n:literal)*) => {
                $( assert_eq!(map.get::<Marked<$n>>().unwrap().0, $n); )*
            };
        }
        insert_all!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31);
        assert_eq!(map.len(), 32);
        check_all!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31);
        assert!(map.get::<Marked<32>>().is_none());
    }

    #[test]
    fn heap_size_is_zero_for_an_empty_map() {
        assert_eq!(ThingMap::<24>::new().heap_size(), 0);
        assert_eq!(ThingMap::<24>::with_capacity(0).heap_size(), 0);
    }

    #[test]
    fn heap_size_counts_the_room_for_values_and_the_boxed_ones() {
        let mut map = ThingMap::<24>::with_capacity(7);
        let table = map.heap_size();
        assert!(table >= 7 * size_of::<(TypeId, RawThing<24>)>());
        assert_eq!(table, map.capacity() * size_of::<(TypeId, RawThing<24>)>());

        // Inline values add nothing to the table that is already there.
        map.insert(1_u64);
        map.insert(String::from("a"));
        assert_eq!(map.heap_size(), table);

        // A boxed value adds its own allocation.
        map.insert([0_u64; 10]);
        assert_eq!(map.heap_size(), table + 80);

        // Another type, another box.
        map.insert([0_u64; 4]);
        assert_eq!(map.heap_size(), table + 80 + 32);

        // Removing a value gives its box back.
        map.remove::<[u64; 10]>();
        assert_eq!(map.heap_size(), table + 32);
        map.remove::<[u64; 4]>();
        assert_eq!(map.heap_size(), table);
    }
}
