//! A `Send + Sync` map with one value per type.
//!
//! See [`SThingMap`] for details.

use crate::heap_size::HeapSize;
use std::any::TypeId;
use std::collections::TryReserveError;
use std::fmt;
use std::hash::BuildHasher;

use crate::thing::DEFAULT_THING_SIZE;
use crate::thing_map::{Entry, ThingMap};
use crate::type_id_hasher::TypeIdBuildHasher;

/// A [`ThingMap`] that is `Send` and `Sync`.
///
/// `ThingMap` can hold values of any type, including ones that are not
/// thread-safe, so it cannot be sent to other threads or shared between them.
/// `SThingMap` only accepts values that are `Send + Sync`
/// ([`insert`](Self::insert) and [`entry`](Self::entry) require it), so the map
/// itself is `Send + Sync` (with a `Send`/`Sync` hasher, which the default
/// is) and can be moved to another thread, shared in an `Arc`, or kept in a
/// `static`.
///
/// Otherwise it is the same as `ThingMap`: the same methods, the same
/// differences from `HashMap`, and the same entry types. It does no locking
/// itself. To modify a map that several threads share, wrap it in a `Mutex` or
/// `RwLock`, or store values that synchronize themselves (atomics,
/// `Mutex<T>`) and modify them through a shared reference.
///
/// # Examples
///
/// ```
/// use std::sync::atomic::{AtomicUsize, Ordering};
/// use std::sync::{Arc, RwLock};
/// use std::thread;
///
/// use anythingy::SThingMap;
///
/// let mut map = SThingMap::<24>::new();
/// map.insert(AtomicUsize::new(0));
/// map.insert(String::from("shared"));
/// let map = Arc::new(RwLock::new(map));
///
/// let workers: Vec<_> = (0..4)
///     .map(|_| {
///         let map = Arc::clone(&map);
///         thread::spawn(move || {
///             let map = map.read().unwrap();
///             map.get::<AtomicUsize>().unwrap().fetch_add(1, Ordering::Relaxed);
///         })
///     })
///     .collect();
/// for worker in workers {
///     worker.join().unwrap();
/// }
///
/// let map = map.read().unwrap();
/// assert_eq!(map.get::<AtomicUsize>().unwrap().load(Ordering::Relaxed), 4);
/// ```
///
/// The map is only as thread-safe as its hasher: with a hasher that is not
/// `Send`, neither is the map.
///
/// ```compile_fail,E0277
/// use std::hash::{BuildHasher, DefaultHasher};
/// use anythingy::SThingMap;
///
/// struct NotSend(*const ());
/// impl BuildHasher for NotSend {
///     type Hasher = DefaultHasher;
///     fn build_hasher(&self) -> DefaultHasher {
///         DefaultHasher::new()
///     }
/// }
///
/// fn assert_send<T: Send>() {}
/// assert_send::<SThingMap<24, NotSend>>();
/// ```
///
/// A value that is not thread-safe is rejected at compile time. `Rc` is not
/// `Send`:
///
/// ```compile_fail,E0277
/// use std::rc::Rc;
/// use anythingy::SThingMap;
///
/// let mut map = SThingMap::<24>::new();
/// map.insert(Rc::new(1));
/// ```
///
/// and `Cell` is `Send` but not `Sync`:
///
/// ```compile_fail,E0277
/// use std::cell::Cell;
/// use anythingy::SThingMap;
///
/// let mut map = SThingMap::<24>::new();
/// map.insert(Cell::new(1));
/// ```
pub struct SThingMap<const SIZE: usize = DEFAULT_THING_SIZE, S = TypeIdBuildHasher> {
    /// Invariant: every value in it is `Send + Sync`. Only `insert` and
    /// `entry` add values, and both require it. No `&mut ThingMap` is ever
    /// handed out, which would let a caller insert a value of any type.
    inner: ThingMap<SIZE, S>,
}

// SAFETY: every value in the map is `Send` (struct invariant), so moving the
// map, which moves or drops those values on another thread, is fine as long
// as the hasher can move too. `ThingMap` is `!Send` only as a conservative
// marker on `Thing`; the values are owned by the map and hold no
// thread-local state.
// The lint cannot see that the values are `Send` by construction; see above.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<const SIZE: usize, S: Send> Send for SThingMap<SIZE, S> {}

// SAFETY: every value in the map is `Sync` (struct invariant), and the shared
// operations only hand out `&T`; nothing in a shared `&SThingMap` mutates
// the map or its values (except through the values' own `Sync` interior
// mutability). The hasher is used through `&S`.
unsafe impl<const SIZE: usize, S: Sync> Sync for SThingMap<SIZE, S> {}

impl<const SIZE: usize> SThingMap<SIZE, TypeIdBuildHasher> {
    /// Creates an empty map. Does not allocate.
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: ThingMap::new(),
        }
    }

    /// Creates an empty map with room for at least `capacity` types.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: ThingMap::with_capacity(capacity),
        }
    }
}

impl<const SIZE: usize, S> SThingMap<SIZE, S> {
    /// Creates an empty map that hashes its keys with `hash_builder`.
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            inner: ThingMap::with_hasher(hash_builder),
        }
    }

    /// Creates an empty map with room for at least `capacity` types, hashing
    /// its keys with `hash_builder`.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            inner: ThingMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    /// Returns a reference to the map's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        self.inner.hasher()
    }

    /// Returns `true` if a value of type `T` can be stored in this map: `SIZE`
    /// is large enough to hold it, or a `Box` of it. See
    /// [`Thing::fitting`](crate::Thing::fitting).
    #[must_use]
    pub const fn fits<T: 'static>() -> bool {
        ThingMap::<SIZE, S>::fits::<T>()
    }

    /// Returns the number of types the map holds a value for.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the map holds nothing.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns how many types the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Removes every value, dropping them. Keeps the allocated capacity.
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Converts into a plain [`ThingMap`], which is no longer `Send` or
    /// `Sync`.
    pub fn into_inner(self) -> ThingMap<SIZE, S> {
        self.inner
    }
}

impl<const SIZE: usize, S: BuildHasher> SThingMap<SIZE, S> {
    /// Reserves room for at least `additional` more types.
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    /// Tries to reserve room for at least `additional` more types.
    ///
    /// # Errors
    ///
    /// Returns an error if the new capacity overflows or the allocator fails.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve(additional)
    }

    /// Shrinks the capacity as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
    }

    /// Shrinks the capacity to `min_capacity` or the current length,
    /// whichever is larger.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity);
    }

    /// Returns `true` if the map holds a value of type `T`.
    pub fn contains_key<T: 'static>(&self) -> bool {
        self.inner.contains_key::<T>()
    }

    /// Stores `value`, replacing and returning the previous value of the same
    /// type, if any.
    ///
    /// `T` must be `Send + Sync`, which is what makes the whole map `Send +
    /// Sync`.
    ///
    /// # Panics
    ///
    /// Panics if `SIZE` is too small to hold a `Box<T>`; see [`Thing::new`](crate::Thing::new).
    pub fn insert<T: 'static + Send + Sync>(&mut self, value: T) -> Option<T> {
        self.inner.insert(value)
    }

    /// Returns a reference to the value of type `T`, if there is one.
    pub fn get<T: 'static>(&self) -> Option<&T> {
        self.inner.get::<T>()
    }

    /// Returns the stored key and a reference to the value of type `T`, if
    /// there is one.
    pub fn get_key_value<T: 'static>(&self) -> Option<(&TypeId, &T)> {
        self.inner.get_key_value::<T>()
    }

    /// Returns a mutable reference to the value of type `T`, if there is one.
    pub fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
        self.inner.get_mut::<T>()
    }

    /// Removes and returns the value of type `T`, if there is one.
    pub fn remove<T: 'static>(&mut self) -> Option<T> {
        self.inner.remove::<T>()
    }

    /// Removes and returns the stored key and the value of type `T`, if there
    /// is one.
    pub fn remove_entry<T: 'static>(&mut self) -> Option<(TypeId, T)> {
        self.inner.remove_entry::<T>()
    }

    /// Gets the entry for type `T`, for in-place insertion or update with a
    /// single lookup. The entry type is the same as [`ThingMap::entry`]'s.
    ///
    /// `T` must be `Send + Sync`.
    ///
    /// # Panics
    ///
    /// Inserting through the entry panics if `SIZE` is too small to hold a
    /// `Box<T>`.
    pub fn entry<T: 'static + Send + Sync>(&mut self) -> Entry<'_, T, SIZE> {
        self.inner.entry::<T>()
    }
}

impl<const SIZE: usize, S: Default> Default for SThingMap<SIZE, S> {
    fn default() -> Self {
        Self {
            inner: ThingMap::default(),
        }
    }
}

impl<const SIZE: usize, S> fmt::Debug for SThingMap<SIZE, S> {
    /// Lists the `TypeId`s of the stored values.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

/// A lower bound, like [`ThingMap`]'s implementation: room for the values, and
/// the boxes of the ones that are boxed.
impl<const SIZE: usize, S> HeapSize for SThingMap<SIZE, S> {
    fn heap_size(&self) -> usize {
        self.inner.heap_size()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::RandomState;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex, OnceLock, RwLock};
    use std::thread;

    type Map = SThingMap<24>;

    fn assert_send_sync<X: Send + Sync>() {}

    // ---- the auto traits ----

    #[test]
    fn the_map_is_send_and_sync() {
        assert_send_sync::<Map>();
        assert_send_sync::<SThingMap<8>>();
        assert_send_sync::<SThingMap<24, RandomState>>();
    }

    // ---- the same behaviour as ThingMap ----

    #[test]
    fn insert_get_get_mut_and_remove() {
        let mut map = Map::new();
        assert!(map.is_empty());
        assert_eq!(map.insert(1u32), None);
        assert_eq!(map.insert(String::from("a")), None);
        assert_eq!(map.insert(2u32), Some(1));
        assert_eq!(map.len(), 2);

        assert_eq!(map.get::<u32>(), Some(&2));
        *map.get_mut::<u32>().unwrap() += 40;
        assert_eq!(map.get::<u32>(), Some(&42));
        assert!(map.contains_key::<String>());
        assert!(!map.contains_key::<u8>());

        let (id, value) = map.get_key_value::<u32>().unwrap();
        assert_eq!((*id, *value), (TypeId::of::<u32>(), 42));
        assert_eq!(map.remove_entry::<u32>(), Some((TypeId::of::<u32>(), 42)));
        assert_eq!(map.remove::<String>().as_deref(), Some("a"));
        assert!(map.is_empty());
    }

    #[test]
    fn entry_api() {
        let mut map = Map::new();
        for _ in 0..3 {
            *map.entry::<u32>().or_insert(0) += 1;
        }
        assert_eq!(map.get::<u32>(), Some(&3));
        map.entry::<Vec<u8>>().or_default().push(1);
        map.entry::<Vec<u8>>()
            .and_modify(|v| v.push(2))
            .or_default();
        assert_eq!(map.get::<Vec<u8>>().unwrap(), &[1, 2]);

        match map.entry::<u32>() {
            Entry::Occupied(entry) => assert_eq!(entry.remove(), 3),
            Entry::Vacant(_) => panic!("expected occupied"),
        }
        assert!(!map.contains_key::<u32>());
    }

    #[test]
    fn into_inner_returns_a_plain_map() {
        let mut map = Map::new();
        map.insert(7u8);
        map.insert(String::from("text"));

        let plain: ThingMap<24> = map.into_inner();
        assert_eq!(plain.len(), 2);
        assert_eq!(plain.get::<u8>(), Some(&7));
        assert_eq!(plain.get::<String>().unwrap(), "text");
    }

    #[test]
    fn housekeeping_default_debug_and_hasher() {
        let mut map = SThingMap::<24>::with_capacity(8);
        assert!(map.capacity() >= 8);
        map.reserve(32);
        map.try_reserve(16).unwrap();
        map.insert(1u8);
        map.clear();
        map.shrink_to(4);
        map.shrink_to_fit();
        assert!(map.is_empty());

        let map: SThingMap = SThingMap::default();
        assert!(map.is_empty());
        assert!(SThingMap::<24>::fits::<String>());
        assert!(!SThingMap::<4>::fits::<String>());

        let mut map = SThingMap::<24, RandomState>::with_hasher(RandomState::new());
        map.insert(1u8);
        let _: &RandomState = map.hasher();
        assert!(format!("{map:?}").starts_with("{TypeId("));
        let map = SThingMap::<24, RandomState>::with_capacity_and_hasher(4, RandomState::new());
        assert!(map.capacity() >= 4);
    }

    // ---- across threads ----

    #[test]
    fn many_threads_read_the_same_map() {
        let mut map = Map::new();
        map.insert(String::from("shared"));
        map.insert(7u64);
        let map = Arc::new(map);

        let readers: Vec<_> = (0..8)
            .map(|_| {
                let map = Arc::clone(&map);
                thread::spawn(move || {
                    let rounds = if cfg!(miri) { 20 } else { 2_000 };
                    for _ in 0..rounds {
                        assert_eq!(map.get::<String>().unwrap(), "shared");
                        assert_eq!(map.get::<u64>(), Some(&7));
                        assert!(map.get::<u8>().is_none());
                    }
                })
            })
            .collect();
        for reader in readers {
            reader.join().unwrap();
        }
    }

    #[test]
    fn scoped_threads_share_a_reference() {
        let mut map = Map::new();
        map.insert(AtomicUsize::new(0));
        let map = &map;
        thread::scope(|scope| {
            for _ in 0..4 {
                scope.spawn(move || {
                    for _ in 0..100 {
                        map.get::<AtomicUsize>()
                            .unwrap()
                            .fetch_add(1, Ordering::Relaxed);
                    }
                });
            }
        });
        assert_eq!(
            map.get::<AtomicUsize>().unwrap().load(Ordering::Relaxed),
            400
        );
    }

    #[test]
    fn values_with_interior_synchronization_are_modified_through_shared_references() {
        let mut map = Map::new();
        map.insert(Mutex::new(Vec::<u32>::new()));
        let map = Arc::new(map);

        let workers: Vec<_> = (0..4u32)
            .map(|id| {
                let map = Arc::clone(&map);
                thread::spawn(move || {
                    for i in 0..25 {
                        map.get::<Mutex<Vec<u32>>>()
                            .unwrap()
                            .lock()
                            .unwrap()
                            .push(id * 100 + i);
                    }
                })
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        let mut all = map
            .get::<Mutex<Vec<u32>>>()
            .unwrap()
            .lock()
            .unwrap()
            .clone();
        all.sort_unstable();
        let mut expected: Vec<u32> = (0..4)
            .flat_map(|id| (0..25).map(move |i| id * 100 + i))
            .collect();
        expected.sort_unstable();
        assert_eq!(all, expected);
    }

    #[test]
    fn moving_the_map_between_threads_keeps_its_values() {
        let map = thread::spawn(|| {
            let mut map = Map::new();
            map.insert(String::from("built elsewhere"));
            map.insert([3u64; 16]); // boxed
            map
        })
        .join()
        .unwrap();
        assert_eq!(map.get::<String>().unwrap(), "built elsewhere");

        let map = thread::spawn(move || {
            let mut map = map;
            map.get_mut::<String>().unwrap().push('!');
            map.entry::<u8>().or_insert(9);
            map
        })
        .join()
        .unwrap();
        assert_eq!(map.get::<String>().unwrap(), "built elsewhere!");
        assert_eq!(map.get::<[u64; 16]>().unwrap()[15], 3);
        assert_eq!(map.get::<u8>(), Some(&9));
    }

    #[test]
    fn a_map_behind_a_rwlock_can_be_written_and_read_from_many_threads() {
        let map = Arc::new(RwLock::new(Map::new()));
        let writers: Vec<_> = (0..4u8)
            .map(|i| {
                let map = Arc::clone(&map);
                thread::spawn(move || {
                    let mut map = map.write().unwrap();
                    match i {
                        0 => drop(map.insert(1u8)),
                        1 => drop(map.insert(2u16)),
                        2 => drop(map.insert(3u32)),
                        _ => drop(map.insert(String::from("four"))),
                    }
                })
            })
            .collect();
        for writer in writers {
            writer.join().unwrap();
        }
        let map = map.read().unwrap();
        assert_eq!(map.len(), 4);
        assert_eq!(map.get::<u8>(), Some(&1));
        assert_eq!(map.get::<u16>(), Some(&2));
        assert_eq!(map.get::<u32>(), Some(&3));
        assert_eq!(map.get::<String>().unwrap(), "four");
    }

    #[test]
    fn values_are_dropped_on_whichever_thread_drops_the_map() {
        struct CountDrop(Arc<AtomicUsize>);
        impl Drop for CountDrop {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let drops = Arc::new(AtomicUsize::new(0));
        let mut map = Map::new();
        map.insert(CountDrop(Arc::clone(&drops))); // inline
        map.insert((CountDrop(Arc::clone(&drops)), [0u64; 8])); // boxed
        assert_eq!(drops.load(Ordering::SeqCst), 0);

        thread::spawn(move || drop(map)).join().unwrap();
        assert_eq!(drops.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn a_global_map_behind_a_mutex() {
        static GLOBAL: OnceLock<Mutex<SThingMap<24>>> = OnceLock::new();
        let global = GLOBAL.get_or_init(|| Mutex::new(SThingMap::new()));

        let workers: Vec<_> = (0..4)
            .map(|_| {
                thread::spawn(move || {
                    let global = GLOBAL.get().unwrap();
                    *global.lock().unwrap().entry::<u64>().or_insert(0) += 1;
                })
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        assert_eq!(global.lock().unwrap().get::<u64>(), Some(&4));
    }

    #[test]
    fn heap_size_counts_the_room_for_values_and_the_boxed_ones() {
        let mut map = SThingMap::<24>::with_capacity(7);
        let table = map.heap_size();
        assert!(table > 0);

        map.insert(1_u64);
        assert_eq!(map.heap_size(), table);

        map.insert([0_u64; 10]);
        assert_eq!(map.heap_size(), table + 80);
    }
}
