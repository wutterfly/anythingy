use std::{any::TypeId, collections::HashMap};

use crate::{DEFAULT_THING_SIZE, Thing};

/// A map for storing type erased values.
#[derive(Debug)]
pub struct AnyMap<const SIZE: usize = DEFAULT_THING_SIZE> {
    map: HashMap<TypeId, Thing<SIZE>>,
}

impl<const SIZE: usize> AnyMap<SIZE> {
    /// Creates a new `AnyMap`.
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Creates an empty `AnyMap` with at least the specified capacity.
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity(capacity),
        }
    }

    /// Returns the number of elements in the `AnyMap`.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the map contains no elements.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Removes all elements from map.
    #[inline]
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns the raw underlying `HashMap`.
    #[inline]
    #[must_use]
    pub fn raw(self) -> HashMap<TypeId, Thing<SIZE>> {
        self.map
    }

    /// Returns a reference to the raw underlying `HashMap`.
    #[inline]
    #[must_use]
    pub const fn raw_ref(&self) -> &HashMap<TypeId, Thing<SIZE>> {
        &self.map
    }

    /// Returns a mutable reference to the raw underlying `HashMap`.
    #[inline]
    #[must_use]
    pub const fn raw_mut(&mut self) -> &mut HashMap<TypeId, Thing<SIZE>> {
        &mut self.map
    }

    /// An iterator visiting all keys in arbitrary order.
    #[inline]
    pub fn keys(&self) -> impl std::iter::Iterator<Item = &TypeId> {
        self.map.keys()
    }

    /// An iterator visiting all values in arbitrary order.
    #[inline]
    pub fn values(&self) -> impl std::iter::Iterator<Item = &Thing<SIZE>> {
        self.map.values()
    }

    /// Returns true if the map contains a value for the associated type.
    #[inline]
    #[must_use]
    pub fn contains_key<T: 'static>(&self) -> bool {
        let id = std::any::TypeId::of::<T>();
        self.map.contains_key(&id)
    }

    /// Shrinks the capacity of the map as much as possible.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
    }

    /// Inserts the given value with its `TypId` as the key into the map.
    ///
    /// If the map did not have this key present, None is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is returned.
    #[inline]
    pub fn insert<T: 'static>(&mut self, value: T) -> Option<T> {
        let id = TypeId::of::<T>();
        let thing = Thing::new(value);
        self.map.insert(id, thing).map(Thing::get::<T>)
    }

    /// Returns a reference to the value corresponding to the `TypeId` of `T`.
    #[inline]
    pub fn get<T: 'static>(&self) -> Option<&T> {
        let id = TypeId::of::<T>();
        self.map.get(&id).map(Thing::get_ref::<T>)
    }

    /// Returns a mutable reference to the value corresponding to the `TypeId` of `T`.
    #[inline]
    pub fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
        let id = TypeId::of::<T>();
        self.map.get_mut(&id).map(Thing::get_mut::<T>)
    }

    /// Removes the value stored for `TypeId` of `T`, if the type was previously in the map.
    #[inline]
    pub fn remove<T: 'static>(&mut self) -> Option<T> {
        let id = TypeId::of::<T>();
        self.map.remove(&id).map(Thing::get::<T>)
    }
}

impl Default for AnyMap {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<const SIZE: usize> std::iter::IntoIterator for AnyMap<SIZE> {
    type Item = (TypeId, Thing<SIZE>);

    type IntoIter = std::collections::hash_map::IntoIter<TypeId, Thing<SIZE>>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::AnyMap as Map;

    mod construction {
        use super::Map;

        #[test]
        fn new_is_empty() {
            let map: Map = Map::new();
            assert!(map.is_empty());
            assert_eq!(map.len(), 0);
        }

        #[test]
        fn default_is_empty() {
            let map: Map = Map::default();
            assert!(map.is_empty());
        }

        #[test]
        fn with_capacity_is_empty() {
            let map: Map = Map::with_capacity(3);
            assert!(map.is_empty());
        }
    }

    mod insert {
        use super::Map;

        #[test]
        fn increases_len() {
            let mut map: Map = Map::with_capacity(3);
            assert!(map.is_empty());

            map.insert(String::new());
            assert_eq!(map.len(), 1);

            map.insert(Vec::<u8>::new());
            assert_eq!(map.len(), 2);

            map.insert(42u128);
            assert_eq!(map.len(), 3);
        }

        #[test]
        fn returns_none_on_new_key() {
            let mut map: Map = Map::new();
            assert!(map.insert(10u32).is_none());
        }

        #[test]
        fn returns_old_value_on_duplicate_key() {
            let mut map: Map = Map::new();
            map.insert(10u32);
            assert_eq!(map.insert(20u32), Some(10u32));
            assert_eq!(map.get::<u32>(), Some(&20u32));
            assert_eq!(map.len(), 1);
        }
    }

    mod get {
        use super::Map;

        #[test]
        fn returns_some_for_present_type() {
            let mut map: Map = Map::with_capacity(3);
            map.insert(String::new());
            map.insert(Vec::<u8>::new());
            map.insert(42u128);

            assert!(map.get::<String>().is_some());
            assert!(map.get::<Vec<u8>>().is_some());
            assert_eq!(map.get::<u128>(), Some(&42u128));
        }

        #[test]
        fn returns_none_for_absent_type() {
            let map: Map = Map::new();
            assert!(map.get::<u64>().is_none());
        }
    }

    mod get_mut {
        use super::Map;

        #[test]
        fn returns_some_for_present_type() {
            let mut map: Map = Map::with_capacity(3);
            map.insert(String::new());
            map.insert(Vec::<u8>::new());
            map.insert(42u128);

            assert!(map.get_mut::<String>().is_some());
            assert!(map.get_mut::<Vec<u8>>().is_some());
            assert_eq!(map.get_mut::<u128>(), Some(&mut 42u128));
        }

        #[test]
        fn returns_none_for_absent_type() {
            let mut map: Map = Map::new();
            assert!(map.get_mut::<u64>().is_none());
        }

        #[test]
        fn mutation_is_visible_via_get() {
            let mut map: Map = Map::new();
            map.insert(10u32);
            *map.get_mut::<u32>().unwrap() = 99;
            assert_eq!(map.get::<u32>(), Some(&99u32));
        }
    }

    mod remove {
        use super::Map;

        #[test]
        fn returns_value_and_shrinks_len() {
            let mut map: Map = Map::with_capacity(3);
            map.insert(String::new());
            map.insert(Vec::<u8>::new());
            map.insert(42u128);

            assert!(map.remove::<String>().is_some());
            assert!(map.remove::<Vec<u8>>().is_some());
            assert_eq!(map.remove::<u128>(), Some(42u128));
        }

        #[test]
        fn returns_none_for_absent_type() {
            let mut map: Map = Map::new();
            assert!(map.remove::<u64>().is_none());
        }
    }

    mod contains_key {
        use super::Map;

        #[test]
        fn false_when_absent_true_when_present() {
            let mut map: Map = Map::new();
            assert!(!map.contains_key::<u32>());

            map.insert(1u32);
            assert!(map.contains_key::<u32>());
            assert!(!map.contains_key::<u64>());

            map.remove::<u32>();
            assert!(!map.contains_key::<u32>());
        }
    }

    mod clear {
        use super::Map;

        #[test]
        fn empties_the_map() {
            let mut map: Map = Map::new();
            map.insert(1u32);
            map.insert(2u64);
            assert_eq!(map.len(), 2);

            map.clear();
            assert!(map.is_empty());
            assert_eq!(map.len(), 0);
            assert!(map.get::<u32>().is_none());
        }
    }

    mod iterators {
        use super::Map;

        #[test]
        fn keys_and_values_length() {
            let mut map: Map = Map::new();
            map.insert(1u32);
            map.insert(2u64);

            assert_eq!(map.keys().count(), 2);
            assert_eq!(map.values().count(), 2);
        }

        #[test]
        fn into_iter_yields_all_pairs() {
            let mut map: Map = Map::new();
            map.insert(1u32);
            map.insert(2u64);

            let pairs: Vec<_> = map.into_iter().collect();
            assert_eq!(pairs.len(), 2);
        }
    }

    mod raw {
        use super::Map;

        #[test]
        fn raw_ref_and_raw_mut_expose_inner_map() {
            let mut map: Map = Map::new();
            map.insert(1u32);

            assert_eq!(map.raw_ref().len(), 1);
            assert_eq!(map.raw_mut().len(), 1);
        }

        #[test]
        fn raw_consumes_and_returns_inner_map() {
            let mut map: Map = Map::new();
            map.insert(1u32);

            let raw = map.raw();
            assert_eq!(raw.len(), 1);
        }

        #[test]
        fn shrink_to_fit_preserves_data() {
            let mut map: Map = Map::with_capacity(100);
            map.insert(1u32);
            map.shrink_to_fit();
            assert_eq!(map.get::<u32>(), Some(&1u32));
        }
    }
}
