use std::any::TypeId;

use crate::{DEFAULT_THING_SIZE, Thing};

/// A map for storing type erased values.
/// For a small number of entries, using a [`Vec`] as underlying data structure is more efficient.
#[derive(Debug)]
pub struct SmallAnyMap<const SIZE: usize = DEFAULT_THING_SIZE> {
    map: Vec<(TypeId, Thing<SIZE>)>,
}

impl<const SIZE: usize> SmallAnyMap<SIZE> {
    /// Creates a new `AnyMap`.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self { map: Vec::new() }
    }

    /// Creates an empty `AnyMap` with at least the specified capacity.
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: Vec::with_capacity(capacity),
        }
    }

    /// Returns the number of elements in the `AnyMap`.
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the map contains no elements.
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Removes all elements from map.
    #[inline]
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns the raw underlying `Vec`.
    #[inline]
    #[must_use]
    pub fn raw(self) -> Vec<(TypeId, Thing<SIZE>)> {
        self.map
    }

    /// Returns a reference to the raw underlying `Vec`.
    #[inline]
    #[must_use]
    pub const fn raw_ref(&self) -> &Vec<(TypeId, Thing<SIZE>)> {
        &self.map
    }

    /// Returns a mutable reference to the raw underlying `Vec`.
    #[inline]
    #[must_use]
    pub const fn raw_mut(&mut self) -> &mut Vec<(TypeId, Thing<SIZE>)> {
        &mut self.map
    }

    /// An iterator visiting all keys in arbitrary order.
    #[inline]
    pub fn keys(&self) -> impl std::iter::Iterator<Item = &TypeId> {
        self.map.iter().map(|(k, _)| k)
    }

    /// An iterator visiting all values in arbitrary order.
    #[inline]
    pub fn values(&self) -> impl std::iter::Iterator<Item = &Thing<SIZE>> {
        self.map.iter().map(|(_, v)| v)
    }

    /// Returns true if the map contains a value for the specified key.
    #[inline]
    #[must_use]
    pub fn contains_key<T: 'static>(&self, key: &TypeId) -> bool {
        self.map.iter().any(|(k, _)| k == key)
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
    #[must_use]
    pub fn insert<T: 'static>(&mut self, value: T) -> Option<T> {
        let id = TypeId::of::<T>();
        let thing = Thing::new(value);

        let found = self.map.iter_mut().find(|(k, _)| k == &id);

        if let Some((_, v)) = found {
            let out = std::mem::replace(v, thing);

            Some(out.get::<T>())
        } else {
            self.map.push((id, thing));
            None
        }
    }

    /// Returns a reference to the value corresponding to the `TypeId` of `T`.
    #[inline]
    #[must_use]
    pub fn get<T: 'static>(&self) -> Option<&T> {
        let id = TypeId::of::<T>();

        self.map
            .iter()
            .find(|(k, _)| k == &id)
            .map(|(_, v)| v.get_ref::<T>())
    }

    /// Returns a mutable reference to the value corresponding to the `TypeId` of `T`.
    #[inline]
    pub fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
        let id = TypeId::of::<T>();
        self.map
            .iter_mut()
            .find(|(k, _)| k == &id)
            .map(|(_, v)| v.get_mut::<T>())
    }

    /// Removes the value stored for `TypeId` of `T`, if the type was previously in the map.
    #[inline]
    pub fn remove<T: 'static>(&mut self) -> Option<T> {
        let id = TypeId::of::<T>();
        let position = self.map.iter().position(|(k, _)| k == &id);

        if let Some(i) = position {
            return Some(self.map.swap_remove(i).1.get::<T>());
        }

        None
    }
}

impl Default for SmallAnyMap {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<const SIZE: usize> std::iter::IntoIterator for SmallAnyMap<SIZE> {
    type Item = (TypeId, Thing<SIZE>);
    type IntoIter = std::vec::IntoIter<(TypeId, Thing<SIZE>)>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::SmallAnyMap as Map;

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

            let _ = map.insert(String::new());
            assert_eq!(map.len(), 1);

            let _ = map.insert(Vec::<u8>::new());
            assert_eq!(map.len(), 2);

            let _ = map.insert(42u128);
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
            let _ = map.insert(10u32);
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
            let _ = map.insert(String::new());
            let _ = map.insert(Vec::<u8>::new());
            let _ = map.insert(42u128);

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
            let _ = map.insert(String::new());
            let _ = map.insert(Vec::<u8>::new());
            let _ = map.insert(42u128);

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
            let _ = map.insert(10u32);
            *map.get_mut::<u32>().unwrap() = 99;
            assert_eq!(map.get::<u32>(), Some(&99u32));
        }
    }

    mod remove {
        use super::Map;

        #[test]
        fn returns_value_and_shrinks_len() {
            let mut map: Map = Map::with_capacity(3);
            let _ = map.insert(String::new());
            let _ = map.insert(Vec::<u8>::new());
            let _ = map.insert(42u128);

            assert!(map.remove::<String>().is_some());
            assert!(map.remove::<Vec<u8>>().is_some());
            assert_eq!(map.remove::<u128>(), Some(42u128));
        }

        #[test]
        fn returns_none_for_absent_type() {
            let mut map: Map = Map::new();
            assert!(map.remove::<u64>().is_none());
        }

        #[test]
        fn swap_remove_keeps_remaining_entries_accessible() {
            // Remove the first-inserted entry; swap_remove moves the last entry
            // into its slot, so the other two must still be reachable.
            let mut map: Map = Map::new();
            let _ = map.insert(1u32);
            let _ = map.insert(2u64);
            let _ = map.insert(3u128);

            assert_eq!(map.remove::<u32>(), Some(1u32));
            assert_eq!(map.len(), 2);
            assert_eq!(map.get::<u64>(), Some(&2u64));
            assert_eq!(map.get::<u128>(), Some(&3u128));
        }
    }

    mod contains_key {
        use super::Map;

        #[test]
        fn false_when_absent_true_when_present() {
            use std::any::TypeId;

            let mut map: Map = Map::new();
            let u32_id = TypeId::of::<u32>();
            let u64_id = TypeId::of::<u64>();

            assert!(!map.contains_key::<u32>(&u32_id));

            let _ = map.insert(1u32);
            assert!(map.contains_key::<u32>(&u32_id));
            assert!(!map.contains_key::<u64>(&u64_id));

            map.remove::<u32>();
            assert!(!map.contains_key::<u32>(&u32_id));
        }
    }

    mod clear {
        use super::Map;

        #[test]
        fn empties_the_map() {
            let mut map: Map = Map::new();
            let _ = map.insert(1u32);
            let _ = map.insert(2u64);
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
            let _ = map.insert(1u32);
            let _ = map.insert(2u64);

            assert_eq!(map.keys().count(), 2);
            assert_eq!(map.values().count(), 2);
        }

        #[test]
        fn into_iter_yields_all_pairs() {
            let mut map: Map = Map::new();
            let _ = map.insert(1u32);
            let _ = map.insert(2u64);

            let pairs: Vec<_> = map.into_iter().collect();
            assert_eq!(pairs.len(), 2);
        }
    }

    mod raw {
        use super::Map;

        #[test]
        fn raw_ref_and_raw_mut_expose_inner_vec() {
            let mut map: Map = Map::new();
            let _ = map.insert(1u32);

            assert_eq!(map.raw_ref().len(), 1);
            assert_eq!(map.raw_mut().len(), 1);
        }

        #[test]
        fn raw_consumes_and_returns_inner_vec() {
            let mut map: Map = Map::new();
            let _ = map.insert(1u32);

            let raw = map.raw();
            assert_eq!(raw.len(), 1);
        }

        #[test]
        fn shrink_to_fit_preserves_data() {
            let mut map: Map = Map::with_capacity(100);
            let _ = map.insert(1u32);
            map.shrink_to_fit();
            assert_eq!(map.get::<u32>(), Some(&1u32));
        }
    }
}
