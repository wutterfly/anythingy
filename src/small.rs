use std::any::TypeId;

use crate::{Thing, DEFAULT_THING_SIZE};

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
    pub fn raw_mut(&mut self) -> &mut Vec<(TypeId, Thing<SIZE>)> {
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
mod tests_anymap {
    use super::SmallAnyMap as Map;

    #[test]
    fn test_anymap_insert() {
        let mut map: Map = Map::with_capacity(3);
        assert!(map.is_empty());

        let data_1 = String::new();
        let _ = map.insert(data_1);
        assert_eq!(map.len(), 1);

        let data_2: Vec<u8> = Vec::new();
        let _ = map.insert(data_2);
        assert_eq!(map.len(), 2);

        let data_3 = 42u128;
        let _ = map.insert(data_3);
        assert_eq!(map.len(), 3);
    }

    #[test]
    fn test_anymap_get() {
        let mut map: Map = Map::with_capacity(3);

        let data_1 = String::new();
        let _ = map.insert(data_1);

        let data_2: Vec<u8> = Vec::new();
        let _ = map.insert(data_2);

        let data_3 = 42u128;
        let _ = map.insert(data_3);

        let out_1 = map.get::<String>();
        assert!(out_1.is_some());

        let out_2 = map.get::<Vec<u8>>();
        assert!(out_2.is_some());

        let out_3 = map.get::<u128>();
        assert!(out_3.is_some());
        assert_eq!(out_3.unwrap(), &data_3);

        let out_4 = map.get::<u64>();
        assert!(out_4.is_none());
    }

    #[test]
    fn test_anymap_get_mut() {
        let mut map: Map = Map::with_capacity(3);

        let data_1 = String::new();
        let _ = map.insert(data_1);

        let data_2: Vec<u8> = Vec::new();
        let _ = map.insert(data_2);

        let mut data_3 = 42u128;
        let _ = map.insert(data_3);

        let out_1 = map.get_mut::<String>();
        assert!(out_1.is_some());

        let out_2 = map.get_mut::<Vec<u8>>();
        assert!(out_2.is_some());

        let out_3 = map.get_mut::<u128>();
        assert!(out_3.is_some());
        assert_eq!(out_3.unwrap(), &mut data_3);

        let out_4 = map.get_mut::<u64>();
        assert!(out_4.is_none());
    }

    #[test]
    fn test_anymap_remove() {
        let mut map: Map = Map::with_capacity(3);

        let data_1 = String::new();
        let _ = map.insert(data_1);

        let data_2: Vec<u8> = Vec::new();
        let _ = map.insert(data_2);

        let data_3 = 42u128;
        let _ = map.insert(data_3);

        let out_1 = map.remove::<String>();
        assert!(out_1.is_some());

        let out_2 = map.remove::<Vec<u8>>();
        assert!(out_2.is_some());

        let out_3 = map.remove::<u128>();
        assert!(out_3.is_some());
        assert_eq!(out_3.unwrap(), data_3);

        let out_4 = map.remove::<u64>();
        assert!(out_4.is_none());
    }
}
