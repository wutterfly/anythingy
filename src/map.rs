use std::{any::TypeId, collections::HashMap};

use crate::Thing;

#[derive(Debug)]
pub struct AnyMap {
    map: HashMap<TypeId, Thing>,
}

impl AnyMap {
    ///
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    ///
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity(capacity),
        }
    }

    ///
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    ///
    #[inline]
    #[must_use]
    pub fn raw(self) -> HashMap<TypeId, Thing> {
        self.map
    }

    ///
    #[inline]
    #[must_use]
    pub const fn raw_ref(&self) -> &HashMap<TypeId, Thing> {
        &self.map
    }

    ///
    #[inline]
    #[must_use]
    pub fn raw_mut(&mut self) -> &mut HashMap<TypeId, Thing> {
        &mut self.map
    }

    ///
    #[inline]
    #[must_use]
    pub fn keys<'a>(&'a self) -> impl std::iter::Iterator<Item = &TypeId> + 'a {
        self.map.keys()
    }

    ///
    #[inline]
    #[must_use]
    pub fn values<'a>(&'a self) -> impl std::iter::Iterator<Item = &Thing> + 'a {
        self.map.values()
    }

    ///
    #[inline]
    #[must_use]
    pub fn contains_key<T: 'static>(&self, key: &TypeId) -> bool {
        self.map.contains_key(key)
    }

    ///
    #[inline]
    #[must_use]
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit()
    }

    ///
    #[inline]
    pub fn insert<T: 'static>(&mut self, t: T) -> Option<T> {
        let id = TypeId::of::<T>();
        let thing = Thing::new(t);
        self.map.insert(id, thing).map(Thing::get::<T>)
    }

    ///
    #[inline]
    pub fn get<T: 'static>(&self) -> Option<&T> {
        let id = TypeId::of::<T>();
        self.map.get(&id).map(Thing::get_ref::<T>)
    }

    ///
    #[inline]
    pub fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
        let id = TypeId::of::<T>();
        self.map.get_mut(&id).map(Thing::get_mut::<T>)
    }

    ///
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

impl std::iter::IntoIterator for AnyMap {
    type Item = (TypeId, Thing);

    type IntoIter = std::collections::hash_map::IntoIter<TypeId, Thing>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

#[cfg(test)]
mod tests_anymap {}
