//! A set backed by a flat vector, searched linearly.
//!
//! See [`LinearSet`] for details and when to prefer it over `HashSet`.

use core::borrow::Borrow;
use core::fmt;
use core::iter::{Chain, FromIterator, FusedIterator};
use core::ops::{BitAnd, BitOr, BitXor, Sub};

use crate::linear_map::{self, LinearMap};

/// A set backed by a `Vec`, searched linearly.
///
/// The counterpart of [`LinearMap`] for when there are no values: elements
/// only need `Eq` (no `Hash`, no `Ord`), and for small sets the contiguous
/// storage makes lookups faster than a hash table's. Like `LinearMap`, it is
/// particularly fast for small plain-data elements such as integers.
///
/// Iteration follows storage order, which is insertion order until
/// [`remove`](Self::remove) or [`take`](Self::take) is used: removal swaps the
/// last element into the vacated slot, so it does not preserve order.
/// [`retain`](Self::retain) does.
///
/// Set operations ([`union`](Self::union), [`intersection`](Self::intersection),
/// and so on) look up every element of one set in the other, so they are
/// O(n·m): meant for the small sets this type is designed for. They yield
/// elements in the order of the set they are called on (for `union`, that
/// set's elements first).
///
/// # Examples
///
/// ```
/// use anythingy::LinearSet;
///
/// let mut visited = LinearSet::new();
/// assert!(visited.insert("a"));
/// assert!(visited.insert("b"));
/// assert!(!visited.insert("a")); // already there
///
/// assert!(visited.contains("a"));
/// assert!(visited.remove("a"));
/// assert_eq!(visited.len(), 1);
/// ```
#[derive(Clone)]
pub struct LinearSet<T> {
    map: LinearMap<T, ()>,
}

impl<T> LinearSet<T> {
    /// Creates an empty set. Does not allocate.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            map: LinearMap::new(),
        }
    }

    /// Creates an empty set with room for at least `capacity` elements.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: LinearMap::with_capacity(capacity),
        }
    }

    /// Returns the number of elements the set can hold without reallocating.
    #[must_use]
    pub const fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Reserves room for at least `additional` more elements.
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional);
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

    /// Returns the number of elements.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the set holds no elements.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Removes every element, keeping the allocated capacity.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Iterates over the elements in storage order.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.map.keys(),
        }
    }

    /// Removes and yields every element, keeping the allocated capacity.
    ///
    /// The set is empty afterwards, even if the iterator is dropped before
    /// it is exhausted or leaked.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::LinearSet;
    ///
    /// let mut set = LinearSet::from([1, 2, 3]);
    /// let mut drained: Vec<_> = set.drain().collect();
    /// drained.sort();
    /// assert_eq!(drained, vec![1, 2, 3]);
    /// assert!(set.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<'_, T> {
        Drain {
            inner: self.map.drain(),
        }
    }

    /// Keeps only the elements for which `f` returns `true`, preserving the
    /// order of the ones that stay.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.map.retain(|element, ()| f(element));
    }
}

impl<T: Eq> LinearSet<T> {
    /// Returns `true` if the set contains `value`.
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.map.contains_key(value)
    }

    /// Returns a reference to the stored element equal to `value`.
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.map.get_key_value(value).map(|(element, ())| element)
    }

    /// Adds `value` to the set. Returns `true` if it was not already there.
    ///
    /// If an equal element is present, it is kept as it is (the new value is
    /// dropped); use [`replace`](Self::replace) to swap it.
    pub fn insert(&mut self, value: T) -> bool {
        self.map.insert(value, ()).is_none()
    }

    /// Adds `value`, replacing and returning the equal element if there was
    /// one. Useful when equal elements can still be told apart.
    pub fn replace(&mut self, value: T) -> Option<T> {
        self.map
            .replace_entry(value, ())
            .map(|(element, ())| element)
    }

    /// Removes `value`, returning `true` if it was present.
    ///
    /// This is O(1) beyond the initial linear scan: it swaps the last
    /// element into the vacated slot, so it does not preserve order.
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.map.remove(value).is_some()
    }

    /// Removes and returns the element equal to `value`, if present. Does
    /// not preserve order; see [`remove`](Self::remove).
    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.map.remove_entry(value).map(|(element, ())| element)
    }

    /// Elements in `self` or `other`: all of `self`'s, then those of `other`
    /// that `self` lacks.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::LinearSet;
    ///
    /// let a = LinearSet::from([1, 2, 3]);
    /// let b = LinearSet::from([3, 4]);
    /// assert_eq!(a.union(&b).copied().collect::<Vec<_>>(), vec![1, 2, 3, 4]);
    /// ```
    #[must_use]
    pub fn union<'a>(&'a self, other: &'a Self) -> Union<'a, T> {
        Union {
            inner: self.iter().chain(other.difference(self)),
        }
    }

    /// Elements in both `self` and `other`, in `self`'s order.
    #[must_use]
    pub fn intersection<'a>(&'a self, other: &'a Self) -> Intersection<'a, T> {
        Intersection {
            iter: self.iter(),
            other,
        }
    }

    /// Elements in `self` but not in `other`, in `self`'s order.
    #[must_use]
    pub fn difference<'a>(&'a self, other: &'a Self) -> Difference<'a, T> {
        Difference {
            iter: self.iter(),
            other,
        }
    }

    /// Elements in exactly one of the two sets: those of `self` that `other`
    /// lacks, then those of `other` that `self` lacks.
    #[must_use]
    pub fn symmetric_difference<'a>(&'a self, other: &'a Self) -> SymmetricDifference<'a, T> {
        SymmetricDifference {
            inner: self.difference(other).chain(other.difference(self)),
        }
    }

    /// Returns `true` if the sets have no element in common.
    #[must_use]
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.iter().all(|element| !other.contains(element))
    }

    /// Returns `true` if every element of `self` is in `other`.
    #[must_use]
    pub fn is_subset(&self, other: &Self) -> bool {
        self.len() <= other.len() && self.iter().all(|element| other.contains(element))
    }

    /// Returns `true` if every element of `other` is in `self`.
    #[must_use]
    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }
}

impl<T> Default for LinearSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug> fmt::Debug for LinearSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

/// Two sets are equal if they hold the same elements, regardless of storage
/// order.
impl<T: Eq> PartialEq for LinearSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.is_subset(other)
    }
}

impl<T: Eq> Eq for LinearSet<T> {}

/// Builds a set from an iterator, dropping duplicates. Every insert searches
/// the set so far, so this is O(n²): meant for small sets.
impl<T: Eq> FromIterator<T> for LinearSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::new();
        set.extend(iter);
        set
    }
}

impl<T: Eq, const N: usize> From<[T; N]> for LinearSet<T> {
    fn from(elements: [T; N]) -> Self {
        elements.into_iter().collect()
    }
}

impl<T: Eq> Extend<T> for LinearSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.map
            .extend(iter.into_iter().map(|element| (element, ())));
    }
}

impl<'a, T: Eq + Copy + 'a> Extend<&'a T> for LinearSet<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().copied());
    }
}

impl<T> IntoIterator for LinearSet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            inner: self.map.into_keys(),
        }
    }
}

impl<'a, T> IntoIterator for &'a LinearSet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

/// `&a | &b`: the union as a new set.
impl<T: Eq + Clone> BitOr<&LinearSet<T>> for &LinearSet<T> {
    type Output = LinearSet<T>;

    fn bitor(self, rhs: &LinearSet<T>) -> LinearSet<T> {
        self.union(rhs).cloned().collect()
    }
}

/// `&a & &b`: the intersection as a new set.
impl<T: Eq + Clone> BitAnd<&LinearSet<T>> for &LinearSet<T> {
    type Output = LinearSet<T>;

    fn bitand(self, rhs: &LinearSet<T>) -> LinearSet<T> {
        self.intersection(rhs).cloned().collect()
    }
}

/// `&a ^ &b`: the symmetric difference as a new set.
impl<T: Eq + Clone> BitXor<&LinearSet<T>> for &LinearSet<T> {
    type Output = LinearSet<T>;

    fn bitxor(self, rhs: &LinearSet<T>) -> LinearSet<T> {
        self.symmetric_difference(rhs).cloned().collect()
    }
}

/// `&a - &b`: the difference as a new set.
impl<T: Eq + Clone> Sub<&LinearSet<T>> for &LinearSet<T> {
    type Output = LinearSet<T>;

    fn sub(self, rhs: &LinearSet<T>) -> LinearSet<T> {
        self.difference(rhs).cloned().collect()
    }
}

/// Implements `Iterator`, `DoubleEndedIterator`, `ExactSizeIterator` and
/// `FusedIterator` for a wrapper around a `LinearMap` iterator in its `inner`
/// field, mapping each item with `$map`.
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

/// An iterator over the elements of a [`LinearSet`]. Created by
/// [`LinearSet::iter`].
pub struct Iter<'a, T> {
    inner: linear_map::Keys<'a, T, ()>,
}
forward_iterator!({'a, T} Iter<'a, T>, &'a T, |element| element);

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An owning iterator over the elements of a [`LinearSet`]. Created by
/// [`LinearSet::into_iter`].
pub struct IntoIter<T> {
    inner: linear_map::IntoKeys<T, ()>,
}
forward_iterator!({T} IntoIter<T>, T, |element| element);

impl<T> fmt::Debug for IntoIter<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IntoIter")
            .field("remaining", &self.len())
            .finish()
    }
}

/// A draining iterator over the elements of a [`LinearSet`]. Created by
/// [`LinearSet::drain`].
pub struct Drain<'a, T> {
    inner: linear_map::Drain<'a, T, ()>,
}
forward_iterator!({'a, T} Drain<'a, T>, T, |(element, ())| element);

impl<T> fmt::Debug for Drain<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Drain")
            .field("remaining", &self.len())
            .finish()
    }
}

/// An iterator over the elements in one set and not another. Created by
/// [`LinearSet::difference`].
pub struct Difference<'a, T> {
    iter: Iter<'a, T>,
    other: &'a LinearSet<T>,
}

impl<'a, T: Eq> Iterator for Difference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let element = self.iter.next()?;
            if !self.other.contains(element) {
                return Some(element);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1)
    }
}

impl<T: Eq> FusedIterator for Difference<'_, T> {}

impl<T> Clone for Difference<'_, T> {
    fn clone(&self) -> Self {
        Difference {
            iter: self.iter.clone(),
            other: self.other,
        }
    }
}

impl<T: Eq + fmt::Debug> fmt::Debug for Difference<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An iterator over the elements in both of two sets. Created by
/// [`LinearSet::intersection`].
pub struct Intersection<'a, T> {
    iter: Iter<'a, T>,
    other: &'a LinearSet<T>,
}

impl<'a, T: Eq> Iterator for Intersection<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let element = self.iter.next()?;
            if self.other.contains(element) {
                return Some(element);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1)
    }
}

impl<T: Eq> FusedIterator for Intersection<'_, T> {}

impl<T> Clone for Intersection<'_, T> {
    fn clone(&self) -> Self {
        Intersection {
            iter: self.iter.clone(),
            other: self.other,
        }
    }
}

impl<T: Eq + fmt::Debug> fmt::Debug for Intersection<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An iterator over the elements in either of two sets. Created by
/// [`LinearSet::union`].
pub struct Union<'a, T> {
    inner: Chain<Iter<'a, T>, Difference<'a, T>>,
}

impl<'a, T: Eq> Iterator for Union<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T: Eq> FusedIterator for Union<'_, T> {}

impl<T> Clone for Union<'_, T> {
    fn clone(&self) -> Self {
        Union {
            inner: self.inner.clone(),
        }
    }
}

impl<T: Eq + fmt::Debug> fmt::Debug for Union<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An iterator over the elements in exactly one of two sets. Created by
/// [`LinearSet::symmetric_difference`].
pub struct SymmetricDifference<'a, T> {
    inner: Chain<Difference<'a, T>, Difference<'a, T>>,
}

impl<'a, T: Eq> Iterator for SymmetricDifference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T: Eq> FusedIterator for SymmetricDifference<'_, T> {}

impl<T> Clone for SymmetricDifference<'_, T> {
    fn clone(&self) -> Self {
        SymmetricDifference {
            inner: self.inner.clone(),
        }
    }
}

impl<T: Eq + fmt::Debug> fmt::Debug for SymmetricDifference<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use std::rc::Rc;

    fn sorted<'a, T: Ord + Copy + 'a>(iter: impl Iterator<Item = &'a T>) -> Vec<T> {
        let mut v: Vec<T> = iter.copied().collect();
        v.sort();
        v
    }

    // ---- basics ----

    #[test]
    fn insert_contains_and_len() {
        let mut set = LinearSet::new();
        assert!(set.is_empty());
        assert!(set.insert("a"));
        assert!(set.insert("b"));
        assert!(!set.insert("a"));
        assert_eq!(set.len(), 2);
        assert!(set.contains("a"));
        assert!(!set.contains("c"));
    }

    #[test]
    fn remove_and_take() {
        let mut set: LinearSet<String> = ["a", "b", "c"].map(String::from).into();
        assert!(set.remove("a"));
        assert!(!set.remove("a"));
        assert_eq!(set.take("b"), Some(String::from("b")));
        assert_eq!(set.take("b"), None);
        assert_eq!(set.len(), 1);
        assert!(set.contains("c"));
    }

    #[test]
    fn borrowed_lookups() {
        let mut set: LinearSet<String> = LinearSet::new();
        set.insert("key".to_string());
        assert!(set.contains("key"));
        assert!(set.contains(&"key".to_string()));
        assert_eq!(set.get("key").map(String::as_str), Some("key"));
        assert!(set.get("nope").is_none());
    }

    #[test]
    fn insert_keeps_the_existing_element_and_replace_swaps_it() {
        // Elements that compare equal but can be told apart.
        #[derive(Debug)]
        struct Tagged(u32, &'static str);
        impl PartialEq for Tagged {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }
        impl Eq for Tagged {}

        let mut set = LinearSet::new();
        assert!(set.insert(Tagged(1, "first")));
        assert!(!set.insert(Tagged(1, "second")));
        assert_eq!(set.get(&Tagged(1, "")).unwrap().1, "first");

        let old = set.replace(Tagged(1, "third")).unwrap();
        assert_eq!(old.1, "first");
        assert_eq!(set.get(&Tagged(1, "")).unwrap().1, "third");
        assert_eq!(set.replace(Tagged(2, "new")).map(|t| t.1), None);
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn clear_keeps_capacity() {
        let mut set = LinearSet::with_capacity(16);
        assert!(set.capacity() >= 16);
        set.insert(1);
        set.clear();
        assert!(set.is_empty());
        assert!(set.capacity() >= 16);
        assert!(!set.contains(&1));
    }

    #[test]
    fn reserve_and_shrink() {
        let mut set: LinearSet<u32> = LinearSet::new();
        assert_eq!(set.capacity(), 0);
        set.reserve(50);
        assert!(set.capacity() >= 50);
        set.insert(1);
        set.shrink_to(10);
        assert!(set.capacity() >= 10);
        set.shrink_to_fit();
        assert!(set.capacity() < 50);
    }

    #[test]
    fn retain_preserves_order() {
        let mut set: LinearSet<i32> = (0..10).collect();
        set.retain(|x| x % 3 != 0);
        assert_eq!(
            set.iter().copied().collect::<Vec<_>>(),
            vec![1, 2, 4, 5, 7, 8]
        );
    }

    #[test]
    fn remove_swaps_the_last_element_in() {
        let mut set = LinearSet::from([1, 2, 3, 4]);
        set.remove(&1);
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![4, 2, 3]);
    }

    #[test]
    fn drain_empties_the_set() {
        let mut set = LinearSet::from([1, 2, 3]);
        let cap = set.capacity();
        assert_eq!(
            sorted(set.drain().collect::<Vec<_>>().iter()),
            vec![1, 2, 3]
        );
        assert!(set.is_empty());
        assert_eq!(set.capacity(), cap);

        let mut set = LinearSet::from([1, 2, 3]);
        let mut drain = set.drain();
        assert_eq!(drain.len(), 3);
        drain.next();
        drop(drain);
        assert!(set.is_empty());
    }

    // ---- construction, conversion and traits ----

    #[test]
    fn from_iterator_array_and_extend() {
        let set: LinearSet<i32> = vec![1, 2, 2, 3, 3, 3].into_iter().collect();
        assert_eq!(set.len(), 3);

        let set = LinearSet::from([5, 5, 6]);
        assert_eq!(set.len(), 2);

        let mut set = LinearSet::new();
        set.extend([1, 2, 3]);
        set.extend(&[3, 4]);
        assert_eq!(sorted(set.iter()), vec![1, 2, 3, 4]);
    }

    #[test]
    fn equality_ignores_order() {
        let a = LinearSet::from([1, 2, 3]);
        let b = LinearSet::from([3, 1, 2]);
        assert_eq!(a, b);
        assert_ne!(a, LinearSet::from([1, 2]));
        assert_ne!(a, LinearSet::from([1, 2, 4]));
        assert_eq!(LinearSet::<i32>::new(), LinearSet::default());
    }

    #[test]
    fn debug_and_clone() {
        let set = LinearSet::from([1, 2]);
        assert_eq!(format!("{set:?}"), "{1, 2}");
        let mut copy = set.clone();
        copy.insert(3);
        assert_eq!(set.len(), 2);
        assert_eq!(copy.len(), 3);
    }

    #[test]
    fn into_iter_by_value_and_by_reference() {
        let set = LinearSet::from(["a".to_string(), "b".to_string()]);
        let mut by_ref: Vec<&String> = (&set).into_iter().collect();
        by_ref.sort();
        assert_eq!(by_ref, vec!["a", "b"]);
        let mut owned: Vec<String> = set.into_iter().collect();
        owned.sort();
        assert_eq!(owned, vec!["a", "b"]);
    }

    #[test]
    fn iterators_are_double_ended_exact_size_and_fused() {
        let set = LinearSet::from([1, 2, 3, 4]);
        let mut iter = set.iter();
        assert_eq!(iter.len(), 4);
        assert_eq!(iter.next_back(), Some(&4));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.len(), 2);
        assert_eq!(iter.by_ref().count(), 2);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);

        assert_eq!(set.clone().into_iter().next_back(), Some(4));
        assert_eq!(set.clone().into_iter().len(), 4);
        assert_eq!(set.iter().clone().count(), 4);
        assert_eq!(format!("{:?}", set.iter()), "[1, 2, 3, 4]");
        assert_eq!(
            format!("{:?}", set.clone().into_iter()),
            "IntoIter { remaining: 4 }"
        );
    }

    #[test]
    fn iterator_types_are_nameable() {
        type Nameable<'a> = (
            Option<super::Iter<'a, i32>>,
            Option<super::IntoIter<i32>>,
            Option<super::Drain<'a, i32>>,
            Option<super::Union<'a, i32>>,
            Option<super::Intersection<'a, i32>>,
            Option<super::Difference<'a, i32>>,
            Option<super::SymmetricDifference<'a, i32>>,
        );
        let none: Nameable<'_> = Default::default();
        assert!(none.0.is_none());
    }

    // ---- set operations ----

    #[test]
    fn set_operations_match_hashset() {
        let cases: [(&[i32], &[i32]); 6] = [
            (&[], &[]),
            (&[1, 2, 3], &[]),
            (&[], &[1, 2, 3]),
            (&[1, 2, 3], &[3, 4, 5]),
            (&[1, 2, 3], &[1, 2, 3]),
            (&[1, 2, 3, 4, 5, 6, 7, 8], &[2, 4, 6, 10]),
        ];
        for (xs, ys) in cases {
            let (a, b) = (
                LinearSet::from_iter(xs.iter().copied()),
                LinearSet::from_iter(ys.iter().copied()),
            );
            let (ha, hb): (HashSet<i32>, HashSet<i32>) =
                (xs.iter().copied().collect(), ys.iter().copied().collect());

            let check = |got: Vec<i32>, want: HashSet<&i32>| {
                let mut want: Vec<i32> = want.into_iter().copied().collect();
                want.sort_unstable();
                assert_eq!(got, want, "{xs:?} vs {ys:?}");
            };
            check(sorted(a.union(&b)), ha.union(&hb).collect());
            check(sorted(a.intersection(&b)), ha.intersection(&hb).collect());
            check(sorted(a.difference(&b)), ha.difference(&hb).collect());
            check(
                sorted(a.symmetric_difference(&b)),
                ha.symmetric_difference(&hb).collect(),
            );
            assert_eq!(a.is_subset(&b), ha.is_subset(&hb));
            assert_eq!(a.is_superset(&b), ha.is_superset(&hb));
            assert_eq!(a.is_disjoint(&b), ha.is_disjoint(&hb));
        }
    }

    #[test]
    fn set_operation_order_follows_the_receiver() {
        let a = LinearSet::from([1, 2, 3]);
        let b = LinearSet::from([5, 3, 4]);
        assert_eq!(
            a.union(&b).copied().collect::<Vec<_>>(),
            vec![1, 2, 3, 5, 4]
        );
        assert_eq!(a.intersection(&b).copied().collect::<Vec<_>>(), vec![3]);
        assert_eq!(a.difference(&b).copied().collect::<Vec<_>>(), vec![1, 2]);
        assert_eq!(
            a.symmetric_difference(&b).copied().collect::<Vec<_>>(),
            vec![1, 2, 5, 4]
        );
    }

    #[test]
    fn set_operation_iterators_clone_debug_and_fuse() {
        let a = LinearSet::from([1, 2, 3]);
        let b = LinearSet::from([2, 3, 4]);
        let mut union = a.union(&b);
        assert_eq!(union.clone().count(), 4);
        assert_eq!(format!("{union:?}"), "[1, 2, 3, 4]");
        for _ in 0..4 {
            union.next();
        }
        assert_eq!(union.next(), None);
        assert_eq!(union.next(), None);
        assert_eq!(format!("{:?}", a.intersection(&b)), "[2, 3]");
        assert_eq!(format!("{:?}", a.difference(&b)), "[1]");
        assert_eq!(format!("{:?}", a.symmetric_difference(&b)), "[1, 4]");
        assert_eq!(a.difference(&b).size_hint(), (0, Some(3)));
    }

    #[test]
    fn operators_build_new_sets() {
        let a = LinearSet::from([1, 2, 3]);
        let b = LinearSet::from([3, 4]);
        assert_eq!(&a | &b, LinearSet::from([1, 2, 3, 4]));
        assert_eq!(&a & &b, LinearSet::from([3]));
        assert_eq!(&a - &b, LinearSet::from([1, 2]));
        assert_eq!(&a ^ &b, LinearSet::from([1, 2, 4]));
        assert_eq!(a.len(), 3); // operands untouched
    }

    #[test]
    fn subset_superset_disjoint_edge_cases() {
        let empty = LinearSet::<i32>::new();
        let a = LinearSet::from([1, 2]);
        assert!(empty.is_subset(&a));
        assert!(empty.is_subset(&empty));
        assert!(a.is_superset(&empty));
        assert!(empty.is_disjoint(&a));
        assert!(a.is_subset(&a));
        assert!(!a.is_subset(&LinearSet::from([1])));
        assert!(!a.is_disjoint(&LinearSet::from([2, 9])));
    }

    // ---- larger sets (block search) ----

    #[test]
    fn works_at_every_size_around_the_block_search_threshold() {
        for n in 0..=100u32 {
            let set: LinearSet<u32> = (0..n).collect();
            assert_eq!(set.len(), n as usize);
            for i in 0..n {
                assert!(set.contains(&i), "n={n} i={i}");
            }
            assert!(!set.contains(&n));
        }
    }

    #[test]
    fn matches_hashset_under_random_operations() {
        let mut state = 0xDEAD_BEEFu64;
        let mut next = move || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            state >> 33
        };

        let steps = if cfg!(miri) { 300 } else { 20_000 };
        let mut set: LinearSet<u16> = LinearSet::new();
        let mut model: HashSet<u16> = HashSet::new();
        for _ in 0..steps {
            let value = (next() % 120) as u16; // enough to exceed 32 elements
            match next() % 6 {
                0..=2 => assert_eq!(set.insert(value), model.insert(value)),
                3 | 4 => assert_eq!(set.remove(&value), model.remove(&value)),
                _ => assert_eq!(set.contains(&value), model.contains(&value)),
            }
            assert_eq!(set.len(), model.len());
        }
        let got: HashSet<u16> = set.into_iter().collect();
        assert_eq!(got, model);
    }

    // ---- drop accounting ----

    #[derive(Clone)]
    struct Tracked(u32, #[allow(dead_code)] Rc<()>);
    impl PartialEq for Tracked {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }
    impl Eq for Tracked {}

    fn live(token: &Rc<()>) -> usize {
        Rc::strong_count(token) - 1
    }

    fn filled(token: &Rc<()>, n: u32) -> LinearSet<Tracked> {
        (0..n).map(|i| Tracked(i, Rc::clone(token))).collect()
    }

    #[test]
    fn duplicate_insert_drops_the_new_value() {
        let token = Rc::new(());
        let mut set = filled(&token, 3);
        assert!(!set.insert(Tracked(1, Rc::clone(&token))));
        assert_eq!(live(&token), 3);
    }

    #[test]
    fn replace_take_remove_retain_and_clear_drop_correctly() {
        let token = Rc::new(());
        let mut set = filled(&token, 6);
        drop(set.replace(Tracked(2, Rc::clone(&token))));
        assert_eq!(live(&token), 6);
        drop(set.take(&Tracked(0, Rc::clone(&token))));
        assert_eq!(live(&token), 5);
        assert!(set.remove(&Tracked(1, Rc::clone(&token))));
        assert_eq!(live(&token), 4);
        set.retain(|t| t.0 % 2 == 0);
        assert_eq!(live(&token), 2);
        set.clear();
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn drain_into_iter_and_drop_release_everything() {
        let token = Rc::new(());
        let mut set = filled(&token, 5);
        let mut drain = set.drain();
        drop(drain.next());
        assert_eq!(live(&token), 4);
        drop(drain);
        assert_eq!(live(&token), 0);

        let set = filled(&token, 5);
        let mut iter = set.into_iter();
        drop(iter.next());
        assert_eq!(live(&token), 4);
        drop(iter);
        assert_eq!(live(&token), 0);

        let set = filled(&token, 3);
        let copy = set.clone();
        assert_eq!(live(&token), 6);
        drop((set, copy));
        assert_eq!(live(&token), 0);
    }
}
