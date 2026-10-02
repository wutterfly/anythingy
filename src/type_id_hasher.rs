//! A hasher for maps keyed by [`TypeId`](core::any::TypeId).
//!
//! See [`TypeIdHasher`].

use core::hash::{BuildHasherDefault, Hasher};

/// A hasher for [`TypeId`](core::any::TypeId) keys, which uses the `TypeId` as
/// it is instead of hashing it again.
///
/// A `TypeId` is already a well-mixed hash of its type, so hashing it a second
/// time, like the default hasher of a `HashMap` does, only costs time. This
/// hasher passes it through. It is the default hasher of `ThingMap`, and it
/// works for any map that is keyed by `TypeId`: a registry of handlers per
/// type, a cache of data per type, or a type map of your own.
///
/// It is meant for keys that already are well-distributed hashes. For other
/// keys, such as small integers, it distributes badly and a map can become
/// slow, so do not use it for those. It has no randomness, which is no concern
/// for a `TypeId`: it comes from the compiler, and not from outside input.
///
/// Use it through [`TypeIdBuildHasher`], as the hasher parameter of a map: of a
/// `HashMap`, a `HashSet`, or the `InlineMap` of this crate.
///
/// # Examples
///
/// ```
/// use std::any::TypeId;
/// use std::collections::HashMap;
///
/// use anythingy::TypeIdBuildHasher;
///
/// let mut names: HashMap<TypeId, &str, TypeIdBuildHasher> = HashMap::default();
/// names.insert(TypeId::of::<u32>(), "u32");
/// names.insert(TypeId::of::<String>(), "String");
///
/// assert_eq!(names[&TypeId::of::<String>()], "String");
/// assert_eq!(names.get(&TypeId::of::<u8>()), None);
/// ```
#[derive(Debug, Default, Clone)]
pub struct TypeIdHasher(u64);

impl Hasher for TypeIdHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write_u64(&mut self, value: u64) {
        // A single write leaves exactly `value` (0 rotated is 0).
        self.0 = self.0.rotate_left(5) ^ value;
    }

    #[inline]
    #[allow(clippy::cast_possible_truncation)] // deliberate: the low half of the value
    fn write_u128(&mut self, value: u128) {
        self.write_u64(value as u64);
        self.write_u64((value >> 64) as u64);
    }

    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_u64(u64::from(byte));
        }
    }
}

/// The `BuildHasher` of [`TypeIdHasher`], to be used as the hasher parameter of
/// a map that is keyed by [`TypeId`](core::any::TypeId).
pub type TypeIdBuildHasher = BuildHasherDefault<TypeIdHasher>;

#[cfg(test)]
mod tests {
    use alloc::collections::BTreeSet;
    use alloc::vec::Vec;
    use core::any::TypeId;
    use core::hash::BuildHasher;

    use super::*;

    #[test]
    fn passes_a_single_write_through() {
        let mut hasher = TypeIdHasher::default();
        hasher.write_u64(0xDEAD_BEEF_1234_5678);
        assert_eq!(hasher.finish(), 0xDEAD_BEEF_1234_5678);
    }

    #[test]
    fn keeps_several_writes_distinct() {
        let hash = |a: u64, b: u64| {
            let mut hasher = TypeIdHasher::default();
            hasher.write_u64(a);
            hasher.write_u64(b);
            hasher.finish()
        };
        assert_ne!(hash(1, 2), hash(2, 1));
        assert_ne!(hash(1, 2), hash(1, 3));

        let mut bytes = TypeIdHasher::default();
        bytes.write(&[1, 2, 3]);
        let mut other = TypeIdHasher::default();
        other.write(&[3, 2, 1]);
        assert_ne!(bytes.finish(), other.finish());

        let mut wide = TypeIdHasher::default();
        wide.write_u128(0x1111_2222_3333_4444_5555_6666_7777_8888);
        assert_ne!(wide.finish(), 0);
    }

    #[test]
    fn an_unused_hasher_finishes_with_zero() {
        assert_eq!(TypeIdHasher::default().finish(), 0);
    }

    #[test]
    fn distinct_types_hash_to_distinct_values() {
        struct Marker<const N: usize>;

        let build = TypeIdBuildHasher::default();
        let ids = [
            TypeId::of::<u8>(),
            TypeId::of::<u16>(),
            TypeId::of::<u32>(),
            TypeId::of::<alloc::string::String>(),
            TypeId::of::<Vec<u8>>(),
            TypeId::of::<Marker<0>>(),
            TypeId::of::<Marker<1>>(),
            TypeId::of::<Marker<2>>(),
        ];

        let hashes: BTreeSet<u64> = ids.iter().map(|id| build.hash_one(id)).collect();
        assert_eq!(hashes.len(), ids.len());
        assert_eq!(build.hash_one(ids[0]), build.hash_one(ids[0]));
    }

    #[cfg(feature = "std")]
    #[test]
    fn works_as_the_hasher_of_a_type_keyed_map() {
        use std::collections::{HashMap, HashSet};

        struct Marker<const N: usize>;

        let mut map: HashMap<TypeId, usize, TypeIdBuildHasher> = HashMap::default();
        map.insert(TypeId::of::<Marker<0>>(), 0);
        map.insert(TypeId::of::<Marker<1>>(), 1);
        map.insert(TypeId::of::<Marker<2>>(), 2);
        map.insert(TypeId::of::<Marker<1>>(), 10);

        assert_eq!(map.len(), 3);
        assert_eq!(map[&TypeId::of::<Marker<1>>()], 10);
        assert_eq!(map.get(&TypeId::of::<Marker<3>>()), None);

        let mut set: HashSet<TypeId, TypeIdBuildHasher> = HashSet::default();
        assert!(set.insert(TypeId::of::<u8>()));
        assert!(!set.insert(TypeId::of::<u8>()));
    }
}
