//! A `Send + Sync` variant of [`Thing`].
//!
//! See [`SThing`].

use crate::heap_size::HeapSize;
use crate::thing::{DEFAULT_THING_SIZE, Thing};

/// A [`Thing`] that is `Send` and `Sync`.
///
/// `Thing` can hold values of any type, including ones that are not
/// thread-safe, so it cannot be sent to other threads or shared between them.
/// `SThing` can only be created from values that are `Send + Sync`, so it is
/// `Send + Sync` itself and can be moved to another thread, shared in an
/// `Arc`, or kept in a `static`.
///
/// Otherwise it works like `Thing`: the same storage (small values inline,
/// larger or over-aligned ones boxed), and the same accessors.
///
/// # Examples
///
/// ```
/// use anythingy::SThing;
///
/// let thing = SThing::<24>::new(String::from("shared"));
///
/// std::thread::scope(|s| {
///     s.spawn(|| assert_eq!(thing.get_ref::<String>(), "shared"));
///     s.spawn(|| assert_eq!(thing.get_ref::<String>(), "shared"));
/// });
/// ```
///
/// Values that are not thread-safe are rejected:
///
/// ```compile_fail,E0277
/// use std::rc::Rc;
/// use anythingy::SThing;
///
/// let thing = SThing::<24>::new(Rc::new(1));
/// ```
///
/// A `Thing` cannot be turned into an `SThing`, but the other direction works,
/// with [`From`]:
///
/// ```
/// use anythingy::{SThing, Thing};
///
/// let thing: Thing = SThing::<24>::new(5_u32).into();
/// assert_eq!(*thing.get_ref::<u32>(), 5);
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct SThing<const SIZE: usize = DEFAULT_THING_SIZE>(Thing<SIZE>);

// SAFETY: an `SThing` can only be constructed by `new`, which requires
// `T: Send`, and the wrapped `Thing` is private, so nothing can put a
// different value in. Moving the `SThing` to another thread therefore moves
// a `Send` value.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<const SIZE: usize> Send for SThing<SIZE> {}

// SAFETY: `new` requires `T: Sync`, so sharing `&SThing` shares `&T` of a
// `Sync` type. No accessor gives shared access to anything else.
unsafe impl<const SIZE: usize> Sync for SThing<SIZE> {}

impl<const SIZE: usize> SThing<SIZE> {
    /// Creates a new `SThing` from a value of type `T`.
    ///
    /// The value is boxed if it is bigger than `SIZE`, or if its alignment is
    /// greater than 8.
    ///
    /// # Panics
    /// Panics, if size of `T` is greater than `SIZE`, but `SIZE` is smaller than size of `Box<T>`.
    #[inline]
    #[must_use]
    pub fn new<T: Send + Sync + 'static>(t: T) -> Self {
        Self(Thing::new(t))
    }

    /// Returns the original value, if the given type and the original type match.
    ///
    /// # Panics
    /// Panics if the given type and the original type do not match.
    #[inline]
    #[must_use]
    pub fn get<T: 'static>(self) -> T {
        self.0.get()
    }

    /// Returns a reference to the original value, if the given type and the original type match.
    ///
    /// # Panics
    /// Panics if the given type and the original type do not match.
    #[inline]
    #[must_use]
    pub fn get_ref<T: 'static>(&self) -> &T {
        self.0.get_ref()
    }

    /// Returns a mutable reference to the original value, if the given type and the original type match.
    ///
    /// # Panics
    /// Panics if the given type and the original type do not match.
    #[inline]
    #[must_use]
    pub fn get_mut<T: 'static>(&mut self) -> &mut T {
        self.0.get_mut()
    }

    /// Returns the original value, if the given type and the original type match.
    /// Returns `None`, if types don't match.
    #[inline]
    #[must_use]
    pub fn try_get<T: 'static>(self) -> Option<T> {
        self.0.try_get()
    }

    /// Returns a reference to the original value, if the given type and the original type match.
    /// Returns `None`, if types don't match.
    #[inline]
    #[must_use]
    pub fn try_get_ref<T: 'static>(&self) -> Option<&T> {
        self.0.try_get_ref()
    }

    /// Returns a mutable reference to the original value, if the given type and the original type match.
    /// Returns `None`, if types don't match.
    #[inline]
    #[must_use]
    pub fn try_get_mut<T: 'static>(&mut self) -> Option<&mut T> {
        self.0.try_get_mut()
    }

    /// Returns the original value without checking that `T` is its type.
    ///
    /// The unchecked counterpart of [`get`](Self::get).
    ///
    /// # Safety
    ///
    /// `T` must be exactly the type this `SThing` was created with, that is
    /// [`is_type::<T>()`](Self::is_type) must be `true`. Otherwise the stored
    /// bytes are reinterpreted as a `T`, which is undefined behavior.
    #[inline]
    #[must_use]
    pub unsafe fn get_unchecked<T: 'static>(self) -> T {
        // SAFETY: forwarded to the caller.
        unsafe { self.0.get_unchecked() }
    }

    /// Returns a reference to the original value without checking that `T` is
    /// its type.
    ///
    /// The unchecked counterpart of [`get_ref`](Self::get_ref).
    ///
    /// # Safety
    ///
    /// `T` must be exactly the type this `SThing` was created with, see
    /// [`get_unchecked`](Self::get_unchecked).
    #[inline]
    #[must_use]
    pub unsafe fn get_ref_unchecked<T: 'static>(&self) -> &T {
        // SAFETY: forwarded to the caller.
        unsafe { self.0.get_ref_unchecked() }
    }

    /// Returns a mutable reference to the original value without checking
    /// that `T` is its type.
    ///
    /// The unchecked counterpart of [`get_mut`](Self::get_mut).
    ///
    /// # Safety
    ///
    /// `T` must be exactly the type this `SThing` was created with, see
    /// [`get_unchecked`](Self::get_unchecked).
    #[inline]
    #[must_use]
    pub unsafe fn get_mut_unchecked<T: 'static>(&mut self) -> &mut T {
        // SAFETY: forwarded to the caller.
        unsafe { self.0.get_mut_unchecked() }
    }

    /// Returns `true` if the stored value is of type `T`.
    #[inline]
    #[must_use]
    pub fn is_type<T: 'static>(&self) -> bool {
        self.0.is_type::<T>()
    }
}

/// Forgets that the value is thread-safe.
impl<const SIZE: usize> From<SThing<SIZE>> for Thing<SIZE> {
    #[inline]
    fn from(thing: SThing<SIZE>) -> Self {
        thing.0
    }
}

/// Reports the allocation of a value that is boxed, which is `0` for a value
/// that is stored inline. See [`Thing`]'s implementation.
impl<const SIZE: usize> HeapSize for SThing<SIZE> {
    #[inline]
    fn heap_size(&self) -> usize {
        self.0.heap_size()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_send_sync<T: Send + Sync>() {}

    #[test]
    fn is_send_and_sync() {
        assert_send_sync::<SThing<8>>();
        assert_send_sync::<SThing>();
    }

    #[test]
    fn same_size_as_thing() {
        assert_eq!(size_of::<SThing<24>>(), size_of::<Thing<24>>());
    }

    #[test]
    fn stores_and_returns_values() {
        let mut thing = SThing::<24>::new(String::from("a"));
        assert!(thing.is_type::<String>());
        assert!(!thing.is_type::<u32>());

        thing.get_mut::<String>().push('b');
        assert_eq!(thing.get_ref::<String>(), "ab");
        assert!(thing.try_get_ref::<u32>().is_none());
        assert!(thing.try_get_mut::<u32>().is_none());
        assert_eq!(thing.get::<String>(), "ab");
    }

    #[test]
    fn try_get_mismatch_is_none() {
        assert!(SThing::<24>::new(1_u8).try_get::<u16>().is_none());
    }

    #[test]
    #[should_panic(expected = "assertion")]
    fn get_mismatch_panics() {
        let _ = SThing::<24>::new(1_u8).get::<u16>();
    }

    #[test]
    fn unchecked_accessors() {
        let mut thing = SThing::<24>::new(7_u32);
        // SAFETY: the stored type is `u32`.
        unsafe {
            *thing.get_mut_unchecked::<u32>() += 1;
            assert_eq!(*thing.get_ref_unchecked::<u32>(), 8);
            assert_eq!(thing.get_unchecked::<u32>(), 8);
        }
    }

    #[test]
    fn big_and_aligned_values_work() {
        #[repr(align(32))]
        struct Aligned(u8);

        let thing = SThing::<8>::new([1_u64, 2, 3, 4]);
        assert_eq!(thing.get::<[u64; 4]>(), [1, 2, 3, 4]);
        assert_eq!(SThing::<24>::new(Aligned(3)).get::<Aligned>().0, 3);
    }

    #[test]
    fn drops_the_value_once() {
        use alloc::sync::Arc;

        let value = Arc::new(());
        let thing = SThing::<24>::new(Arc::clone(&value));
        assert_eq!(Arc::strong_count(&value), 2);
        drop(thing);
        assert_eq!(Arc::strong_count(&value), 1);
    }

    #[test]
    fn moves_between_threads() {
        let thing = SThing::<24>::new(String::from("moved"));
        let text = std::thread::spawn(move || thing.get::<String>())
            .join()
            .unwrap();
        assert_eq!(text, "moved");
    }

    #[test]
    fn converts_into_thing() {
        let thing: Thing<24> = SThing::new(9_i64).into();
        assert_eq!(*thing.get_ref::<i64>(), 9);
    }

    #[test]
    fn heap_size_is_the_box_of_a_big_value() {
        assert_eq!(SThing::<24>::new(5_u64).heap_size(), 0);
        assert_eq!(SThing::<8>::new([0_u64; 10]).heap_size(), 80);
    }
}
