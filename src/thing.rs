use std::{
    any::TypeId,
    cell::UnsafeCell,
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
};

/// Default size of [`Thing`][crate::Thing].
/// Chosen to be 3x [`std::mem::size_of::<usize>()`], to facilitate [`Vec`]/[`String`] without boxing them, to prevent double pointers.
pub const DEFAULT_THING_SIZE: usize = std::mem::size_of::<usize>() * 3;

/// A Structure for storing type-erased values. Similar to [`Box<dyn Any>`][std::any::Any] it can store values of any type.
///
/// What makes this structure special is, that the `SIZE` of Thing can be specified.
/// For values of type `T`, where size of `T` is smaller/equal to `SIZE`, no additional allocation is needed.
///
/// For types `T` that are greater then `SIZE`, the value gets boxed.
///
/// For types `T` which alignment is greater then 8, the value gets also boxed.
///
/// # Send / Sync
/// By default, `Thing` is not `Send` or `Sync`, since it contains raw pointers and manual drop glue.
/// To use `Thing` in a  `Send`/`Sync` manner, wrap it in a struct that implements the appropriate traits, and enforce construction only with appropriate constrains.
///
///
/// # Safety notes
/// - The internals write `T` into a byte buffer and later read it back. The code ensures that types with
///   alignment > 8 are boxed, and `Thing` is repr(align(8)), so alignment requirements for unboxed values are satisfied.
/// - Conversions are performed with explicit `ptr::write` / `ptr::read` into a `MaybeUninit<[u8; SIZE]>` backing buffer,
///   avoiding reading inactive union fields.
#[derive(Debug)]
#[repr(align(8))]
pub struct Thing<const SIZE: usize = DEFAULT_THING_SIZE> {
    id: TypeId,
    drop: fn(UnsafeCell<AlignedBytes<SIZE>>),
    data: UnsafeCell<AlignedBytes<SIZE>>,
    _not_send_sync: PhantomData<*const ()>,
}

#[derive(Debug)]
#[repr(align(8))]
struct AlignedBytes<const SIZE: usize>([MaybeUninit<u8>; SIZE]);

impl<const SIZE: usize> Thing<SIZE> {
    /// Creates a new `Thing` from generic type `T`. Uses the boxed value, if size of `T` is bigger then `SIZE`.
    ///
    /// If the alignment of type `T` is greater then 8, `T` gets also boxed.
    ///
    /// # Panics
    /// Panics, if size of `T` is greater then `SIZE`, but `SIZE` is smaller then size of `Box<T>`.
    #[inline]
    #[must_use]
    pub fn new<T: 'static>(t: T) -> Self {
        // save type
        let id = TypeId::of::<T>();

        if Self::boxed::<T>() {
            // check that Thing can hold at least a Box.
            assert!(
                Self::fitting::<Box<T>>(),
                "Thing<SIZE> too small to hold Box<T>"
            );

            // convert type from bytes (Box<T>)
            let convert = Convert::new(Box::new(t));

            // convert type to bytes
            let data = convert.bytes();

            return Self {
                id,
                drop: Self::drop_glue::<T>,
                data,
                _not_send_sync: PhantomData,
            };
        }

        // convert type from bytes (T)
        let convert = Convert::new(t);

        // convert type to bytes
        let data = convert.bytes();

        // get drop glue
        let drop = if std::mem::needs_drop::<T>() {
            Self::drop_glue::<T>
        } else {
            Self::empty_drop_glue
        };

        Self {
            id,
            drop,
            data,
            _not_send_sync: PhantomData,
        }
    }

    /// Returns the original type of `Thing`, if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    #[inline]
    #[must_use]
    pub fn get<T: 'static>(mut self) -> T {
        // check that types are matching
        assert!(self.is_type::<T>());

        // Prevent double-drop: mark drop as empty; we'll move the data out ourselves.
        self.drop = Self::empty_drop_glue;

        let data = unsafe { self.move_data_uninit() };

        if Self::boxed::<T>() {
            // convert type from bytes
            let convert = Convert::<SIZE, Box<T>>::from_bytes(data);

            // move value out of box
            return *convert.get();
        }

        // convert type from bytes
        let convert = Convert::<SIZE, T>::from_bytes(data);

        convert.get()
    }

    /// Returns a reference to the original type of `Thing`, if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    #[inline]
    #[must_use]
    pub fn get_ref<T: 'static>(&self) -> &T {
        // check that types are matching
        assert!(self.is_type::<T>());

        if Self::boxed::<T>() {
            // For boxed case the stored value is a `Box<T>`; get_ref returns &Box<T> then `.as_ref()` to get &T.
            return Convert::<SIZE, Box<T>>::get_ref(&self.data).as_ref();
        }

        Convert::<SIZE, T>::get_ref(&self.data)
    }

    /// Returns a mutable reference to the original type of `Thing`, if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    #[inline]
    #[must_use]
    pub fn get_mut<T: 'static>(&mut self) -> &mut T {
        // check that types are matching
        assert!(self.is_type::<T>());

        if Self::boxed::<T>() {
            return Convert::<SIZE, Box<T>>::get_mut(&mut self.data).as_mut();
        }

        Convert::<SIZE, T>::get_mut(&mut self.data)
    }

    /// Returns the original type of `Thing`, if given type and original type match.
    /// Returns `None`, if types don't match.
    #[inline]
    #[must_use]
    pub fn try_get<T: 'static>(mut self) -> Option<T> {
        // check that types are matching
        if !self.is_type::<T>() {
            return None;
        }

        // Prevent double-drop
        self.drop = Self::empty_drop_glue;

        let data = unsafe { self.move_data_uninit() };

        if Self::boxed::<T>() {
            // convert type from bytes
            let convert = Convert::<SIZE, Box<T>>::from_bytes(data);

            // move value out of box
            return Some(*convert.get());
        }

        // convert type from bytes
        let convert = Convert::<SIZE, T>::from_bytes(data);

        Some(convert.get())
    }

    /// Returns a reference to the original type of `Thing`, if given type and original type match.
    /// Returns `None`, if types don't match.
    #[inline]
    #[must_use]
    pub fn try_get_ref<T: 'static>(&self) -> Option<&T> {
        // check that types are matching
        if !self.is_type::<T>() {
            return None;
        }

        if Self::boxed::<T>() {
            return Some(Convert::<SIZE, Box<T>>::get_ref(&self.data).as_ref());
        }

        Some(Convert::<SIZE, T>::get_ref(&self.data))
    }

    /// Returns a mutable reference to the original type of `Thing`, if given type and original type match.
    /// Returns `None`, if types don't match.
    #[inline]
    #[must_use]
    pub fn try_get_mut<T: 'static>(&mut self) -> Option<&mut T> {
        // check that types are matching
        if !self.is_type::<T>() {
            return None;
        }

        if Self::boxed::<T>() {
            return Some(Convert::<SIZE, Box<T>>::get_mut(&mut self.data).as_mut());
        }

        Some(Convert::<SIZE, T>::get_mut(&mut self.data))
    }

    /// Returns true, if erased type is equal to given type.
    #[inline]
    #[must_use]
    pub fn is_type<T: 'static>(&self) -> bool {
        self.id == TypeId::of::<T>()
    }

    /// Returns true, if `T` can be made into a `Thing`.
    ///
    /// Returns false, if `SIZE` is smaller then a needed `Box<T>`.
    #[inline]
    #[must_use]
    pub const fn fitting<T: 'static>() -> bool {
        Self::size_requirement::<T>() <= SIZE
    }

    /// Returns the minimum required `SIZE`, to fit `T` into a `Thing`.
    ///
    /// This function does not differentiate if `T` has to be boxed or not.
    /// For minimum size requirement while `T` can remain unboxed, see `size_requirement_unboxed`.
    #[inline]
    #[must_use]
    pub const fn size_requirement<T: 'static>() -> usize {
        let size = std::mem::size_of::<T>();
        let boxed = std::mem::size_of::<Box<T>>();
        let align = std::mem::align_of::<T>();

        // value always has to be boxed if align is greater then 8
        if align > 8 || size > boxed {
            return boxed;
        }

        size
    }

    /// Returns the minimum required `SIZE`, to fit `T` into a `Thing` while `T` can remain unboxed.
    /// If `T` has to be boxed, return `None`.
    #[inline]
    #[must_use]
    pub const fn size_requirement_unboxed<T: 'static>() -> Option<usize> {
        let size = std::mem::size_of::<T>();
        let align = std::mem::align_of::<T>();

        // value always has to be boxed if align is greater then 8
        if align > 8 {
            return None;
        }

        Some(size)
    }

    /// Returns true, if `T` has to be boxed to be made into a `Thing`.
    #[inline]
    #[must_use]
    pub const fn boxed<T: 'static>() -> bool {
        if let Some(size) = Self::size_requirement_unboxed::<T>() {
            size > SIZE
        } else {
            true
        }
    }

    /// This is unsafe, because it leaves self.data in an invalid state,
    const unsafe fn move_data_uninit(&mut self) -> UnsafeCell<AlignedBytes<SIZE>> {
        let fill = UnsafeCell::new(AlignedBytes([MaybeUninit::<u8>::uninit(); SIZE]));

        std::mem::replace(&mut self.data, fill)
    }

    #[inline]
    fn drop_glue<T: 'static>(data: UnsafeCell<AlignedBytes<SIZE>>) {
        if Self::boxed::<T>() {
            // convert type from bytes (Box<T>)
            let convert = Convert::<SIZE, Box<T>>::from_bytes(data);

            // move value out of box and drop
            let t: Box<T> = convert.get();
            drop(t);
            return;
        }

        // Sanity check: if the type would be stored unboxed, its alignment must fit into our buffer.
        // If this fails in debug builds it indicates a mismatch between `boxed::<T>()` and actual alignment.
        debug_assert!(
            std::mem::align_of::<T>() <= std::mem::align_of::<AlignedBytes<SIZE>>(),
            "alignment of T exceeds alignment of Thing storage; T should have been boxed"
        );

        // convert bytes to t
        let convert = Convert::<SIZE, T>::from_bytes(data);
        let t: T = convert.get();

        drop(t);
    }

    #[inline]
    const fn empty_drop_glue<const S: usize>(_: UnsafeCell<AlignedBytes<S>>) {}
}

impl<const SIZE: usize> std::ops::Drop for Thing<SIZE> {
    #[inline]
    fn drop(&mut self) {
        // Take ownership of the bytes buffer and call the stored drop function.
        let drop_buf = unsafe { self.move_data_uninit() };
        (self.drop)(drop_buf);
    }
}

/// Convert struct: explicit byte buffer backing plus pointer operations.
///
/// This avoids reading inactive union fields by using explicit `ptr::write`/`ptr::read` to manage `T` in the byte buffer.
#[repr(align(8))]
struct Convert<const SIZE: usize, T> {
    bytes: ManuallyDrop<UnsafeCell<AlignedBytes<SIZE>>>,
    _marker: PhantomData<T>,
}

impl<const SIZE: usize, T> Convert<SIZE, T> {
    #[inline]
    fn new(value: T) -> Self {
        // Ensure the compile-time size fits into our slot (for unboxed storage)
        let size = core::mem::size_of::<T>();
        assert!(size <= SIZE, "type size exceeds slot SIZE");

        // Debug-time alignment check: types that would be stored unboxed must satisfy the buffer's alignment.
        debug_assert!(
            std::mem::align_of::<T>() <= std::mem::align_of::<AlignedBytes<SIZE>>(),
            "alignment of T exceeds alignment of Thing storage; consider boxing T"
        );

        // Allocate the bytes buffer (aligned wrapper)
        let bytes_cell = UnsafeCell::new(AlignedBytes([MaybeUninit::<u8>::uninit(); SIZE]));
        let conv = Self {
            bytes: ManuallyDrop::new(bytes_cell),
            _marker: PhantomData,
        };

        // Compute a properly-typed pointer into the buffer.
        // Safety: Thing is repr(align(8)). Call sites ensure that types with align > 8 are boxed, so align_of::<T>() <= 8 here.
        let ptr_to_t = conv
            .bytes
            .get()
            .cast::<AlignedBytes<SIZE>>()
            .cast::<u8>()
            .cast::<T>();

        unsafe {
            // Write the value into the buffer. This avoids creating an intermediate active union field.
            std::ptr::write(ptr_to_t, value);
        }

        conv
    }

    #[inline]
    const fn bytes(self) -> UnsafeCell<AlignedBytes<SIZE>> {
        // Move out the underlying bytes buffer without running any drops
        ManuallyDrop::into_inner(self.bytes)
    }

    #[inline]
    const fn from_bytes(bytes: UnsafeCell<AlignedBytes<SIZE>>) -> Self {
        Self {
            bytes: ManuallyDrop::new(bytes),
            _marker: PhantomData,
        }
    }

    #[inline]
    fn get(self) -> T {
        // Move the T value out of the bytes buffer
        let bytes = ManuallyDrop::into_inner(self.bytes);
        let ptr_to_t = bytes
            .get()
            .cast::<AlignedBytes<SIZE>>()
            .cast::<u8>()
            .cast::<T>();

        // Debug-time alignment check: ensure the stored T is properly aligned for an aligned read.
        debug_assert!(
            std::mem::align_of::<T>() <= std::mem::align_of::<AlignedBytes<SIZE>>(),
            "get: alignment of T ({}) exceeds buffer alignment ({}); T should have been boxed",
            std::mem::align_of::<T>(),
            std::mem::align_of::<AlignedBytes<SIZE>>()
        );

        // Use aligned read now that we assert alignment in debug; this is potentially faster on some targets.
        unsafe { std::ptr::read(ptr_to_t.cast_const()) }
    }

    #[inline]
    fn get_ref(data: &UnsafeCell<AlignedBytes<SIZE>>) -> &T {
        // Debug-time alignment check: ensure the stored T would be properly aligned for reference creation.
        debug_assert!(
            std::mem::align_of::<T>() <= std::mem::align_of::<AlignedBytes<SIZE>>(),
            "alignment of T exceeds alignment of Thing storage; T should have been boxed"
        );

        let ptr_to_t = data.get().cast_const().cast::<u8>().cast::<T>();
        unsafe { &*ptr_to_t }
    }

    #[inline]
    fn get_mut(data: &mut UnsafeCell<AlignedBytes<SIZE>>) -> &mut T {
        // Debug-time alignment check: ensure the stored T would be properly aligned for mutable reference creation.
        debug_assert!(
            std::mem::align_of::<T>() <= std::mem::align_of::<AlignedBytes<SIZE>>(),
            "alignment of T exceeds alignment of Thing storage; T should have been boxed"
        );

        let ptr_to_t = std::ptr::from_mut::<AlignedBytes<SIZE>>(data.get_mut())
            .cast::<u8>()
            .cast::<T>();
        unsafe { &mut *ptr_to_t }
    }
}

impl<const SIZE: usize, T> std::fmt::Debug for Convert<SIZE, T> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = std::any::type_name::<T>();
        let bytes = unsafe { &*(self.bytes.get().cast_const()) };
        write!(f, "{name}: {bytes:?}")
    }
}

#[cfg(test)]
mod tests {
    use crate::Thing;

    mod predicates {
        use super::Thing;

        #[test]
        fn size_requirement_unboxed_returns_size_for_normal_types() {
            assert_eq!(Thing::<1>::size_requirement_unboxed::<u8>(), Some(1));
            assert_eq!(Thing::<24>::size_requirement_unboxed::<u8>(), Some(1));
        }

        #[test]
        fn size_requirement_unboxed_returns_none_for_high_alignment() {
            #[repr(align(16))]
            struct A16(#[allow(dead_code)] u8);
            assert_eq!(Thing::<24>::size_requirement_unboxed::<A16>(), None);
        }

        #[test]
        fn size_requirement_returns_box_size_for_high_alignment() {
            #[repr(align(16))]
            struct A16(#[allow(dead_code)] u8);
            assert_eq!(
                Thing::<24>::size_requirement::<A16>(),
                std::mem::size_of::<Box<A16>>()
            );
        }

        #[test]
        fn size_requirement_returns_type_size_for_normal_types() {
            assert_eq!(Thing::<24>::size_requirement::<u8>(), 1);
            assert_eq!(Thing::<24>::size_requirement::<u64>(), 8);
        }

        #[test]
        fn boxed_true_when_type_too_large_for_slot() {
            assert!(Thing::<1>::boxed::<u32>());
        }

        #[test]
        fn boxed_false_when_type_fits_in_slot() {
            assert!(!Thing::<24>::boxed::<u64>());
        }

        #[test]
        fn boxed_true_for_high_alignment_type() {
            #[repr(align(16))]
            struct A(#[allow(dead_code)] u8);
            assert!(Thing::<24>::boxed::<A>());
        }

        #[test]
        fn fitting_true_when_type_fits() {
            assert!(Thing::<8>::fitting::<u64>());
        }

        #[test]
        fn fitting_false_when_slot_too_small() {
            assert!(!Thing::<1>::fitting::<u64>());
        }
    }

    mod unboxed {
        use super::Thing;

        #[test]
        fn get_roundtrip() {
            assert_eq!(Thing::<24>::new(1u8).get::<u8>(), 1u8);
            assert_eq!(Thing::<24>::new(2u16).get::<u16>(), 2u16);
            assert_eq!(Thing::<24>::new(3u32).get::<u32>(), 3u32);
            let t = Thing::<24>::new((10u64, 20u64, 30u64));
            assert_eq!(t.get::<(u64, u64, u64)>(), (10u64, 20u64, 30u64));
        }

        #[test]
        fn get_ref_then_get_mut_then_get() {
            let mut t: Thing<24> = Thing::new(10usize);
            assert_eq!(*t.get_ref::<usize>(), 10usize);
            *t.get_mut::<usize>() = 20usize;
            assert_eq!(t.get::<usize>(), 20usize);
        }

        #[test]
        fn zst_roundtrip() {
            struct Z;
            let t: Thing<1> = Thing::new(Z);
            let _z: Z = t.get::<Z>();
        }

        #[test]
        fn exact_size_slot() {
            let arr: Thing<8> = Thing::new([7u8; 8]);
            assert_eq!(arr.get::<[u8; 8]>(), [7u8; 8]);
        }

        #[test]
        fn string_ownership_roundtrip() {
            let t: Thing<24> = Thing::new(String::from("owned"));
            assert_eq!(t.get::<String>(), "owned");
        }

        #[test]
        fn vec_roundtrip() {
            let t: Thing<24> = Thing::new(vec![1u8, 2, 3]);
            assert_eq!(t.get::<Vec<u8>>(), vec![1u8, 2, 3]);
        }

        #[test]
        fn get_ref_with_interior_mutability() {
            use std::sync::RwLock;
            struct Inner {
                lock: RwLock<u32>,
            }
            let t: Thing<24> = Thing::new(Inner {
                lock: RwLock::new(99),
            });
            assert_eq!(*t.get_ref::<Inner>().lock.read().unwrap(), 99);
        }

        #[test]
        fn get_panics_on_type_mismatch() {
            let result = std::panic::catch_unwind(|| {
                let t: Thing<24> = Thing::new(1u32);
                let _ = t.get::<u64>();
            });
            assert!(result.is_err());
        }

        #[test]
        fn get_ref_panics_on_type_mismatch() {
            let result = std::panic::catch_unwind(|| {
                let t: Thing<24> = Thing::new(1u32);
                let _ = t.get_ref::<u64>();
            });
            assert!(result.is_err());
        }

        #[test]
        fn get_mut_panics_on_type_mismatch() {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut t: Thing<24> = Thing::new(1u32);
                let _ = t.get_mut::<u64>();
            }));
            assert!(result.is_err());
        }
    }

    mod boxed {
        use super::Thing;

        #[test]
        fn get_roundtrip_size_forced() {
            let big = (1usize, 2usize, 3usize, 4usize);
            let thing: Thing<8> = Thing::new(big);
            assert_eq!(thing.get::<(usize, usize, usize, usize)>().2, 3usize);
        }

        #[test]
        fn get_roundtrip_alignment_forced() {
            #[repr(align(16))]
            struct A16(u8);
            assert!(Thing::<24>::boxed::<A16>());
            let val = Thing::<32>::new(A16(5)).get::<A16>();
            assert_eq!(val.0, 5u8);
        }

        #[test]
        fn six_usize_tuple_roundtrip() {
            let big = (0usize, 1usize, 2usize, 3usize, 4usize, 5usize);
            let out = Thing::<8>::new(big).get::<(usize, usize, usize, usize, usize, usize)>();
            assert_eq!(out.0, 0usize);
        }
    }

    mod try_get {
        use super::Thing;

        #[test]
        fn unboxed_success() {
            assert_eq!(Thing::<24>::new(99u32).try_get::<u32>(), Some(99u32));
        }

        #[test]
        fn unboxed_mismatch_returns_none() {
            assert!(Thing::<24>::new(55u64).try_get::<u32>().is_none());
        }

        #[test]
        fn boxed_success() {
            #[repr(align(16))]
            #[derive(Debug, PartialEq)]
            struct A16(u32);
            assert_eq!(Thing::<32>::new(A16(77)).try_get::<A16>(), Some(A16(77)));
        }
    }

    mod try_get_ref {
        use super::Thing;

        #[test]
        fn unboxed_success() {
            let t: Thing<24> = Thing::new(100u32);
            assert_eq!(t.try_get_ref::<u32>(), Some(&100u32));
        }

        #[test]
        fn unboxed_mismatch_returns_none() {
            assert!(Thing::<24>::new(55u64).try_get_ref::<u32>().is_none());
        }

        #[test]
        fn boxed_success() {
            #[repr(align(16))]
            struct A16(u32);
            let t: Thing<32> = Thing::new(A16(88));
            assert_eq!(t.try_get_ref::<A16>().unwrap().0, 88);
        }
    }

    mod try_get_mut {
        use super::Thing;

        #[test]
        fn unboxed_success_and_mutation() {
            let mut t: Thing<24> = Thing::new(42u32);
            *t.try_get_mut::<u32>().unwrap() = 99;
            assert_eq!(t.get_ref::<u32>(), &99u32);
        }

        #[test]
        fn unboxed_mismatch_returns_none() {
            let mut t: Thing<24> = Thing::new(66u32);
            assert!(t.try_get_mut::<u64>().is_none());
        }

        #[test]
        fn boxed_success_and_mutation() {
            #[repr(align(16))]
            struct A16(u32);
            let mut t: Thing<32> = Thing::new(A16(99));
            t.try_get_mut::<A16>().unwrap().0 = 100;
            assert_eq!(t.get_ref::<A16>().0, 100);
        }
    }

    mod drop_glue {
        use super::Thing;
        use std::sync::atomic::{AtomicUsize, Ordering};

        static DROPS: AtomicUsize = AtomicUsize::new(0);

        struct CountDrop;
        impl Drop for CountDrop {
            fn drop(&mut self) {
                DROPS.fetch_add(1, Ordering::SeqCst);
            }
        }

        #[test]
        fn unboxed_drop_runs_once() {
            DROPS.store(0, Ordering::SeqCst);
            drop(Thing::<32>::new(CountDrop));
            assert_eq!(DROPS.load(Ordering::SeqCst), 1);
        }

        #[test]
        fn boxed_drop_runs() {
            #[repr(align(16))]
            struct AlignDrop(CountDrop);

            DROPS.store(0, Ordering::SeqCst);
            drop(Thing::<32>::new(AlignDrop(CountDrop)));
            assert!(DROPS.load(Ordering::SeqCst) >= 1);
        }
    }

    mod debug {
        use super::Thing;

        #[test]
        fn thing_debug_is_non_empty() {
            let t: Thing<24> = Thing::new(42u32);
            assert!(!format!("{t:?}").is_empty());
        }
    }
}
