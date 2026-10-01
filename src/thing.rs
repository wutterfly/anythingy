//! A type-erased value that stores small values inline.
//!
//! See [`Thing`].

use crate::heap_size::HeapSize;
use alloc::boxed::Box;
use core::{
    any::TypeId,
    cell::UnsafeCell,
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
};

/// Default size of [`Thing`].
/// Chosen to be 3x `size_of::<usize>()`, to facilitate `Vec`/`String` without boxing them, to prevent double pointers.
pub const DEFAULT_THING_SIZE: usize = core::mem::size_of::<usize>() * 3;

/// A structure for storing type-erased values. Similar to [`Box<dyn Any>`][core::any::Any] it can store values of any type.
///
/// What makes this structure special is that the `SIZE` of Thing can be specified.
/// For values of type `T`, where size of `T` is smaller than or equal to `SIZE`, no additional allocation is needed.
///
/// For types `T` that are greater than `SIZE`, the value gets boxed.
///
/// For types `T` which alignment is greater than 8, the value gets also boxed.
///
/// # Send / Sync
///
/// A `Thing` is neither `Send` nor `Sync`, because it can hold any type,
/// including ones that are not thread-safe. To move or share type-erased
/// values between threads, use [`SThing`](crate::SThing), which can only be
/// created from `Send + Sync` values.
///
/// ```compile_fail,E0277
/// fn assert_send<T: Send>() {}
/// assert_send::<anythingy::Thing<24>>();
/// ```
///
/// ```compile_fail,E0277
/// fn assert_sync<T: Sync>() {}
/// assert_sync::<anythingy::Thing<24>>();
/// ```
///
/// # Unchecked access
/// [`get`](Self::get), [`get_ref`](Self::get_ref) and [`get_mut`](Self::get_mut)
/// check the type first and panic on a mismatch; the `try_` variants return
/// `None`. If the type is already known, the `unsafe` [`get_unchecked`](Self::get_unchecked),
/// [`get_ref_unchecked`](Self::get_ref_unchecked) and
/// [`get_mut_unchecked`](Self::get_mut_unchecked) skip the check, like the
/// `downcast_unchecked` methods on `dyn Any`. A wrong type is undefined behavior.
///
// Implementation notes:
// - The internals write `T` into a byte buffer and later read it back. The code ensures that types with
//   alignment > 8 are boxed, and `Thing` is repr(align(8)), so alignment requirements for unboxed values are satisfied.
// - Conversions are performed with explicit `ptr::write` / `ptr::read` into a `MaybeUninit<[u8; SIZE]>` backing buffer,
//   avoiding reading inactive union fields.
#[derive(Debug)]
#[repr(align(8))]
pub struct Thing<const SIZE: usize = DEFAULT_THING_SIZE> {
    id: TypeId,
    raw: RawThing<SIZE>,
}

/// The storage of a [`Thing`] without its `TypeId`: a type-erased value and
/// the one function that knows how to handle it (see [`Op`]).
///
/// It cannot check types, so all of its accessors are `unsafe`: the caller
/// has to know the type. This is what a container that already tracks the
/// type elsewhere (like `ThingMap`, whose key is the `TypeId`) stores, so it
/// does not pay for a second copy of the id.
///
/// In debug builds it also remembers the `TypeId`, so the unchecked accessors
/// can assert that the caller's claim is right. Release builds do not have
/// that field, so a `RawThing` is 16 bytes smaller than a `Thing` there.
#[derive(Debug)]
#[repr(align(8))]
pub(crate) struct RawThing<const SIZE: usize> {
    glue: Glue<SIZE>,
    data: UnsafeCell<AlignedBytes<SIZE>>,
    #[cfg(debug_assertions)]
    debug_id: TypeId,
    _not_send_sync: PhantomData<*const ()>,
}

#[derive(Debug)]
#[repr(align(8))]
struct AlignedBytes<const SIZE: usize>([MaybeUninit<u8>; SIZE]);

/// What a [`RawThing`]'s function is asked to do with the value it belongs to.
///
/// A single function pointer serves every operation, so that the storage
/// stays one pointer plus the data, and a call is a plain indirect call, with
/// no table to look through.
#[derive(Debug, Clone, Copy)]
enum Op {
    /// Drops the value in place. The buffer must not be used afterwards.
    Drop,
    /// Returns the bytes the value has on the heap. Touches nothing.
    HeapSize,
}

/// The function stored in a [`RawThing`], made for one type `T`.
///
/// # Safety
/// The pointer must point at the buffer of the `RawThing` that the function
/// was made for, which holds a value of that type.
type Glue<const SIZE: usize> = unsafe fn(*mut AlignedBytes<SIZE>, Op) -> usize;

impl<const SIZE: usize> Thing<SIZE> {
    /// Creates a new `Thing` from generic type `T`. Uses the boxed value, if size of `T` is bigger than `SIZE`.
    ///
    /// If the alignment of type `T` is greater than 8, `T` gets also boxed.
    ///
    /// # Panics
    /// Panics, if size of `T` is greater than `SIZE`, but `SIZE` is smaller than size of `Box<T>`.
    #[inline]
    #[must_use]
    pub fn new<T: 'static>(t: T) -> Self {
        Self {
            id: TypeId::of::<T>(),
            raw: RawThing::new(t),
        }
    }

    /// Returns the original type of `Thing`, if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    #[inline]
    #[must_use]
    pub fn get<T: 'static>(self) -> T {
        // check that types are matching
        assert!(self.is_type::<T>());

        // SAFETY: the type was just checked.
        unsafe { self.get_unchecked() }
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

        // SAFETY: the type was just checked.
        unsafe { self.get_ref_unchecked() }
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

        // SAFETY: the type was just checked.
        unsafe { self.get_mut_unchecked() }
    }

    /// Returns the original type of `Thing`, if given type and original type match.
    /// Returns `None`, if types don't match.
    #[inline]
    #[must_use]
    pub fn try_get<T: 'static>(self) -> Option<T> {
        // check that types are matching
        if !self.is_type::<T>() {
            return None;
        }

        // SAFETY: the type was just checked.
        Some(unsafe { self.get_unchecked() })
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

        // SAFETY: the type was just checked.
        Some(unsafe { self.get_ref_unchecked() })
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

        // SAFETY: the type was just checked.
        Some(unsafe { self.get_mut_unchecked() })
    }

    /// Returns the original value without checking that `T` is its type.
    ///
    /// The unchecked counterpart of [`get`](Self::get), like the
    /// `downcast_unchecked` methods on `dyn Any`: it skips the type check, so
    /// it is a little faster and never panics.
    ///
    /// # Safety
    ///
    /// `T` must be exactly the type this `Thing` was created with, that is
    /// [`is_type::<T>()`](Self::is_type) must be `true`. Otherwise the stored
    /// bytes are reinterpreted as a `T`, which is undefined behavior.
    ///
    /// Debug builds assert the type and panic on a mismatch instead of
    /// proceeding, but release builds do not check.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::Thing;
    ///
    /// let thing = Thing::<24>::new(String::from("hello"));
    /// // The caller knows this is a `String`.
    /// let text: String = unsafe { thing.get_unchecked() };
    /// assert_eq!(text, "hello");
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn get_unchecked<T: 'static>(self) -> T {
        debug_assert!(
            self.is_type::<T>(),
            "get_unchecked called with a type that does not match the stored one"
        );

        // SAFETY: the caller guarantees that `T` is the stored type.
        unsafe { self.raw.get_unchecked::<T>() }
    }

    /// Returns a reference to the original value without checking that `T` is
    /// its type.
    ///
    /// The unchecked counterpart of [`get_ref`](Self::get_ref), like
    /// `downcast_ref_unchecked` on `dyn Any`.
    ///
    /// # Safety
    ///
    /// `T` must be exactly the type this `Thing` was created with, that is
    /// [`is_type::<T>()`](Self::is_type) must be `true`. Otherwise the stored
    /// bytes are reinterpreted as a `T`, which is undefined behavior.
    ///
    /// Debug builds assert the type and panic on a mismatch instead of
    /// proceeding, but release builds do not check.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::Thing;
    ///
    /// let thing = Thing::<24>::new(42u32);
    /// let value: &u32 = unsafe { thing.get_ref_unchecked() };
    /// assert_eq!(*value, 42);
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn get_ref_unchecked<T: 'static>(&self) -> &T {
        debug_assert!(
            self.is_type::<T>(),
            "get_ref_unchecked called with a type that does not match the stored one"
        );

        // SAFETY: the caller guarantees that `T` is the stored type.
        unsafe { self.raw.get_ref_unchecked::<T>() }
    }

    /// Returns a mutable reference to the original value without checking
    /// that `T` is its type.
    ///
    /// The unchecked counterpart of [`get_mut`](Self::get_mut), like
    /// `downcast_mut_unchecked` on `dyn Any`.
    ///
    /// # Safety
    ///
    /// `T` must be exactly the type this `Thing` was created with, that is
    /// [`is_type::<T>()`](Self::is_type) must be `true`. Otherwise the stored
    /// bytes are reinterpreted as a `T`, which is undefined behavior.
    ///
    /// Debug builds assert the type and panic on a mismatch instead of
    /// proceeding, but release builds do not check.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::Thing;
    ///
    /// let mut thing = Thing::<24>::new(vec![1, 2]);
    /// unsafe { thing.get_mut_unchecked::<Vec<i32>>() }.push(3);
    /// assert_eq!(thing.get_ref::<Vec<i32>>(), &[1, 2, 3]);
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn get_mut_unchecked<T: 'static>(&mut self) -> &mut T {
        debug_assert!(
            self.is_type::<T>(),
            "get_mut_unchecked called with a type that does not match the stored one"
        );

        // SAFETY: the caller guarantees that `T` is the stored type.
        unsafe { self.raw.get_mut_unchecked::<T>() }
    }

    /// Returns true, if erased type is equal to given type.
    #[inline]
    #[must_use]
    pub fn is_type<T: 'static>(&self) -> bool {
        self.id == TypeId::of::<T>()
    }

    /// Returns true, if `T` can be made into a `Thing`.
    ///
    /// Returns false, if `SIZE` is smaller than a needed `Box<T>`.
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
        let size = core::mem::size_of::<T>();
        let boxed = core::mem::size_of::<Box<T>>();
        let align = core::mem::align_of::<T>();

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
        let size = core::mem::size_of::<T>();
        let align = core::mem::align_of::<T>();

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
}

impl<const SIZE: usize> RawThing<SIZE> {
    /// Creates the storage for `t`. Uses a boxed value if `T` is bigger than
    /// `SIZE` or over-aligned; see [`Thing::new`].
    ///
    /// # Panics
    /// Panics, if size of `T` is greater than `SIZE`, but `SIZE` is smaller than size of `Box<T>`.
    #[inline]
    pub(crate) fn new<T: 'static>(t: T) -> Self {
        if Thing::<SIZE>::boxed::<T>() {
            // check that the storage can hold at least a Box.
            assert!(
                Thing::<SIZE>::fitting::<Box<T>>(),
                "Thing<SIZE> too small to hold Box<T>"
            );

            // convert type from bytes (Box<T>)
            let convert = Convert::new(Box::new(t));

            // convert type to bytes
            let data = convert.bytes();

            return Self::from_parts(Self::glue::<T>, data, TypeId::of::<T>());
        }

        // convert type from bytes (T)
        let convert = Convert::new(t);

        // convert type to bytes
        let data = convert.bytes();

        // Values that are stored inline and need no drop have nothing to do,
        // and nothing on the heap, so they share one function that does
        // nothing.
        let glue = if core::mem::needs_drop::<T>() {
            Self::glue::<T>
        } else {
            Self::empty_glue
        };

        Self::from_parts(glue, data, TypeId::of::<T>())
    }

    #[inline]
    #[cfg_attr(not(debug_assertions), allow(unused_variables))]
    fn from_parts(glue: Glue<SIZE>, data: UnsafeCell<AlignedBytes<SIZE>>, id: TypeId) -> Self {
        Self {
            glue,
            data,
            #[cfg(debug_assertions)]
            debug_id: id,
            _not_send_sync: PhantomData,
        }
    }

    /// In debug builds, asserts that the stored value is a `T`.
    #[inline]
    fn debug_check<T: 'static>(&self) {
        #[cfg(debug_assertions)]
        assert!(
            self.debug_id == TypeId::of::<T>(),
            "RawThing accessed with a type that does not match the stored one"
        );
    }

    /// Returns the stored value.
    ///
    /// # Safety
    /// `T` must be exactly the type this storage was created with.
    #[inline]
    pub(crate) unsafe fn get_unchecked<T: 'static>(mut self) -> T {
        self.debug_check::<T>();

        // Prevent double-drop: mark the glue as empty; we'll move the data out ourselves.
        self.glue = Self::empty_glue;

        // SAFETY: the buffer is moved out exactly once, and `glue` was just
        // replaced by one that does nothing, so nothing reads or drops it again.
        let data = unsafe { self.move_data_uninit() };

        if Thing::<SIZE>::boxed::<T>() {
            // convert type from bytes
            let convert = Convert::<SIZE, Box<T>>::from_bytes(data);

            // move value out of box
            return *convert.get();
        }

        // convert type from bytes
        let convert = Convert::<SIZE, T>::from_bytes(data);

        convert.get()
    }

    /// Returns a reference to the stored value.
    ///
    /// # Safety
    /// `T` must be exactly the type this storage was created with.
    #[inline]
    pub(crate) unsafe fn get_ref_unchecked<T: 'static>(&self) -> &T {
        self.debug_check::<T>();

        if Thing::<SIZE>::boxed::<T>() {
            // For boxed case the stored value is a `Box<T>`; get_ref returns &Box<T> then `.as_ref()` to get &T.
            return Convert::<SIZE, Box<T>>::get_ref(&self.data).as_ref();
        }

        Convert::<SIZE, T>::get_ref(&self.data)
    }

    /// Returns a mutable reference to the stored value.
    ///
    /// # Safety
    /// `T` must be exactly the type this storage was created with.
    #[inline]
    pub(crate) unsafe fn get_mut_unchecked<T: 'static>(&mut self) -> &mut T {
        self.debug_check::<T>();

        if Thing::<SIZE>::boxed::<T>() {
            return Convert::<SIZE, Box<T>>::get_mut(&mut self.data).as_mut();
        }

        Convert::<SIZE, T>::get_mut(&mut self.data)
    }

    /// This is unsafe, because it leaves self.data in an invalid state,
    const unsafe fn move_data_uninit(&mut self) -> UnsafeCell<AlignedBytes<SIZE>> {
        let fill = UnsafeCell::new(AlignedBytes([MaybeUninit::<u8>::uninit(); SIZE]));

        core::mem::replace(&mut self.data, fill)
    }

    /// The function for a value of type `T` that is stored in a `RawThing`.
    ///
    /// # Safety
    /// See [`Glue`]. `Op::Drop` additionally leaves the buffer logically
    /// moved out: it must not be dropped or read again.
    #[inline]
    unsafe fn glue<T: 'static>(data: *mut AlignedBytes<SIZE>, op: Op) -> usize {
        let boxed = Thing::<SIZE>::boxed::<T>();

        match op {
            // A boxed value's allocation is the size of the value. What the
            // value itself owns is not known here.
            Op::HeapSize => {
                if boxed {
                    core::mem::size_of::<T>()
                } else {
                    0
                }
            }
            Op::Drop => {
                if boxed {
                    // SAFETY: the buffer holds the `Box<T>` that `new` wrote
                    // there, which is moved out exactly once and dropped.
                    drop(unsafe { core::ptr::read(data.cast::<Box<T>>()) });
                } else {
                    // Sanity check: if the type would be stored unboxed, its alignment must fit into our buffer.
                    // If this fails in debug builds it indicates a mismatch between `boxed::<T>()` and actual alignment.
                    debug_assert!(
                        core::mem::align_of::<T>() <= core::mem::align_of::<AlignedBytes<SIZE>>(),
                        "alignment of T exceeds alignment of Thing storage; T should have been boxed"
                    );

                    // SAFETY: the buffer holds the `T` that `new` wrote there,
                    // which is dropped in place exactly once.
                    unsafe { core::ptr::drop_in_place(data.cast::<T>()) };
                }
                0
            }
        }
    }

    /// The function for values that are stored inline and need no drop.
    ///
    /// # Safety
    /// Always safe to call, it does not touch the buffer.
    #[inline]
    const unsafe fn empty_glue(_: *mut AlignedBytes<SIZE>, _: Op) -> usize {
        0
    }

    /// Returns the bytes that the value has allocated on the heap: the size of
    /// the value if it is boxed, and `0` if it is stored inline. What the
    /// value owns itself is not included.
    #[inline]
    pub(crate) fn heap_size(&self) -> usize {
        // SAFETY: `glue` was made for the value in `data`. `HeapSize` reads
        // nothing from the buffer, so the pointer from the `UnsafeCell` is
        // enough, and `&self` is not violated.
        unsafe { (self.glue)(self.data.get(), Op::HeapSize) }
    }
}

impl<const SIZE: usize> core::ops::Drop for RawThing<SIZE> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: `glue` was made for the value in `data`, and the buffer is
        // never used again after this.
        unsafe { (self.glue)(core::ptr::from_mut(self.data.get_mut()), Op::Drop) };
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
            core::mem::align_of::<T>() <= core::mem::align_of::<AlignedBytes<SIZE>>(),
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
            core::ptr::write(ptr_to_t, value);
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
            core::mem::align_of::<T>() <= core::mem::align_of::<AlignedBytes<SIZE>>(),
            "get: alignment of T ({}) exceeds buffer alignment ({}); T should have been boxed",
            core::mem::align_of::<T>(),
            core::mem::align_of::<AlignedBytes<SIZE>>()
        );

        // Use aligned read now that we assert alignment in debug; this is potentially faster on some targets.
        unsafe { core::ptr::read(ptr_to_t.cast_const()) }
    }

    #[inline]
    fn get_ref(data: &UnsafeCell<AlignedBytes<SIZE>>) -> &T {
        // Debug-time alignment check: ensure the stored T would be properly aligned for reference creation.
        debug_assert!(
            core::mem::align_of::<T>() <= core::mem::align_of::<AlignedBytes<SIZE>>(),
            "alignment of T exceeds alignment of Thing storage; T should have been boxed"
        );

        let ptr_to_t = data.get().cast_const().cast::<u8>().cast::<T>();
        unsafe { &*ptr_to_t }
    }

    #[inline]
    fn get_mut(data: &mut UnsafeCell<AlignedBytes<SIZE>>) -> &mut T {
        // Debug-time alignment check: ensure the stored T would be properly aligned for mutable reference creation.
        debug_assert!(
            core::mem::align_of::<T>() <= core::mem::align_of::<AlignedBytes<SIZE>>(),
            "alignment of T exceeds alignment of Thing storage; T should have been boxed"
        );

        let ptr_to_t = core::ptr::from_mut::<AlignedBytes<SIZE>>(data.get_mut())
            .cast::<u8>()
            .cast::<T>();
        unsafe { &mut *ptr_to_t }
    }
}

impl<const SIZE: usize, T> core::fmt::Debug for Convert<SIZE, T> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let name = core::any::type_name::<T>();
        let bytes = unsafe { &*(self.bytes.get().cast_const()) };
        write!(f, "{name}: {bytes:?}")
    }
}

/// Reports the allocation of a value that is too big for `SIZE`, or over-aligned,
/// and is boxed. A value that is stored inline has nothing on the heap, so this
/// is `0`.
///
/// What the value owns is not included, since a `Thing` does not know its type:
/// a `String` stored in a `Thing` reports `0`, not the length of its text.
impl<const SIZE: usize> HeapSize for Thing<SIZE> {
    #[inline]
    fn heap_size(&self) -> usize {
        self.raw.heap_size()
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

        // Each test has its own counter and its own type that increments it:
        // tests run in parallel, so they must not share one.
        static UNBOXED_DROPS: AtomicUsize = AtomicUsize::new(0);
        static BOXED_DROPS: AtomicUsize = AtomicUsize::new(0);

        struct UnboxedCountDrop;
        impl Drop for UnboxedCountDrop {
            fn drop(&mut self) {
                UNBOXED_DROPS.fetch_add(1, Ordering::SeqCst);
            }
        }

        #[repr(align(16))]
        struct BoxedCountDrop;
        impl Drop for BoxedCountDrop {
            fn drop(&mut self) {
                BOXED_DROPS.fetch_add(1, Ordering::SeqCst);
            }
        }

        #[test]
        fn unboxed_drop_runs_once() {
            drop(Thing::<32>::new(UnboxedCountDrop));
            assert_eq!(UNBOXED_DROPS.load(Ordering::SeqCst), 1);
        }

        #[test]
        fn boxed_drop_runs_once() {
            // Alignment above 8, so it is boxed.
            assert!(Thing::<32>::boxed::<BoxedCountDrop>());
            drop(Thing::<32>::new(BoxedCountDrop));
            assert_eq!(BOXED_DROPS.load(Ordering::SeqCst), 1);
        }
    }

    mod unchecked {
        use super::Thing;
        use std::rc::Rc;

        #[repr(align(16))]
        #[derive(Debug, PartialEq)]
        struct Aligned(u32);

        #[test]
        fn get_unchecked_round_trips_inline_and_boxed_values() {
            // SAFETY (all `unsafe` below): the type argument always matches
            // the type the `Thing` was created with.
            let inline: Thing<24> = Thing::new(String::from("inline"));
            assert_eq!(unsafe { inline.get_unchecked::<String>() }, "inline");

            let big: Thing<24> = Thing::new([7u64; 16]); // too large: boxed
            assert!(Thing::<24>::boxed::<[u64; 16]>());
            assert_eq!(unsafe { big.get_unchecked::<[u64; 16]>() }, [7u64; 16]);

            let aligned: Thing<32> = Thing::new(Aligned(5)); // alignment above 8: boxed
            assert!(Thing::<32>::boxed::<Aligned>());
            assert_eq!(unsafe { aligned.get_unchecked::<Aligned>() }, Aligned(5));

            let small: Thing<8> = Thing::new(3u8);
            assert_eq!(unsafe { small.get_unchecked::<u8>() }, 3);

            let zst: Thing<0> = Thing::new(());
            let () = unsafe { zst.get_unchecked::<()>() };
        }

        #[test]
        fn get_ref_and_mut_unchecked_see_and_change_the_same_value() {
            let mut inline: Thing<24> = Thing::new(vec![1, 2]);
            let mut boxed: Thing<8> = Thing::new(vec![1, 2]); // Vec is 24 bytes: boxed
            assert!(Thing::<8>::boxed::<Vec<i32>>());

            unsafe {
                inline.get_mut_unchecked::<Vec<i32>>().push(3);
                boxed.get_mut_unchecked::<Vec<i32>>().push(3);
                assert_eq!(inline.get_ref_unchecked::<Vec<i32>>(), &[1, 2, 3]);
                assert_eq!(boxed.get_ref_unchecked::<Vec<i32>>(), &[1, 2, 3]);
            }
            // The checked accessors agree.
            assert_eq!(inline.get_ref::<Vec<i32>>(), &[1, 2, 3]);
            assert_eq!(boxed.get_ref::<Vec<i32>>(), &[1, 2, 3]);
        }

        #[test]
        fn unchecked_accessors_match_the_checked_ones() {
            let thing: Thing<24> = Thing::new(42u64);
            let checked = *thing.get_ref::<u64>();
            let unchecked = unsafe { *thing.get_ref_unchecked::<u64>() };
            assert_eq!(checked, unchecked);
            assert_eq!(unsafe { thing.get_unchecked::<u64>() }, 42);
        }

        #[test]
        fn get_unchecked_moves_ownership_without_double_drop() {
            let token = Rc::new(());

            // Inline: an `Rc` is 8 bytes, which fits in `Thing<24>`.
            let thing: Thing<24> = Thing::new(Rc::clone(&token));
            let value = unsafe { thing.get_unchecked::<Rc<()>>() };
            assert_eq!(Rc::strong_count(&token), 2);
            drop(value);
            assert_eq!(Rc::strong_count(&token), 1);

            // Boxed: 16 bytes do not fit in `Thing<8>`.
            assert!(Thing::<8>::boxed::<(Rc<()>, u64)>());
            let thing: Thing<8> = Thing::new((Rc::clone(&token), 9u64));
            let value = unsafe { thing.get_unchecked::<(Rc<()>, u64)>() };
            assert_eq!(Rc::strong_count(&token), 2);
            drop(value);
            assert_eq!(Rc::strong_count(&token), 1);
        }

        #[test]
        fn unchecked_reads_leave_the_thing_droppable_exactly_once() {
            let token = Rc::new(());
            let thing: Thing<24> = Thing::new(Rc::clone(&token));
            let peek = unsafe { thing.get_ref_unchecked::<Rc<()>>() };
            assert_eq!(Rc::strong_count(peek), 2);
            drop(thing);
            assert_eq!(Rc::strong_count(&token), 1);
        }

        #[test]
        #[cfg(debug_assertions)]
        #[should_panic(expected = "does not match")]
        fn debug_builds_catch_a_wrong_type_in_get_unchecked() {
            let thing: Thing<24> = Thing::new(1u32);
            // Deliberately wrong. Debug builds panic before touching the
            // data; this is never done in release builds.
            let _ = unsafe { thing.get_unchecked::<String>() };
        }

        #[test]
        #[cfg(debug_assertions)]
        #[should_panic(expected = "does not match")]
        fn debug_builds_catch_a_wrong_type_in_get_ref_unchecked() {
            let thing: Thing<24> = Thing::new(1u32);
            let _ = unsafe { thing.get_ref_unchecked::<u64>() };
        }

        #[test]
        #[cfg(debug_assertions)]
        #[should_panic(expected = "does not match")]
        fn debug_builds_catch_a_wrong_type_in_get_mut_unchecked() {
            let mut thing: Thing<24> = Thing::new(1u32);
            let _ = unsafe { thing.get_mut_unchecked::<i32>() };
        }
    }

    mod raw {
        use crate::thing::RawThing;
        use core::any::TypeId;
        use std::rc::Rc;

        #[repr(align(16))]
        #[derive(Debug, PartialEq)]
        struct Aligned(u32);

        #[test]
        #[cfg(not(debug_assertions))]
        fn a_raw_thing_is_16_bytes_smaller_than_a_thing_in_release_builds() {
            use crate::thing::Thing;

            assert_eq!(core::mem::size_of::<RawThing<24>>(), 32);
            assert_eq!(core::mem::size_of::<Thing<24>>(), 48);
            assert_eq!(core::mem::size_of::<RawThing<8>>(), 16);
            assert_eq!(core::mem::size_of::<Thing<8>>(), 32);
            // What a `ThingMap` entry holds.
            assert_eq!(core::mem::size_of::<(TypeId, RawThing<24>)>(), 48);
            assert_eq!(core::mem::size_of::<(TypeId, Thing<24>)>(), 64);
        }

        #[test]
        #[cfg(debug_assertions)]
        fn debug_builds_keep_the_type_id_to_check_the_accessors() {
            assert_eq!(
                core::mem::size_of::<RawThing<24>>(),
                32 + core::mem::size_of::<TypeId>()
            );
        }

        #[test]
        fn round_trips_inline_boxed_and_zero_sized_values() {
            // SAFETY (all `unsafe` below): the type argument always matches
            // the type the storage was created with.
            let inline = RawThing::<24>::new(String::from("inline"));
            assert_eq!(unsafe { inline.get_unchecked::<String>() }, "inline");

            let boxed = RawThing::<24>::new([7u64; 16]);
            assert_eq!(unsafe { boxed.get_unchecked::<[u64; 16]>() }, [7u64; 16]);

            let aligned = RawThing::<32>::new(Aligned(5)); // alignment above 8: boxed
            assert_eq!(unsafe { aligned.get_unchecked::<Aligned>() }, Aligned(5));

            let zst = RawThing::<0>::new(());
            let () = unsafe { zst.get_unchecked::<()>() };
        }

        #[test]
        fn references_read_and_change_the_stored_value() {
            for boxed in [false, true] {
                if boxed {
                    let mut raw = RawThing::<8>::new(vec![1, 2]); // 24 bytes: boxed
                    unsafe { raw.get_mut_unchecked::<Vec<i32>>().push(3) };
                    assert_eq!(unsafe { raw.get_ref_unchecked::<Vec<i32>>() }, &[1, 2, 3]);
                } else {
                    let mut raw = RawThing::<24>::new(vec![1, 2]);
                    unsafe { raw.get_mut_unchecked::<Vec<i32>>().push(3) };
                    assert_eq!(unsafe { raw.get_ref_unchecked::<Vec<i32>>() }, &[1, 2, 3]);
                }
            }
        }

        #[test]
        fn dropping_and_taking_drop_the_value_exactly_once() {
            let token = Rc::new(());
            for size_is_small in [false, true] {
                // Dropped without ever being read.
                if size_is_small {
                    drop(RawThing::<8>::new((Rc::clone(&token), 0u64))); // boxed
                } else {
                    drop(RawThing::<24>::new(Rc::clone(&token)));
                }
                assert_eq!(Rc::strong_count(&token), 1);

                // Moved out, then dropped by the caller.
                let value = if size_is_small {
                    let raw = RawThing::<8>::new((Rc::clone(&token), 0u64));
                    let (rc, _) = unsafe { raw.get_unchecked::<(Rc<()>, u64)>() };
                    rc
                } else {
                    let raw = RawThing::<24>::new(Rc::clone(&token));
                    unsafe { raw.get_unchecked::<Rc<()>>() }
                };
                assert_eq!(Rc::strong_count(&token), 2);
                drop(value);
                assert_eq!(Rc::strong_count(&token), 1);
            }
        }

        #[test]
        #[cfg(debug_assertions)]
        #[should_panic(expected = "does not match")]
        fn debug_builds_catch_a_wrong_type_in_get_unchecked() {
            let raw = RawThing::<24>::new(1u32);
            let _ = unsafe { raw.get_unchecked::<String>() };
        }

        #[test]
        #[cfg(debug_assertions)]
        #[should_panic(expected = "does not match")]
        fn debug_builds_catch_a_wrong_type_in_get_ref_unchecked() {
            let raw = RawThing::<24>::new(1u32);
            let _ = unsafe { raw.get_ref_unchecked::<u64>() };
        }

        #[test]
        #[cfg(debug_assertions)]
        #[should_panic(expected = "does not match")]
        fn debug_builds_catch_a_wrong_type_in_get_mut_unchecked() {
            let mut raw = RawThing::<24>::new(1u32);
            let _ = unsafe { raw.get_mut_unchecked::<i32>() };
        }
    }

    mod debug {
        use super::Thing;

        #[test]
        fn thing_debug_is_non_empty() {
            let t: Thing<24> = Thing::new(42u32);
            assert_ne!(format!("{t:?}"), "");
        }
    }

    mod heap_size {
        use crate::{HeapSize, Thing};
        use alloc::rc::Rc;
        use alloc::string::String;

        #[repr(align(16))]
        struct OverAligned(#[allow(dead_code)] u8);

        #[test]
        fn inline_values_have_nothing_on_the_heap() {
            assert_eq!(Thing::<24>::new(5_u64).heap_size(), 0);
            assert_eq!(Thing::<24>::new([0_u8; 24]).heap_size(), 0);
            assert_eq!(Thing::<24>::new(()).heap_size(), 0);
            // A type that needs a drop, but is stored inline.
            assert_eq!(Thing::<24>::new(String::from("text")).heap_size(), 0);
        }

        #[test]
        fn boxed_values_report_the_size_of_the_value() {
            // Too big for the slot.
            assert_eq!(Thing::<8>::new([0_u64; 10]).heap_size(), 80);
            assert_eq!(Thing::<24>::new([0_u8; 25]).heap_size(), 25);
            // Over-aligned, so boxed although it is small.
            assert_eq!(Thing::<24>::new(OverAligned(1)).heap_size(), 16);
            // Too big, and also needs a drop.
            assert_eq!(
                Thing::<8>::new([String::new(), String::new()]).heap_size(),
                48
            );
        }

        #[test]
        fn what_a_value_owns_is_not_counted() {
            let text = String::from("a text that lives on the heap");
            assert_eq!(Thing::<24>::new(text).heap_size(), 0);
        }

        #[test]
        fn asking_does_not_disturb_the_value() {
            let token = Rc::new(());

            let boxed = Thing::<8>::new((Rc::clone(&token), 0_u64, 0_u64));
            let inline = Thing::<24>::new(Rc::clone(&token));
            for _ in 0..3 {
                assert_eq!(boxed.heap_size(), 24);
                assert_eq!(inline.heap_size(), 0);
            }
            assert_eq!(Rc::strong_count(&token), 3);

            // Still readable, and dropped exactly once.
            assert!(Rc::ptr_eq(inline.get_ref::<Rc<()>>(), &token));
            drop(boxed);
            assert_eq!(Rc::strong_count(&token), 2);
            drop(inline);
            assert_eq!(Rc::strong_count(&token), 1);
        }

        #[test]
        fn a_moved_out_value_is_not_dropped_again() {
            let token = Rc::new(());
            let thing = Thing::<24>::new(Rc::clone(&token));
            assert_eq!(thing.heap_size(), 0);

            let value: Rc<()> = thing.get();
            assert_eq!(Rc::strong_count(&token), 2);
            drop(value);
            assert_eq!(Rc::strong_count(&token), 1);
        }
    }
}
