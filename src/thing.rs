use std::{
    any::TypeId,
    cell::UnsafeCell,
    mem::{ManuallyDrop, MaybeUninit},
};

/// Default size of [`Thing`][crate::Thing].
/// Chosen to be 3x [`std::mem::size_of<usize>()`], to facilitate [`Vec`]/[`String`] without boxing them, to prevent double pointers.
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
/// # Send, Sync, UnwindSafe, RefUnwindSafe
/// Because the type of the contained thing is erased, no assumption can be made, whether the contained thing implements any of the marker traits.
/// Here it is advised, to create a wrapper type, that checks at creation for required traits.
///
/// ## Example
/// ```rust
/// # use anythingy::{Thing};
/// # use std::panic::{RefUnwindSafe, UnwindSafe};
/// struct Wrapper(Thing);
///
/// impl RefUnwindSafe for Wrapper {}
/// impl UnwindSafe for Wrapper {}
/// // SAFETY: Trait bounds get checked at creation.
/// unsafe impl Sync for Wrapper {}
/// unsafe impl Send for Wrapper {}
///
/// impl Wrapper {
///     pub fn new<T>(value: T) -> Self
///     where
///         T: Send + Sync + UnwindSafe + RefUnwindSafe + 'static
///     {
///         Self(Thing::new(value))
///     }
/// }
/// ```
#[derive(Debug)]
#[repr(align(8))]
pub struct Thing<const SIZE: usize = DEFAULT_THING_SIZE> {
    id: TypeId,
    drop: fn(UnsafeCell<[MaybeUninit<u8>; SIZE]>),
    data: UnsafeCell<[MaybeUninit<u8>; SIZE]>,
}

impl<const SIZE: usize> Thing<SIZE> {
    /// Creates a new `Thing` from generic type `T`. Uses the boxed value, if size of `T`  is bigger then `SIZE`.
    ///
    /// If the alignment of type `T` is greater then 8, `T` gets also boxed.
    ///
    /// # Panics
    /// Panics, if size of `T` is greater then `SIZE`, but `SIZE` is smaller then size of `Box<T>`.
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// let number_thing: Thing<24> = Thing::new(42u64);
    /// let sting_thing: Thing<24> = Thing::new(String::new());
    /// let byte_thing: Thing<24> = Thing::new(Vec::<u8>::new());
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn new<T: 'static>(t: T) -> Self {
        // save type
        let id = TypeId::of::<T>();

        if Self::boxed::<T>() {
            // check that Thing can hold at least a Box.
            assert!(Self::fitting::<Box<T>>());

            // convert type from bytes
            let convert = Convert::new(Box::new(t));

            // convert type to bytes
            let data = convert.bytes();

            return Self {
                id,
                drop: Self::drop_glue::<T>,
                data,
            };
        }

        // convert type from bytes
        let convert = Convert::new(t);

        // convert type to bytes
        let data = convert.bytes();

        // get drop glue
        let drop = if std::mem::needs_drop::<T>() {
            Self::drop_glue::<T>
        } else {
            Self::empty_drop_glue
        };

        Self { id, drop, data }
    }

    /// Returns the original type of `Thing`, if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// let number_thing: Thing<24> = Thing::new(42u64);
    /// let number = number_thing.get::<u64>();
    /// assert_eq!(number, 42);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn get<T: 'static>(mut self) -> T {
        // check that types are matching
        assert!(self.is_type::<T>());

        // IMPORTANT:
        // marked self as NOT drop, even if it is
        // self gets dropped at the end of the function call, while a valid instance of T also gets returned,
        // this leads to a double drop
        self.drop = Self::empty_drop_glue;

        let data = unsafe { self.move_data_uninit() };

        if Self::boxed::<T>() {
            assert!(Self::fitting::<Box<T>>());

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
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// let number_thing: Thing<24> = Thing::new(42u64);
    /// let number = number_thing.get_ref::<u64>();
    /// assert_eq!(number, &42);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn get_ref<T: 'static>(&self) -> &T {
        // check that types are matching
        assert!(self.is_type::<T>());

        if Self::boxed::<T>() {
            return Convert::<SIZE, Box<T>>::get_ref(&self.data).as_ref();
        }

        Convert::<SIZE, T>::get_ref(&self.data)
    }

    /// Returns a mutable reference to the original type of `Thing`, if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// let mut number_thing: Thing<24> = Thing::new(42u64);
    /// let number = number_thing.get_mut::<u64>();
    /// assert_eq!(number, &mut 42);
    /// *number = 123;
    ///
    /// let number = number_thing.get_mut::<u64>();
    /// assert_eq!(number, &mut 123);
    /// # }
    /// ```
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
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// let number_thing: Thing<24> = Thing::new(42u64);
    /// let number = number_thing.try_get::<u64>();
    /// assert_eq!(number, Some(42));
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn try_get<T: 'static>(mut self) -> Option<T> {
        // check that types are matching
        if !self.is_type::<T>() {
            return None;
        }

        // IMPORTANT:
        // marked self as NOT drop, even if it is
        // self gets dropped at the end of the function call, while a valid instance of T also gets returned,
        // this leads to a double drop
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
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// let number_thing: Thing<24> = Thing::new(42u64);
    /// let number = number_thing.try_get_ref::<u64>();
    /// assert_eq!(number, Some(&42));
    /// # }
    /// ```
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
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// let mut number_thing: Thing<24> = Thing::new(42u64);
    /// let number = number_thing.try_get_mut::<u64>();
    /// assert_eq!(number, Some(&mut 42));
    /// # }
    /// ```
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
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// let number_thing: Thing<24> = Thing::new(42u64);
    /// assert!(number_thing.is_type::<u64>());
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn is_type<T: 'static>(&self) -> bool {
        self.id == TypeId::of::<T>()
    }

    /// Returns true, if `T` can be made into a `Thing`.
    ///
    /// Returns false, if `SIZE` is smaller then a needed `Box<T>`.
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// // fitting
    /// assert!(Thing::<1>::fitting::<u8>());
    /// // not fitting
    /// assert!(!Thing::<1>::fitting::<u16>());
    /// // fitting
    /// assert!(Thing::<2>::fitting::<u16>());
    /// // fitting, but boxed
    /// assert!(Thing::<16>::fitting::<String>());
    /// // fitting
    /// assert!(Thing::<24>::fitting::<String>());
    /// # }
    /// ```
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
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// // not boxed
    /// assert_eq!(Thing::<2>::size_requirement_unboxed::<u8>(), Some(1));
    /// // not boxed
    /// assert_eq!(Thing::<2>::size_requirement_unboxed::<u16>(),Some(2));
    /// // boxed
    /// assert_eq!(Thing::<2>::size_requirement_unboxed::<u32>(), Some(4));
    /// // not boxed
    /// assert_eq!(Thing::<100>::size_requirement_unboxed::<u64>(),Some(8));
    /// // boxed (maybe, TODO: fix this once alignment change hit stable)
    /// assert!(Thing::<8>::size_requirement_unboxed::<u128>().is_none() == (std::mem::align_of::<u128>() > 8));
    /// # }
    /// ```
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
    ///
    /// Returns false, if `SIZE` is smaller then size of `T` or alignment of `T` is greater then 8.
    ///
    /// # Example
    /// ```rust
    /// # use anythingy::{Thing};
    /// # fn main() {
    /// // not boxed
    /// assert!(!Thing::<2>::boxed::<u8>());
    /// // not boxed
    /// assert!(!Thing::<2>::boxed::<u16>());
    /// // boxed
    /// assert!(Thing::<2>::boxed::<u32>());
    /// // not boxed
    /// assert!(!Thing::<100>::boxed::<u64>());
    /// // boxed
    /// assert!(Thing::<100>::boxed::<u128>() == (std::mem::align_of::<u128>() > 8));
    /// # }
    /// ```
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
    unsafe fn move_data_uninit(&mut self) -> UnsafeCell<[MaybeUninit<u8>; SIZE]> {
        let fill = UnsafeCell::new([MaybeUninit::<u8>::uninit(); SIZE]);

        std::mem::replace(&mut self.data, fill)
    }

    #[inline]
    fn drop_glue<T: 'static>(data: UnsafeCell<[MaybeUninit<u8>; SIZE]>) {
        if Self::boxed::<T>() {
            // convert type from bytes
            let convert = Convert::<SIZE, Box<T>>::from_bytes(data);

            // move value out of box
            let t: Box<T> = convert.get();

            // drop
            drop(t);

            return;
        }

        // convert bytes to t
        let convert = Convert::from_bytes(data);
        let t: T = convert.get();

        // drop
        drop(t);
    }

    #[inline]
    const fn empty_drop_glue<const S: usize>(_: UnsafeCell<[MaybeUninit<u8>; S]>) {}
}

impl<const SIZE: usize> std::ops::Drop for Thing<SIZE> {
    #[inline]
    fn drop(&mut self) {
        let drop = unsafe { self.move_data_uninit() };

        (self.drop)(drop);
    }
}

/// A structure to convert a given value of type T into raw bytes and back. Using a union here instead of `std::mem::transmute`, because
/// `std::mem::transmute` can only convert between types of equal size.
#[repr(align(8))]
union Convert<const SIZE: usize, T> {
    bytes: ManuallyDrop<UnsafeCell<[MaybeUninit<u8>; SIZE]>>,
    data: ManuallyDrop<UnsafeCell<T>>,
}

impl<const SIZE: usize, T> Convert<SIZE, T> {
    #[inline]
    const fn new(value: T) -> Self {
        let size = core::mem::size_of::<T>();

        assert!(size <= SIZE);

        Self {
            data: ManuallyDrop::new(UnsafeCell::new(value)),
        }
    }

    #[inline]
    const fn bytes(self) -> UnsafeCell<[MaybeUninit<u8>; SIZE]> {
        // SAFETY:
        // This is safe, because Convert can only be constructed correctly.
        ManuallyDrop::into_inner(unsafe { self.bytes })
    }

    #[inline]
    const fn from_bytes(bytes: UnsafeCell<[MaybeUninit<u8>; SIZE]>) -> Self {
        Self {
            bytes: ManuallyDrop::new(bytes),
        }
    }

    #[inline]
    fn get(self) -> T {
        // SAFETY:
        // This is safe, because we guaranteed at creation of this Convert, that the type is correct.
        ManuallyDrop::into_inner(unsafe { self.data }).into_inner()
    }

    #[inline]
    const fn get_ref(data: &UnsafeCell<[MaybeUninit<u8>; SIZE]>) -> &T {
        let bytes = std::ptr::from_ref::<UnsafeCell<[std::mem::MaybeUninit<u8>; SIZE]>>(data);
        let ptr = bytes.cast::<T>();

        unsafe { &*ptr }
    }

    #[inline]
    fn get_mut(data: &mut UnsafeCell<[MaybeUninit<u8>; SIZE]>) -> &mut T {
        let bytes = std::ptr::from_mut::<UnsafeCell<[std::mem::MaybeUninit<u8>; SIZE]>>(data);
        let ptr = bytes.cast::<T>();

        unsafe { &mut *ptr }
    }
}

impl<const SIZE: usize, T> std::fmt::Debug for Convert<SIZE, T> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = std::any::type_name::<T>();

        let bytes = unsafe { &*(self.bytes.get() as *const _) };

        write!(f, "{name}: {:?}", bytes)
    }
}

#[cfg(test)]
mod tests_thing {

    use std::sync::RwLock;

    use crate::Thing;

    #[test]
    fn test_fitting() {
        let fitting = Thing::<1>::fitting::<u8>();
        assert!(fitting);

        let fitting = Thing::<1>::fitting::<u16>();
        assert!(!fitting);

        let fitting = Thing::<2>::fitting::<u16>();
        assert!(fitting);
    }

    #[test]
    fn test_thing_new_unboxed() {
        let data_1 = 123u8;
        let _: Thing = Thing::new(data_1);

        let data_2 = 123usize;
        let _: Thing = Thing::new(data_2);

        let data_3 = (123usize, 456usize);
        let _: Thing = Thing::new(data_3);

        let data_4 = String::new();
        let _: Thing = Thing::new(data_4);
    }

    #[test]
    fn test_thing_new_boxed() {
        let data_1 = (123usize, 456usize, 789usize, 012usize);
        let _: Thing = Thing::new(data_1);
    }

    #[test]
    #[should_panic]
    fn test_thing_new_boxed_too_small() {
        let data_1 = 123u32;
        _ = Thing::<1>::new(data_1);
    }

    #[test]
    fn test_thing_get_unboxed() {
        let data_1 = 123usize;
        let thing_1: Thing = Thing::new(data_1);
        let data_1_out = thing_1.get::<usize>();
        assert_eq!(data_1, data_1_out);

        let data_2 = (123usize, 456usize);
        let thing_2: Thing = Thing::new(data_2);
        let data_2_out = thing_2.get::<(usize, usize)>();
        assert_eq!(data_2, data_2_out);
    }

    #[test]
    fn test_thing_get_boxed() {
        let data_1 = (123usize, 456usize, 789usize, 012usize);
        let thing_1: Thing = Thing::new(data_1);
        let data_1_out = thing_1.get::<(usize, usize, usize, usize)>();
        assert_eq!(data_1, data_1_out);
    }

    #[test]
    fn test_thing_get_ref_unboxed() {
        let data_1 = 123usize;
        let thing_1: Thing = Thing::new(data_1);
        let data_1_out = thing_1.get_ref::<usize>();
        assert_eq!(&data_1, data_1_out);

        let data_2 = (123usize, 456usize);
        let thing_2: Thing = Thing::new(data_2);
        let data_2_out = thing_2.get_ref::<(usize, usize)>();
        assert_eq!(&data_2, data_2_out);
    }

    #[test]
    fn test_thing_get_ref_boxed() {
        let data_1 = (123usize, 456usize, 789usize, 012usize);
        let thing_1: Thing = Thing::new(data_1);
        let data_1_out = thing_1.get_ref::<(usize, usize, usize, usize)>();
        assert_eq!(&data_1, data_1_out);
    }

    #[test]
    fn test_thing_get_mut_unboxed() {
        let data_1 = 123usize;
        let mut thing_1: Thing = Thing::new(data_1);
        let data_1_out = thing_1.get_mut::<usize>();
        assert_eq!(&data_1, data_1_out);
        *data_1_out = 987;
        let data_1_out = thing_1.get::<usize>();
        assert_eq!(987, data_1_out);

        let data_2 = (123usize, 456usize);
        let mut thing_2: Thing = Thing::new(data_2);
        let data_2_out = thing_2.get_mut::<(usize, usize)>();
        assert_eq!(&data_2, data_2_out);
        *data_2_out = (987, 654);
        let data_2_out = thing_2.get::<(usize, usize)>();
        assert_eq!((987, 654), data_2_out);
    }

    #[test]
    fn test_thing_get_mut_boxed() {
        let data_1 = (123usize, 456usize, 789usize, 012usize);
        let mut thing_1: Thing = Thing::new(data_1);
        let data_1_out = thing_1.get_mut::<(usize, usize, usize, usize)>();
        assert_eq!(&data_1, data_1_out);
        *data_1_out = (987, 654, 321, 012);
        let data_1_out = thing_1.get::<(usize, usize, usize, usize)>();
        assert_eq!((987, 654, 321, 012), data_1_out);
    }

    #[test]
    fn test_thing_alignment() {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        #[repr(align(16))]
        struct TestAlign {
            data: u8,
        }

        let data_1 = TestAlign { data: 42 };
        let thing: Thing = Thing::new(data_1);

        let out_1 = thing.get_ref::<TestAlign>();
        assert_eq!(&data_1, out_1)
    }

    #[test]
    fn test_get_ref_with_unsafecell() {
        /// Using types that contain interior mutability was problematic.
        ///
        /// De-referencing a *const T to a &T, where T contains (somewhere) a UnsafeCell, is UB.
        /// A shared reference (&T) points to immutable memory, allowing certain optimizations. UnsafeCell disables this.
        /// Because Thing is a generic type, it can't be ruled out that the stored type contains a UnsafeCell.
        /// The prevent UB upfront, internal data is always wrapped in an UnsafeCell.
        ///
        /// Miri Error:
        /// trying to retag from <205684> for SharedReadWrite permission at [..], but that tag only grants SharedReadOnly permission for this location
        struct Test {
            _lock: RwLock<u32>,
        }

        let data_1 = Test {
            _lock: RwLock::new(42),
        };

        let thing_1: Thing = Thing::new(data_1);
        let data_1_out = thing_1.get_ref::<Test>();
        assert_eq!(*data_1_out._lock.read().unwrap(), 42);
    }
}
