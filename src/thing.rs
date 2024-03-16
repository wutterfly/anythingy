use std::{
    any::TypeId,
    mem::{ManuallyDrop, MaybeUninit},
};

/// Default size of `Thing`.
/// Choosen to be 3x the size of usize, to facilitate Vec/String without boxing them, to prevent double pointers.
pub const DEFAULT_THING_SIZE: usize = std::mem::size_of::<usize>() * 3;

/// A Structure for storing type-erased values. Similar to `Box<dyn Any>` it can store values of any type.
///
/// What makes this structure special is, that the `SIZE` of Thing can be specified.
/// For values of type `T`, where size of `T` is smaller/equal to `SIZE`, no additional allocation is needed.
///
/// For types `T` that are greater then `SIZE`, the value gets boxed.
///
/// For types `T` wich alignment is greate then 8, the value gets also boxed.
#[derive(Debug)]
#[repr(align(8))]
pub struct Thing<const SIZE: usize = DEFAULT_THING_SIZE> {
    id: TypeId,
    drop: fn([MaybeUninit<u8>; SIZE]),
    data: [MaybeUninit<u8>; SIZE],
}

impl<const SIZE: usize> Thing<SIZE> {
    /// Creates a new `Thing` from generic type `T`. Uses the boxed value, if size of `T`  is bigger then `SIZE`.
    ///
    /// If the alignment of type `T` is greater then 8, `T` gets also boxed.
    ///
    /// # Panics
    /// Panics, if size of `T` is greate then `SIZE`, but `SIZE` is smaller then size of `Box<T>`.
    #[inline]
    #[must_use]
    pub fn new<T: 'static>(t: T) -> Self {
        // save type
        let id = TypeId::of::<T>();

        if Self::boxed::<T>() {
            // check that Thing can hold at least a Box.
            assert!(std::mem::size_of::<Box<T>>() <= SIZE);

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
    #[inline]
    #[must_use]
    pub fn get<T: 'static>(mut self) -> T {
        let id = TypeId::of::<T>();

        // check that types are matching
        assert_eq!(id, self.id);

        // IMPORTANT:
        // markt this as NOT drop, even if it is
        // this gets dropped at the end of the function call, while a valid instance of T also gets returned,
        // this leads to a double drop
        self.drop = Self::empty_drop_glue;

        if Self::boxed::<T>() {
            // convert type from bytes
            let convert = Convert::<SIZE, Box<T>>::from_bytes(self.data);

            // move value out of box
            return *convert.get();
        }

        // convert type from bytes
        let convert = Convert::<SIZE, T>::from_bytes(self.data);

        convert.get()
    }

    /// Returns a reference to the original type of `Thing`, if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    #[inline]
    #[must_use]
    pub fn get_ref<T: 'static>(&self) -> &T {
        let id = TypeId::of::<T>();

        // check that types are matching
        assert_eq!(id, self.id);

        if Self::boxed::<T>() {
            let boxed: &Box<T> = unsafe { std::mem::transmute(&self.data) };

            return boxed;
        }

        let out = unsafe { std::mem::transmute(&self.data) };
        out
    }

    /// Returns a mutable reference to the original type of `Thing`, if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    #[inline]
    #[must_use]
    pub fn get_mut<T: 'static>(&mut self) -> &mut T {
        let id = TypeId::of::<T>();

        // check that types are matching
        assert_eq!(id, self.id);

        if Self::boxed::<T>() {
            let boxed: &mut Box<T> = unsafe { std::mem::transmute(&mut self.data) };

            return boxed;
        }

        let out: &mut T = unsafe { std::mem::transmute(&mut self.data) };

        out
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

        // IMPORTANT:
        // markt this as NOT drop, even if it is
        // this gets dropped at the end of the function call, while a valid instance of T also gets returned,
        // this leads to a double drop
        self.drop = Self::empty_drop_glue;

        if Self::boxed::<T>() {
            // convert type from bytes
            let convert = Convert::<SIZE, Box<T>>::from_bytes(self.data);

            // move value out of box
            return Some(*convert.get());
        }

        // convert type from bytes
        let convert = Convert::<SIZE, T>::from_bytes(self.data);

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
            let boxed: &Box<T> = unsafe { std::mem::transmute(&self.data) };

            return Some(boxed);
        }

        let out = unsafe { std::mem::transmute(&self.data) };
        Some(out)
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
            let boxed: &mut Box<T> = unsafe { std::mem::transmute(&mut self.data) };

            return Some(boxed);
        }

        let out: &mut T = unsafe { std::mem::transmute(&mut self.data) };

        Some(out)
    }

    /// Returns true, if erased type is equal to given type.
    #[inline]
    #[must_use]
    pub fn is_type<T: 'static>(&self) -> bool {
        self.id == TypeId::of::<T>()
    }

    #[inline]
    const fn boxed<T: 'static>() -> bool {
        let align = std::mem::align_of::<T>();

        std::mem::size_of::<T>() > SIZE || align > 8
    }

    #[inline]
    fn drop_glue<T: 'static>(data: [MaybeUninit<u8>; SIZE]) {
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
    const fn empty_drop_glue<const S: usize>(_: [MaybeUninit<u8>; S]) {}
}

impl<const SIZE: usize> std::ops::Drop for Thing<SIZE> {
    #[inline]
    fn drop(&mut self) {
        (self.drop)(self.data);
    }
}

/// A structure to convert a given value of type T into raw bytes and back. Using a union here instead of `std::mem::transmute`, because
/// `std::mem::transmute` can only convert between types of equal size.
#[repr(align(8))]
union Convert<const SIZE: usize, T> {
    bytes: [MaybeUninit<u8>; SIZE],
    data: ManuallyDrop<T>,
}

impl<const SIZE: usize, T> Convert<SIZE, T> {
    #[inline]
    pub const fn new(value: T) -> Self {
        let size = core::mem::size_of::<T>();

        assert!(size <= SIZE);

        Self {
            data: ManuallyDrop::new(value),
        }
    }

    #[inline]
    pub const fn bytes(self) -> [MaybeUninit<u8>; SIZE] {
        // SAFETY:
        // This is safe, because Convert can only be constructed correctly.
        unsafe { self.bytes }
    }

    #[inline]
    pub const fn from_bytes(bytes: [MaybeUninit<u8>; SIZE]) -> Self {
        Self { bytes }
    }

    #[inline]
    pub const fn get(self) -> T {
        // SAFETY:
        // This is safe, because we guaranteed at creation of this Convert, that the type is correct.
        ManuallyDrop::into_inner(unsafe { self.data })
    }
}

impl<const SIZE: usize, T: Copy> Clone for Convert<SIZE, T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<const SIZE: usize, T: Copy> Copy for Convert<SIZE, T> {}

impl<const SIZE: usize, T> std::fmt::Debug for Convert<SIZE, T> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = std::any::type_name::<T>();
        write!(f, "{name}: {:?}", unsafe { self.bytes })
    }
}

#[cfg(test)]
mod tests_thing {

    use crate::Thing;

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
}
