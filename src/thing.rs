use std::{
    any::TypeId,
    mem::{ManuallyDrop, MaybeUninit},
};

/// Default size of `Thing`.
/// Choosen to be 3x the size of usize, to facilitate Vec/String without boxing them, to prevent double pointers.
pub const DEFAULT_THING_SIZE: usize = std::mem::size_of::<usize>() * 3;

///
#[derive(Debug)]
pub struct Thing<const SIZE: usize = DEFAULT_THING_SIZE> {
    id: TypeId,
    drop: fn([MaybeUninit<u8>; SIZE]),
    data: [MaybeUninit<u8>; SIZE],
    boxed: bool,
}

impl<const SIZE: usize> Thing<SIZE> {
    /// Creates a new event from generic type `T`.
    ///
    /// # Panics
    /// Panics, if type `T` is bigger then `SIZE`.
    #[inline]
    #[must_use]
    pub fn new<T: 'static>(t: T) -> Self {
        // save type
        let id = TypeId::of::<T>();

        if std::mem::size_of::<T>() > SIZE {
            // convert type from bytes
            let convert = Convert::new(Box::new(t));

            // convert type to bytes
            let data = convert.bytes();

            return Self {
                id,
                drop: Self::drop_glue::<T>,
                data,
                boxed: true,
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

        Self {
            id,
            drop,
            data,
            boxed: false,
        }
    }

    /// Returns the original type of the event if given type and original type match.
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

        if std::mem::size_of::<T>() > SIZE {
            // convert type from bytes
            let convert = Convert::<SIZE, Box<T>>::from_bytes(self.data);

            // move value out of box
            return *convert.get();
        }

        // convert type from bytes
        let convert = Convert::<SIZE, T>::from_bytes(self.data);

        convert.get()
    }

    /// Returns the original type of the event if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    #[inline]
    #[must_use]
    pub fn get_ref<T: 'static>(&self) -> &T {
        let id = TypeId::of::<T>();

        // check that types are matching
        assert_eq!(id, self.id);

        if std::mem::size_of::<T>() > SIZE {
            // convert type from bytes
            let convert = ConvertRef::<SIZE, Box<T>>::from_bytes(&self.data);

            // move value out of box
            return convert.get();
        }

        // convert type from bytes
        let convert = ConvertRef::<SIZE, T>::from_bytes(&self.data);

        convert.get()
    }

    /// Returns the original type of the event if given type and original type match.
    ///
    /// # Panics
    /// Panics if given type and original type do not match.
    #[inline]
    #[must_use]
    pub fn get_mut<T: 'static>(&mut self) -> &mut T {
        let id = TypeId::of::<T>();

        // check that types are matching
        assert_eq!(id, self.id);

        if std::mem::size_of::<T>() > SIZE {
            // convert type from bytes
            let convert = ConvertRefMut::<SIZE, Box<T>>::from_bytes(&mut self.data);

            // move value out of box
            return convert.get();
        }

        // convert type from bytes
        let convert = ConvertRefMut::<SIZE, T>::from_bytes(&mut self.data);

        convert.get()
    }

    ///
    #[inline]
    #[must_use]
    pub fn is_type<T: 'static>(&self) -> bool {
        let id = TypeId::of::<T>();
        self.id == id
    }

    ///
    #[inline]
    #[must_use]
    pub const fn is_boxed(&self) -> bool {
        self.boxed
    }

    #[inline]
    fn drop_glue<T: 'static>(data: [MaybeUninit<u8>; SIZE]) {
        if std::mem::size_of::<T>() > SIZE {
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

///
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

///
union ConvertRef<'a, const N: usize, T> {
    data: &'a T,
    bytes: &'a [MaybeUninit<u8>; N],
}

impl<'a, T, const N: usize> ConvertRef<'a, N, T> {
    #[inline]
    pub const fn from_bytes(bytes: &'a [MaybeUninit<u8>; N]) -> Self {
        Self { bytes }
    }

    #[inline]
    pub const fn get(self) -> &'a T {
        // SAFETY:
        // This is safe, because we guaranteed at creation of this Convert, that the type is correct.
        unsafe { self.data }
    }
}

///
union ConvertRefMut<'a, const N: usize, T> {
    data: &'a mut T,
    bytes: &'a mut [MaybeUninit<u8>; N],
}

impl<'a, T, const N: usize> ConvertRefMut<'a, N, T> {
    #[inline]
    pub fn from_bytes(bytes: &'a mut [MaybeUninit<u8>; N]) -> Self {
        Self { bytes }
    }

    #[inline]
    pub fn get(self) -> &'a mut T {
        // SAFETY:
        // This is safe, because we guaranteed at creation of this Convert, that the type is correct.
        unsafe { self.data }
    }
}

#[cfg(test)]
mod tests_thing {

    use crate::Thing;

    #[test]
    fn test_thing_new_unboxed() {
        let data_1 = 123usize;
        let thing_1: Thing = Thing::new(data_1);
        assert!(!thing_1.is_boxed());

        let data_2 = (123usize, 456usize);
        let thing_2: Thing = Thing::new(data_2);
        assert!(!thing_2.is_boxed());

        let data_3 = String::new();
        let thing_3: Thing = Thing::new(data_3);
        assert!(!thing_3.is_boxed());
    }

    #[test]
    fn test_thing_new_boxed() {
        let data_1 = (123usize, 456usize, 789usize, 012usize);
        let thing_1: Thing = Thing::new(data_1);
        assert!(thing_1.is_boxed());
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
}
