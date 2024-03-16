#[macro_export]
macro_rules! bench_impl {
    ($map: ty) => {
        fn insert(map: &mut $map) {
            let _ = map.insert(123u8);
            let _ = map.insert(123u16);
            let _ = map.insert(123u32);
            let _ = map.insert(123u64);
            let _ = map.insert(123u128);

            let _ = map.insert(123i8);
            let _ = map.insert(123i16);
            let _ = map.insert(123i32);
            let _ = map.insert(123i64);
            let _ = map.insert(123i128);

            let _ = map.insert(123usize);
            let _ = map.insert(123isize);

            let _ = map.insert(123.0f32);
            let _ = map.insert(123.0f64);
        }

        fn get(map: &$map) {
            let _ = map.get::<u8>();
            let _ = map.get::<u16>();
            let _ = map.get::<u32>();
            let _ = map.get::<u64>();
            let _ = map.get::<u128>();

            let _ = map.get::<i8>();
            let _ = map.get::<i16>();
            let _ = map.get::<i32>();
            let _ = map.get::<i64>();
            let _ = map.get::<i128>();

            let _ = map.get::<usize>();
            let _ = map.get::<isize>();

            let _ = map.get::<f32>();
            let _ = map.get::<f64>();
        }

        fn remove(map: &mut $map) {
            let _ = map.remove::<u8>();
            let _ = map.remove::<u16>();
            let _ = map.remove::<u32>();
            let _ = map.remove::<u64>();
            let _ = map.remove::<u128>();

            let _ = map.remove::<i8>();
            let _ = map.remove::<i16>();
            let _ = map.remove::<i32>();
            let _ = map.remove::<i64>();
            let _ = map.remove::<i128>();

            let _ = map.remove::<usize>();
            let _ = map.remove::<isize>();

            let _ = map.remove::<f32>();
            let _ = map.remove::<f64>();
        }
    };
}
