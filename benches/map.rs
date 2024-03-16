use anything::AnyMap;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

type Map = AnyMap;

fn insert(map: &mut Map) {
    map.insert(123u8);
    map.insert(123u16);
    map.insert(123u32);
    map.insert(123u64);
    map.insert(123u128);

    map.insert(123i8);
    map.insert(123i16);
    map.insert(123i32);
    map.insert(123i64);
    map.insert(123i128);

    map.insert(123usize);
    map.insert(123isize);

    map.insert(123.0f32);
    map.insert(123.0f64);
}

fn get(map: &Map) {
    map.get::<u8>();
    map.get::<u16>();
    map.get::<u32>();
    map.get::<u64>();
    map.get::<u128>();

    map.get::<i8>();
    map.get::<i16>();
    map.get::<i32>();
    map.get::<i64>();
    map.get::<i128>();

    map.get::<usize>();
    map.get::<isize>();

    map.get::<f32>();
    map.get::<f64>();
}

fn remove(map: &mut Map) {
    map.remove::<u8>();
    map.remove::<u16>();
    map.remove::<u32>();
    map.remove::<u64>();
    map.remove::<u128>();

    map.remove::<i8>();
    map.remove::<i16>();
    map.remove::<i32>();
    map.remove::<i64>();
    map.remove::<i128>();

    map.remove::<usize>();
    map.remove::<isize>();

    map.remove::<f32>();
    map.remove::<f64>();
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut map: Map = Map::with_capacity(512);

    c.bench_function("map insert", |b| b.iter(|| insert(black_box(&mut map))));

    c.bench_function("map get", |b| b.iter(|| get(black_box(&map))));

    c.bench_function("map remove", |b| b.iter(|| remove(black_box(&mut map))));

    map.clear();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
