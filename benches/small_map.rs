mod bench;

use anythingy::SmallAnyMap;
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

type Map = SmallAnyMap;

bench_impl!(Map);

fn criterion_benchmark(c: &mut Criterion) {
    let mut map: Map = Map::with_capacity(512);

    c.bench_function("small map insert", |b| {
        b.iter(|| insert(black_box(&mut map)))
    });

    c.bench_function("small map get", |b| b.iter(|| get(black_box(&map))));

    c.bench_function("small map remove", |b| {
        b.iter(|| remove(black_box(&mut map)))
    });

    map.clear();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
