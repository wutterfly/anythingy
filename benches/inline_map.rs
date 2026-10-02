use std::collections::HashMap;
use std::hint::black_box;

use anythingy::InlineMap;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

/// Up to 8 entries are inline, so 2, 4 and 8 never allocate, and 16 and 64
/// have spilled to a hash map.
const SIZES: &[u32] = &[2, 4, 8, 16, 64];

type Inline = InlineMap<u32, u32, 8>;

fn inline_of(size: u32) -> Inline {
    (0..size).map(|i| (i, i)).collect()
}

fn hash_of(size: u32) -> HashMap<u32, u32> {
    (0..size).map(|i| (i, i)).collect()
}

/// Building a map from nothing, which includes the move to a hash map for the
/// sizes above 8.
fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    for &size in SIZES {
        group.bench_with_input(BenchmarkId::new("InlineMap<8>", size), &size, |b, &size| {
            b.iter(|| {
                let mut map = Inline::new();
                for i in 0..size {
                    map.insert(black_box(i), black_box(i));
                }
                map
            });
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &size, |b, &size| {
            b.iter(|| {
                let mut map = HashMap::new();
                for i in 0..size {
                    map.insert(black_box(i), black_box(i));
                }
                map
            });
        });
    }
    group.finish();
}

/// Looking up keys that are in the map.
fn bench_get_hit(c: &mut Criterion) {
    let mut group = c.benchmark_group("get_hit");
    for &size in SIZES {
        let inline = inline_of(size);
        let hash = hash_of(size);
        group.bench_with_input(BenchmarkId::new("InlineMap<8>", size), &size, |b, &size| {
            b.iter(|| {
                let mut sum = 0;
                for i in 0..size {
                    sum += inline.get(&black_box(i)).copied().unwrap_or(0);
                }
                sum
            });
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &size, |b, &size| {
            b.iter(|| {
                let mut sum = 0;
                for i in 0..size {
                    sum += hash.get(&black_box(i)).copied().unwrap_or(0);
                }
                sum
            });
        });
    }
    group.finish();
}

/// Looking up keys that are not in the map.
fn bench_get_miss(c: &mut Criterion) {
    let mut group = c.benchmark_group("get_miss");
    for &size in SIZES {
        let inline = inline_of(size);
        let hash = hash_of(size);
        group.bench_with_input(BenchmarkId::new("InlineMap<8>", size), &size, |b, &size| {
            b.iter(|| {
                let mut found = 0;
                for i in size..size * 2 {
                    found += usize::from(inline.contains_key(&black_box(i)));
                }
                found
            });
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &size, |b, &size| {
            b.iter(|| {
                let mut found = 0;
                for i in size..size * 2 {
                    found += usize::from(hash.contains_key(&black_box(i)));
                }
                found
            });
        });
    }
    group.finish();
}

/// Visiting every entry.
fn bench_iterate(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterate");
    for &size in SIZES {
        let inline = inline_of(size);
        let hash = hash_of(size);
        group.bench_with_input(BenchmarkId::new("InlineMap<8>", size), &size, |b, _| {
            b.iter(|| inline.iter().map(|(k, v)| k ^ v).sum::<u32>());
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &size, |b, _| {
            b.iter(|| hash.iter().map(|(k, v)| k ^ v).sum::<u32>());
        });
    }
    group.finish();
}

/// Creating a small map, filling it and dropping it, where not allocating
/// matters most.
fn bench_create_fill_drop(c: &mut Criterion) {
    let mut group = c.benchmark_group("create_fill_drop");
    for &size in &[2_u32, 4, 8] {
        group.bench_with_input(BenchmarkId::new("InlineMap<8>", size), &size, |b, &size| {
            b.iter(|| {
                let mut map = Inline::new();
                for i in 0..size {
                    map.insert(black_box(i), black_box(i));
                }
                black_box(map.len())
            });
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &size, |b, &size| {
            b.iter(|| {
                let mut map = HashMap::new();
                for i in 0..size {
                    map.insert(black_box(i), black_box(i));
                }
                black_box(map.len())
            });
        });
    }
    group.finish();
}

/// A map with room for 32 entries inline, filled with 16 and 32 entries, to see
/// how far scanning the keys keeps beating hashing them.
fn bench_wide_inline(c: &mut Criterion) {
    type Wide = InlineMap<u32, u32, 32>;

    let mut group = c.benchmark_group("wide_inline_get");
    for &size in &[16_u32, 24, 32] {
        let inline: Wide = (0..size).map(|i| (i, i)).collect();
        assert!(!inline.spilled());
        let hash = hash_of(size);

        group.bench_with_input(
            BenchmarkId::new("InlineMap<32> hit", size),
            &size,
            |b, &size| {
                b.iter(|| {
                    let mut sum = 0;
                    for i in 0..size {
                        sum += inline.get(&black_box(i)).copied().unwrap_or(0);
                    }
                    sum
                });
            },
        );
        group.bench_with_input(BenchmarkId::new("HashMap hit", size), &size, |b, &size| {
            b.iter(|| {
                let mut sum = 0;
                for i in 0..size {
                    sum += hash.get(&black_box(i)).copied().unwrap_or(0);
                }
                sum
            });
        });
        group.bench_with_input(
            BenchmarkId::new("InlineMap<32> miss", size),
            &size,
            |b, &size| {
                b.iter(|| {
                    let mut found = 0;
                    for i in size..size * 2 {
                        found += usize::from(inline.contains_key(&black_box(i)));
                    }
                    found
                });
            },
        );
        group.bench_with_input(BenchmarkId::new("HashMap miss", size), &size, |b, &size| {
            b.iter(|| {
                let mut found = 0;
                for i in size..size * 2 {
                    found += usize::from(hash.contains_key(&black_box(i)));
                }
                found
            });
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_insert,
    bench_get_hit,
    bench_get_miss,
    bench_iterate,
    bench_create_fill_drop,
    bench_wide_inline
);
criterion_main!(benches);
