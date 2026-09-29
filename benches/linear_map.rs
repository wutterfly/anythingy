use std::collections::{BTreeMap, HashMap};
use std::hint::black_box;

use anythingy::LinearMap;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

const SIZES: &[usize] = &[4, 8, 16, 32, 64, 256];

fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    for &size in SIZES {
        group.bench_with_input(BenchmarkId::new("LinearMap", size), &size, |b, &size| {
            b.iter(|| {
                let mut map = LinearMap::new();
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
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), &size, |b, &size| {
            b.iter(|| {
                let mut map = BTreeMap::new();
                for i in 0..size {
                    map.insert(black_box(i), black_box(i));
                }
                map
            });
        });
    }
    group.finish();
}

fn bench_get_hit(c: &mut Criterion) {
    let mut group = c.benchmark_group("get_hit");
    for &size in SIZES {
        let linear: LinearMap<usize, usize> = (0..size).map(|i| (i, i)).collect();
        let hash: HashMap<usize, usize> = (0..size).map(|i| (i, i)).collect();
        let btree: BTreeMap<usize, usize> = (0..size).map(|i| (i, i)).collect();
        // Look up the last key so LinearMap always does a full scan.
        let key = size - 1;

        group.bench_with_input(BenchmarkId::new("LinearMap", size), &key, |b, &key| {
            b.iter(|| black_box(linear.get(&key)));
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &key, |b, &key| {
            b.iter(|| black_box(hash.get(&key)));
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), &key, |b, &key| {
            b.iter(|| black_box(btree.get(&key)));
        });
    }
    group.finish();
}

fn bench_get_miss(c: &mut Criterion) {
    let mut group = c.benchmark_group("get_miss");
    for &size in SIZES {
        let linear: LinearMap<usize, usize> = (0..size).map(|i| (i, i)).collect();
        let hash: HashMap<usize, usize> = (0..size).map(|i| (i, i)).collect();
        let btree: BTreeMap<usize, usize> = (0..size).map(|i| (i, i)).collect();
        let key = size + 1;

        group.bench_with_input(BenchmarkId::new("LinearMap", size), &key, |b, &key| {
            b.iter(|| black_box(linear.get(&key)));
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &key, |b, &key| {
            b.iter(|| black_box(hash.get(&key)));
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), &key, |b, &key| {
            b.iter(|| black_box(btree.get(&key)));
        });
    }
    group.finish();
}

fn bench_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("remove");
    for &size in SIZES {
        group.bench_with_input(BenchmarkId::new("LinearMap", size), &size, |b, &size| {
            b.iter_batched(
                || (0..size).map(|i| (i, i)).collect::<LinearMap<_, _>>(),
                |mut map| black_box(map.remove(&(size / 2))),
                criterion::BatchSize::SmallInput,
            );
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &size, |b, &size| {
            b.iter_batched(
                || (0..size).map(|i| (i, i)).collect::<HashMap<_, _>>(),
                |mut map| black_box(map.remove(&(size / 2))),
                criterion::BatchSize::SmallInput,
            );
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), &size, |b, &size| {
            b.iter_batched(
                || (0..size).map(|i| (i, i)).collect::<BTreeMap<_, _>>(),
                |mut map| black_box(map.remove(&(size / 2))),
                criterion::BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

/// Lookups with `String` keys, where comparing is expensive: checks that the
/// fast path for small plain keys is not applied here.
fn bench_get_hit_string(c: &mut Criterion) {
    let mut group = c.benchmark_group("get_hit_string");
    for &size in SIZES {
        let names: Vec<String> = (0..size).map(|i| format!("key-number-{i:04}")).collect();
        let linear: LinearMap<String, usize> = names.iter().cloned().zip(0..size).collect();
        let hash: HashMap<String, usize> = names.iter().cloned().zip(0..size).collect();
        let key = names[size - 1].as_str();

        group.bench_with_input(BenchmarkId::new("LinearMap", size), &key, |b, &key| {
            b.iter(|| black_box(linear.get(key)));
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &key, |b, &key| {
            b.iter(|| black_box(hash.get(key)));
        });
    }
    group.finish();
}

/// Sum of all values: iteration cost over the two-vector layout.
fn bench_iterate(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterate");
    for &size in SIZES {
        let linear: LinearMap<usize, usize> = (0..size).map(|i| (i, i)).collect();
        let hash: HashMap<usize, usize> = (0..size).map(|i| (i, i)).collect();
        let btree: BTreeMap<usize, usize> = (0..size).map(|i| (i, i)).collect();

        group.bench_with_input(BenchmarkId::new("LinearMap", size), &(), |b, _| {
            b.iter(|| black_box(&linear).iter().map(|(_, v)| *v).sum::<usize>());
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &(), |b, _| {
            b.iter(|| black_box(&hash).values().sum::<usize>());
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), &(), |b, _| {
            b.iter(|| black_box(&btree).values().sum::<usize>());
        });
    }
    group.finish();
}

/// Counting occurrences with the entry API: one search per event.
fn bench_entry_count(c: &mut Criterion) {
    let mut group = c.benchmark_group("entry_count");
    for &size in SIZES {
        // 4 events per distinct key.
        let events: Vec<usize> = (0..size * 4).map(|i| i % size).collect();

        group.bench_with_input(BenchmarkId::new("LinearMap", size), &events, |b, events| {
            b.iter(|| {
                let mut map = LinearMap::new();
                for &e in events {
                    *map.entry(e).or_insert(0usize) += 1;
                }
                map
            });
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &events, |b, events| {
            b.iter(|| {
                let mut map = HashMap::new();
                for &e in events {
                    *map.entry(e).or_insert(0usize) += 1;
                }
                map
            });
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), &events, |b, events| {
            b.iter(|| {
                let mut map = BTreeMap::new();
                for &e in events {
                    *map.entry(e).or_insert(0usize) += 1;
                }
                map
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
    bench_remove,
    bench_get_hit_string,
    bench_iterate,
    bench_entry_count
);
criterion_main!(benches);
