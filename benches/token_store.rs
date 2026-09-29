use std::collections::HashMap;
use std::hint::black_box;

use anythingy::TokenStore;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use slotmap::SlotMap;

const SIZES: &[usize] = &[16, 256, 4096];

/// A pseudo-random but repeatable order of indices in `0..n`, so lookups
/// do not just walk memory front to back.
fn shuffled(n: usize) -> Vec<usize> {
    let mut order: Vec<usize> = (0..n).collect();
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    for i in (1..n).rev() {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        order.swap(i, (state >> 33) as usize % (i + 1));
    }
    order
}

/// Filling a store with `n` values.
fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    for &n in SIZES {
        group.bench_with_input(BenchmarkId::new("TokenStore", n), &n, |b, &n| {
            b.iter(|| {
                let mut store = TokenStore::new();
                for i in 0..n {
                    black_box(store.insert(black_box(i as u64)));
                }
                store
            });
        });
        group.bench_with_input(BenchmarkId::new("SlotMap", n), &n, |b, &n| {
            b.iter(|| {
                let mut map = SlotMap::new();
                for i in 0..n {
                    black_box(map.insert(black_box(i as u64)));
                }
                map
            });
        });
        group.bench_with_input(
            BenchmarkId::new("Vec<Option<T>> (plain index)", n),
            &n,
            |b, &n| {
                b.iter(|| {
                    let mut v = Vec::new();
                    for i in 0..n {
                        v.push(Some(black_box(i as u64)));
                    }
                    v
                });
            },
        );
        group.bench_with_input(BenchmarkId::new("HashMap<u64, T>", n), &n, |b, &n| {
            b.iter(|| {
                let mut map = HashMap::new();
                for i in 0..n {
                    map.insert(black_box(i as u64), black_box(i as u64));
                }
                map
            });
        });
    }
    group.finish();
}

/// Looking up `n` values by token, in shuffled order.
fn bench_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("get");
    for &n in SIZES {
        let order = shuffled(n);

        let mut store = TokenStore::new();
        let tokens: Vec<_> = (0..n).map(|i| store.insert(i as u64)).collect();
        group.bench_with_input(BenchmarkId::new("TokenStore", n), &order, |b, order| {
            b.iter(|| {
                let mut sum = 0u64;
                for &i in order {
                    sum += *store.get(black_box(tokens[i])).unwrap();
                }
                sum
            });
        });

        let mut map = SlotMap::new();
        let keys: Vec<_> = (0..n).map(|i| map.insert(i as u64)).collect();
        group.bench_with_input(BenchmarkId::new("SlotMap", n), &order, |b, order| {
            b.iter(|| {
                let mut sum = 0u64;
                for &i in order {
                    sum += *map.get(black_box(keys[i])).unwrap();
                }
                sum
            });
        });

        let plain: Vec<Option<u64>> = (0..n).map(|i| Some(i as u64)).collect();
        group.bench_with_input(
            BenchmarkId::new("Vec<Option<T>> (plain index)", n),
            &order,
            |b, order| {
                b.iter(|| {
                    let mut sum = 0u64;
                    for &i in order {
                        sum += plain[black_box(i)].unwrap();
                    }
                    sum
                });
            },
        );

        let hash: HashMap<u64, u64> = (0..n).map(|i| (i as u64, i as u64)).collect();
        group.bench_with_input(
            BenchmarkId::new("HashMap<u64, T>", n),
            &order,
            |b, order| {
                b.iter(|| {
                    let mut sum = 0u64;
                    for &i in order {
                        sum += hash[&black_box(i as u64)];
                    }
                    sum
                });
            },
        );
    }
    group.finish();
}

/// Steady-state churn: remove one value and insert a new one, `n` times,
/// in a store that stays full. Exercises slot reuse.
fn bench_churn(c: &mut Criterion) {
    let mut group = c.benchmark_group("churn");
    for &n in SIZES {
        let order = shuffled(n);

        group.bench_with_input(BenchmarkId::new("TokenStore", n), &order, |b, order| {
            b.iter_batched(
                || {
                    let mut store = TokenStore::new();
                    let tokens: Vec<_> = (0..n).map(|i| store.insert(i as u64)).collect();
                    (store, tokens)
                },
                |(mut store, mut tokens)| {
                    for &i in order {
                        store.remove(tokens[i]);
                        tokens[i] = store.insert(black_box(i as u64));
                    }
                    (store, tokens)
                },
                BatchSize::SmallInput,
            );
        });

        group.bench_with_input(BenchmarkId::new("SlotMap", n), &order, |b, order| {
            b.iter_batched(
                || {
                    let mut map = SlotMap::new();
                    let keys: Vec<_> = (0..n).map(|i| map.insert(i as u64)).collect();
                    (map, keys)
                },
                |(mut map, mut keys)| {
                    for &i in order {
                        map.remove(keys[i]);
                        keys[i] = map.insert(black_box(i as u64));
                    }
                    (map, keys)
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

/// Summing every value: iteration over a store with 1 in 4 slots vacant.
fn bench_iterate(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterate");
    for &n in SIZES {
        let mut store = TokenStore::new();
        let tokens: Vec<_> = (0..n).map(|i| store.insert(i as u64)).collect();
        for t in tokens.iter().step_by(4) {
            store.remove(*t);
        }
        group.bench_with_input(BenchmarkId::new("TokenStore", n), &(), |b, _| {
            b.iter(|| black_box(&store).values().sum::<u64>());
        });

        let mut map = SlotMap::new();
        let keys: Vec<_> = (0..n).map(|i| map.insert(i as u64)).collect();
        for k in keys.iter().step_by(4) {
            map.remove(*k);
        }
        group.bench_with_input(BenchmarkId::new("SlotMap", n), &(), |b, _| {
            b.iter(|| black_box(&map).values().sum::<u64>());
        });
    }
    group.finish();
}

criterion_group!(benches, bench_insert, bench_get, bench_churn, bench_iterate);
criterion_main!(benches);
