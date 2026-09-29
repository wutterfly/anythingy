use std::collections::{BTreeSet, HashSet};
use std::hint::black_box;

use anythingy::LinearSet;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

const SIZES: &[usize] = &[4, 8, 16, 32, 64, 256];

/// Membership test for the last element, so the linear scan does a full pass.
fn bench_contains_hit(c: &mut Criterion) {
    let mut group = c.benchmark_group("set_contains_hit");
    for &n in SIZES {
        let linear: LinearSet<usize> = (0..n).collect();
        let hash: HashSet<usize> = (0..n).collect();
        let btree: BTreeSet<usize> = (0..n).collect();
        let key = n - 1;
        group.bench_with_input(BenchmarkId::new("LinearSet", n), &key, |b, k| {
            b.iter(|| black_box(linear.contains(black_box(k))));
        });
        group.bench_with_input(BenchmarkId::new("HashSet", n), &key, |b, k| {
            b.iter(|| black_box(hash.contains(black_box(k))));
        });
        group.bench_with_input(BenchmarkId::new("BTreeSet", n), &key, |b, k| {
            b.iter(|| black_box(btree.contains(black_box(k))));
        });
    }
    group.finish();
}

/// Membership test for an absent element.
fn bench_contains_miss(c: &mut Criterion) {
    let mut group = c.benchmark_group("set_contains_miss");
    for &n in SIZES {
        let linear: LinearSet<usize> = (0..n).collect();
        let hash: HashSet<usize> = (0..n).collect();
        let btree: BTreeSet<usize> = (0..n).collect();
        let key = n + 1;
        group.bench_with_input(BenchmarkId::new("LinearSet", n), &key, |b, k| {
            b.iter(|| black_box(linear.contains(black_box(k))));
        });
        group.bench_with_input(BenchmarkId::new("HashSet", n), &key, |b, k| {
            b.iter(|| black_box(hash.contains(black_box(k))));
        });
        group.bench_with_input(BenchmarkId::new("BTreeSet", n), &key, |b, k| {
            b.iter(|| black_box(btree.contains(black_box(k))));
        });
    }
    group.finish();
}

/// Building a set of `n` distinct elements.
fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("set_insert");
    for &n in SIZES {
        group.bench_with_input(BenchmarkId::new("LinearSet", n), &n, |b, &n| {
            b.iter(|| {
                let mut set = LinearSet::new();
                for i in 0..n {
                    set.insert(black_box(i));
                }
                set
            });
        });
        group.bench_with_input(BenchmarkId::new("HashSet", n), &n, |b, &n| {
            b.iter(|| {
                let mut set = HashSet::new();
                for i in 0..n {
                    set.insert(black_box(i));
                }
                set
            });
        });
        group.bench_with_input(BenchmarkId::new("BTreeSet", n), &n, |b, &n| {
            b.iter(|| {
                let mut set = BTreeSet::new();
                for i in 0..n {
                    set.insert(black_box(i));
                }
                set
            });
        });
    }
    group.finish();
}

/// Intersection of two overlapping sets (half the elements shared).
fn bench_intersection(c: &mut Criterion) {
    let mut group = c.benchmark_group("set_intersection");
    for &n in SIZES {
        let a: LinearSet<usize> = (0..n).collect();
        let b: LinearSet<usize> = (n / 2..n + n / 2).collect();
        let ha: HashSet<usize> = (0..n).collect();
        let hb: HashSet<usize> = (n / 2..n + n / 2).collect();
        group.bench_with_input(BenchmarkId::new("LinearSet", n), &(), |bench, _| {
            bench.iter(|| black_box(&a).intersection(black_box(&b)).count());
        });
        group.bench_with_input(BenchmarkId::new("HashSet", n), &(), |bench, _| {
            bench.iter(|| black_box(&ha).intersection(black_box(&hb)).count());
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_contains_hit,
    bench_contains_miss,
    bench_insert,
    bench_intersection
);
criterion_main!(benches);
