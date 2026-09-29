use std::hint::black_box;

use anythingy::InlineVec;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use smallvec::SmallVec;

/// Lengths below, at and above the inline capacity of 8.
const LENGTHS: &[usize] = &[2, 4, 8, 16, 64];

/// Building a vector by pushing `n` elements. Short vectors show the
/// saved allocation; long ones show the cost of spilling.
fn bench_push(c: &mut Criterion) {
    let mut group = c.benchmark_group("vec_push");
    for &n in LENGTHS {
        group.bench_with_input(BenchmarkId::new("InlineVec<_, 8>", n), &n, |b, &n| {
            b.iter(|| {
                let mut v: InlineVec<u64, 8> = InlineVec::new();
                for i in 0..n {
                    v.push(black_box(i as u64));
                }
                v
            });
        });
        group.bench_with_input(BenchmarkId::new("SmallVec<_, 8>", n), &n, |b, &n| {
            b.iter(|| {
                let mut v: SmallVec<[u64; 8]> = SmallVec::new();
                for i in 0..n {
                    v.push(black_box(i as u64));
                }
                v
            });
        });
        group.bench_with_input(BenchmarkId::new("Vec", n), &n, |b, &n| {
            b.iter(|| {
                let mut v: Vec<u64> = Vec::new();
                for i in 0..n {
                    v.push(black_box(i as u64));
                }
                v
            });
        });
    }
    group.finish();
}

/// Summing the elements of an existing vector.
fn bench_iterate(c: &mut Criterion) {
    let mut group = c.benchmark_group("vec_iterate");
    for &n in LENGTHS {
        let inline: InlineVec<u64, 8> = (0..n as u64).collect();
        let small: SmallVec<[u64; 8]> = (0..n as u64).collect();
        let vec: Vec<u64> = (0..n as u64).collect();
        group.bench_with_input(BenchmarkId::new("InlineVec<_, 8>", n), &(), |b, _| {
            b.iter(|| black_box(&inline).iter().sum::<u64>());
        });
        group.bench_with_input(BenchmarkId::new("SmallVec<_, 8>", n), &(), |b, _| {
            b.iter(|| black_box(&small).iter().sum::<u64>());
        });
        group.bench_with_input(BenchmarkId::new("Vec", n), &(), |b, _| {
            b.iter(|| black_box(&vec).iter().sum::<u64>());
        });
    }
    group.finish();
}

/// Cloning a vector of `u64`s: an inline vector needs no allocation while it
/// is short, a `Vec` always needs one.
fn bench_clone(c: &mut Criterion) {
    let mut group = c.benchmark_group("vec_clone_u64");
    for &n in LENGTHS {
        let inline: InlineVec<u64, 8> = (0..n as u64).collect();
        let small: SmallVec<[u64; 8]> = (0..n as u64).collect();
        let vec: Vec<u64> = (0..n as u64).collect();
        group.bench_with_input(BenchmarkId::new("InlineVec<_, 8>", n), &(), |b, _| {
            b.iter(|| black_box(&inline).clone());
        });
        group.bench_with_input(BenchmarkId::new("SmallVec<_, 8>", n), &(), |b, _| {
            b.iter(|| black_box(&small).clone());
        });
        group.bench_with_input(BenchmarkId::new("Vec", n), &(), |b, _| {
            b.iter(|| black_box(&vec).clone());
        });
    }
    group.finish();
}

/// Inserting at the front, which shifts everything.
fn bench_insert_front(c: &mut Criterion) {
    let mut group = c.benchmark_group("vec_insert_front");
    for &n in &[4usize, 8, 32] {
        group.bench_with_input(BenchmarkId::new("InlineVec<_, 8>", n), &n, |b, &n| {
            b.iter_batched(
                || (0..n as u64).collect::<InlineVec<u64, 8>>(),
                |mut v| {
                    v.insert(0, black_box(99));
                    v
                },
                BatchSize::SmallInput,
            );
        });
        group.bench_with_input(BenchmarkId::new("SmallVec<_, 8>", n), &n, |b, &n| {
            b.iter_batched(
                || (0..n as u64).collect::<SmallVec<[u64; 8]>>(),
                |mut v| {
                    v.insert(0, black_box(99));
                    v
                },
                BatchSize::SmallInput,
            );
        });
        group.bench_with_input(BenchmarkId::new("Vec", n), &n, |b, &n| {
            b.iter_batched(
                || (0..n as u64).collect::<Vec<u64>>(),
                |mut v| {
                    v.insert(0, black_box(99));
                    v
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_push,
    bench_iterate,
    bench_clone,
    bench_insert_front
);
criterion_main!(benches);
