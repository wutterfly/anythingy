use std::hint::black_box;

use anythingy::FreeList;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

const BLOCK: u64 = 1 << 30;

/// Number of live allocations the list is fragmented into before measuring.
const FRAGMENTS: &[u64] = &[1, 16, 256, 4096];

/// A list with `count` free ranges: allocations of 256 bytes next to each
/// other, and every second one freed.
fn fragmented(count: u64) -> (FreeList, Vec<u64>) {
    let mut list = FreeList::<u64>::new(BLOCK);
    let offsets: Vec<u64> = (0..count * 2)
        .map(|_| list.allocate(256, 16).unwrap())
        .collect();
    let mut kept = Vec::new();
    for (i, &offset) in offsets.iter().enumerate() {
        if i % 2 == 0 {
            list.free(offset, 256);
        } else {
            kept.push(offset);
        }
    }
    (list, kept)
}

/// Allocate and free the same size, which finds the best of `count` ranges.
fn bench_allocate_free(c: &mut Criterion) {
    let mut group = c.benchmark_group("allocate_free");
    for &count in FRAGMENTS {
        group.bench_with_input(BenchmarkId::new("FreeList", count), &count, |b, &count| {
            let (mut list, _kept) = fragmented(count);
            b.iter(|| {
                let offset = list.allocate(black_box(128), 16).unwrap();
                list.free(offset, 128);
            });
        });
    }
    group.finish();
}

/// An allocation that does not fit anywhere, in a list of `count` small free ranges.
fn bench_too_big(c: &mut Criterion) {
    let mut group = c.benchmark_group("allocate_too_big");
    for &count in FRAGMENTS {
        group.bench_with_input(BenchmarkId::new("FreeList", count), &count, |b, &count| {
            let (mut list, _kept) = fragmented(count);
            // The big tail of the block is gone, only the 256-byte holes are left.
            list.allocate(BLOCK - count * 512 - 256, 1).unwrap();
            b.iter(|| list.allocate(black_box(1024), 16));
        });
    }
    group.finish();
}

/// Allocate and free a size that exactly matches one of the free ranges, the first one.
fn bench_exact_fit(c: &mut Criterion) {
    let mut group = c.benchmark_group("allocate_exact_fit");
    for &count in FRAGMENTS {
        group.bench_with_input(BenchmarkId::new("FreeList", count), &count, |b, &count| {
            let (mut list, _kept) = fragmented(count);
            b.iter(|| {
                let offset = list.allocate(black_box(256), 16).unwrap();
                list.free(offset, 256);
            });
        });
    }
    group.finish();
}

/// Fill a fresh block with small allocations, then free them in order.
fn bench_fill_and_free(c: &mut Criterion) {
    let mut group = c.benchmark_group("fill_and_free");
    group.bench_function("1000 allocations", |b| {
        b.iter(|| {
            let mut list = FreeList::<u64>::new(BLOCK);
            let offsets: Vec<u64> = (0..1000)
                .map(|_| list.allocate(black_box(512), 64).unwrap())
                .collect();
            for offset in offsets {
                list.free(offset, 512);
            }
            list
        });
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_allocate_free,
    bench_too_big,
    bench_exact_fit,
    bench_fill_and_free
);
criterion_main!(benches);
