use std::any::Any;
use std::hint::black_box;

use anythingy::Thing;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};

/// 8 bytes: always fits inline in the default `Thing`.
type Small = u64;
/// 24 bytes, no heap pointer of its own: still inline in the default `Thing`.
type Medium = [u64; 3];
/// 64 bytes: too large for the default `Thing`, so it gets boxed.
type Large = [u64; 8];

fn medium() -> Medium {
    [1, 2, 3]
}

fn large() -> Large {
    [1, 2, 3, 4, 5, 6, 7, 8]
}

/// Creating a value and dropping it again (allocation cost dominates for boxed variants).
fn bench_create_drop(c: &mut Criterion) {
    let mut group = c.benchmark_group("thing/create_drop");

    macro_rules! case {
        ($name:literal, $make:expr) => {
            group.bench_function(BenchmarkId::new("plain", $name), |b| {
                b.iter(|| black_box($make))
            });
            group.bench_function(BenchmarkId::new("Box<dyn Any>", $name), |b| {
                b.iter(|| drop(black_box(Box::new($make) as Box<dyn Any>)))
            });
            group.bench_function(BenchmarkId::new("Thing", $name), |b| {
                b.iter(|| drop(black_box(Thing::<24>::new($make))))
            });
        };
    }

    case!("u64 (inline)", black_box(7u64));
    case!("[u64;3] (inline)", black_box(medium()));
    case!("[u64;8] (boxed)", black_box(large()));
    group.bench_function(BenchmarkId::new("plain", "String"), |b| {
        b.iter(|| drop(black_box(String::from("hello world"))))
    });
    group.bench_function(BenchmarkId::new("Box<dyn Any>", "String"), |b| {
        b.iter(|| {
            drop(black_box(
                Box::new(String::from("hello world")) as Box<dyn Any>
            ))
        })
    });
    group.bench_function(BenchmarkId::new("Thing", "String"), |b| {
        b.iter(|| drop(black_box(Thing::<24>::new(String::from("hello world")))))
    });
    group.finish();
}

/// Read access through a shared reference to an already-constructed value.
fn bench_read(c: &mut Criterion) {
    let mut group = c.benchmark_group("thing/read_ref");

    macro_rules! case {
        ($name:literal, $ty:ty, $val:expr) => {{
            let plain: $ty = $val;
            let boxed_any: Box<dyn Any> = Box::<$ty>::new($val);
            let thing = Thing::<24>::new::<$ty>($val);
            group.bench_function(BenchmarkId::new("plain", $name), |b| {
                b.iter(|| black_box(&plain).iter_sum())
            });
            group.bench_function(BenchmarkId::new("Box<dyn Any> downcast_ref", $name), |b| {
                b.iter(|| {
                    black_box(&boxed_any)
                        .downcast_ref::<$ty>()
                        .unwrap()
                        .iter_sum()
                })
            });
            group.bench_function(BenchmarkId::new("Thing get_ref", $name), |b| {
                b.iter(|| black_box(&thing).get_ref::<$ty>().iter_sum())
            });
            group.bench_function(BenchmarkId::new("Thing try_get_ref", $name), |b| {
                b.iter(|| black_box(&thing).try_get_ref::<$ty>().unwrap().iter_sum())
            });
            group.bench_function(BenchmarkId::new("Thing get_ref_unchecked", $name), |b| {
                // SAFETY: `thing` was created from a `$ty`.
                b.iter(|| unsafe { black_box(&thing).get_ref_unchecked::<$ty>() }.iter_sum())
            });
        }};
    }

    case!("u64 (inline)", Small, 7);
    case!("[u64;3] (inline)", Medium, medium());
    case!("[u64;8] (boxed)", Large, large());
    group.finish();
}

/// Mutation through a mutable reference.
fn bench_write(c: &mut Criterion) {
    let mut group = c.benchmark_group("thing/write_mut");

    macro_rules! case {
        ($name:literal, $ty:ty, $val:expr) => {{
            let mut plain: $ty = $val;
            let mut boxed_any: Box<dyn Any> = Box::<$ty>::new($val);
            let mut thing = Thing::<24>::new::<$ty>($val);
            group.bench_function(BenchmarkId::new("plain", $name), |b| {
                b.iter(|| black_box(&mut plain).bump())
            });
            group.bench_function(BenchmarkId::new("Box<dyn Any> downcast_mut", $name), |b| {
                b.iter(|| {
                    black_box(&mut boxed_any)
                        .downcast_mut::<$ty>()
                        .unwrap()
                        .bump()
                })
            });
            group.bench_function(BenchmarkId::new("Thing get_mut", $name), |b| {
                b.iter(|| black_box(&mut thing).get_mut::<$ty>().bump())
            });
            group.bench_function(BenchmarkId::new("Thing get_mut_unchecked", $name), |b| {
                // SAFETY: `thing` was created from a `$ty`.
                b.iter(|| unsafe { black_box(&mut thing).get_mut_unchecked::<$ty>() }.bump())
            });
        }};
    }

    case!("u64 (inline)", Small, 7);
    case!("[u64;3] (inline)", Medium, medium());
    case!("[u64;8] (boxed)", Large, large());
    group.finish();
}

/// Moving the value back out (consumes the container).
fn bench_take(c: &mut Criterion) {
    let mut group = c.benchmark_group("thing/take");

    macro_rules! case {
        ($name:literal, $ty:ty, $val:expr) => {
            group.bench_function(BenchmarkId::new("Box<dyn Any> downcast", $name), |b| {
                b.iter_batched(
                    || Box::<$ty>::new($val) as Box<dyn Any>,
                    |v| *v.downcast::<$ty>().unwrap(),
                    BatchSize::SmallInput,
                )
            });
            group.bench_function(BenchmarkId::new("Thing get", $name), |b| {
                b.iter_batched(
                    || Thing::<24>::new::<$ty>($val),
                    |v| v.get::<$ty>(),
                    BatchSize::SmallInput,
                )
            });
            group.bench_function(BenchmarkId::new("Thing get_unchecked", $name), |b| {
                b.iter_batched(
                    || Thing::<24>::new::<$ty>($val),
                    // SAFETY: the `Thing` was created from a `$ty`.
                    |v| unsafe { v.get_unchecked::<$ty>() },
                    BatchSize::SmallInput,
                )
            });
        };
    }

    case!("u64 (inline)", Small, 7);
    case!("[u64;3] (inline)", Medium, medium());
    case!("[u64;8] (boxed)", Large, large());
    group.finish();
}

/// A heterogeneous `Vec` of erased values, iterated and read: the typical use case.
fn bench_heterogeneous_vec(c: &mut Criterion) {
    const N: usize = 1024;
    let mut group = c.benchmark_group("thing/vec_of_erased_sum");

    let boxed: Vec<Box<dyn Any>> = (0..N as u64).map(|i| Box::new(i) as Box<dyn Any>).collect();
    let things: Vec<Thing<8>> = (0..N as u64).map(Thing::<8>::new).collect();
    let things_default: Vec<Thing> = (0..N as u64).map(Thing::new).collect();
    let plain: Vec<u64> = (0..N as u64).collect();

    group.bench_function("Vec<u64> (baseline)", |b| {
        b.iter(|| black_box(&plain).iter().sum::<u64>())
    });
    group.bench_function("Vec<Box<dyn Any>>", |b| {
        b.iter(|| {
            black_box(&boxed)
                .iter()
                .map(|v| *v.downcast_ref::<u64>().unwrap())
                .sum::<u64>()
        })
    });
    group.bench_function("Vec<Thing<8>>", |b| {
        b.iter(|| {
            black_box(&things)
                .iter()
                .map(|v| *v.get_ref::<u64>())
                .sum::<u64>()
        })
    });
    group.bench_function("Vec<Thing<24>>", |b| {
        b.iter(|| {
            black_box(&things_default)
                .iter()
                .map(|v| *v.get_ref::<u64>())
                .sum::<u64>()
        })
    });
    group.finish();
}

trait Ops {
    fn iter_sum(&self) -> u64;
    fn bump(&mut self);
}

impl Ops for u64 {
    fn iter_sum(&self) -> u64 {
        *self
    }
    fn bump(&mut self) {
        *self = self.wrapping_add(1);
    }
}

impl<const N: usize> Ops for [u64; N] {
    fn iter_sum(&self) -> u64 {
        self.iter().sum()
    }
    fn bump(&mut self) {
        self[0] = self[0].wrapping_add(1);
    }
}

criterion_group!(
    benches,
    bench_create_drop,
    bench_read,
    bench_write,
    bench_take,
    bench_heterogeneous_vec
);
criterion_main!(benches);
