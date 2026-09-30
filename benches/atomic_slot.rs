use std::hint::black_box;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

use anythingy::AtomicSlot;
use criterion::{Criterion, criterion_group, criterion_main};

/// A value that needs a heap allocation of its own, to see what dropping the
/// replaced value costs.
type Boxed = Box<[u64; 4]>;

const OPS: u64 = 10_000;

/// Single thread, no contention: the raw per-operation overhead.
fn bench_single_thread(c: &mut Criterion) {
    let mut group = c.benchmark_group("single_thread");

    group.bench_function("AtomicSlot push (u64)", |b| {
        let slot = AtomicSlot::new();
        b.iter(|| {
            for i in 0..OPS {
                slot.push(black_box(i));
            }
        });
    });

    group.bench_function("Mutex<Option> push (u64)", |b| {
        let slot = Mutex::new(None);
        b.iter(|| {
            for i in 0..OPS {
                *slot.lock().unwrap() = Some(black_box(i));
            }
        });
    });

    group.bench_function("AtomicSlot push+take (u64)", |b| {
        let slot = AtomicSlot::new();
        b.iter(|| {
            for i in 0..OPS {
                slot.push(black_box(i));
                black_box(slot.take());
            }
        });
    });

    group.bench_function("Mutex<Option> push+take (u64)", |b| {
        let slot = Mutex::new(None);
        b.iter(|| {
            for i in 0..OPS {
                *slot.lock().unwrap() = Some(black_box(i));
                black_box(slot.lock().unwrap().take());
            }
        });
    });

    group.bench_function("AtomicSlot push (Box, drops the replaced one)", |b| {
        let slot = AtomicSlot::new();
        b.iter(|| {
            for i in 0..OPS {
                slot.push(Boxed::new([black_box(i); 4]));
            }
        });
    });

    group.bench_function("Mutex<Option> push (Box, drops the replaced one)", |b| {
        let slot = Mutex::new(None);
        b.iter(|| {
            for i in 0..OPS {
                *slot.lock().unwrap() = Some(Boxed::new([black_box(i); 4]));
            }
        });
    });

    group.bench_function("AtomicSlot take (empty)", |b| {
        let slot = AtomicSlot::<u64>::new();
        b.iter(|| {
            for _ in 0..OPS {
                black_box(slot.take());
            }
        });
    });

    group.bench_function("Mutex<Option> take (empty)", |b| {
        let slot = Mutex::<Option<u64>>::new(None);
        b.iter(|| {
            for _ in 0..OPS {
                black_box(slot.lock().unwrap().take());
            }
        });
    });

    group.finish();
}

/// Several threads pushing into the same slot at once, with one thread taking
/// from it, the shape the slot is meant for: producers with "latest value
/// wins", and one consumer that polls.
fn bench_contended(c: &mut Criterion) {
    let mut group = c.benchmark_group("contended_push_with_consumer");
    const PER_THREAD: u64 = 2_500;

    for &producers in &[1_usize, 2, 4, 8] {
        group.bench_function(format!("AtomicSlot/{producers}"), |b| {
            b.iter(|| {
                let slot = AtomicSlot::new();
                let done = AtomicBool::new(false);
                thread::scope(|s| {
                    s.spawn(|| {
                        while !done.load(Ordering::Acquire) {
                            black_box(slot.take());
                        }
                    });
                    thread::scope(|inner| {
                        for _ in 0..producers {
                            inner.spawn(|| {
                                for i in 0..PER_THREAD {
                                    slot.push(black_box(i));
                                }
                            });
                        }
                    });
                    done.store(true, Ordering::Release);
                });
            });
        });

        group.bench_function(format!("Mutex<Option>/{producers}"), |b| {
            b.iter(|| {
                let slot = Mutex::new(None);
                let done = AtomicBool::new(false);
                thread::scope(|s| {
                    s.spawn(|| {
                        while !done.load(Ordering::Acquire) {
                            black_box(slot.lock().unwrap().take());
                        }
                    });
                    thread::scope(|inner| {
                        for _ in 0..producers {
                            inner.spawn(|| {
                                for i in 0..PER_THREAD {
                                    *slot.lock().unwrap() = Some(black_box(i));
                                }
                            });
                        }
                    });
                    done.store(true, Ordering::Release);
                });
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_single_thread, bench_contended);
criterion_main!(benches);
