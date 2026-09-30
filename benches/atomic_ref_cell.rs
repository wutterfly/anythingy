use std::cell::RefCell;
use std::hint::black_box;
use std::sync::{Mutex, RwLock};
use std::thread;

use anythingy::AtomicRefCell;
use criterion::{Criterion, criterion_group, criterion_main};

const OPS: u64 = 10_000;

/// Single thread, no contention: the cost of taking and releasing a borrow.
fn bench_single_thread(c: &mut Criterion) {
    let mut group = c.benchmark_group("single_thread");

    group.bench_function("RefCell borrow (not thread-safe)", |b| {
        let cell = RefCell::new(1_u64);
        b.iter(|| {
            for _ in 0..OPS {
                black_box(*cell.borrow());
            }
        });
    });

    group.bench_function("AtomicRefCell borrow", |b| {
        let cell = AtomicRefCell::new(1_u64);
        b.iter(|| {
            for _ in 0..OPS {
                black_box(*cell.borrow());
            }
        });
    });

    group.bench_function("AtomicRefCell borrow_unchecked", |b| {
        let cell = AtomicRefCell::new(1_u64);
        b.iter(|| {
            for _ in 0..OPS {
                // SAFETY: nothing borrows the cell mutably.
                black_box(unsafe { *cell.borrow_unchecked() });
            }
        });
    });

    group.bench_function("RwLock read", |b| {
        let lock = RwLock::new(1_u64);
        b.iter(|| {
            for _ in 0..OPS {
                black_box(*lock.read().unwrap());
            }
        });
    });

    group.bench_function("Mutex lock", |b| {
        let lock = Mutex::new(1_u64);
        b.iter(|| {
            for _ in 0..OPS {
                black_box(*lock.lock().unwrap());
            }
        });
    });

    group.bench_function("RefCell borrow_mut (not thread-safe)", |b| {
        let cell = RefCell::new(0_u64);
        b.iter(|| {
            for _ in 0..OPS {
                *cell.borrow_mut() += black_box(1);
            }
        });
    });

    group.bench_function("AtomicRefCell borrow_mut", |b| {
        let cell = AtomicRefCell::new(0_u64);
        b.iter(|| {
            for _ in 0..OPS {
                *cell.borrow_mut() += black_box(1);
            }
        });
    });

    group.bench_function("RwLock write", |b| {
        let lock = RwLock::new(0_u64);
        b.iter(|| {
            for _ in 0..OPS {
                *lock.write().unwrap() += black_box(1);
            }
        });
    });

    group.bench_function("Mutex lock (write)", |b| {
        let lock = Mutex::new(0_u64);
        b.iter(|| {
            for _ in 0..OPS {
                *lock.lock().unwrap() += black_box(1);
            }
        });
    });

    group.finish();
}

/// Several threads reading the same value at once, the case that an
/// `AtomicRefCell` or `RwLock` is for: every read touches the same counter.
fn bench_contended_readers(c: &mut Criterion) {
    let mut group = c.benchmark_group("contended_readers");
    const PER_THREAD: u64 = 5_000;

    for &threads in &[1_usize, 2, 4, 8] {
        group.bench_function(format!("AtomicRefCell/{threads}"), |b| {
            let cell = AtomicRefCell::new(1_u64);
            b.iter(|| {
                thread::scope(|s| {
                    for _ in 0..threads {
                        s.spawn(|| {
                            for _ in 0..PER_THREAD {
                                black_box(*cell.borrow());
                            }
                        });
                    }
                });
            });
        });

        group.bench_function(format!("RwLock/{threads}"), |b| {
            let lock = RwLock::new(1_u64);
            b.iter(|| {
                thread::scope(|s| {
                    for _ in 0..threads {
                        s.spawn(|| {
                            for _ in 0..PER_THREAD {
                                black_box(*lock.read().unwrap());
                            }
                        });
                    }
                });
            });
        });
    }

    group.finish();
}

/// Several threads writing the same value. The `AtomicRefCell` threads retry
/// instead of waiting, which is how it is meant to be used for writes.
fn bench_contended_writers(c: &mut Criterion) {
    let mut group = c.benchmark_group("contended_writers");
    const PER_THREAD: u64 = 2_000;

    for &threads in &[1_usize, 2, 4, 8] {
        group.bench_function(format!("AtomicRefCell (try_borrow_mut)/{threads}"), |b| {
            let cell = AtomicRefCell::new(0_u64);
            b.iter(|| {
                thread::scope(|s| {
                    for _ in 0..threads {
                        s.spawn(|| {
                            for _ in 0..PER_THREAD {
                                loop {
                                    if let Ok(mut value) = cell.try_borrow_mut() {
                                        *value += 1;
                                        break;
                                    }
                                    std::hint::spin_loop();
                                }
                            }
                        });
                    }
                });
            });
        });

        group.bench_function(format!("RwLock write/{threads}"), |b| {
            let lock = RwLock::new(0_u64);
            b.iter(|| {
                thread::scope(|s| {
                    for _ in 0..threads {
                        s.spawn(|| {
                            for _ in 0..PER_THREAD {
                                *lock.write().unwrap() += 1;
                            }
                        });
                    }
                });
            });
        });

        group.bench_function(format!("Mutex/{threads}"), |b| {
            let lock = Mutex::new(0_u64);
            b.iter(|| {
                thread::scope(|s| {
                    for _ in 0..threads {
                        s.spawn(|| {
                            for _ in 0..PER_THREAD {
                                *lock.lock().unwrap() += 1;
                            }
                        });
                    }
                });
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_single_thread,
    bench_contended_readers,
    bench_contended_writers
);
criterion_main!(benches);
