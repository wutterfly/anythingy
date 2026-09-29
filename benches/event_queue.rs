use std::hint::black_box;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use anythingy::EventQueue;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};

const PRODUCER_COUNTS: &[usize] = &[1, 2, 4, 8];

/// Single-threaded push throughput: no contention at all, just the raw
/// per-push overhead of each structure.
fn bench_single_thread_push(c: &mut Criterion) {
    let mut group = c.benchmark_group("single_thread_push");
    const N: usize = 10_000;

    group.bench_function("Vec (baseline, no sync)", |b| {
        b.iter_batched(
            Vec::new,
            |mut v| {
                for i in 0..N {
                    v.push(black_box(i));
                }
                v
            },
            BatchSize::LargeInput,
        );
    });

    group.bench_function("EventQueue", |b| {
        b.iter_batched(
            EventQueue::new,
            |q| {
                for i in 0..N {
                    q.push(black_box(i));
                }
                q
            },
            BatchSize::LargeInput,
        );
    });

    group.bench_function("Mutex<Vec>", |b| {
        b.iter_batched(
            || Mutex::new(Vec::new()),
            |m| {
                for i in 0..N {
                    m.lock().unwrap().push(black_box(i));
                }
                m
            },
            BatchSize::LargeInput,
        );
    });

    group.bench_function("crossbeam unbounded", |b| {
        b.iter_batched(
            crossbeam_channel::unbounded::<usize>,
            |(tx, rx)| {
                for i in 0..N {
                    tx.send(black_box(i)).unwrap();
                }
                (tx, rx)
            },
            BatchSize::LargeInput,
        );
    });

    group.finish();
}

/// Multi-producer push throughput at increasing producer counts. This is
/// where sharded, per-thread accumulation (EventQueue) should pull ahead
/// of anything that serializes producers on one shared structure.
fn bench_multi_thread_push(c: &mut Criterion) {
    let mut group = c.benchmark_group("multi_thread_push");
    const PER_THREAD: usize = 2_000;

    for &producers in PRODUCER_COUNTS {
        group.bench_with_input(
            BenchmarkId::new("EventQueue", producers),
            &producers,
            |b, &producers| {
                b.iter_batched(
                    || Arc::new(EventQueue::new()),
                    |q| {
                        thread::scope(|scope| {
                            for _ in 0..producers {
                                let q = Arc::clone(&q);
                                scope.spawn(move || {
                                    for i in 0..PER_THREAD {
                                        q.push(black_box(i));
                                    }
                                });
                            }
                        });
                        q
                    },
                    BatchSize::LargeInput,
                );
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Mutex<Vec>", producers),
            &producers,
            |b, &producers| {
                b.iter_batched(
                    || Arc::new(Mutex::new(Vec::new())),
                    |m| {
                        thread::scope(|scope| {
                            for _ in 0..producers {
                                let m = Arc::clone(&m);
                                scope.spawn(move || {
                                    for i in 0..PER_THREAD {
                                        m.lock().unwrap().push(black_box(i));
                                    }
                                });
                            }
                        });
                        m
                    },
                    BatchSize::LargeInput,
                );
            },
        );

        group.bench_with_input(
            BenchmarkId::new("crossbeam", producers),
            &producers,
            |b, &producers| {
                b.iter_batched(
                    crossbeam_channel::unbounded::<usize>,
                    |(tx, rx)| {
                        thread::scope(|scope| {
                            for _ in 0..producers {
                                let tx = tx.clone();
                                scope.spawn(move || {
                                    for i in 0..PER_THREAD {
                                        tx.send(black_box(i)).unwrap();
                                    }
                                });
                            }
                        });
                        rx
                    },
                    BatchSize::LargeInput,
                );
            },
        );
    }
    group.finish();
}

/// Cost of a single "drain everything accumulated" call, after filling
/// each structure from one thread.
fn bench_drain(c: &mut Criterion) {
    let mut group = c.benchmark_group("drain");
    const N: usize = 50_000;

    group.bench_function("EventQueue", |b| {
        b.iter_batched(
            || {
                let q = EventQueue::new();
                for i in 0..N {
                    q.push(i);
                }
                q
            },
            |q| black_box(q.drain()),
            BatchSize::LargeInput,
        );
    });

    group.bench_function("Mutex<Vec> (mem::take)", |b| {
        b.iter_batched(
            || {
                let m = Mutex::new(Vec::new());
                {
                    let mut guard = m.lock().unwrap();
                    for i in 0..N {
                        guard.push(i);
                    }
                }
                m
            },
            |m| black_box(std::mem::take(&mut *m.lock().unwrap())),
            BatchSize::LargeInput,
        );
    });

    group.bench_function("crossbeam (try_recv loop)", |b| {
        b.iter_batched(
            || {
                let (tx, rx) = crossbeam_channel::unbounded();
                for i in 0..N {
                    tx.send(i).unwrap();
                }
                rx
            },
            |rx| {
                let mut v = Vec::with_capacity(N);
                while let Ok(x) = rx.try_recv() {
                    v.push(x);
                }
                black_box(v)
            },
            BatchSize::LargeInput,
        );
    });

    group.finish();
}

/// End-to-end "producers push a batch, then one drain collects it all"
/// round trip, at increasing producer counts -- the shape closest to real
/// event-bus usage (as opposed to the pure push- or drain-only benches
/// above).
fn bench_produce_then_drain(c: &mut Criterion) {
    let mut group = c.benchmark_group("produce_then_drain");
    const PER_THREAD: usize = 2_000;

    for &producers in PRODUCER_COUNTS {
        group.bench_with_input(
            BenchmarkId::new("EventQueue", producers),
            &producers,
            |b, &producers| {
                b.iter_batched(
                    || Arc::new(EventQueue::new()),
                    |q| {
                        thread::scope(|scope| {
                            for _ in 0..producers {
                                let q = Arc::clone(&q);
                                scope.spawn(move || {
                                    for i in 0..PER_THREAD {
                                        q.push(black_box(i));
                                    }
                                });
                            }
                        });
                        black_box(q.drain())
                    },
                    BatchSize::LargeInput,
                );
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Mutex<Vec>", producers),
            &producers,
            |b, &producers| {
                b.iter_batched(
                    || Arc::new(Mutex::new(Vec::new())),
                    |m| {
                        thread::scope(|scope| {
                            for _ in 0..producers {
                                let m = Arc::clone(&m);
                                scope.spawn(move || {
                                    for i in 0..PER_THREAD {
                                        m.lock().unwrap().push(black_box(i));
                                    }
                                });
                            }
                        });
                        black_box(std::mem::take(&mut *m.lock().unwrap()))
                    },
                    BatchSize::LargeInput,
                );
            },
        );

        group.bench_with_input(
            BenchmarkId::new("crossbeam", producers),
            &producers,
            |b, &producers| {
                b.iter_batched(
                    crossbeam_channel::unbounded::<usize>,
                    |(tx, rx)| {
                        thread::scope(|scope| {
                            for _ in 0..producers {
                                let tx = tx.clone();
                                scope.spawn(move || {
                                    for i in 0..PER_THREAD {
                                        tx.send(black_box(i)).unwrap();
                                    }
                                });
                            }
                        });
                        drop(tx);
                        let mut v = Vec::with_capacity(producers * PER_THREAD);
                        while let Ok(x) = rx.try_recv() {
                            v.push(x);
                        }
                        black_box(v)
                    },
                    BatchSize::LargeInput,
                );
            },
        );
    }
    group.finish();
}

/// Steady state: the same queue is filled and drained over and over, the way
/// a game loop or an event bus uses it. Each round pushes `PER_ROUND` events
/// from one thread; only the drain (and reading the events) is timed, since
/// that is the part that differs between the variants. The pushes into a
/// queue that keeps its buffers are covered by `single_thread_push`.
fn bench_steady_state(c: &mut Criterion) {
    let mut group = c.benchmark_group("steady_state_drain");
    const PER_ROUND: usize = 10_000;

    group.bench_function("EventQueue::drain", |b| {
        let q = EventQueue::new();
        b.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                for i in 0..PER_ROUND {
                    q.push(i);
                }
                let start = Instant::now();
                let events = q.drain();
                black_box(events.iter().sum::<usize>());
                total += start.elapsed();
            }
            total
        });
    });

    group.bench_function("EventQueue::drain_into (reused Vec)", |b| {
        let q = EventQueue::new();
        let mut out = Vec::new();
        b.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                for i in 0..PER_ROUND {
                    q.push(i);
                }
                let start = Instant::now();
                out.clear();
                q.drain_into(&mut out);
                black_box(out.iter().sum::<usize>());
                total += start.elapsed();
            }
            total
        });
    });

    group.bench_function("EventQueue::drain_each", |b| {
        let q = EventQueue::new();
        b.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                for i in 0..PER_ROUND {
                    q.push(i);
                }
                let start = Instant::now();
                let mut sum = 0;
                q.drain_each(|batch| sum += batch.iter().sum::<usize>());
                black_box(sum);
                total += start.elapsed();
            }
            total
        });
    });

    group.bench_function("Mutex<Vec> (swap with reused Vec)", |b| {
        let m = Mutex::new(Vec::new());
        let mut out = Vec::new();
        b.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                for i in 0..PER_ROUND {
                    m.lock().unwrap().push(i);
                }
                let start = Instant::now();
                out.clear();
                std::mem::swap(&mut *m.lock().unwrap(), &mut out);
                black_box(out.iter().sum::<usize>());
                total += start.elapsed();
            }
            total
        });
    });

    group.finish();
}

/// Like `steady_state_round`, but with several producer threads, so that a
/// drain has more than one buffer to collect. Thread start-up is part of
/// every round, and is the same for all variants.
fn bench_steady_state_threads(c: &mut Criterion) {
    let mut group = c.benchmark_group("steady_state_round_4_threads");
    const THREADS: usize = 4;
    const PER_THREAD: usize = 2_500;

    fn produce(q: &EventQueue<usize>) {
        thread::scope(|s| {
            for _ in 0..THREADS {
                s.spawn(|| {
                    for i in 0..PER_THREAD {
                        q.push(i);
                    }
                });
            }
        });
    }

    group.bench_function("EventQueue::drain", |b| {
        let q = EventQueue::new();
        b.iter(|| {
            produce(&q);
            black_box(q.drain().iter().sum::<usize>())
        });
    });

    group.bench_function("EventQueue::drain_into (reused Vec)", |b| {
        let q = EventQueue::new();
        let mut out = Vec::new();
        b.iter(|| {
            produce(&q);
            out.clear();
            q.drain_into(&mut out);
            black_box(out.iter().sum::<usize>())
        });
    });

    group.bench_function("EventQueue::drain_each", |b| {
        let q = EventQueue::new();
        b.iter(|| {
            produce(&q);
            let mut sum = 0;
            q.drain_each(|batch| sum += batch.iter().sum::<usize>());
            black_box(sum)
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_single_thread_push,
    bench_multi_thread_push,
    bench_drain,
    bench_produce_then_drain,
    bench_steady_state,
    bench_steady_state_threads
);
criterion_main!(benches);
