//! `EventQueue`: many threads push events, one place drains them all.
//!
//! Run with: `cargo run --example event_queue`

use std::thread;

use anythingy::EventQueue;

fn main() {
    let queue = EventQueue::new();

    // Any number of threads can push through a shared reference.
    thread::scope(|scope| {
        for worker in 0..3 {
            let queue = &queue;
            scope.spawn(move || {
                queue.push(format!("worker {worker}: started"));
                queue.push(format!("worker {worker}: done"));
            });
        }
    });

    // Check how many events are waiting.
    println!("{} events pending", queue.len());

    // Take everything pushed so far. Each thread's own events keep their
    // order; the order between threads is unspecified.
    for event in queue.drain() {
        println!("{event}");
    }

    assert!(queue.is_empty());
}
