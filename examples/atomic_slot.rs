//! `AtomicSlot`: a mailbox between threads that only keeps the latest value.
//!
//! Run with: `cargo run --example atomic_slot`

use std::thread;
use std::time::Duration;

use anythingy::AtomicSlot;

struct Reading {
    sequence: u32,
    celsius: f32,
}

fn main() {
    let latest = AtomicSlot::new();

    thread::scope(|s| {
        // A sensor thread publishes readings. Each `push` replaces the
        // previous reading if nobody has taken it yet.
        s.spawn(|| {
            for sequence in 1..=5 {
                latest.push(Reading {
                    sequence,
                    celsius: 20.0 + sequence as f32,
                });
                thread::sleep(Duration::from_millis(20));
            }
        });

        // The main thread polls. `take` returns the newest reading, or `None`
        // if nothing new has arrived since the last `take`.
        let mut last = 0;
        while last < 5 {
            if let Some(reading) = latest.take() {
                println!("{:.1} C (reading {})", reading.celsius, reading.sequence);
                last = reading.sequence;
            }
            thread::sleep(Duration::from_millis(5));
        }
    });

    // The slot is empty again.
    assert!(latest.take().is_none());
}
