//! `SyncThingMap`: a `ThingMap` that can be shared between threads.
//!
//! Run with: `cargo run --example sync_thing_map`

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, RwLock};
use std::thread;

use anythingy::SyncThingMap;

struct Config {
    workers: usize,
}

fn main() {
    // Only `Send + Sync` values are accepted, so the map itself is
    // `Send + Sync` and can be shared.
    let mut resources = SyncThingMap::<24>::new();
    resources.insert(Config { workers: 4 });
    resources.insert(AtomicUsize::new(0));
    let resources = Arc::new(RwLock::new(resources));

    let workers = resources.read().unwrap().get::<Config>().unwrap().workers;
    let handles: Vec<_> = (0..workers)
        .map(|_| {
            let resources = Arc::clone(&resources);
            thread::spawn(move || {
                // Shared access: atomics can be changed through `&`.
                let resources = resources.read().unwrap();
                resources
                    .get::<AtomicUsize>()
                    .unwrap()
                    .fetch_add(1, Ordering::Relaxed);
            })
        })
        .collect();
    for handle in handles {
        handle.join().unwrap();
    }

    // Exclusive access, to add or replace values, goes through the lock.
    resources.write().unwrap().insert(String::from("done"));

    let resources = resources.read().unwrap();
    println!(
        "counted {}",
        resources
            .get::<AtomicUsize>()
            .unwrap()
            .load(Ordering::Relaxed)
    );
    println!("status: {}", resources.get::<String>().unwrap());

    // This would not compile: `Rc` is not `Send`.
    // resources.insert(std::rc::Rc::new(1));
}
