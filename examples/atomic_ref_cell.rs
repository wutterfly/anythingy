//! `AtomicRefCell`: a `RefCell` that can be shared between threads.
//!
//! Run with: `cargo run --example atomic_ref_cell`

use std::thread;

use anythingy::AtomicRefCell;

fn main() {
    let scores = AtomicRefCell::new(Vec::<u32>::new());

    thread::scope(|s| {
        // Several threads add to the same vector. A conflicting borrow never
        // waits: `try_borrow_mut` reports it, and the thread tries again.
        for player in 0..4 {
            let scores = &scores;
            s.spawn(move || {
                loop {
                    if let Ok(mut scores) = scores.try_borrow_mut() {
                        scores.push(player * 10);
                        break;
                    }
                }
            });
        }
    });

    // Any number of shared borrows at once.
    let first = scores.borrow();
    let second = scores.borrow();
    println!("{} scores, {} seen twice", first.len(), second.len());

    // An exclusive borrow is refused while they are alive.
    assert!(scores.try_borrow_mut().is_err());
    drop((first, second));

    scores.borrow_mut().sort_unstable();
    println!("sorted: {:?}", *scores.borrow());
}
