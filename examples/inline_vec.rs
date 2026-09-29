//! `InlineVec`: a vector that keeps its first few elements inline, without
//! allocating, and moves to the heap only when it grows past that.
//!
//! Run with: `cargo run --example inline_vec`

use anythingy::InlineVec;

fn main() {
    // Room for 4 elements inline.
    let mut v: InlineVec<u32, 4> = InlineVec::new();

    // Up to 4 elements: no heap allocation.
    v.push(1);
    v.push(2);
    v.push(3);
    println!("spilled: {}", v.spilled()); // false

    // It works like a `Vec`, and like a slice.
    v.insert(0, 10);
    assert_eq!(v.pop(), Some(3));
    println!("sum: {}", v.iter().sum::<u32>());

    // Growing past the inline capacity moves the elements to the heap.
    v.extend([7, 8, 9]);
    println!("spilled: {}", v.spilled()); // true
    v.sort(); // slice methods work too
    assert_eq!(v, [1, 2, 7, 8, 9, 10]);

    // Drain a range, keep the rest.
    let removed: Vec<_> = v.drain(1..3).collect();
    assert_eq!(removed, vec![2, 7]);
    assert_eq!(v, [1, 8, 9, 10]);

    // Once spilled it stays on the heap, until you shrink it back.
    v.shrink_to_fit();
    println!("spilled after shrink_to_fit: {}", v.spilled()); // false
}
