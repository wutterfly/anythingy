//! `LinearSet`: a small set backed by a `Vec`, for elements that are only `Eq`.
//!
//! Run with: `cargo run --example linear_set`

use anythingy::LinearSet;

fn main() {
    let mut seen = LinearSet::new();

    // Insert; `false` means it was already there.
    assert!(seen.insert("alice"));
    assert!(seen.insert("bob"));
    assert!(!seen.insert("alice"));

    // Look up and remove.
    assert!(seen.contains("bob"));
    assert!(seen.remove("bob"));
    assert_eq!(seen.len(), 1);

    // Set operations.
    let a = LinearSet::from([1, 2, 3]);
    let b = LinearSet::from([3, 4]);
    let union: Vec<_> = a.union(&b).collect();
    println!("union: {union:?}");
    println!("common: {:?}", a.intersection(&b).collect::<Vec<_>>());
    println!("only in a: {:?}", a.difference(&b).collect::<Vec<_>>());
    assert!(!a.is_disjoint(&b));

    // Operators build new sets.
    let both = &a | &b;
    assert_eq!(both.len(), 4);
}
