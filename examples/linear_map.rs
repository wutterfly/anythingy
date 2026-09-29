//! `LinearMap`: a small map backed by a `Vec`, for keys that are only `Eq`.
//!
//! Run with: `cargo run --example linear_map`

use anythingy::LinearMap;

fn main() {
    let mut ages = LinearMap::new();

    // Insert; the old value is returned if the key already existed.
    ages.insert("alice", 30);
    ages.insert("bob", 25);
    assert_eq!(ages.insert("alice", 31), Some(30));

    // Look up.
    assert_eq!(ages.get("alice"), Some(&31));
    assert!(ages.contains_key("bob"));

    // Update in place.
    *ages.get_mut("bob").unwrap() += 1;

    // Iterate.
    for (name, age) in &ages {
        println!("{name} is {age}");
    }

    // Remove (does not preserve insertion order).
    assert_eq!(ages.remove("bob"), Some(26));
    assert_eq!(ages.len(), 1);
}
