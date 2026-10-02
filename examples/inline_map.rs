//! `InlineMap`: a hash map that keeps its first few entries inline.
//!
//! Run with: `cargo run --example inline_map`

use anythingy::InlineMap;

fn main() {
    // Room for four entries inside the map itself, so no allocation yet.
    let mut stock: InlineMap<&str, u32, 4> = InlineMap::new();

    // The same API as `HashMap`.
    stock.insert("apples", 3);
    stock.insert("pears", 1);
    *stock.entry("apples").or_insert(0) += 2;
    assert_eq!(stock.get("apples"), Some(&5));
    assert!(!stock.spilled());

    // The fifth entry moves all of them into a hash map.
    stock.insert("plums", 7);
    stock.insert("cherries", 9);
    stock.insert("figs", 2);
    assert!(stock.spilled());

    // Iteration order is unspecified, as for a `HashMap`.
    for (name, count) in &stock {
        println!("{name}: {count}");
    }

    assert_eq!(stock.remove("figs"), Some(2));
    assert_eq!(stock.len(), 4);
}
