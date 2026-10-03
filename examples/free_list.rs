//! `FreeList`: handing out parts of one block of memory.
//!
//! Run with: `cargo run --example free_list`

use anythingy::FreeList;

fn main() {
    // A block of 1 KiB. The list only does the bookkeeping, the memory itself
    // (a buffer, a GPU allocation, a file) is up to the caller.
    let mut list = FreeList::<u64>::new(1024);

    let a = list.allocate(100, 1).unwrap();
    let b = list.allocate(200, 64).unwrap();
    let c = list.allocate(100, 1).unwrap();
    println!("a at {a}, b at {b} (aligned to 64), c at {c}");

    // Freeing makes room again, and neighbours merge into one range.
    list.free(a, 100);
    list.free(c, 100);
    println!(
        "free: {} bytes, largest piece: {}",
        list.free_bytes(),
        list.largest_free()
    );

    list.free(b, 200);
    println!("unused again: {}", list.is_unused());
}
