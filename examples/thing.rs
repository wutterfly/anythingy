//! `Thing`: a type-erased value, like `Box<dyn Any>`, but small values are
//! stored inline without allocating.
//!
//! Run with: `cargo run --example thing`

use anythingy::Thing;

fn main() {
    // Store values of different types in one collection.
    // (`Thing` defaults to a 24-byte inline buffer, so this annotation selects it.)
    let mut things: Vec<Thing> = vec![Thing::new(42u32), Thing::new(String::from("hello"))];

    // Borrow, checking the type first.
    assert!(things[0].is_type::<u32>());
    assert_eq!(things[0].try_get_ref::<u32>(), Some(&42));
    assert_eq!(things[0].try_get_ref::<String>(), None);

    // Mutate in place.
    things[1].get_mut::<String>().push_str(", world");

    // Take the value back out (consumes the `Thing`).
    let text: String = things.remove(1).get();
    assert_eq!(text, "hello, world");

    // Choose the inline size yourself: values larger than `SIZE` are boxed.
    let small = Thing::<8>::new(7u64); // fits inline
    assert!(!Thing::<8>::boxed::<u64>());
    assert!(Thing::<8>::boxed::<String>());
    assert_eq!(*small.get_ref::<u64>(), 7);
}
