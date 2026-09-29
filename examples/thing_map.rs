//! `ThingMap`: one value per type, looked up by the type.
//!
//! Run with: `cargo run --example thing_map`

use anythingy::ThingMap;

struct Config {
    verbose: bool,
}

struct FrameCounter(u64);

fn main() {
    // A map from a type to a value of that type.
    let mut resources = ThingMap::<24>::new();

    // Store one value per type.
    resources.insert(Config { verbose: true });
    resources.insert(FrameCounter(0));

    // Look it up by naming the type. No type check happens at runtime,
    // the type itself is the key.
    if resources.get::<Config>().unwrap().verbose {
        println!("verbose mode");
    }
    resources.get_mut::<FrameCounter>().unwrap().0 += 1;

    // Create on first use.
    resources
        .entry::<Vec<String>>()
        .or_default()
        .push("started".into());
    println!("log: {:?}", resources.get::<Vec<String>>().unwrap());

    // A type that was never stored is simply absent.
    assert!(resources.get::<u32>().is_none());

    // Take a value back out.
    let counter = resources.remove::<FrameCounter>().unwrap();
    println!("frames: {}", counter.0);
}
