//! `bit_flags!`: a set of flags in one small integer.
//!
//! Run with: `cargo run --example bit_flags`

use anythingy::bit_flags;

bit_flags! {
    /// What a buffer can be used for.
    pub struct Usage: u32 {
        /// Source of a copy.
        const TRANSFER_SRC = 1 << 0;
        /// Destination of a copy.
        const TRANSFER_DST = 1 << 1;
        /// Vertex data.
        const VERTEX = 1 << 2;
        /// Both directions of a copy, declared first so that it is named when both are set.
        const TRANSFER = Self::TRANSFER_SRC.bits() | Self::TRANSFER_DST.bits();
    }
}

fn main() {
    // Combine with `|`, and ask with `contains`.
    let mut usage = Usage::VERTEX | Usage::TRANSFER_DST;
    println!("{usage:?} ({:#b})", usage.bits());
    println!(
        "can be a copy target: {}",
        usage.contains(Usage::TRANSFER_DST)
    );
    println!(
        "can be a copy source: {}",
        usage.contains(Usage::TRANSFER_SRC)
    );

    // Change in place.
    usage.insert(Usage::TRANSFER_SRC);
    println!("after insert: {usage:?}");
    usage.remove(Usage::VERTEX);
    println!("after remove: {usage:?}");

    // Everything that is not set, and the flags one by one.
    println!("not set: {:?}", !usage);
    for flag in (Usage::VERTEX | Usage::TRANSFER_SRC).iter() {
        println!("set: {flag:?}");
    }

    // Raw bits from outside are checked against the declared flags.
    println!("from 0b101: {:?}", Usage::from_bits(0b101));
    println!("from 0b1000: {:?}", Usage::from_bits(0b1000));
}
