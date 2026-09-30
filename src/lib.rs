//! Collections and containers that make different space/time trade-offs than
//! the ones in `std::collections`.
//!
//! | Type | What it is |
//! |---|---|
//! | [`Thing`], [`SThing`] | A type-erased value, like `Box<dyn Any>`, that stores small values inline (the second is thread-safe) |
//! | [`AtomicRefCell`] | A `RefCell` that can be shared between threads, with borrows checked at runtime and never waited for |
//! | [`AtomicSlot`] | A single-value mailbox shared between threads, where the latest value replaces the previous one |
//! | [`TokenStore`] | Values addressed by small `Copy` tokens that detect stale use (a generational index) |
//! | [`InlineVec`] | A vector that keeps its first few elements inline and only allocates beyond that |
//! | [`LinearMap`], [`LinearSet`] | A map and a set in a flat vector, for small sizes and keys that are only `Eq` |
#![cfg_attr(
    feature = "std",
    doc = "| [`ThingMap`], [`SThingMap`] | One value per type, looked up by the type (the second is thread-safe) |"
)]
#![cfg_attr(
    feature = "std",
    doc = "| [`EventQueue`] | A multi-producer queue that is drained in batches |"
)]
//!
//! # Features and `no_std`
//!
//! The crate is `no_std`-compatible and only needs `alloc`. The default `std`
//! feature adds the types that need the standard library (`ThingMap`,
//! `SThingMap` and `EventQueue`, listed above only when it is enabled).
//! To use the rest without `std`:
//!
//! ```toml
//! anythingy = { version = "0.3", default-features = false }
//! ```
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![warn(missing_docs)]
#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]
#![allow(clippy::module_name_repetitions)]

extern crate alloc;

pub mod atomic_ref_cell;
pub mod atomic_slot;
#[cfg(feature = "std")]
pub mod event_queue;
pub mod inline_vec;
pub mod linear_map;
pub mod linear_set;
pub mod sthing;
#[cfg(feature = "std")]
pub mod sthing_map;
pub mod thing;
#[cfg(feature = "std")]
pub mod thing_map;
pub mod token_store;

pub use atomic_ref_cell::AtomicRefCell;
pub use atomic_slot::AtomicSlot;
#[cfg(feature = "std")]
pub use event_queue::EventQueue;
pub use inline_vec::InlineVec;
pub use linear_map::LinearMap;
pub use linear_set::LinearSet;
pub use sthing::SThing;
#[cfg(feature = "std")]
pub use sthing_map::SThingMap;
pub use thing::Thing;
#[cfg(feature = "std")]
pub use thing_map::ThingMap;
pub use token_store::{Token, TokenStore};

// Compiles and runs the code in the README as a doctest, without adding it
// to the crate documentation.
#[cfg(all(doctest, feature = "std"))]
#[doc = include_str!("../README.md")]
struct ReadmeDoctests;
