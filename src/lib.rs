//! # Anything
//! **This is a work-in-progess project and not for production use.**
//!
//! A library for dynamic typing.
//!
//! It's main feature is the [`Thing`] type, that works similar to [`Box<dyn Any>`][std::any::Any], but can be sized at compile time.
//! Additonal 'TypeMaps' for storing objects of different types are provided:
//!
//! * [`crate::AnyMap`] using a [`HashMap<TypeId, Thing>`][std::collections::hash_map::HashMap] for storing a large number of different types.
//! * [`crate::SmallAnyMap`] using a [`Vec<(std::any::TypeId, anything::Thing)>`][Vec] for storing a small number of different types.
//!
//! # Example
//! ```rust
//! # use anything::Thing;
//! # fn main() {
//!    let number_thing: Thing<24> = Thing::new(42u64);
//!    let sting_thing: Thing<24> = Thing::new(String::from("Hello there"));
//!    let bytes_thing: Thing<24> = Thing::new(Vec::from(b"so uncivilized"));
//!
//!    let number = number_thing.get::<u64>();
//!    assert_eq!(number, 42);
//!
//!    let string = sting_thing.get::<String>();
//!    assert_eq!(&string, "Hello there");
//!
//!    let bytes = bytes_thing.get::<Vec<u8>>();
//!    assert_eq!(&bytes, b"so uncivilized");
//! # }
//! ```

#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]
#![allow(clippy::module_name_repetitions)]

mod map;
mod small;
mod thing;

pub use map::AnyMap;
pub use small::SmallAnyMap;
pub use thing::{Thing, DEFAULT_THING_SIZE};
