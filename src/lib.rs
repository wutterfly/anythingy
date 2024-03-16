#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]
#![allow(clippy::module_name_repetitions)]

mod map;
mod small;
mod thing;

pub use map::AnyMap;
pub use small::SmallAnyMap;
pub use thing::{Thing, DEFAULT_THING_SIZE};
