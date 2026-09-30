# Anythingy

[![Rust](https://github.com/wutterfly/anythingy/actions/workflows/rust.yml/badge.svg)](https://github.com/wutterfly/anythingy/actions/workflows/rust.yml)

Collections and containers with different space/time trade-offs than the ones in `std::collections`.
`no_std` compatible (needs `alloc`). Pre-1.0: the API may change between minor versions.

| Type | What it is |
|---|---|
| `Thing`, `SThing` | A type-erased value, like `Box<dyn Any>`, that stores small values inline (the second is `Send + Sync`) |
| `AtomicSlot` | A single-value mailbox shared between threads, where the latest value replaces the previous one |
| `TokenStore` | Values addressed by small `Copy` tokens that detect stale use (a generational index) |
| `InlineVec` | A vector that keeps its first few elements inline and only allocates beyond that |
| `LinearMap`, `LinearSet` | A map and a set in a flat vector, for small sizes and keys that are only `Eq` |
| `ThingMap`, `SThingMap` | One value per type, looked up by the type (the second is `Send + Sync`) |
| `EventQueue` | A multi-producer queue that is drained in batches |

## Example

```rust
use anythingy::{InlineVec, Thing, ThingMap, TokenStore};

// A type-erased value; small values need no allocation.
let thing: Thing<24> = Thing::new(String::from("hello"));
assert_eq!(thing.get::<String>(), "hello");

// Values addressed by tokens that notice stale use.
let mut textures = TokenStore::new();
let grass = textures.insert("grass");
textures.remove(grass);
assert!(textures.get(grass).is_none());

// A vector that allocates only when it outgrows its inline storage.
let mut args: InlineVec<u32, 4> = InlineVec::new();
args.extend([1, 2, 3]);
assert!(!args.spilled());

// One value per type.
let mut resources = ThingMap::<24>::new();
resources.insert(42u32);
assert_eq!(resources.get::<u32>(), Some(&42));
```

## Features

The default `std` feature adds `ThingMap`, `SThingMap` and `EventQueue`. Everything else works with
only `core` and `alloc`:

```toml
anythingy = { version = "0.3", default-features = false }
```

Requires Rust 1.88 or newer.

## Licence

This project is licensed under the [MIT license](./LICENCE).
