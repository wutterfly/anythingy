# Changelog

## 0.3.3

### Added

- `AtomicSlot`: a single-value slot that threads hand values to each other through. `push` stores a value and drops the previous one, `take` removes it. It allocates only when created, works without `std`, and is `Send + Sync` whenever `T: Send`.

## 0.3.2

`EventQueue` draining no longer throws its buffers away, and pushing is faster.

### Added

- `EventQueue::drain_into`: drains into a `Vec` you provide, so it can be reused between calls.
- `EventQueue::drain_each`: hands the events to a callback one thread's batch at a time, without copying them or allocating. The batches can only be read.

### Changed

- `EventQueue::drain` and the other drain methods leave each thread's buffer in place with its capacity, so the next pushes do not have to allocate again. Buffers that have grown much larger than they are used are trimmed back gradually, but never to nothing.
- `EventQueue::drain` reserves its result once instead of growing it.
- `EventQueue::push` is about two to three times faster on a single thread, and slightly faster with several.

### Fixed

- A panic while pushing to an `EventQueue` no longer leaves the thread's buffer locked, which would have made other threads spin forever.

## 0.3.1

Breaking release: the crate now hosts a set of data structures instead of only `Thing` and its maps.

### Added

- `TokenStore` and `Token`: values addressed by small `Copy` tokens that detect stale use.
- `InlineVec`: a vector that keeps its first few elements inline.
- `LinearMap` and `LinearSet`: a map and a set in a flat vector, for small sizes.
- `SThing`: a `Thing` that is `Send + Sync`.
- `ThingMap` and `SThingMap`: one value per type, looked up by the type. `SThingMap` is `Send + Sync`.
- `EventQueue`: a multi-producer queue that is drained in batches.
- `Thing::get_unchecked`, `Thing::get_ref_unchecked` and `Thing::get_mut_unchecked`, the `unsafe` counterparts of the checked accessors.
- `no_std` support (with `alloc`). The default `std` feature adds `ThingMap`, `SThingMap` and `EventQueue`.
- `rust-version = "1.88"`.

### Removed

- `AnyMap`: replaced by `ThingMap`, whose methods follow `HashMap` (including `entry`). It has no `raw`, `raw_ref`, `raw_mut`, `keys` or `values`.
- `SmallAnyMap`.

### Changed

- `Thing` keeps its API. Its `Debug` output differs.
