# Changelog

## 0.3.0

Breaking release: the crate now hosts a set of data structures instead of only `Thing` and its maps.

### Added

- `TokenStore` and `Token`: values addressed by small `Copy` tokens that detect stale use.
- `InlineVec`: a vector that keeps its first few elements inline.
- `LinearMap` and `LinearSet`: a map and a set in a flat vector, for small sizes.
- `ThingMap` and `SyncThingMap`: one value per type, looked up by the type. `SyncThingMap` is `Send + Sync`.
- `EventQueue`: a multi-producer queue that is drained in batches.
- `Thing::get_unchecked`, `Thing::get_ref_unchecked` and `Thing::get_mut_unchecked`, the `unsafe` counterparts of the checked accessors.
- `no_std` support (with `alloc`). The default `std` feature adds `ThingMap`, `SyncThingMap` and `EventQueue`.
- `rust-version = "1.88"`.

### Removed

- `AnyMap`: replaced by `ThingMap`, whose methods follow `HashMap` (including `entry`). It has no `raw`, `raw_ref`, `raw_mut`, `keys` or `values`.
- `SmallAnyMap`.

### Changed

- `Thing` keeps its API. Its `Debug` output differs.
