# Changelog

## 0.3.6

### Added

- `FreeList`: the bookkeeping for handing out parts of one block of memory, such as a GPU allocation. `allocate` takes the smallest free range that fits (best fit) at the alignment asked for, `free` gives a range back and merges it with free neighbours, and a double free panics instead of handing out the same bytes twice. It counts in `u64` by default, or any of `u16`, `u32`, `u128` and `usize` (`FreeList<usize>`), knows nothing about what the memory is, works without `std`, and implements `HeapSize`. It keeps a few free ranges in a flat vector, and moves to two indexes (by offset and by size) when the block is fragmented into more than 64, so `allocate` and `free` stay fast either way.

## 0.3.5

### Added

- `InlineMap`: a hash map that keeps its first `N` entries inline, without allocating, and moves them into a `HashMap` when it grows past that. It has the API of `HashMap`, including `entry`, iterators and `HeapSize`, and needs the `std` feature.
- `TypeIdHasher` and `TypeIdBuildHasher`: the cheap pass-through hasher for `TypeId` keys, now in a module of its own so that it can be used for any map keyed by `TypeId`, not just `ThingMap`. They work without `std`, and are still available from `thing_map`.

### Changed

- `InlineVec` and `InlineMap` are 8 bytes smaller for most sizes of their inline part: they no longer store a tag that tells whether they spilled to the heap.
- `InlineMap` searches big inline maps of small keys block by block, which makes a lookup that finds nothing up to a third faster once there are 16 or more entries.
- `AtomicSlot` allocates once instead of twice, so creating and dropping one is about twice as fast. Each of its two cells has a cache line of its own, which is why `HeapSize` reports 128 bytes for it.

## 0.3.4

### Added

- `HeapSize`: a trait that reports how many bytes of heap memory a structure has allocated for itself. It is implemented for `AtomicRefCell`, `AtomicSlot`, `EventQueue`, `InlineVec`, `LinearMap`, `LinearSet`, `TokenStore`, `Thing`, `SThing`, `ThingMap` and `SThingMap`, and for the types of the standard library that allocate: `Vec`, `String`, `VecDeque`, `BinaryHeap` and `Box` report their allocation exactly, `LinkedList`, `BTreeMap`, `BTreeSet`, `Rc`, `Arc`, and with `std` `HashMap` and `HashSet` a lower bound, since their layout is not exposed. `ThingMap` and `SThingMap` report a lower bound as well, plus the boxes of the values that did not fit inline.

### Changed

- Dropping a `Thing`, and the values of a `ThingMap`, is faster, up to about twice as fast for values that are stored inline. The value is dropped in place, and the buffer is no longer copied out first.

## 0.3.3

### Added

- `AtomicSlot`: a single-value slot that threads hand values to each other through. `push` stores a value and drops the previous one, `take` removes it. It allocates only when created, works without `std`, and is `Send + Sync` whenever `T: Send`.
- `AtomicRefCell`: a `RefCell` that can be shared between threads. Borrows are checked at runtime and a conflict is reported (`try_borrow`, `try_borrow_mut`) or panics (`borrow`, `borrow_mut`), it never waits. It works without `std`, allocates nothing, and is `Sync` when `T: Send + Sync`.
  - The methods of `RefCell`: `replace`, `replace_with`, `swap`, `take`, `get_mut`, `into_inner` and `as_ptr`, and the `unsafe` `borrow_unchecked` and `borrow_mut_unchecked`.
  - The guards `AtomicRef` and `AtomicRefMut`, with `map`, `filter_map` and `AtomicRef::clone`.
  - `Default`, `From`, `Clone`, `Debug`, `PartialEq`, `Eq`, `PartialOrd` and `Ord`, and support for unsized values such as `AtomicRefCell<[T]>` and `AtomicRefCell<dyn Trait>`.

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
