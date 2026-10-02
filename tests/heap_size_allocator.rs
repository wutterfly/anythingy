//! Checks `HeapSize` against what the allocator really hands out.
//!
//! Where a structure knows its allocation, `heap_size` must match it exactly.
//! Where the standard library does not expose the layout (hash tables,
//! B-trees, linked lists), `heap_size` is a lower bound, and the test checks
//! that the allocator really hands out at least that much, and not absurdly
//! more.

// Miri tracks every allocation itself, so counting them proves nothing there.
// It also rejects wrapping the system allocator on Windows, where over-aligned
// blocks keep a header in front of the pointer that they hand out.
#![cfg(not(miri))]

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
#[cfg(feature = "std")]
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

use anythingy::{AtomicSlot, HeapSize, InlineVec, LinearMap, LinearSet, Thing, TokenStore};
#[cfg(feature = "std")]
use anythingy::{SThingMap, ThingMap};

thread_local! {
    /// Bytes currently allocated by this thread (allocated minus freed). A
    /// plain `Cell` with no destructor, so it is usable from inside the
    /// allocator at any time.
    static LIVE: Cell<isize> = const { Cell::new(0) };

    /// How many times this thread has asked for memory.
    static ALLOCATIONS: Cell<usize> = const { Cell::new(0) };
}

struct Counting;

fn add(bytes: isize) {
    LIVE.with(|live| live.set(live.get() + bytes));
}

// SAFETY: forwards every call to the system allocator, and only counts.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.with(|count| count.set(count.get() + 1));
        add(layout.size() as isize);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        add(-(layout.size() as isize));
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        add(new_size as isize - layout.size() as isize);
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

fn live() -> isize {
    LIVE.with(Cell::get)
}

fn allocations() -> usize {
    ALLOCATIONS.with(Cell::get)
}

/// A different type for every `N`, with a size of `N` words.
#[allow(dead_code)]
struct Words<const N: usize>([u64; N]);

/// Asserts, without allocating, that the bytes allocated since `before` are
/// exactly what `heap_size` reports.
#[track_caller]
fn assert_matches(before: isize, reported: usize) {
    let allocated = live() - before;
    assert!(
        allocated == reported as isize,
        "the allocator handed out {allocated} bytes, heap_size reported {reported}"
    );
}

/// Asserts, without allocating, that `heap_size` is a lower bound of the bytes
/// allocated since `before`, and that it is within a small factor of them. The
/// slack covers what the standard library keeps besides the entries: control
/// bytes, links, and room that is not used yet.
#[track_caller]
fn assert_lower_bound(before: isize, reported: usize) {
    let allocated = live() - before;
    let reported = reported as isize;
    assert!(
        reported <= allocated,
        "heap_size reported {reported} bytes, but the allocator handed out only {allocated}"
    );
    assert!(
        allocated <= 4 * reported + 256,
        "the allocator handed out {allocated} bytes, heap_size reported only {reported}"
    );
}

#[test]
fn thing_reports_its_box() {
    let before = live();
    let boxed = Thing::<8>::new([0_u64; 10]);
    let reported = boxed.heap_size();
    assert_matches(before, reported);
    drop(boxed);
    assert_matches(before, 0);

    let before = live();
    let inline = Thing::<24>::new(7_u64);
    let reported = inline.heap_size();
    assert_matches(before, reported);
    assert_eq!(reported, 0);
}

#[cfg(feature = "std")]
#[test]
fn thing_map_is_a_lower_bound_while_it_grows() {
    let mut map = ThingMap::<24>::new();
    let before = live();
    assert_matches(before, map.heap_size());

    // Different types, inline and boxed, so the table grows through its first
    // sizes. The boxes are counted exactly, the table as a lower bound.
    macro_rules! insert_and_check {
        ($($n:literal),*) => {$(
            map.insert(Words::<$n>([0; $n]));
            let reported = map.heap_size();
            assert_lower_bound(before, reported);
        )*};
    }
    insert_and_check!(
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20
    );

    let reported = map.heap_size();
    drop(map);
    assert!(reported > 0);
    assert_matches(before, 0);
}

#[cfg(feature = "std")]
#[test]
fn thing_map_with_reserved_room_is_a_lower_bound() {
    for capacity in (0..300).chain([1_000, 4_096, 10_000]) {
        let before = live();
        let map = ThingMap::<24>::with_capacity(capacity);
        let reported = map.heap_size();
        assert_lower_bound(before, reported);
        drop(map);
        assert_matches(before, 0);
    }

    let before = live();
    let big = ThingMap::<64>::with_capacity(100);
    let reported = big.heap_size();
    assert_lower_bound(before, reported);
    drop(big);

    let before = live();
    let small = ThingMap::<8>::with_capacity(100);
    let reported = small.heap_size();
    assert_lower_bound(before, reported);
}

#[cfg(feature = "std")]
#[test]
fn sthing_map_reports_like_thing_map() {
    let before = live();
    let mut map = SThingMap::<24>::with_capacity(20);
    map.insert([0_u64; 12]);
    map.insert(1_u32);
    let reported = map.heap_size();
    assert_lower_bound(before, reported);
}

#[test]
fn vec_backed_structures_report_their_buffers() {
    let before = live();
    let mut vec = InlineVec::<u64, 2>::new();
    vec.extend(0..100);
    let reported = vec.heap_size();
    assert_matches(before, reported);

    let before = live();
    let mut map = LinearMap::<u32, u64>::new();
    for i in 0..100 {
        map.insert(i, u64::from(i));
    }
    let reported = map.heap_size();
    assert_matches(before, reported);

    let before = live();
    let mut set = LinearSet::<u64>::new();
    for i in 0..100 {
        set.insert(i);
    }
    let reported = set.heap_size();
    assert_matches(before, reported);

    let before = live();
    let mut store = TokenStore::<u64>::new();
    for i in 0..100 {
        store.insert(i);
    }
    let reported = store.heap_size();
    assert_matches(before, reported);
}

#[test]
fn std_buffers_report_their_capacity_exactly() {
    let before = live();
    let mut vec = Vec::<u64>::new();
    for i in 0..100 {
        vec.push(i);
    }
    let reported = vec.heap_size();
    assert_matches(before, reported);

    let before = live();
    let mut text = String::new();
    for _ in 0..50 {
        text.push_str("text ");
    }
    let reported = text.heap_size();
    assert_matches(before, reported);

    let before = live();
    let mut deque = VecDeque::<u32>::new();
    for i in 0..100 {
        deque.push_back(i);
        if i % 3 == 0 {
            deque.push_front(i);
        }
    }
    let reported = deque.heap_size();
    assert_matches(before, reported);

    let before = live();
    let mut heap = BinaryHeap::<u16>::new();
    for i in 0..100 {
        heap.push(i);
    }
    let reported = heap.heap_size();
    assert_matches(before, reported);
}

#[test]
fn std_box_reports_its_allocation_exactly() {
    let before = live();
    let boxed = Box::new([0_u64; 10]);
    let reported = boxed.heap_size();
    assert_matches(before, reported);
    drop(boxed);
    assert_matches(before, 0);

    let before = live();
    let slice: Box<[u32]> = vec![0_u32; 25].into_boxed_slice();
    let reported = slice.heap_size();
    assert_matches(before, reported);

    let before = live();
    let text: Box<str> = Box::from("a text on the heap");
    let reported = text.heap_size();
    assert_matches(before, reported);
}

#[test]
fn std_shared_pointers_are_a_lower_bound() {
    let before = live();
    let rc = Rc::new([0_u64; 10]);
    let reported = rc.heap_size();
    assert_lower_bound(before, reported);
    assert!(reported > 0);
    drop(rc);
    assert_matches(before, 0);

    let before = live();
    let arc = Arc::new([0_u8; 40]);
    let reported = arc.heap_size();
    assert_lower_bound(before, reported);

    let before = live();
    let text: Arc<str> = Arc::from("a shared text");
    let reported = text.heap_size();
    assert_lower_bound(before, reported);
}

#[test]
fn std_linked_list_is_a_lower_bound() {
    for len in [0_usize, 1, 5, 100] {
        let before = live();
        let mut list = LinkedList::<u64>::new();
        for i in 0..len {
            list.push_back(i as u64);
        }
        let reported = list.heap_size();
        assert_lower_bound(before, reported);
    }

    // Small elements are padded up inside their nodes.
    let before = live();
    let mut small = LinkedList::<u8>::new();
    small.push_back(1);
    small.push_back(2);
    let reported = small.heap_size();
    assert_lower_bound(before, reported);
}

#[cfg(feature = "std")]
#[test]
fn std_hash_collections_are_a_lower_bound() {
    for count in [0_u64, 1, 3, 4, 7, 8, 100, 1_000] {
        let before = live();
        let mut map = HashMap::<u64, u32>::new();
        for i in 0..count {
            map.insert(i, 0);
        }
        let reported = map.heap_size();
        assert_lower_bound(before, reported);
        drop(map);

        let before = live();
        let mut set = HashSet::<u64>::new();
        for i in 0..count {
            set.insert(i);
        }
        let reported = set.heap_size();
        assert_lower_bound(before, reported);
        drop(set);

        let before = live();
        let set = HashSet::<u8>::with_capacity(count as usize);
        let reported = set.heap_size();
        assert_lower_bound(before, reported);
    }
}

#[test]
fn std_btree_collections_are_a_lower_bound() {
    for count in [1_u32, 10, 100, 1_000] {
        // In order, which leaves the nodes about half full ...
        let before = live();
        let mut ordered = BTreeMap::<u32, u64>::new();
        for i in 0..count {
            ordered.insert(i, 0);
        }
        let reported = ordered.heap_size();
        assert!(reported > 0);
        assert_lower_bound(before, reported);
        drop(ordered);

        // ... and scattered, which fills them more.
        let before = live();
        let mut scattered = BTreeSet::<u64>::new();
        for i in 0..u64::from(count) {
            scattered.insert(i.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        }
        let reported = scattered.heap_size();
        assert_lower_bound(before, reported);
    }
}

#[test]
fn atomic_slot_allocates_once_and_never_again() {
    let before = allocations();
    let slot = AtomicSlot::<u64>::new();
    assert_eq!(allocations() - before, 1, "both cells are one allocation");

    slot.push(1);
    slot.push(2);
    assert_eq!(slot.take(), Some(2));
    assert_eq!(slot.take(), None);
    assert_eq!(
        allocations() - before,
        1,
        "pushing and taking do not allocate"
    );

    let live_before = live();
    let boxed = AtomicSlot::<Box<[u64; 4]>>::new();
    let reported = boxed.heap_size();
    assert_matches(live_before, reported);
}
