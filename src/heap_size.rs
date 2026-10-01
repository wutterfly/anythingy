//! Reporting how much heap memory a data structure has allocated.
//!
//! See [`HeapSize`]. Besides the structures of this crate, it is implemented
//! for the types of the standard library that allocate: [`Vec`], [`String`],
//! [`VecDeque`], [`BinaryHeap`] and [`Box`], which report their allocation
//! exactly, and [`LinkedList`], [`BTreeMap`], [`BTreeSet`], [`Rc`] and [`Arc`],
//! and with the `std` feature `HashMap` and `HashSet`, which report a lower
//! bound, since their layout is not exposed.

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
use alloc::rc::Rc;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

/// A value that can report how many bytes of heap memory it has allocated for
/// itself.
///
/// The number is the size that the value asked the allocator for, such as the
/// capacity of a vector's buffer times the size of its elements. It counts
/// what the structure itself owns, and nothing more:
///
/// - **Not the value itself.** The bytes of the value (what
///   [`core::mem::size_of_val`] returns) live wherever the value
///   lives, on the stack, in a field or in another allocation. A structure
///   that keeps everything inline reports `0`.
/// - **Not what its elements own.** A buffer of `String`s is counted by the
///   `String` handles it holds, not by the text they point to.
/// - **Not the allocator's overhead.** Allocators round sizes up and keep
///   bookkeeping of their own, which is not visible here.
///
/// Reserved but unused capacity is counted, since it is allocated.
///
/// # A best-effort figure
///
/// The number is the best that an implementation can tell, and it is not a
/// guarantee that it is complete. Some types do not say how big their
/// allocations are: the layout of a hash table or a B-tree is not exposed. Such
/// a type can still report what it is certain of, so the figure may be lower
/// than what is really allocated. Treat it as a measure of how much memory a
/// structure holds on to, and not as an exact account of the allocator's books.
///
/// # For implementors
///
/// - **Report what you can know.** Use the public interface of the type, such
///   as its capacity, and the behavior that it documents. Where the real size
///   is known, report it exactly.
/// - **Prefer too little over too much.** If the exact size is not available,
///   report a lower bound: only count allocations that certainly exist. Do not
///   guess at the internals of a type that you do not own, or copy its private
///   layout, because that breaks silently when the type changes.
/// - **Say what is left out.** Describe in the documentation of the
///   implementation what the figure does not include, so that a reader knows
///   how much to trust it.
/// - **Stay shallow.** Count the structure's own allocations, as described
///   above, and not what its elements own.
///
/// # Examples
///
/// ```
/// use anythingy::{HeapSize, InlineVec};
///
/// let mut values = InlineVec::<u32, 4>::new();
/// values.extend([1, 2, 3, 4]);
/// assert_eq!(values.heap_size(), 0); // all four are still inline
///
/// values.push(5); // spills to the heap
/// assert!(values.heap_size() >= 5 * size_of::<u32>());
/// ```
///
/// It is implemented for the collections of the standard library that
/// allocate, too:
///
/// ```
/// use anythingy::HeapSize;
///
/// let mut numbers = Vec::<u64>::with_capacity(10);
/// numbers.push(1);
/// assert_eq!(numbers.heap_size(), numbers.capacity() * 8);
/// ```
pub trait HeapSize {
    /// Returns the number of bytes of heap memory this value has allocated, as
    /// far as the implementation can tell.
    ///
    /// See the [trait documentation](HeapSize#a-best-effort-figure) for what
    /// the figure includes, and when it can be lower than the real allocation.
    fn heap_size(&self) -> usize;
}

impl<T> HeapSize for Vec<T> {
    /// Counts the buffer, including the capacity that is not used.
    #[inline]
    fn heap_size(&self) -> usize {
        self.capacity() * size_of::<T>()
    }
}

impl HeapSize for String {
    /// Counts the buffer of text, including the capacity that is not used.
    #[inline]
    fn heap_size(&self) -> usize {
        self.capacity()
    }
}

impl<T> HeapSize for VecDeque<T> {
    /// Counts the ring buffer, including the capacity that is not used.
    #[inline]
    fn heap_size(&self) -> usize {
        self.capacity() * size_of::<T>()
    }
}

impl<T> HeapSize for BinaryHeap<T> {
    /// Counts the buffer, including the capacity that is not used.
    #[inline]
    fn heap_size(&self) -> usize {
        self.capacity() * size_of::<T>()
    }
}

impl<T: ?Sized> HeapSize for Box<T> {
    /// Counts the allocation that holds the value, which is as big as the
    /// value. It is `0` for a value of size zero, which is not allocated.
    ///
    /// What the value owns is not included: a `Box<Vec<u8>>` counts the
    /// `Vec` itself, and not its buffer.
    #[inline]
    fn heap_size(&self) -> usize {
        size_of_val::<T>(&**self)
    }
}

impl<T: ?Sized> HeapSize for Rc<T> {
    /// A lower bound: the value, which is stored in the allocation that the
    /// handles share.
    ///
    /// The reference counts that the allocation also holds are left out. Every
    /// handle reports the whole shared allocation, so adding up the sizes of
    /// several handles to the same value counts it more than once.
    #[inline]
    fn heap_size(&self) -> usize {
        size_of_val::<T>(&**self)
    }
}

impl<T: ?Sized> HeapSize for Arc<T> {
    /// A lower bound: the value, which is stored in the allocation that the
    /// handles share.
    ///
    /// The reference counts that the allocation also holds are left out. Every
    /// handle reports the whole shared allocation, so adding up the sizes of
    /// several handles to the same value counts it more than once.
    #[inline]
    fn heap_size(&self) -> usize {
        size_of_val::<T>(&**self)
    }
}

impl<T> HeapSize for LinkedList<T> {
    /// A lower bound: every element is allocated in a node of its own, which
    /// holds the element and the links to the two neighbouring nodes.
    ///
    /// Any padding of the node, and whatever else the standard library keeps
    /// in it, is left out.
    #[inline]
    fn heap_size(&self) -> usize {
        self.len() * (size_of::<T>() + 2 * size_of::<usize>())
    }
}

impl<K, V> HeapSize for BTreeMap<K, V> {
    /// A lower bound: the keys and values that are stored.
    ///
    /// The standard library does not expose how a B-tree is laid out. What the
    /// nodes hold besides the entries, and the room they keep for entries that
    /// are not there, is left out.
    #[inline]
    fn heap_size(&self) -> usize {
        self.len() * (size_of::<K>() + size_of::<V>())
    }
}

impl<T> HeapSize for BTreeSet<T> {
    /// A lower bound: the elements that are stored. See the implementation for
    /// [`BTreeMap`].
    #[inline]
    fn heap_size(&self) -> usize {
        self.len() * size_of::<T>()
    }
}

#[cfg(feature = "std")]
impl<K, V, S> HeapSize for std::collections::HashMap<K, V, S> {
    /// A lower bound: room for as many entries as the map can hold without
    /// growing, which is its [`capacity`](std::collections::HashMap::capacity).
    ///
    /// The standard library does not expose how a hash table is laid out. The
    /// control data that it keeps for each bucket, and the buckets beyond the
    /// capacity, are left out.
    #[inline]
    fn heap_size(&self) -> usize {
        self.capacity() * size_of::<(K, V)>()
    }
}

#[cfg(feature = "std")]
impl<T, S> HeapSize for std::collections::HashSet<T, S> {
    /// A lower bound: room for as many elements as the set can hold without
    /// growing, like the implementation for
    /// [`HashMap`](std::collections::HashMap).
    #[inline]
    fn heap_size(&self) -> usize {
        self.capacity() * size_of::<T>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn buffers_report_their_capacity() {
        let mut vec = Vec::<u32>::new();
        assert_eq!(vec.heap_size(), 0);
        vec.reserve_exact(10);
        assert_eq!(vec.heap_size(), vec.capacity() * 4);
        assert!(vec.heap_size() >= 40);

        let mut text = String::new();
        assert_eq!(text.heap_size(), 0);
        text.push_str("some text");
        assert_eq!(text.heap_size(), text.capacity());

        let deque = VecDeque::<u64>::with_capacity(10);
        assert_eq!(deque.heap_size(), deque.capacity() * 8);
        assert!(deque.heap_size() >= 80);

        let heap = BinaryHeap::<u16>::with_capacity(10);
        assert_eq!(heap.heap_size(), heap.capacity() * 2);
    }

    #[test]
    fn what_the_elements_own_is_not_counted() {
        let strings = vec![String::from("a long enough piece of text"); 3];
        assert_eq!(
            strings.heap_size(),
            strings.capacity() * size_of::<String>()
        );
    }

    #[test]
    fn zero_sized_elements_have_nothing_on_the_heap() {
        let mut vec = Vec::<()>::new();
        vec.extend([(), (), ()]);
        assert_eq!(vec.heap_size(), 0);
        assert_eq!(VecDeque::<()>::from([(), ()]).heap_size(), 0);
    }

    #[test]
    fn boxes_report_the_size_of_the_value() {
        use core::fmt::Debug;

        assert_eq!(Box::new(5_u64).heap_size(), 8);
        assert_eq!(Box::new([0_u8; 100]).heap_size(), 100);
        assert_eq!(Box::new(()).heap_size(), 0);

        // Unsized values: the length of the slice or the text, and the real
        // type behind a trait object.
        let slice: Box<[u32]> = Box::new([1, 2, 3]);
        assert_eq!(slice.heap_size(), 12);
        let text: Box<str> = Box::from("hello");
        assert_eq!(text.heap_size(), 5);
        let object: Box<dyn Debug> = Box::new(7_u16);
        assert_eq!(object.heap_size(), 2);

        // What the value owns is not counted, only the value itself.
        let vec = Box::new(Vec::<u8>::with_capacity(1_000));
        assert_eq!(vec.heap_size(), size_of::<Vec<u8>>());
    }

    #[test]
    fn shared_pointers_report_the_value_for_every_handle() {
        use core::fmt::Debug;

        let rc = Rc::new([0_u32; 4]);
        let other = Rc::clone(&rc);
        assert_eq!(rc.heap_size(), 16);
        assert_eq!(other.heap_size(), 16);

        let arc: Arc<str> = Arc::from("hello world");
        let other = Arc::clone(&arc);
        assert_eq!(arc.heap_size(), 11);
        assert_eq!(other.heap_size(), 11);

        let object: Arc<dyn Debug> = Arc::new(7_u64);
        assert_eq!(object.heap_size(), 8);

        assert_eq!(Rc::new(()).heap_size(), 0);
        assert_eq!(Arc::new(()).heap_size(), 0);
    }

    #[test]
    fn linked_list_counts_the_elements_and_their_links() {
        let mut list = LinkedList::new();
        assert_eq!(list.heap_size(), 0);
        list.push_back(1_u64);
        list.push_front(2);
        assert_eq!(list.heap_size(), 2 * (8 + 2 * size_of::<usize>()));
    }

    #[test]
    fn btree_collections_report_a_lower_bound() {
        let mut map = BTreeMap::new();
        assert_eq!(map.heap_size(), 0);
        for i in 0..100_u32 {
            map.insert(i, u64::from(i));
        }
        assert_eq!(map.heap_size(), 100 * (4 + 8));

        let set: BTreeSet<u16> = (0..50).collect();
        assert_eq!(set.heap_size(), 50 * 2);
    }

    #[cfg(feature = "std")]
    #[test]
    fn hash_collections_count_the_entries_they_have_room_for() {
        use std::collections::{HashMap, HashSet};

        let mut map = HashMap::<u32, u64>::new();
        assert_eq!(map.heap_size(), 0);
        map.insert(1, 1);
        assert_eq!(map.heap_size(), map.capacity() * size_of::<(u32, u64)>());
        assert!(map.heap_size() >= size_of::<(u32, u64)>());

        let set = HashSet::<u64>::with_capacity(100);
        assert_eq!(set.heap_size(), set.capacity() * 8);
        assert!(set.heap_size() >= 100 * 8);
    }
}
