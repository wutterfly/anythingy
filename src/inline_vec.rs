//! A vector that keeps its first few elements inline.
//!
//! See [`InlineVec`] for details.

use crate::heap_size::HeapSize;
use alloc::vec::Vec;
use core::borrow::{Borrow, BorrowMut};
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::num::NonZeroUsize;
use core::ops::{Bound, Deref, DerefMut, RangeBounds};
use core::ptr::{self, NonNull};
use core::slice;

/// A vector that stores up to `N` elements inline, without allocating, and
/// moves to the heap ("spills") when it grows beyond that.
///
/// It behaves like a [`Vec`]: it dereferences to a slice, so every slice
/// method works (`iter`, `sort`, `binary_search`, indexing, ...), and it has
/// the familiar `push`, `pop`, `insert`, `remove`, `drain`, `retain`,
/// `truncate` and `extend`. The difference is where the elements live. Short
/// vectors, which are the common case for things like the arguments of a call,
/// the children of a tree node or a handful of tokens, never touch the
/// allocator; only the rare long one pays for it.
///
/// * While the length is at most `N` and the vector has not spilled, the
///   elements are stored inside the `InlineVec` itself, so the value is as
///   large as `N` elements plus a little bookkeeping.
/// * The first push beyond `N` moves everything into a heap buffer. From then
///   on it is a plain `Vec` internally.
/// * Once spilled it stays on the heap, even if it shrinks back to `N`
///   elements or fewer. [`shrink_to_fit`](Self::shrink_to_fit) moves it back
///   inline when the elements fit. Check with [`spilled`](Self::spilled).
///
/// Pick `N` so that the inline part covers the typical length; a large `N`
/// makes every `InlineVec` (and anything containing one) large, and moving it
/// around copies all `N` slots.
///
/// # Examples
///
/// ```
/// use anythingy::InlineVec;
///
/// let mut v: InlineVec<u32, 4> = InlineVec::new();
/// v.push(1);
/// v.push(2);
/// v.push(3);
/// assert!(!v.spilled()); // still inline
/// assert_eq!(v.iter().sum::<u32>(), 6);
///
/// v.extend([4, 5]); // one past the inline capacity
/// assert!(v.spilled());
/// assert_eq!(v, [1, 2, 3, 4, 5]);
/// ```
pub struct InlineVec<T, const N: usize> {
    repr: Repr<T, N>,
}

/// Where the elements are.
///
/// # Invariants
///
/// For `Inline { len, buf }`: `len <= N`, and exactly `buf[..len]` are
/// initialized and owned by the vector.
enum Repr<T, const N: usize> {
    Inline { len: Len, buf: [MaybeUninit<T>; N] },
    Heap(Vec<T>),
}

/// The number of inline elements, stored as one more than it is, which makes it
/// a number that is never zero.
///
/// That is all it is for: the compiler can then use the value zero of this
/// field to tell that the elements are on the heap, and store both cases in the
/// same space, instead of adding a tag that tells them apart. That saves 8 bytes
/// when the inline elements take 32 bytes or more.
#[derive(Clone, Copy)]
struct Len(NonZeroUsize);

impl Len {
    /// No elements.
    const ZERO: Self = Self(NonZeroUsize::MIN);

    /// A number of elements that are in an array, so it is far below
    /// `usize::MAX` in any vector that can exist. If it was not, this panics,
    /// and does not produce a length that is wrong.
    #[inline]
    const fn new(len: usize) -> Self {
        match NonZeroUsize::new(len.wrapping_add(1)) {
            Some(stored) => Self(stored),
            None => panic!("too many elements"),
        }
    }

    #[inline]
    const fn get(self) -> usize {
        self.0.get() - 1
    }
}

/// The capacity to ask for when spilling to make room for `needed` elements:
/// at least double the inline capacity, so the first spill leaves headroom.
fn spill_capacity<const N: usize>(needed: usize) -> usize {
    needed.max(N.saturating_mul(2)).max(4)
}

impl<T, const N: usize> InlineVec<T, N> {
    /// The number of elements that fit inline.
    pub const INLINE_CAPACITY: usize = N;

    /// Creates an empty vector. Does not allocate.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            repr: Repr::Inline {
                len: Len::ZERO,
                buf: [const { MaybeUninit::uninit() }; N],
            },
        }
    }

    /// Creates an empty vector with room for at least `capacity` elements.
    /// Allocates only if `capacity` is more than `N`.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= N {
            Self::new()
        } else {
            Self {
                repr: Repr::Heap(Vec::with_capacity(capacity)),
            }
        }
    }

    /// Returns `true` if the elements are on the heap.
    #[inline]
    pub const fn spilled(&self) -> bool {
        matches!(self.repr, Repr::Heap(_))
    }

    /// Returns the number of elements the vector can hold without
    /// reallocating: `N` while inline, the heap buffer's capacity once
    /// spilled.
    #[inline]
    pub const fn capacity(&self) -> usize {
        match &self.repr {
            Repr::Inline { .. } => N,
            Repr::Heap(vec) => vec.capacity(),
        }
    }

    /// Returns the number of elements.
    #[inline]
    pub const fn len(&self) -> usize {
        match &self.repr {
            Repr::Inline { len, .. } => len.get(),
            Repr::Heap(vec) => vec.len(),
        }
    }

    /// Returns `true` if the vector holds no elements.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the elements as a slice.
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        match &self.repr {
            Repr::Inline { len, buf } => {
                // SAFETY: `buf[..len]` is initialized (type invariant), and
                // `MaybeUninit<T>` has the same layout as `T`.
                unsafe { slice::from_raw_parts(buf.as_ptr().cast::<T>(), len.get()) }
            }
            Repr::Heap(vec) => vec.as_slice(),
        }
    }

    /// Returns the elements as a mutable slice.
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        match &mut self.repr {
            Repr::Inline { len, buf } => {
                // SAFETY: as in `as_slice`.
                unsafe { slice::from_raw_parts_mut(buf.as_mut_ptr().cast::<T>(), len.get()) }
            }
            Repr::Heap(vec) => vec.as_mut_slice(),
        }
    }

    /// Returns a pointer to the first element (dangling if the vector is
    /// empty and has no buffer).
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        match &self.repr {
            Repr::Inline { buf, .. } => buf.as_ptr().cast::<T>(),
            Repr::Heap(vec) => vec.as_ptr(),
        }
    }

    /// Returns a mutable pointer to the first element.
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        match &mut self.repr {
            Repr::Inline { buf, .. } => buf.as_mut_ptr().cast::<T>(),
            Repr::Heap(vec) => vec.as_mut_ptr(),
        }
    }

    /// Sets the length without touching the elements.
    ///
    /// # Safety
    ///
    /// `new_len` must be at most the capacity, and the elements in
    /// `..new_len` must be initialized. Elements dropped out of the range are
    /// not dropped by this call.
    #[inline]
    unsafe fn set_len(&mut self, new_len: usize) {
        match &mut self.repr {
            Repr::Inline { len, .. } => {
                debug_assert!(new_len <= N);
                *len = Len::new(new_len);
            }
            // SAFETY: the caller upholds `Vec::set_len`'s contract.
            Repr::Heap(vec) => unsafe { vec.set_len(new_len) },
        }
    }

    /// Moves the inline elements to a new heap buffer with room for at least
    /// `min_capacity`, and returns it. Does nothing if already on the heap.
    #[cold]
    #[inline(never)]
    fn spill(&mut self, min_capacity: usize) -> &mut Vec<T> {
        if let Repr::Inline { len, buf } = &mut self.repr {
            // Allocate first: if this panics, nothing has been touched.
            let inline_len = len.get();
            let mut vec = Vec::with_capacity(min_capacity.max(inline_len));
            // SAFETY: `buf[..len]` is initialized; `vec` has room for at
            // least `len` elements and is a separate allocation, so the
            // ranges do not overlap. Afterwards the elements are owned by
            // `vec`; `len` is reset and the inline array (of `MaybeUninit`,
            // which has no drop glue) is discarded below without dropping
            // them.
            unsafe {
                ptr::copy_nonoverlapping(buf.as_ptr().cast::<T>(), vec.as_mut_ptr(), inline_len);
                vec.set_len(inline_len);
            }
            *len = Len::ZERO;
            self.repr = Repr::Heap(vec);
        }
        match &mut self.repr {
            Repr::Heap(vec) => vec,
            Repr::Inline { .. } => unreachable!("just spilled"),
        }
    }

    /// The heap buffer, spilling first if needed to hold `additional` more
    /// elements.
    fn heap_vec(&mut self, additional: usize) -> &mut Vec<T> {
        if !self.spilled() {
            let needed = self
                .len()
                .checked_add(additional)
                .expect("capacity overflow");
            self.spill(spill_capacity::<N>(needed));
        }
        match &mut self.repr {
            Repr::Heap(vec) => vec,
            Repr::Inline { .. } => unreachable!("spilled above"),
        }
    }

    /// Reserves room for at least `additional` more elements, spilling to
    /// the heap if that is more than fits inline.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    pub fn reserve(&mut self, additional: usize) {
        let len = self.len();
        if let Repr::Heap(vec) = &mut self.repr {
            vec.reserve(additional);
            return;
        }
        let needed = len.checked_add(additional).expect("capacity overflow");
        if needed > N {
            self.spill(spill_capacity::<N>(needed));
        }
    }

    /// Shrinks the capacity as much as possible. If the elements fit inline
    /// this moves them back inline and frees the heap buffer.
    pub fn shrink_to_fit(&mut self) {
        if let Repr::Heap(vec) = &mut self.repr {
            if vec.len() <= N {
                let len = vec.len();
                let mut buf: [MaybeUninit<T>; N] = [const { MaybeUninit::uninit() }; N];
                // SAFETY: `vec[..len]` is initialized and `len <= N`; `buf` is
                // a separate array. Setting the vec's length to 0 hands the
                // elements over, so dropping the vec (by the assignment
                // below) only frees its buffer.
                unsafe {
                    ptr::copy_nonoverlapping(vec.as_ptr(), buf.as_mut_ptr().cast::<T>(), len);
                    vec.set_len(0);
                }
                self.repr = Repr::Inline {
                    len: Len::new(len),
                    buf,
                };
            } else {
                vec.shrink_to_fit();
            }
        }
    }

    /// Appends an element.
    #[inline]
    pub fn push(&mut self, value: T) {
        if let Repr::Inline { len, buf } = &mut self.repr
            && len.get() < N
        {
            buf[len.get()] = MaybeUninit::new(value);
            *len = Len::new(len.get() + 1);
            return;
        }
        self.heap_vec(1).push(value);
    }

    /// Removes and returns the last element.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        match &mut self.repr {
            Repr::Inline { len, buf } => {
                if len.get() == 0 {
                    return None;
                }
                *len = Len::new(len.get() - 1);
                // SAFETY: `buf[len]` was initialized (it was inside the old
                // length) and is now outside the length, so it is read
                // exactly once.
                Some(unsafe { buf[len.get()].assume_init_read() })
            }
            Repr::Heap(vec) => vec.pop(),
        }
    }

    /// Inserts `value` at `index`, shifting the elements after it.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    pub fn insert(&mut self, index: usize, value: T) {
        let len = self.len();
        assert!(
            index <= len,
            "insertion index (is {index}) should be <= len (is {len})"
        );
        if let Repr::Inline { len, buf } = &mut self.repr
            && len.get() < N
        {
            let base = buf.as_mut_ptr().cast::<T>();
            // SAFETY: `index <= len < N`, so both the shifted range
            // `[index + 1, len + 1)` and the gap at `index` are inside
            // the array. The shift moves initialized elements up by one
            // (`ptr::copy` handles the overlap) and the gap is then
            // written, so afterwards `[..len + 1]` is initialized.
            unsafe {
                ptr::copy(base.add(index), base.add(index + 1), len.get() - index);
                ptr::write(base.add(index), value);
            }
            *len = Len::new(len.get() + 1);
            return;
        }
        self.heap_vec(1).insert(index, value);
    }

    /// Removes and returns the element at `index`, shifting the elements
    /// after it.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        assert!(
            index < len,
            "removal index (is {index}) should be < len (is {len})"
        );
        match &mut self.repr {
            Repr::Inline { len, buf } => {
                let base = buf.as_mut_ptr().cast::<T>();
                // SAFETY: `index < len`, so the element is initialized. It is
                // read out, then the tail is shifted down over the gap, and
                // the length shrinks by one, so nothing is read twice or left
                // counted while moved out.
                unsafe {
                    let value = ptr::read(base.add(index));
                    ptr::copy(base.add(index + 1), base.add(index), len.get() - index - 1);
                    *len = Len::new(len.get() - 1);
                    value
                }
            }
            Repr::Heap(vec) => vec.remove(index),
        }
    }

    /// Removes and returns the element at `index`, replacing it with the
    /// last element. O(1), but does not preserve order.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    pub fn swap_remove(&mut self, index: usize) -> T {
        let len = self.len();
        assert!(
            index < len,
            "swap_remove index (is {index}) should be < len (is {len})"
        );
        self.as_mut_slice().swap(index, len - 1);
        self.pop().expect("length was checked to be non-zero")
    }

    /// Shortens the vector to `len` elements, dropping the rest. Does
    /// nothing if it is already that short.
    pub fn truncate(&mut self, new_len: usize) {
        match &mut self.repr {
            Repr::Inline { len, buf } => {
                if new_len >= len.get() {
                    return;
                }
                let old_len = len.get();
                // Shrink first, so that if a destructor panics the elements
                // are not dropped a second time.
                *len = Len::new(new_len);
                // SAFETY: `[new_len, old_len)` was initialized and is now
                // outside the length, so it is dropped exactly once here.
                unsafe {
                    ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                        buf.as_mut_ptr().cast::<T>().add(new_len),
                        old_len - new_len,
                    ));
                }
            }
            Repr::Heap(vec) => vec.truncate(new_len),
        }
    }

    /// Removes every element, keeping the capacity (and staying on the heap
    /// if spilled).
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Keeps only the elements for which `f` returns `true`, preserving
    /// their order.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|element| f(element));
    }

    /// Like [`retain`](Self::retain), but `f` gets a mutable reference.
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        // Moves each kept element down with a swap, then drops the leftover
        // tail. Entirely safe code, so a panic in `f` leaves a valid vector.
        let elements = self.as_mut_slice();
        let mut kept = 0;
        for i in 0..elements.len() {
            if f(&mut elements[i]) {
                if kept != i {
                    elements.swap(kept, i);
                }
                kept += 1;
            }
        }
        self.truncate(kept);
    }

    /// Appends clones of the elements of `other`.
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        self.reserve(other.len());
        for element in other {
            self.push(element.clone());
        }
    }

    /// Resizes to `new_len`, truncating or filling with clones of `value`.
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        let len = self.len();
        if new_len <= len {
            self.truncate(new_len);
        } else {
            self.reserve(new_len - len);
            for _ in len..new_len {
                self.push(value.clone());
            }
        }
    }

    /// Converts into a `Vec`. If the vector already lives on the heap this
    /// reuses the buffer without copying.
    pub fn into_vec(mut self) -> Vec<T> {
        match &mut self.repr {
            Repr::Heap(vec) => core::mem::take(vec),
            Repr::Inline { len, buf } => {
                let mut vec = Vec::with_capacity(len.get());
                // SAFETY: `buf[..len]` is initialized; `vec` has room for
                // `len` elements. The length is then reset to 0 so that
                // dropping `self` does not drop the moved elements.
                unsafe {
                    ptr::copy_nonoverlapping(buf.as_ptr().cast::<T>(), vec.as_mut_ptr(), len.get());
                    vec.set_len(len.get());
                }
                *len = Len::ZERO;
                vec
            }
        }
    }

    /// Removes the elements in `range` and yields them, shifting the
    /// elements after the range down when the iterator is dropped.
    ///
    /// If the iterator is leaked instead of dropped, the drained range and
    /// everything after it are leaked too, but the vector stays valid.
    ///
    /// # Panics
    ///
    /// Panics if the range is decreasing or reaches past the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use anythingy::InlineVec;
    ///
    /// let mut v = InlineVec::<_, 8>::from([1, 2, 3, 4, 5]);
    /// let middle: Vec<_> = v.drain(1..4).collect();
    /// assert_eq!(middle, vec![2, 3, 4]);
    /// assert_eq!(v, [1, 5]);
    /// ```
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<'_, T, N> {
        let len = self.len();
        let start = match range.start_bound() {
            Bound::Included(&start) => start,
            Bound::Excluded(&start) => start.checked_add(1).expect("range start overflow"),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&end) => end.checked_add(1).expect("range end overflow"),
            Bound::Excluded(&end) => end,
            Bound::Unbounded => len,
        };
        assert!(start <= end, "range starts at {start} but ends at {end}");
        assert!(end <= len, "range end {end} out of range for length {len}");

        // SAFETY: `start <= len`, and `[..start]` stays initialized. The
        // elements from `start` on are now owned by the `Drain` (this is the
        // "leak amplification" trick: if the `Drain` is forgotten, they are
        // leaked, never seen twice).
        unsafe { self.set_len(start) };
        // The buffer pointer is taken through the same raw pointer the
        // `Drain` keeps, so that it is derived from it.
        let vec = NonNull::from(&mut *self);
        // SAFETY: `vec` was just created from a live `&mut`.
        let base = unsafe { (*vec.as_ptr()).as_mut_ptr() };
        Drain {
            vec,
            base,
            cur: start,
            end,
            tail_start: end,
            tail_len: len - end,
            _marker: PhantomData,
        }
    }
}

impl<T, const N: usize> Drop for InlineVec<T, N> {
    fn drop(&mut self) {
        if let Repr::Inline { len, buf } = &mut self.repr {
            // SAFETY: `buf[..len]` is initialized and owned by us, and this
            // is the only place that drops it. (A heap `Vec` drops itself.)
            unsafe {
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                    buf.as_mut_ptr().cast::<T>(),
                    len.get(),
                ));
            }
        }
    }
}

impl<T, const N: usize> Default for InlineVec<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> Deref for InlineVec<T, N> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> DerefMut for InlineVec<T, N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const N: usize> AsRef<[T]> for InlineVec<T, N> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> AsMut<[T]> for InlineVec<T, N> {
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const N: usize> Borrow<[T]> for InlineVec<T, N> {
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> BorrowMut<[T]> for InlineVec<T, N> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T: Clone, const N: usize> Clone for InlineVec<T, N> {
    fn clone(&self) -> Self {
        match &self.repr {
            // `Vec::clone` copies the buffer in one go for plain-data types.
            Repr::Heap(vec) => Self {
                repr: Repr::Heap(vec.clone()),
            },
            Repr::Inline { .. } => {
                let mut clone = Self::new();
                clone.extend(self.iter().cloned());
                clone
            }
        }
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for InlineVec<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_slice(), f)
    }
}

impl<T: Hash, const N: usize> Hash for InlineVec<T, N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Same as a slice, so it agrees with the `Borrow<[T]>` impl.
        self.as_slice().hash(state);
    }
}

impl<T: PartialEq<U>, U, const N: usize, const M: usize> PartialEq<InlineVec<U, M>>
    for InlineVec<T, N>
{
    fn eq(&self, other: &InlineVec<U, M>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: PartialEq<U>, U, const N: usize> PartialEq<[U]> for InlineVec<T, N> {
    fn eq(&self, other: &[U]) -> bool {
        self.as_slice() == other
    }
}

impl<T: PartialEq<U>, U, const N: usize> PartialEq<&[U]> for InlineVec<T, N> {
    fn eq(&self, other: &&[U]) -> bool {
        self.as_slice() == *other
    }
}

impl<T: PartialEq<U>, U, const N: usize, const M: usize> PartialEq<[U; M]> for InlineVec<T, N> {
    fn eq(&self, other: &[U; M]) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: PartialEq<U>, U, const N: usize> PartialEq<Vec<U>> for InlineVec<T, N> {
    fn eq(&self, other: &Vec<U>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: Eq, const N: usize> Eq for InlineVec<T, N> {}

impl<T: PartialOrd, const N: usize> PartialOrd for InlineVec<T, N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T: Ord, const N: usize> Ord for InlineVec<T, N> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<T, const N: usize> Extend<T> for InlineVec<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for element in iter {
            self.push(element);
        }
    }
}

impl<'a, T: Copy + 'a, const N: usize> Extend<&'a T> for InlineVec<T, N> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().copied());
    }
}

impl<T, const N: usize> FromIterator<T> for InlineVec<T, N> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut vec = Self::new();
        vec.extend(iter);
        vec
    }
}

impl<T, const N: usize, const M: usize> From<[T; M]> for InlineVec<T, N> {
    fn from(array: [T; M]) -> Self {
        let mut vec = Self::with_capacity(M);
        vec.extend(array);
        vec
    }
}

impl<T: Clone, const N: usize> From<&[T]> for InlineVec<T, N> {
    fn from(slice: &[T]) -> Self {
        let mut vec = Self::with_capacity(slice.len());
        vec.extend_from_slice(slice);
        vec
    }
}

/// Takes over the `Vec`'s buffer without copying, so the result counts as
/// spilled even if it is short. See [`InlineVec::shrink_to_fit`].
impl<T, const N: usize> From<Vec<T>> for InlineVec<T, N> {
    fn from(vec: Vec<T>) -> Self {
        Self {
            repr: Repr::Heap(vec),
        }
    }
}

impl<T, const N: usize> From<InlineVec<T, N>> for Vec<T> {
    fn from(vec: InlineVec<T, N>) -> Self {
        vec.into_vec()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a InlineVec<T, N> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> slice::Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut InlineVec<T, N> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T, const N: usize> IntoIterator for InlineVec<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    fn into_iter(mut self) -> IntoIter<T, N> {
        let end = self.len();
        // SAFETY: the elements now belong to the iterator. With a length of
        // 0, dropping the vector (which the iterator does when it goes away)
        // does not drop them again.
        unsafe { self.set_len(0) };
        IntoIter {
            vec: self,
            start: 0,
            end,
        }
    }
}

/// An owning iterator over the elements of an [`InlineVec`]. Created by
/// [`InlineVec::into_iter`].
pub struct IntoIter<T, const N: usize> {
    /// Holds the storage; its length is 0, the live elements are
    /// `start..end` of its buffer and owned by this iterator.
    vec: InlineVec<T, N>,
    start: usize,
    end: usize,
}

impl<T, const N: usize> IntoIter<T, N> {
    /// The elements not yet yielded.
    pub const fn as_slice(&self) -> &[T] {
        // SAFETY: `start..end` are initialized and owned by the iterator,
        // and the pointer covers the whole buffer.
        unsafe { slice::from_raw_parts(self.vec.as_ptr().add(self.start), self.end - self.start) }
    }
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        if self.start == self.end {
            return None;
        }
        // SAFETY: `start < end`, so this element is initialized; `start`
        // moves past it, so it is read only once.
        let value = unsafe { ptr::read(self.vec.as_ptr().add(self.start)) };
        self.start += 1;
        Some(value)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.start;
        (remaining, Some(remaining))
    }
}

impl<T, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        if self.start == self.end {
            return None;
        }
        self.end -= 1;
        // SAFETY: as in `next`, from the other end.
        Some(unsafe { ptr::read(self.vec.as_ptr().add(self.end)) })
    }
}

impl<T, const N: usize> ExactSizeIterator for IntoIter<T, N> {}
impl<T, const N: usize> FusedIterator for IntoIter<T, N> {}

impl<T, const N: usize> Drop for IntoIter<T, N> {
    fn drop(&mut self) {
        // SAFETY: `start..end` are initialized, owned by the iterator and
        // not yet yielded, so they are dropped exactly once here. The `vec`
        // field (length 0) then frees its buffer, if it has one, when the
        // fields are dropped, even if a destructor above panics.
        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                self.vec.as_mut_ptr().add(self.start),
                self.end - self.start,
            ));
        }
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for IntoIter<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIter").field(&self.as_slice()).finish()
    }
}

/// A draining iterator for [`InlineVec`]. Created by [`InlineVec::drain`].
///
/// The drained range is removed from the vector when the iterator is dropped,
/// whether or not it was run to the end.
// Implementation notes: modeled on `Vec`'s `Drain`. While it exists, the
// vector's length is set to where the drained range starts, so the drained
// elements and the tail after them are not reachable from the vector; the
// `Drain` owns them. On drop the remaining drained elements are dropped and
// the tail is moved back, even if a destructor panics.
pub struct Drain<'a, T, const N: usize> {
    vec: NonNull<InlineVec<T, N>>,
    /// The start of the vector's buffer, for reading the drained elements.
    base: *mut T,
    /// Next element to yield from the front / one past the next from the
    /// back.
    cur: usize,
    end: usize,
    /// Where the tail (the elements after the drained range) starts, and
    /// how many it has.
    tail_start: usize,
    tail_len: usize,
    _marker: PhantomData<&'a mut InlineVec<T, N>>,
}

impl<T, const N: usize> Iterator for Drain<'_, T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        if self.cur == self.end {
            return None;
        }
        // SAFETY: `cur < end`, and `cur..end` are initialized elements
        // owned by this `Drain`; `cur` moves past this one, so it is read
        // only once.
        let value = unsafe { ptr::read(self.base.add(self.cur)) };
        self.cur += 1;
        Some(value)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.cur;
        (remaining, Some(remaining))
    }
}

impl<T, const N: usize> DoubleEndedIterator for Drain<'_, T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        if self.cur == self.end {
            return None;
        }
        self.end -= 1;
        // SAFETY: as in `next`, from the other end.
        Some(unsafe { ptr::read(self.base.add(self.end)) })
    }
}

impl<T, const N: usize> ExactSizeIterator for Drain<'_, T, N> {}
impl<T, const N: usize> FusedIterator for Drain<'_, T, N> {}

impl<T, const N: usize> Drop for Drain<'_, T, N> {
    fn drop(&mut self) {
        /// Moves the tail back and restores the length when dropped, so that
        /// it happens even if dropping the remaining elements panics.
        struct MoveTail<'r, 'a, T, const N: usize>(&'r mut Drain<'a, T, N>);

        impl<T, const N: usize> Drop for MoveTail<'_, '_, T, N> {
            fn drop(&mut self) {
                let drain = &mut *self.0;
                if drain.tail_len > 0 {
                    // SAFETY: the `Drain` has exclusive access to the vector
                    // (it holds its `&mut` borrow). The vector's length is
                    // `start` and the tail `[tail_start, tail_start +
                    // tail_len)` is initialized and owned by the drain, so
                    // moving it down to `start` (`ptr::copy` handles the
                    // overlap) and extending the length hands it back.
                    unsafe {
                        let vec = drain.vec.as_mut();
                        let start = vec.len();
                        if drain.tail_start != start {
                            let base = vec.as_mut_ptr();
                            ptr::copy(base.add(drain.tail_start), base.add(start), drain.tail_len);
                        }
                        vec.set_len(start + drain.tail_len);
                    }
                }
            }
        }

        let remaining = self.end - self.cur;
        let guard = MoveTail(self);
        if remaining > 0 {
            // SAFETY: `cur..end` are initialized, owned by the drain and not
            // yet yielded, so they are dropped exactly once here. The pointer
            // is derived afresh from the vector, not from the earlier `base`.
            unsafe {
                let vec = guard.0.vec.as_mut();
                let first = vec.as_mut_ptr().add(guard.0.cur);
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(first, remaining));
            }
        }
        // `guard` drops here, and also if the line above unwinds.
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for Drain<'_, T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Drain")
            .field("remaining", &(self.end - self.cur))
            .finish()
    }
}

/// Counts the buffer that the elements moved to once they no longer fit
/// inline, which is `0` before that.
impl<T, const N: usize> HeapSize for InlineVec<T, N> {
    fn heap_size(&self) -> usize {
        match &self.repr {
            Repr::Inline { .. } => 0,
            Repr::Heap(vec) => vec.capacity() * size_of::<T>(),
        }
    }
}

#[cfg(test)]
mod tests {
    // Test values are small and narrowed on purpose, and helper types are
    // declared next to the test that uses them.
    #![allow(clippy::cast_possible_truncation, clippy::items_after_statements)]
    use super::*;
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::rc::Rc;

    fn inline_vec<const N: usize>(items: &[u32]) -> InlineVec<u32, N> {
        items.iter().copied().collect()
    }

    /// Whether `p` points into the memory of `v` itself (inline storage).
    fn points_inside<T, const N: usize>(v: &InlineVec<T, N>, p: *const T) -> bool {
        let start = std::ptr::from_ref(v) as usize;
        let addr = p as usize;
        addr >= start && addr < start + core::mem::size_of_val(v)
    }

    // ---- inline / spilled behaviour ----

    #[test]
    fn new_is_empty_inline_and_does_not_allocate() {
        let v: InlineVec<u32, 4> = InlineVec::new();
        assert!(v.is_empty());
        assert_eq!(v.len(), 0);
        assert!(!v.spilled());
        assert_eq!(v.capacity(), 4);
        assert_eq!(InlineVec::<u32, 4>::INLINE_CAPACITY, 4);
        assert_eq!(v.as_slice(), &[] as &[u32]);

        const EMPTY: InlineVec<u8, 3> = InlineVec::new(); // usable in const context
        assert!(EMPTY.is_empty());
    }

    #[test]
    fn elements_stay_inside_the_struct_up_to_n() {
        let mut v: InlineVec<u32, 4> = InlineVec::new();
        for i in 0..4 {
            v.push(i);
            assert!(!v.spilled());
            assert!(points_inside(&v, v.as_ptr()));
        }
        assert_eq!(v, [0, 1, 2, 3]);
    }

    #[test]
    fn pushing_past_n_spills_and_keeps_order() {
        let mut v: InlineVec<u32, 4> = inline_vec(&[0, 1, 2, 3]);
        v.push(4);
        assert!(v.spilled());
        assert!(!points_inside(&v, v.as_ptr()));
        assert!(v.capacity() >= 5);
        assert_eq!(v, [0, 1, 2, 3, 4]);
        for i in 5..100 {
            v.push(i);
        }
        assert_eq!(v.len(), 100);
        assert!(v.iter().copied().eq(0..100));
    }

    #[test]
    fn stays_spilled_until_shrink_to_fit() {
        let mut v: InlineVec<u32, 4> = inline_vec(&[0, 1, 2, 3, 4, 5]);
        assert!(v.spilled());
        v.truncate(2);
        assert!(v.spilled()); // sticky
        v.shrink_to_fit();
        assert!(!v.spilled());
        assert!(points_inside(&v, v.as_ptr()));
        assert_eq!(v, [0, 1]);

        // Too many for inline: shrinks the heap buffer but stays spilled.
        let mut big: InlineVec<u32, 4> = InlineVec::with_capacity(100);
        big.extend(0..10);
        big.shrink_to_fit();
        assert!(big.spilled());
        assert!(big.capacity() < 100);
        assert_eq!(big.len(), 10);
    }

    #[test]
    fn shrink_to_fit_moves_owned_values_back_inline() {
        let mut v: InlineVec<String, 3> = ["a", "b", "c", "d", "e"].map(String::from).into();
        v.truncate(2);
        v.shrink_to_fit();
        assert!(!v.spilled());
        assert_eq!(v, ["a".to_string(), "b".to_string()]);
        v.push("c".to_string());
        assert_eq!(v.len(), 3);
        assert!(!v.spilled());
    }

    #[test]
    fn with_capacity_and_reserve() {
        let small: InlineVec<u32, 4> = InlineVec::with_capacity(3);
        assert!(!small.spilled());
        let large: InlineVec<u32, 4> = InlineVec::with_capacity(10);
        assert!(large.spilled());
        assert!(large.capacity() >= 10);
        assert!(large.is_empty());

        let mut v: InlineVec<u32, 4> = inline_vec(&[1, 2]);
        v.reserve(2); // 4 total: still fits
        assert!(!v.spilled());
        v.reserve(3); // 5 total: does not
        assert!(v.spilled());
        assert!(v.capacity() >= 5);
        assert_eq!(v, [1, 2]);
        v.reserve(100);
        assert!(v.capacity() >= 102);
    }

    #[test]
    fn zero_inline_capacity_always_uses_the_heap() {
        let mut v: InlineVec<u32, 0> = InlineVec::new();
        assert_eq!(v.capacity(), 0);
        v.push(1);
        assert!(v.spilled());
        v.extend([2, 3]);
        assert_eq!(v, [1, 2, 3]);
        assert_eq!(v.pop(), Some(3));
        v.shrink_to_fit();
        assert!(v.spilled()); // nothing fits inline

        let mut one: InlineVec<u32, 1> = InlineVec::new();
        one.push(1);
        assert!(!one.spilled());
        one.push(2);
        assert!(one.spilled());
        assert_eq!(one, [1, 2]);
    }

    #[test]
    fn zero_sized_elements() {
        let mut v: InlineVec<(), 4> = InlineVec::new();
        for _ in 0..3 {
            v.push(());
        }
        assert_eq!(v.len(), 3);
        assert!(!v.spilled());
        for _ in 0..10 {
            v.push(());
        }
        assert_eq!(v.len(), 13);
        assert_eq!(v.pop(), Some(()));
        v.insert(2, ());
        v.remove(0);
        assert_eq!(v.len(), 12);
        assert_eq!(v.drain(3..7).count(), 4);
        assert_eq!(v.len(), 8);
        assert_eq!(v.into_iter().count(), 8);
    }

    #[test]
    fn moving_the_vec_keeps_its_elements() {
        let v: InlineVec<String, 4> = ["a", "b", "c"].map(String::from).into();
        let boxed = Box::new(v);
        let back = *boxed;
        assert_eq!(back, ["a".to_string(), "b".to_string(), "c".to_string()]);
        assert!(!back.spilled());
    }

    #[test]
    fn overaligned_elements_are_aligned() {
        #[repr(align(64))]
        #[derive(Debug, PartialEq)]
        struct Aligned(u8);

        let mut v: InlineVec<Aligned, 3> = InlineVec::new();
        v.push(Aligned(1));
        v.push(Aligned(2));
        assert_eq!(v.as_ptr() as usize % 64, 0);
        assert_eq!(&raw const v[1] as usize % 64, 0);
        v.insert(0, Aligned(0));
        v.push(Aligned(3)); // spills
        assert_eq!(v.as_ptr() as usize % 64, 0);
        assert_eq!(v.iter().map(|a| a.0).collect::<Vec<_>>(), vec![0, 1, 2, 3]);
    }

    #[test]
    fn send_and_sync_follow_the_element_type() {
        fn assert_send_sync<X: Send + Sync>() {}
        assert_send_sync::<InlineVec<u32, 4>>();
        assert_send_sync::<InlineVec<String, 0>>();
        assert_send_sync::<IntoIter<u32, 4>>();
    }

    // ---- element operations ----

    #[test]
    fn push_and_pop() {
        let mut v: InlineVec<u32, 2> = InlineVec::new();
        assert_eq!(v.pop(), None);
        v.push(1);
        v.push(2);
        v.push(3);
        assert_eq!(v.pop(), Some(3));
        assert_eq!(v.pop(), Some(2));
        assert_eq!(v.pop(), Some(1));
        assert_eq!(v.pop(), None);
    }

    #[test]
    fn insert_at_every_position_matches_vec() {
        for len in 0..=7usize {
            for index in 0..=len {
                let mut v: InlineVec<u32, 4> = (0..len as u32).collect();
                let mut model: Vec<u32> = (0..len as u32).collect();
                v.insert(index, 99);
                model.insert(index, 99);
                assert_eq!(v.as_slice(), model.as_slice(), "len={len} index={index}");
            }
        }
    }

    #[test]
    fn remove_at_every_position_matches_vec() {
        for len in 1..=7usize {
            for index in 0..len {
                let mut v: InlineVec<u32, 4> = (0..len as u32).collect();
                let mut model: Vec<u32> = (0..len as u32).collect();
                assert_eq!(v.remove(index), model.remove(index));
                assert_eq!(v.as_slice(), model.as_slice(), "len={len} index={index}");
            }
        }
    }

    #[test]
    fn swap_remove_at_every_position_matches_vec() {
        for len in 1..=7usize {
            for index in 0..len {
                let mut v: InlineVec<u32, 4> = (0..len as u32).collect();
                let mut model: Vec<u32> = (0..len as u32).collect();
                assert_eq!(v.swap_remove(index), model.swap_remove(index));
                assert_eq!(v.as_slice(), model.as_slice(), "len={len} index={index}");
            }
        }
    }

    #[test]
    #[should_panic(expected = "insertion index")]
    fn insert_past_the_end_panics() {
        let mut v: InlineVec<u32, 4> = inline_vec(&[1, 2]);
        v.insert(3, 0);
    }

    #[test]
    #[should_panic(expected = "removal index")]
    fn remove_out_of_bounds_panics() {
        let mut v: InlineVec<u32, 4> = inline_vec(&[1, 2]);
        v.remove(2);
    }

    #[test]
    #[should_panic(expected = "swap_remove index")]
    fn swap_remove_out_of_bounds_panics() {
        let mut v: InlineVec<u32, 4> = InlineVec::new();
        v.swap_remove(0);
    }

    #[test]
    fn truncate_clear_and_resize() {
        let mut v: InlineVec<u32, 4> = (0..6).collect();
        v.truncate(10); // longer than len: no-op
        assert_eq!(v.len(), 6);
        v.truncate(3);
        assert_eq!(v, [0, 1, 2]);
        v.clear();
        assert!(v.is_empty());
        assert!(v.spilled()); // clear keeps the heap buffer

        let mut w: InlineVec<u32, 4> = inline_vec(&[1, 2]);
        w.resize(4, 7);
        assert_eq!(w, [1, 2, 7, 7]);
        assert!(!w.spilled());
        w.resize(6, 9);
        assert!(w.spilled());
        assert_eq!(w, [1, 2, 7, 7, 9, 9]);
        w.resize(1, 0);
        assert_eq!(w, [1]);
    }

    #[test]
    fn retain_and_retain_mut_preserve_order() {
        for len in [3usize, 9] {
            let mut v: InlineVec<u32, 4> = (0..len as u32).collect();
            v.retain(|x| x % 3 != 1);
            let expected: Vec<u32> = (0..len as u32).filter(|x| x % 3 != 1).collect();
            assert_eq!(v.as_slice(), expected.as_slice());

            let mut w: InlineVec<u32, 4> = (0..len as u32).collect();
            w.retain_mut(|x| {
                *x += 100;
                *x % 2 == 0
            });
            let expected: Vec<u32> = (0..len as u32)
                .map(|x| x + 100)
                .filter(|x| x % 2 == 0)
                .collect();
            assert_eq!(w.as_slice(), expected.as_slice());
        }
    }

    #[test]
    fn extend_and_extend_from_slice() {
        let mut v: InlineVec<u32, 4> = InlineVec::new();
        v.extend([1, 2]);
        v.extend(&[3]);
        v.extend_from_slice(&[4, 5]);
        assert_eq!(v, [1, 2, 3, 4, 5]);
        assert!(v.spilled());

        let mut s: InlineVec<String, 2> = InlineVec::new();
        s.extend_from_slice(&["x".to_string(), "y".to_string(), "z".to_string()]);
        assert_eq!(s.len(), 3);
    }

    // ---- conversions ----

    #[test]
    fn from_arrays_of_any_length() {
        let small = InlineVec::<u32, 4>::from([1, 2]);
        assert!(!small.spilled());
        let exact = InlineVec::<u32, 4>::from([1, 2, 3, 4]);
        assert!(!exact.spilled());
        let big = InlineVec::<u32, 4>::from([1, 2, 3, 4, 5]);
        assert!(big.spilled());
        assert_eq!(big, [1, 2, 3, 4, 5]);
        let empty = InlineVec::<u32, 4>::from([0u32; 0]);
        assert!(empty.is_empty());
    }

    #[test]
    fn from_slice_and_from_iterator() {
        let v =
            InlineVec::<String, 2>::from(&["a".to_string(), "b".to_string(), "c".to_string()][..]);
        assert_eq!(v.len(), 3);
        let w: InlineVec<u32, 4> = (1..=3).collect();
        assert_eq!(w, [1, 2, 3]);
    }

    #[test]
    fn from_vec_reuses_the_buffer() {
        let vec = vec![1u32, 2, 3];
        let ptr = vec.as_ptr();
        let v = InlineVec::<u32, 8>::from(vec);
        assert!(v.spilled()); // even though it would fit inline
        assert_eq!(v.as_ptr(), ptr);

        let back: Vec<u32> = v.into();
        assert_eq!(back.as_ptr(), ptr);
        assert_eq!(back, vec![1, 2, 3]);
    }

    #[test]
    fn into_vec_inline_and_spilled() {
        let inline = InlineVec::<String, 4>::from(["a", "b"].map(String::from));
        assert_eq!(inline.into_vec(), vec!["a".to_string(), "b".to_string()]);
        let heap = InlineVec::<String, 1>::from(["a", "b", "c"].map(String::from));
        assert_eq!(
            heap.into_vec(),
            vec!["a".to_string(), "b".to_string(), "c".to_string()]
        );
        let empty: InlineVec<String, 2> = InlineVec::new();
        assert_eq!(empty.into_vec(), [] as [std::string::String; 0]);
    }

    // ---- drain ----

    #[test]
    fn drain_every_range_matches_vec() {
        for len in 0..=7usize {
            for start in 0..=len {
                for end in start..=len {
                    let mut v: InlineVec<String, 4> = (0..len).map(|i| i.to_string()).collect();
                    let mut model: Vec<String> = (0..len).map(|i| i.to_string()).collect();
                    let got: Vec<String> = v.drain(start..end).collect();
                    let want: Vec<String> = model.drain(start..end).collect();
                    assert_eq!(got, want, "len={len} range={start}..{end}");
                    assert_eq!(
                        v.as_slice(),
                        model.as_slice(),
                        "len={len} range={start}..{end}"
                    );
                }
            }
        }
    }

    #[test]
    fn drain_range_kinds() {
        let make = || -> InlineVec<u32, 4> { (0..6).collect() };
        let mut v = make();
        assert_eq!(v.drain(..).collect::<Vec<_>>(), vec![0, 1, 2, 3, 4, 5]);
        assert!(v.is_empty());
        let mut v = make();
        assert_eq!(v.drain(2..).collect::<Vec<_>>(), vec![2, 3, 4, 5]);
        assert_eq!(v, [0, 1]);
        let mut v = make();
        assert_eq!(v.drain(..=1).collect::<Vec<_>>(), vec![0, 1]);
        assert_eq!(v, [2, 3, 4, 5]);
        let mut v = make();
        assert_eq!(v.drain(1..=1).collect::<Vec<_>>(), vec![1]);
        assert_eq!(v, [0, 2, 3, 4, 5]);
        let mut v = make();
        assert_eq!(v.drain(3..3).count(), 0);
        assert_eq!(v.len(), 6);
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn drain_past_the_end_panics() {
        let mut v: InlineVec<u32, 4> = inline_vec(&[1, 2, 3]);
        v.drain(1..5);
    }

    #[test]
    #[should_panic(expected = "starts at")]
    #[allow(clippy::reversed_empty_ranges)]
    fn drain_decreasing_range_panics() {
        let mut v: InlineVec<u32, 4> = inline_vec(&[1, 2, 3]);
        v.drain(2..1);
    }

    #[test]
    fn drain_from_both_ends_and_partial_consumption() {
        for len in [4usize, 8] {
            let mut v: InlineVec<String, 4> = (0..len).map(|i| i.to_string()).collect();
            let mut drain = v.drain(1..len - 1);
            assert_eq!(drain.len(), len - 2);
            assert_eq!(drain.next().as_deref(), Some("1"));
            assert_eq!(
                drain.next_back().as_deref(),
                Some((len - 2).to_string().as_str())
            );
            assert_eq!(drain.len(), len - 4);
            drop(drain); // the rest is dropped, the tail moved back
            let expected: Vec<String> = vec!["0".to_string(), (len - 1).to_string()];
            assert_eq!(v.as_slice(), expected.as_slice());
        }
    }

    #[test]
    fn leaking_a_drain_leaves_a_valid_vec() {
        let mut v: InlineVec<u32, 4> = (0..6).collect();
        core::mem::forget(v.drain(2..4));
        // Elements from the range start are gone, nothing else is exposed.
        assert_eq!(v, [0, 1]);
        v.push(7);
        assert_eq!(v, [0, 1, 7]);

        let mut w: InlineVec<u32, 8> = (0..5).collect();
        core::mem::forget(w.drain(1..3));
        assert_eq!(w, [0]);
    }

    #[test]
    fn drain_debug() {
        let mut v: InlineVec<u32, 4> = (0..4).collect();
        assert_eq!(format!("{:?}", v.drain(1..3)), "Drain { remaining: 2 }");
    }

    // ---- into_iter ----

    #[test]
    fn into_iter_yields_everything_inline_and_spilled() {
        for len in [0usize, 3, 4, 5, 9] {
            let v: InlineVec<String, 4> = (0..len).map(|i| i.to_string()).collect();
            let collected: Vec<String> = v.into_iter().collect();
            assert_eq!(
                collected,
                (0..len).map(|i| i.to_string()).collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn into_iter_is_double_ended_exact_size_and_fused() {
        let v: InlineVec<String, 4> = (0..6).map(|i| i.to_string()).collect();
        let mut iter = v.into_iter();
        assert_eq!(iter.len(), 6);
        assert_eq!(iter.next().as_deref(), Some("0"));
        assert_eq!(iter.next_back().as_deref(), Some("5"));
        assert_eq!(iter.as_slice(), ["1", "2", "3", "4"].map(String::from));
        assert_eq!(iter.size_hint(), (4, Some(4)));
        assert_eq!(iter.by_ref().count(), 4);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn into_iter_debug() {
        let v: InlineVec<u32, 4> = (1..=3).collect();
        let mut iter = v.into_iter();
        iter.next();
        assert_eq!(format!("{iter:?}"), "IntoIter([2, 3])");
    }

    #[test]
    fn iteration_by_reference() {
        let mut v: InlineVec<u32, 4> = (1..=3).collect();
        for x in &mut v {
            *x *= 10;
        }
        let sum: u32 = (&v).into_iter().sum();
        assert_eq!(sum, 60);
    }

    // ---- trait impls ----

    #[test]
    fn slice_methods_through_deref() {
        let mut v: InlineVec<u32, 4> = inline_vec(&[3, 1, 2]);
        v.sort_unstable();
        assert_eq!(v, [1, 2, 3]);
        assert_eq!(v.binary_search(&2), Ok(1));
        assert_eq!(v.first(), Some(&1));
        assert_eq!(v.last(), Some(&3));
        assert!(v.contains(&3));
        assert_eq!(v[1], 2);
        assert_eq!(&v[1..], [2, 3]);
        v[0] = 10;
        assert_eq!(v.iter().rev().copied().collect::<Vec<_>>(), vec![3, 2, 10]);
        v.reverse();
        assert_eq!(v, [3, 2, 10]);
        assert_eq!(v.windows(2).count(), 2);

        let mut big: InlineVec<u32, 2> = (0..20).rev().collect();
        big.sort_unstable();
        assert!(big.windows(2).all(|w| w[0] <= w[1]));
    }

    #[test]
    fn clone_is_independent_and_debug_matches_slice() {
        for len in [2usize, 6] {
            let v: InlineVec<String, 4> = (0..len).map(|i| i.to_string()).collect();
            let mut copy = v.clone();
            copy[0].push('!');
            copy.push("new".to_string());
            assert_eq!(v[0], "0");
            assert_eq!(v.len(), len);
            assert_eq!(copy.len(), len + 1);
        }
        let v: InlineVec<u32, 4> = inline_vec(&[1, 2]);
        assert_eq!(format!("{v:?}"), "[1, 2]");
        assert_eq!(format!("{v:#?}"), format!("{:#?}", [1, 2]));
    }

    #[test]
    fn clone_keeps_the_storage_kind() {
        let inline: InlineVec<u32, 4> = inline_vec(&[1, 2]);
        assert!(!inline.spilled());
        let copy = inline;
        assert!(points_inside(&copy, copy.as_ptr()));
        let spilled: InlineVec<u32, 4> = inline_vec(&[1, 2, 3, 4, 5]);
        assert!(spilled.spilled());
        // A spilled vector that would fit inline stays spilled when cloned.
        let mut shrunk = spilled;
        shrunk.truncate(2);
        assert!(shrunk.clone().spilled());
        assert_eq!(shrunk.clone(), [1, 2]);
    }

    #[test]
    fn equality_across_types_and_capacities() {
        let a: InlineVec<u32, 4> = inline_vec(&[1, 2, 3]);
        let b: InlineVec<u32, 8> = inline_vec(&[1, 2, 3]);
        let c: InlineVec<u32, 1> = inline_vec(&[1, 2, 3]); // spilled
        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(a, [1, 2, 3]);
        assert_eq!(a, vec![1, 2, 3]);
        assert_eq!(a, &[1u32, 2, 3][..]);
        assert_eq!(a, *[1u32, 2, 3].as_slice());
        assert_ne!(a, [1, 2]);
        assert_ne!(a, inline_vec::<4>(&[1, 2, 4]));
    }

    #[test]
    fn ordering_and_hashing_match_slices() {
        use std::collections::hash_map::DefaultHasher;

        let a: InlineVec<u32, 4> = inline_vec(&[1, 2, 3]);
        let b: InlineVec<u32, 4> = inline_vec(&[1, 2, 4]);
        assert!(a < b);
        assert_eq!(a.cmp(&b), Ordering::Less);
        assert_eq!(a.partial_cmp(&a), Some(Ordering::Equal));

        let hash = |value: &dyn Fn(&mut DefaultHasher)| {
            let mut hasher = DefaultHasher::new();
            value(&mut hasher);
            hasher.finish()
        };
        let spilled: InlineVec<u32, 1> = inline_vec(&[1, 2, 3]);
        assert_eq!(hash(&|h| a.hash(h)), hash(&|h| [1u32, 2, 3][..].hash(h)));
        assert_eq!(hash(&|h| a.hash(h)), hash(&|h| spilled.hash(h)));
    }

    #[test]
    fn borrow_as_ref_and_default() {
        let mut v: InlineVec<u32, 4> = InlineVec::default();
        v.push(5);
        let slice: &[u32] = v.as_ref();
        assert_eq!(slice, [5]);
        let borrowed: &[u32] = core::borrow::Borrow::borrow(&v);
        assert_eq!(borrowed, [5]);
        let mutable: &mut [u32] = v.as_mut();
        mutable[0] = 6;
        assert_eq!(v, [6]);
    }

    // ---- drop accounting ----

    fn live(token: &Rc<()>) -> usize {
        Rc::strong_count(token) - 1
    }

    struct Tracked(#[allow(dead_code)] Rc<()>);

    fn tracked<const N: usize>(token: &Rc<()>, n: usize) -> InlineVec<Tracked, N> {
        (0..n).map(|_| Tracked(Rc::clone(token))).collect()
    }

    #[test]
    fn dropping_drops_every_element_inline_and_spilled() {
        for n in [0usize, 3, 4, 5, 10] {
            let token = Rc::new(());
            let v = tracked::<4>(&token, n);
            assert_eq!(live(&token), n);
            drop(v);
            assert_eq!(live(&token), 0, "n={n}");
        }
    }

    #[test]
    fn spilling_moves_elements_without_cloning_or_dropping() {
        let token = Rc::new(());
        let mut v = tracked::<4>(&token, 4);
        assert_eq!(live(&token), 4);
        v.push(Tracked(Rc::clone(&token))); // spills
        assert!(v.spilled());
        assert_eq!(live(&token), 5);
        v.shrink_to_fit();
        assert_eq!(live(&token), 5);
        v.truncate(3);
        assert_eq!(live(&token), 3);
        v.shrink_to_fit(); // back inline
        assert!(!v.spilled());
        assert_eq!(live(&token), 3);
    }

    #[test]
    fn removal_operations_drop_exactly_what_they_remove() {
        for n in [5usize, 8] {
            let token = Rc::new(());
            let mut v = tracked::<4>(&token, n);
            drop(v.pop());
            assert_eq!(live(&token), n - 1);
            drop(v.remove(0));
            assert_eq!(live(&token), n - 2);
            drop(v.swap_remove(0));
            assert_eq!(live(&token), n - 3);
            v.truncate(1);
            assert_eq!(live(&token), 1);
            v.clear();
            assert_eq!(live(&token), 0);
        }
    }

    #[test]
    fn retain_resize_extend_and_insert_track_ownership() {
        let token = Rc::new(());
        let mut v = tracked::<4>(&token, 6);
        let mut i = 0;
        v.retain(|_| {
            i += 1;
            i % 2 == 0
        });
        assert_eq!(live(&token), 3);
        v.insert(1, Tracked(Rc::clone(&token)));
        assert_eq!(live(&token), 4);
        v.extend((0..3).map(|_| Tracked(Rc::clone(&token))));
        assert_eq!(live(&token), 7);
        drop(v);
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn drain_and_into_iter_release_what_they_own() {
        for n in [3usize, 8] {
            let token = Rc::new(());
            let mut v = tracked::<4>(&token, n);
            let mut drain = v.drain(1..n);
            drop(drain.next());
            assert_eq!(live(&token), n - 1);
            drop(drain);
            assert_eq!(live(&token), 1);
            drop(v);
            assert_eq!(live(&token), 0);

            let v = tracked::<4>(&token, n);
            let mut iter = v.into_iter();
            drop(iter.next());
            drop(iter.next_back());
            assert_eq!(live(&token), n - 2);
            drop(iter);
            assert_eq!(live(&token), 0);
        }
    }

    #[test]
    fn into_vec_and_from_vec_transfer_ownership() {
        let token = Rc::new(());
        let v = tracked::<4>(&token, 3);
        let vec = v.into_vec();
        assert_eq!(live(&token), 3);
        let back = InlineVec::<Tracked, 2>::from(vec);
        assert_eq!(live(&token), 3);
        drop(back);
        assert_eq!(live(&token), 0);
    }

    // ---- panic safety ----

    /// Panics when dropped if `explode` is set (unless already unwinding).
    struct Bomb {
        _token: Rc<()>,
        explode: bool,
    }

    impl Drop for Bomb {
        fn drop(&mut self) {
            assert!(!self.explode || std::thread::panicking(), "bomb");
        }
    }

    fn bombs<const N: usize>(token: &Rc<()>, n: usize, explode_at: usize) -> InlineVec<Bomb, N> {
        (0..n)
            .map(|i| Bomb {
                _token: Rc::clone(token),
                explode: i == explode_at,
            })
            .collect()
    }

    #[test]
    fn a_panicking_destructor_in_truncate_still_drops_the_rest_once() {
        for count in [3usize, 6] {
            let token = Rc::new(());
            let mut v = bombs::<4>(&token, count, 1);
            let result = catch_unwind(AssertUnwindSafe(|| v.truncate(1)));
            assert!(result.is_err());
            assert_eq!(v.len(), 1);
            assert_eq!(live(&token), 1, "count={count}");
            drop(v);
            assert_eq!(live(&token), 0);
        }
    }

    #[test]
    fn a_panicking_destructor_in_drain_still_restores_the_tail() {
        for count in [3usize, 6] {
            let token = Rc::new(());
            let mut v = bombs::<4>(&token, count, 1);
            let result = catch_unwind(AssertUnwindSafe(|| {
                let drain = v.drain(1..3);
                drop(drain);
            }));
            assert!(result.is_err());
            assert_eq!(v.len(), count - 2, "count={count}");
            assert_eq!(live(&token), v.len());
            drop(v);
            assert_eq!(live(&token), 0);
        }
    }

    #[test]
    fn a_panicking_destructor_in_into_iter_drops_everything_once() {
        for count in [3usize, 6] {
            let token = Rc::new(());
            let v = bombs::<4>(&token, count, 2);
            let mut iter = v.into_iter();
            drop(iter.next());
            let result = catch_unwind(AssertUnwindSafe(move || drop(iter)));
            assert!(result.is_err());
            assert_eq!(live(&token), 0, "count={count}");
        }
    }

    #[test]
    fn a_panicking_destructor_when_dropping_the_vec_drops_the_rest() {
        for count in [3usize, 6] {
            let token = Rc::new(());
            let v = bombs::<4>(&token, count, 1);
            let result = catch_unwind(AssertUnwindSafe(move || drop(v)));
            assert!(result.is_err());
            assert_eq!(live(&token), 0, "count={count}");
        }
    }

    struct CloneBomb {
        token: Rc<()>,
        explode: bool,
    }

    impl Clone for CloneBomb {
        fn clone(&self) -> Self {
            assert!(!self.explode, "clone bomb");
            Self {
                token: Rc::clone(&self.token),
                explode: false,
            }
        }
    }

    #[test]
    fn a_panicking_clone_does_not_leak_the_clones_made_so_far() {
        for count in [3usize, 6] {
            let token = Rc::new(());
            let v: InlineVec<CloneBomb, 4> = (0..count)
                .map(|i| CloneBomb {
                    token: Rc::clone(&token),
                    explode: i == 2,
                })
                .collect();
            assert_eq!(live(&token), count);
            let result = catch_unwind(AssertUnwindSafe(|| v.clone()));
            assert!(result.is_err());
            assert_eq!(live(&token), count, "count={count}");
            drop(v);
            assert_eq!(live(&token), 0);
        }
    }

    #[test]
    fn a_panicking_iterator_in_extend_keeps_what_was_pushed() {
        let token = Rc::new(());
        let mut v: InlineVec<Tracked, 2> = InlineVec::new();
        let mut produced = 0;
        let result = catch_unwind(AssertUnwindSafe(|| {
            v.extend(core::iter::from_fn(|| {
                produced += 1;
                assert!(produced != 4, "iterator failed");
                Some(Tracked(Rc::clone(&token)))
            }));
        }));
        assert!(result.is_err());
        assert_eq!(v.len(), 3);
        assert_eq!(live(&token), 3);
        drop(v);
        assert_eq!(live(&token), 0);
    }

    #[test]
    fn a_panicking_retain_closure_leaves_a_valid_vec() {
        for count in [3usize, 8] {
            let token = Rc::new(());
            let mut v = tracked::<4>(&token, count);
            let mut seen = 0;
            let result = catch_unwind(AssertUnwindSafe(|| {
                v.retain(|_| {
                    seen += 1;
                    assert!(seen != 3, "closure failed");
                    seen % 2 == 0
                });
            }));
            assert!(result.is_err());
            assert_eq!(v.len(), count);
            assert_eq!(live(&token), count);
            drop(v);
            assert_eq!(live(&token), 0);
        }
    }

    // ---- randomized comparison with Vec ----

    fn compare_with_vec<const N: usize>(seed: u64, steps: usize) {
        let mut state = seed;
        let mut next = move || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            state >> 33
        };

        let mut v: InlineVec<String, N> = InlineVec::new();
        let mut model: Vec<String> = Vec::new();
        for step in 0..steps {
            let len = model.len();
            match next() % 14 {
                0..=2 => {
                    let s = format!("v{step}");
                    v.push(s.clone());
                    model.push(s);
                }
                3 => assert_eq!(v.pop(), model.pop()),
                4 | 5 => {
                    let index = (next() as usize) % (len + 1);
                    let s = format!("i{step}");
                    v.insert(index, s.clone());
                    model.insert(index, s);
                }
                6 if len > 0 => {
                    let index = (next() as usize) % len;
                    assert_eq!(v.remove(index), model.remove(index));
                }
                7 if len > 0 => {
                    let index = (next() as usize) % len;
                    assert_eq!(v.swap_remove(index), model.swap_remove(index));
                }
                8 => {
                    let new_len = (next() as usize) % (len + 2);
                    v.truncate(new_len);
                    model.truncate(new_len);
                }
                9 => {
                    let keep = (next() % 3) as usize;
                    v.retain(|s| s.len() % 3 != keep);
                    model.retain(|s| s.len() % 3 != keep);
                }
                10 => {
                    let a = (next() as usize) % (len + 1);
                    let b = a + (next() as usize) % (len - a + 1);
                    let got: Vec<String> = v.drain(a..b).collect();
                    let want: Vec<String> = model.drain(a..b).collect();
                    assert_eq!(got, want);
                }
                11 => {
                    let extra: Vec<String> =
                        (0..next() % 4).map(|i| format!("e{step}.{i}")).collect();
                    v.extend(extra.clone());
                    model.extend(extra);
                }
                12 => {
                    v.shrink_to_fit();
                    let clone = v.clone();
                    assert_eq!(clone.as_slice(), model.as_slice());
                }
                _ => {
                    if next() % 8 == 0 {
                        let round_trip = core::mem::take(&mut v).into_vec();
                        assert_eq!(round_trip, model);
                        v = InlineVec::from(round_trip);
                    } else {
                        v.reserve((next() % 6) as usize);
                    }
                }
            }
            assert_eq!(v.as_slice(), model.as_slice(), "step {step}");
            assert!(v.capacity() >= v.len());
            if !v.spilled() {
                assert!(v.len() <= N);
                assert!(points_inside(&v, v.as_ptr()) || N == 0 || v.is_empty());
            }
        }
    }

    #[test]
    fn matches_vec_under_random_operations() {
        let steps = if cfg!(miri) { 120 } else { 5_000 };
        compare_with_vec::<0>(1, steps);
        compare_with_vec::<1>(2, steps);
        compare_with_vec::<4>(3, steps);
        compare_with_vec::<8>(4, steps);
    }

    #[test]
    fn heap_size_is_zero_while_inline_and_the_buffer_after() {
        let mut v = InlineVec::<u32, 4>::new();
        assert_eq!(v.heap_size(), 0);
        v.extend([1, 2, 3, 4]);
        assert_eq!(v.heap_size(), 0);

        v.push(5);
        assert!(v.heap_size() >= 5 * size_of::<u32>());
        assert_eq!(v.heap_size(), v.capacity() * size_of::<u32>());

        // Unused capacity still counts.
        v.clear();
        assert_eq!(v.heap_size(), v.capacity() * size_of::<u32>());

        let big = InlineVec::<u64, 2>::with_capacity(100);
        assert_eq!(big.heap_size(), big.capacity() * size_of::<u64>());
    }

    #[test]
    fn heap_size_ignores_zero_sized_elements() {
        let mut v = InlineVec::<(), 1>::new();
        v.extend([(), (), ()]);
        assert_eq!(v.heap_size(), 0);
    }

    /// A vector does not store a tag that tells whether it spilled: the length of
    /// the inline elements is never zero (see `Len`), so the compiler uses that
    /// value to mark a vector that spilled. When the inline elements are bigger
    /// than a `Vec`, the vector is exactly as big as they are, with their length.
    #[cfg(target_pointer_width = "64")]
    #[test]
    fn the_spilled_state_takes_no_extra_space() {
        use core::mem::{align_of, size_of};

        fn check<T, const N: usize>() {
            // The length, padded to the alignment of the elements, then the elements.
            let header = align_of::<T>().max(8);
            let inline = (header + N * size_of::<T>()).next_multiple_of(header);
            assert!(
                inline >= 32,
                "only for elements that are bigger than a `Vec`"
            );
            assert_eq!(size_of::<InlineVec<T, N>>(), inline, "N = {N}");
        }

        check::<u8, 32>();
        check::<u32, 8>();
        check::<u32, 16>();
        check::<u64, 4>();
        check::<u64, 8>();
        check::<String, 2>();
        check::<String, 4>();
        check::<u128, 2>();
    }
}
