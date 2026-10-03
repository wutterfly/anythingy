//! A free list: the bookkeeping for handing out parts of one block of memory.
//!
//! See [`FreeList`] for details.

use crate::heap_size::HeapSize;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;
use core::ops::{Add, AddAssign, Sub, SubAssign};

/// Up to this many free ranges, they are kept in a flat sorted vector. One more, and they move
/// into the two indexes.
const SPILL_LEN: usize = 64;

/// Once the free ranges are in the indexes, and there are only this many left, they move back
/// into the vector. It is lower than `SPILL_LEN`, so that a list that hovers around it does not
/// move back and forth with every call.
const UNSPILL_LEN: usize = SPILL_LEN / 2;

mod sealed {
    pub trait Sealed {}
}

/// The unsigned integer types that a [`FreeList`] can count offsets and sizes in: `u16`, `u32`,
/// `u64`, `u128` and `usize`.
///
/// It is sealed: it only exists to be named as a bound, and is not meant to be implemented.
pub trait Offset:
    sealed::Sealed
    + Copy
    + Ord
    + Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + AddAssign
    + SubAssign
{
    /// The number 0.
    const ZERO: Self;

    /// `self + other`, or `None` on overflow.
    #[must_use]
    fn checked_add(self, other: Self) -> Option<Self>;

    /// `self * other`, or `None` on overflow.
    #[must_use]
    fn checked_mul(self, other: Self) -> Option<Self>;

    /// `self / other`, rounded up.
    #[must_use]
    fn div_ceil(self, other: Self) -> Self;
}

macro_rules! offset {
    ($($int:ty),*) => {$(
        impl sealed::Sealed for $int {}

        impl Offset for $int {
            const ZERO: Self = 0;

            fn checked_add(self, other: Self) -> Option<Self> {
                <$int>::checked_add(self, other)
            }

            fn checked_mul(self, other: Self) -> Option<Self> {
                <$int>::checked_mul(self, other)
            }

            fn div_ceil(self, other: Self) -> Self {
                <$int>::div_ceil(self, other)
            }
        }
    )*};
}

offset!(u16, u32, u64, u128, usize);

/// A free range of the block: `size` bytes starting at `offset`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Range<I> {
    offset: I,
    size: I,
}

impl<I: Offset> Range<I> {
    /// The end of the range, which has to be in the block, so it does not overflow.
    fn end(self) -> I {
        self.offset + self.size
    }
}

/// Keeps track of which parts of one block of memory are free, and hands out parts of it.
///
/// It knows nothing about Vulkan, or about pointers: a block is just the range `0..size`, and
/// offsets and sizes are numbers of type `I`, which is `u64` unless said otherwise (`u32` makes
/// the list smaller, `usize` fits offsets into memory of this process). Two free ranges never
/// touch (they are merged when they would), so a block that is entirely free is always a single
/// range.
///
/// Alignment is the alignment of the offset. That is the alignment of the allocation, as long as
/// the block itself starts at a multiple of it, which is the case for the memory of a Vulkan
/// allocation. For memory at an arbitrary address, align the address, not the offset.
///
/// An allocation is exactly the `size` bytes asked for. When alignment forces a gap before it,
/// that gap simply stays free.
///
/// Because a number literal alone does not say which integer type is meant, call it as
/// `FreeList::<u64>::new(1024)` or from a typed value, and not as `FreeList::new(1024)`.
///
/// # Performance
/// While there are few free ranges (up to 64), they are kept in one sorted vector, which is the
/// fastest there is for that few: [`allocate`](Self::allocate) looks at all of them. When the
/// block gets fragmented into more ranges, they move into two indexes, one by offset to merge a
/// range that is freed with its neighbours, and one by size to find the best fit. Then
/// [`allocate`](Self::allocate) and [`free`](Self::free) take time logarithmic in the number of
/// free ranges (`allocate` more only when many ranges that are big enough miss the alignment).
/// The ranges move back into the vector when they get few again. The results are the same
/// either way.
#[derive(Debug, Clone)]
pub struct FreeList<I: Offset = u64> {
    size: I,
    /// The sum of the sizes of the free ranges.
    free_bytes: I,
    ranges: Ranges<I>,
}

/// The free ranges, in one of two layouts. `FreeList` decides which, from how many there are.
#[derive(Debug, Clone)]
enum Ranges<I> {
    /// Sorted by offset.
    Flat {
        ranges: Vec<Range<I>>,
        /// An upper bound of the size of the biggest range, so an allocation that is bigger
        /// fails without a scan. It is exact after a scan that found nothing, and it only grows
        /// in between (when a range is freed).
        largest_hint: I,
    },
    Indexed {
        /// Offset to size.
        by_offset: BTreeMap<I, I>,
        /// The same ranges as `(size, offset)`, which sorts them by size, and by offset among
        /// equal sizes.
        by_size: BTreeSet<(I, I)>,
    },
}

/// The range an allocation was found in.
#[derive(Clone, Copy)]
struct Found<I> {
    range: Range<I>,
    /// The aligned offset the allocation starts at.
    offset: I,
    /// The position of the range in the vector (not used by the indexes).
    index: usize,
}

impl<I: Offset> FreeList<I> {
    /// Creates the free list of a block of `size` bytes, which is entirely free.
    #[must_use]
    pub fn new(size: I) -> Self {
        let ranges = if size == I::ZERO {
            Vec::new()
        } else {
            vec![Range {
                offset: I::ZERO,
                size,
            }]
        };

        Self {
            size,
            free_bytes: size,
            ranges: Ranges::Flat {
                ranges,
                largest_hint: size,
            },
        }
    }

    /// The size of the whole block.
    #[must_use]
    pub const fn size(&self) -> I {
        self.size
    }

    /// The number of bytes that are free, in total (they are not necessarily in one piece).
    #[must_use]
    pub const fn free_bytes(&self) -> I {
        self.free_bytes
    }

    /// The size of the biggest free piece: the biggest allocation that can succeed, when it
    /// has no alignment to meet.
    #[must_use]
    pub fn largest_free(&self) -> I {
        self.ranges.largest()
    }

    /// Whether nothing is allocated.
    #[must_use]
    pub fn is_unused(&self) -> bool {
        self.free_bytes == self.size
    }

    /// Allocates `size` bytes at a multiple of `alignment`, and returns the offset.
    ///
    /// Of the free ranges the allocation fits in, it takes the smallest one (best fit), which
    /// leaves the big ranges for big allocations, and the lowest one among equals. Returns `None`
    /// if there is no such range.
    ///
    /// # Panics
    /// If `size` or `alignment` is zero.
    pub fn allocate(&mut self, size: I, alignment: I) -> Option<I> {
        assert!(size > I::ZERO, "allocations have a size");
        assert!(alignment > I::ZERO, "alignments are at least 1");

        let found = self.ranges.find_best(size, alignment)?;
        let offset = found.offset;
        self.ranges.allocate_from(found, size);
        self.free_bytes -= size;

        Some(offset)
    }

    /// Gives the `size` bytes at `offset` back, which have to be exactly an allocation made
    /// with [`allocate`](Self::allocate). Free ranges next to it are merged with it.
    ///
    /// # Panics
    /// If the range is not inside the block, or (partly) free already: that is a double free
    /// or a wrong size, and carrying on would hand out the same memory twice.
    pub fn free(&mut self, offset: I, size: I) {
        assert!(size > I::ZERO, "allocations have a size");
        let range = Range { offset, size };
        assert!(
            offset.checked_add(size).is_some_and(|end| end <= self.size),
            "freeing {range:?}, which is outside the block of {:?} bytes",
            self.size
        );

        let (previous, next, at) = self.ranges.neighbours(offset);
        assert!(
            previous.is_none_or(|previous| previous.end() <= range.offset),
            "freeing {range:?}, which overlaps the free range {previous:?}"
        );
        assert!(
            next.is_none_or(|next| range.end() <= next.offset),
            "freeing {range:?}, which overlaps the free range {next:?}"
        );

        let previous = previous.filter(|previous| previous.end() == range.offset);
        let next = next.filter(|next| range.end() == next.offset);
        self.ranges.release(range, previous, next, at);
        self.free_bytes += size;
    }
}

impl<I: Offset> Ranges<I> {
    /// The size of the biggest range.
    fn largest(&self) -> I {
        match self {
            Self::Flat { ranges, .. } => ranges
                .iter()
                .map(|range| range.size)
                .max()
                .unwrap_or(I::ZERO),
            Self::Indexed { by_size, .. } => by_size.last().map_or(I::ZERO, |&(size, _)| size),
        }
    }

    /// The best range for an allocation, with the aligned offset in it.
    fn find_best(&mut self, size: I, alignment: I) -> Option<Found<I>> {
        match self {
            Self::Flat {
                ranges,
                largest_hint,
            } => {
                // Nothing is that big, no need to look.
                if size > *largest_hint {
                    return None;
                }

                let mut best: Option<Found<I>> = None;
                let mut largest = I::ZERO;
                for (index, &range) in ranges.iter().enumerate() {
                    largest = largest.max(range.size);
                    let Some(offset) = fit(range, size, alignment) else {
                        continue;
                    };

                    // A range that is exactly the allocation can not be beaten.
                    if offset == range.offset && range.size == size {
                        return Some(Found {
                            range,
                            offset,
                            index,
                        });
                    }

                    // Smaller ranges win, and the first (lowest) one among equals.
                    if best
                        .as_ref()
                        .is_none_or(|best| range.size < best.range.size)
                    {
                        best = Some(Found {
                            range,
                            offset,
                            index,
                        });
                    }
                }

                if best.is_none() {
                    // The scan saw every range, so this is the exact size of the biggest.
                    *largest_hint = largest;
                }
                best
            }
            Self::Indexed { by_size, .. } => {
                // The ranges that are big enough, smallest first. The first one that still fits
                // once its start is aligned is the best fit.
                by_size
                    .range((size, I::ZERO)..)
                    .find_map(|&(range_size, offset)| {
                        let range = Range {
                            offset,
                            size: range_size,
                        };
                        fit(range, size, alignment).map(|offset| Found {
                            range,
                            offset,
                            index: 0,
                        })
                    })
            }
        }
    }

    /// Takes `size` bytes at `found.offset` out of the range it was found in. What is left in
    /// front of the allocation (alignment gap) and behind it stays free.
    fn allocate_from(&mut self, found: Found<I>, size: I) {
        let Found {
            range,
            offset,
            index,
        } = found;
        let before = Range {
            offset: range.offset,
            size: offset - range.offset,
        };
        let after = Range {
            offset: offset + size,
            size: range.end() - (offset + size),
        };

        match self {
            Self::Flat { ranges, .. } => {
                match (before.size > I::ZERO, after.size > I::ZERO) {
                    (false, false) => {
                        ranges.remove(index);
                    }
                    (true, false) => ranges[index] = before,
                    (false, true) => ranges[index] = after,
                    (true, true) => {
                        ranges[index] = before;
                        ranges.insert(index + 1, after);
                    }
                }
                self.rebalance();
            }
            Self::Indexed { .. } => {
                self.remove(range);
                if before.size > I::ZERO {
                    self.insert(before);
                }
                if after.size > I::ZERO {
                    self.insert(after);
                }
                self.rebalance();
            }
        }
    }

    /// The free range that starts before `offset`, and the one that starts at or after it, and
    /// the position in the vector where a range at `offset` goes (0 for the indexes).
    fn neighbours(&self, offset: I) -> (Option<Range<I>>, Option<Range<I>>, usize) {
        match self {
            Self::Flat { ranges, .. } => {
                let at = ranges.partition_point(|range| range.offset < offset);
                (
                    at.checked_sub(1).map(|index| ranges[index]),
                    ranges.get(at).copied(),
                    at,
                )
            }
            Self::Indexed { by_offset, .. } => {
                let previous = by_offset
                    .range(..offset)
                    .next_back()
                    .map(|(&offset, &size)| Range { offset, size });
                let next = by_offset
                    .range(offset..)
                    .next()
                    .map(|(&offset, &size)| Range { offset, size });
                (previous, next, 0)
            }
        }
    }

    /// Makes `range` free, together with the neighbours that touch it (which are the ones
    /// `neighbours` returned, if they do, and `at` is the position it returned).
    fn release(
        &mut self,
        range: Range<I>,
        previous: Option<Range<I>>,
        next: Option<Range<I>>,
        at: usize,
    ) {
        match self {
            Self::Flat {
                ranges,
                largest_hint,
            } => {
                let merged = match (previous.is_some(), next.is_some()) {
                    // Bridges the gap between two free ranges: they become one.
                    (true, true) => {
                        let next_size = ranges[at].size;
                        ranges[at - 1].size += range.size + next_size;
                        ranges.remove(at);
                        ranges[at - 1].size
                    }
                    (true, false) => {
                        ranges[at - 1].size += range.size;
                        ranges[at - 1].size
                    }
                    (false, true) => {
                        ranges[at].offset = range.offset;
                        ranges[at].size += range.size;
                        ranges[at].size
                    }
                    (false, false) => {
                        ranges.insert(at, range);
                        range.size
                    }
                };
                *largest_hint = (*largest_hint).max(merged);
                self.rebalance();
            }
            Self::Indexed { .. } => {
                let mut merged = range;
                if let Some(previous) = previous {
                    self.remove(previous);
                    merged = Range {
                        offset: previous.offset,
                        size: previous.size + merged.size,
                    };
                }
                if let Some(next) = next {
                    self.remove(next);
                    merged.size += next.size;
                }
                self.insert(merged);
                self.rebalance();
            }
        }
    }

    /// Adds a range to both indexes.
    fn insert(&mut self, range: Range<I>) {
        if let Self::Indexed { by_offset, by_size } = self {
            by_offset.insert(range.offset, range.size);
            by_size.insert((range.size, range.offset));
        }
    }

    /// Removes a range, which is in the indexes, from both.
    fn remove(&mut self, range: Range<I>) {
        if let Self::Indexed { by_offset, by_size } = self {
            by_offset.remove(&range.offset);
            by_size.remove(&(range.size, range.offset));
        }
    }

    /// Moves the ranges to the other layout when there are too many or too few for this one.
    fn rebalance(&mut self) {
        match self {
            Self::Flat { ranges, .. } if ranges.len() > SPILL_LEN => {
                let by_offset: BTreeMap<I, I> = ranges
                    .iter()
                    .map(|range| (range.offset, range.size))
                    .collect();
                let by_size: BTreeSet<(I, I)> = ranges
                    .iter()
                    .map(|range| (range.size, range.offset))
                    .collect();
                *self = Self::Indexed { by_offset, by_size };
            }
            Self::Indexed { by_offset, .. } if by_offset.len() <= UNSPILL_LEN => {
                let ranges: Vec<Range<I>> = by_offset
                    .iter()
                    .map(|(&offset, &size)| Range { offset, size })
                    .collect();
                let largest_hint = ranges
                    .iter()
                    .map(|range| range.size)
                    .max()
                    .unwrap_or(I::ZERO);
                *self = Self::Flat {
                    ranges,
                    largest_hint,
                };
            }
            _ => {}
        }
    }
}

/// A lower bound once the ranges are in the indexes: they store at least the offset and size of
/// every free range, and the nodes of the trees come on top of that. Exact before that.
impl<I: Offset> HeapSize for FreeList<I> {
    fn heap_size(&self) -> usize {
        match &self.ranges {
            Ranges::Flat { ranges, .. } => ranges.capacity() * size_of::<Range<I>>(),
            Ranges::Indexed { by_offset, by_size } => {
                (by_offset.len() + by_size.len()) * size_of::<(I, I)>()
            }
        }
    }
}

/// The offset an allocation of `size` bytes at a multiple of `alignment` (which is not zero)
/// would have in `range`, if it fits.
fn fit<I: Offset>(range: Range<I>, size: I, alignment: I) -> Option<I> {
    let offset = align_up(range.offset, alignment)?;
    let end = offset.checked_add(size)?;
    (end <= range.end()).then_some(offset)
}

/// Rounds `value` up to a multiple of `alignment` (which is not zero). `None` on overflow.
fn align_up<I: Offset>(value: I, alignment: I) -> Option<I> {
    value.div_ceil(alignment).checked_mul(alignment)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_indexed<I: Offset>(list: &FreeList<I>) -> bool {
        matches!(list.ranges, Ranges::Indexed { .. })
    }

    /// `count` free ranges of 4 bytes, with a 4-byte allocation between every two of them, and
    /// the allocations it left, in a block of `8 * count - 4` bytes.
    fn fragmented(count: u64) -> (FreeList, Vec<u64>) {
        let mut list = FreeList::<u64>::new(8 * count - 4);
        let offsets: Vec<u64> = (0..2 * count - 1)
            .map(|_| list.allocate(4, 1).unwrap())
            .collect();
        let mut kept = Vec::new();
        for (i, &offset) in offsets.iter().enumerate() {
            if i % 2 == 0 {
                list.free(offset, 4);
            } else {
                kept.push(offset);
            }
        }
        (list, kept)
    }

    #[test]
    fn heap_size_counts_the_free_ranges() {
        let mut list = FreeList::<u64>::new(100);
        assert_eq!(list.heap_size(), list.size_of_ranges());

        assert_eq!(list.allocate(50, 1), Some(0));
        assert_eq!(list.heap_size(), list.size_of_ranges());

        // Many ranges: they are in the indexes, which count two entries for each.
        let (list, _kept) = fragmented(100);
        assert!(is_indexed(&list));
        assert_eq!(list.heap_size(), 100 * 2 * size_of::<(u64, u64)>());
    }

    impl FreeList<u64> {
        fn size_of_ranges(&self) -> usize {
            match &self.ranges {
                Ranges::Flat { ranges, .. } => ranges.capacity() * size_of::<Range<u64>>(),
                Ranges::Indexed { .. } => unreachable!("only used while there are few ranges"),
            }
        }
    }

    #[test]
    fn many_free_ranges_move_into_the_indexes_and_back() {
        let (mut list, kept) = fragmented(SPILL_LEN as u64);
        assert!(!is_indexed(&list), "the limit itself still fits the vector");

        // One more range is one too many.
        let (mut list2, kept2) = fragmented(SPILL_LEN as u64 + 1);
        assert!(is_indexed(&list2));

        // Freeing what is between the ranges merges them, until there are few enough to go back.
        for &offset in &kept2 {
            list2.free(offset, 4);
        }
        assert!(!is_indexed(&list2));
        assert!(list2.is_unused());
        assert_eq!(list2.largest_free(), list2.size());

        // Staying at the limit changes nothing.
        for &offset in &kept {
            list.free(offset, 4);
        }
        assert!(list.is_unused());
    }

    #[test]
    fn hovering_around_the_limit_does_not_move_every_call() {
        let (mut list, _kept) = fragmented(SPILL_LEN as u64 + 1);
        assert!(is_indexed(&list));

        // Allocating the first free range away, and giving it back, leaves the ranges where
        // they are: it takes many calls to cross back.
        let offset = list.allocate(4, 1).unwrap();
        assert!(is_indexed(&list));
        list.free(offset, 4);
        assert!(is_indexed(&list));
    }

    #[test]
    #[allow(clippy::cast_possible_truncation)] // the block is under 1000 bytes, offsets fit usize
    fn both_layouts_give_the_same_answers_as_brute_force() {
        // The block is a map of every byte, and the expected best fit is read off it: the free
        // runs are exactly the free ranges, because ranges that touch are merged.
        const BLOCK: usize = 2048;
        let (mut list, kept) = fragmented(120);
        assert!(is_indexed(&list));
        let block = list.size() as usize;
        assert!(block <= BLOCK);

        let mut used = vec![true; block];
        for range in 0..block / 8 {
            // The first and every second 4-byte group is free, see `fragmented`.
            for byte in 0..4 {
                used[range * 8 + byte] = false;
            }
        }
        used[block - 4..].fill(false);
        let mut live: Vec<(u64, u64)> = kept.iter().map(|&offset| (offset, 4)).collect();

        let mut state = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = move |bound: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) % bound
        };

        // Miri is slow, and this checks every byte on every step.
        let steps = if cfg!(miri) { 150 } else { 4000 };
        for _ in 0..steps {
            if live.is_empty() || next(100) < 50 {
                let size = 1 + next(12);
                let alignment = 1 << next(4);

                // Brute force: the smallest free run it fits in, the lowest among equals.
                let mut expected: Option<(u64, u64)> = None; // (run size, offset)
                let mut start = 0;
                while start < block {
                    if used[start] {
                        start += 1;
                        continue;
                    }
                    let end = (start..block).find(|&i| used[i]).unwrap_or(block);
                    let offset = (start as u64).next_multiple_of(alignment);
                    let run = (end - start) as u64;
                    if offset + size <= end as u64 && expected.is_none_or(|(best, _)| run < best) {
                        expected = Some((run, offset));
                    }
                    start = end;
                }

                let got = list.allocate(size, alignment);
                assert_eq!(got, expected.map(|(_, offset)| offset));
                if let Some(offset) = got {
                    used[offset as usize..(offset + size) as usize].fill(true);
                    live.push((offset, size));
                }
            } else {
                let (offset, size) = live.swap_remove(next(live.len() as u64) as usize);
                used[offset as usize..(offset + size) as usize].fill(false);
                list.free(offset, size);
            }
        }
    }

    #[test]
    fn works_with_the_other_integer_types() {
        fn run<I: Offset + TryFrom<u64>>()
        where
            <I as TryFrom<u64>>::Error: Debug,
        {
            let n = |value: u64| I::try_from(value).unwrap();

            let mut list = FreeList::new(n(1000));
            assert_eq!(list.allocate(n(10), n(1)), Some(n(0)));
            assert_eq!(list.allocate(n(100), n(64)), Some(n(64)));
            assert_eq!(list.free_bytes(), n(890));
            assert_eq!(list.largest_free(), n(836));

            list.free(n(64), n(100));
            list.free(n(0), n(10));
            assert!(list.is_unused());
            assert_eq!(list.largest_free(), n(1000));
        }

        run::<u16>();
        run::<u32>();
        run::<u64>();
        run::<u128>();
        run::<usize>();
    }

    #[test]
    fn a_small_integer_type_does_not_overflow() {
        // The block is the biggest u16 can describe. The end of an allocation is at most
        // u16::MAX, but the sum of an offset and a size can be more than that.
        let mut list = FreeList::<u16>::new(u16::MAX);
        assert_eq!(list.allocate(u16::MAX, 1), Some(0));
        assert_eq!(list.allocate(1, 1), None);
        list.free(0, u16::MAX);
        assert!(list.is_unused());

        // Rounding the start up to the alignment would pass the biggest number of the type:
        // there is no such offset, so it does not fit (and it does not wrap around to 0).
        assert_eq!(list.allocate(10, 1), Some(0));
        assert_eq!(list.allocate(1, u16::MAX), None);
    }

    #[test]
    #[should_panic(expected = "outside")]
    fn a_range_that_overflows_the_type_is_outside_the_block() {
        let mut list = FreeList::<u16>::new(100);
        let _a = list.allocate(100, 1).unwrap();

        list.free(60_000, 60_000);
    }

    #[test]
    fn starts_entirely_free() {
        let list = FreeList::<u64>::new(1024);

        assert_eq!(list.size(), 1024);
        assert_eq!(list.free_bytes(), 1024);
        assert_eq!(list.largest_free(), 1024);
        assert!(list.is_unused());
    }

    #[test]
    fn allocates_from_the_start() {
        let mut list = FreeList::<u64>::new(1024);

        assert_eq!(list.allocate(100, 1), Some(0));
        assert_eq!(list.allocate(100, 1), Some(100));
        assert_eq!(list.free_bytes(), 824);
        assert!(!list.is_unused());
    }

    #[test]
    fn the_whole_block_can_be_one_allocation() {
        let mut list = FreeList::<u64>::new(256);

        assert_eq!(list.allocate(256, 1), Some(0));
        assert_eq!(list.free_bytes(), 0);
        assert_eq!(list.allocate(1, 1), None);

        list.free(0, 256);
        assert!(list.is_unused());
    }

    #[test]
    fn fails_when_nothing_fits() {
        let mut list = FreeList::<u64>::new(100);

        assert_eq!(list.allocate(101, 1), None);
        // A failed allocation changes nothing.
        assert_eq!(list.free_bytes(), 100);
        assert_eq!(list.allocate(100, 1), Some(0));
    }

    #[test]
    fn aligns_the_offset_and_keeps_the_gap_free() {
        let mut list = FreeList::<u64>::new(1024);
        assert_eq!(list.allocate(10, 1), Some(0));

        // Next free byte is 10, the allocation has to start at 64.
        assert_eq!(list.allocate(100, 64), Some(64));
        // The gap 10..64 is still free, and usable by smaller allocations.
        assert_eq!(list.free_bytes(), 1024 - 10 - 100);
        assert_eq!(list.allocate(54, 1), Some(10));
    }

    #[test]
    fn alignment_can_make_an_allocation_not_fit() {
        let mut list = FreeList::<u64>::new(100);
        assert_eq!(list.allocate(1, 1), Some(0));

        // 99 bytes are free from offset 1, but at a multiple of 64 only 36 are left.
        assert_eq!(list.allocate(50, 64), None);
        assert_eq!(list.allocate(36, 64), Some(64));
    }

    #[test]
    fn works_with_alignments_that_are_not_a_power_of_two() {
        let mut list = FreeList::<u64>::new(1000);
        assert_eq!(list.allocate(1, 1), Some(0));

        assert_eq!(list.allocate(10, 12), Some(12));
    }

    #[test]
    fn best_fit_takes_the_smallest_range_that_fits() {
        let mut list = FreeList::<u64>::new(1000);
        // Layout: [a: 0..300] [x: 300..400] [b: 400..500] [y: 500..520] [rest: 520..1000]
        let a = list.allocate(300, 1).unwrap();
        let x = list.allocate(100, 1).unwrap();
        let b = list.allocate(100, 1).unwrap();
        let y = list.allocate(20, 1).unwrap();
        list.free(a, 300);
        list.free(b, 100);
        // Free ranges now: 0..300, 400..500, 520..1000. Best fit for 90 is the 100-byte range.
        assert_eq!(list.allocate(90, 1), Some(400));
        // 250 fits in 0..300 and in 520..1000: the smaller one wins.
        assert_eq!(list.allocate(250, 1), Some(0));
        let _ = (x, y);
    }

    #[test]
    fn an_exact_fit_is_taken_even_when_it_is_not_the_first() {
        let mut list = FreeList::<u64>::new(1000);
        let a = list.allocate(300, 1).unwrap();
        let _x = list.allocate(10, 1).unwrap();
        let b = list.allocate(100, 1).unwrap();
        let _y = list.allocate(10, 1).unwrap();
        list.free(a, 300);
        list.free(b, 100);

        // Free: 0..300, 310..410 (exactly 100), 420..1000.
        assert_eq!(list.allocate(100, 1), Some(310));
    }

    #[test]
    fn a_too_big_allocation_fails_and_frees_make_it_possible_again() {
        let mut list = FreeList::<u64>::new(100);
        let a = list.allocate(60, 1).unwrap();
        let _b = list.allocate(40, 1).unwrap();

        assert_eq!(list.allocate(61, 1), None);
        assert_eq!(list.allocate(1, 1), None);

        // Freeing makes bigger allocations possible again.
        list.free(a, 60);
        assert_eq!(list.allocate(61, 1), None);
        assert_eq!(list.allocate(60, 1), Some(0));
    }

    #[test]
    fn freeing_merges_with_the_previous_range() {
        let mut list = FreeList::<u64>::new(300);
        let a = list.allocate(100, 1).unwrap();
        let b = list.allocate(100, 1).unwrap();
        let _c = list.allocate(100, 1).unwrap();

        list.free(a, 100);
        list.free(b, 100);

        // One range of 200 bytes, not two of 100.
        assert_eq!(list.largest_free(), 200);
        assert_eq!(list.allocate(200, 1), Some(0));
    }

    #[test]
    fn freeing_merges_with_the_next_range() {
        let mut list = FreeList::<u64>::new(300);
        let _a = list.allocate(100, 1).unwrap();
        let b = list.allocate(100, 1).unwrap();
        let c = list.allocate(100, 1).unwrap();

        list.free(c, 100);
        list.free(b, 100);

        assert_eq!(list.largest_free(), 200);
        assert_eq!(list.allocate(200, 1), Some(100));
    }

    #[test]
    fn freeing_merges_both_neighbours() {
        let mut list = FreeList::<u64>::new(300);
        let a = list.allocate(100, 1).unwrap();
        let b = list.allocate(100, 1).unwrap();
        let c = list.allocate(100, 1).unwrap();

        list.free(a, 100);
        list.free(c, 100);
        // Two separate ranges: 200 bytes free, but no allocation of 200 fits.
        assert_eq!(list.free_bytes(), 200);
        assert_eq!(list.largest_free(), 100);

        // The middle one bridges them.
        list.free(b, 100);
        assert!(list.is_unused());
        assert_eq!(list.largest_free(), 300);
    }

    #[test]
    fn a_freed_range_is_found_again() {
        let mut list = FreeList::<u64>::new(100);
        assert_eq!(list.allocate(100, 1), Some(0));
        list.free(0, 100);

        assert_eq!(list.allocate(100, 1), Some(0));
    }

    #[test]
    #[should_panic(expected = "overlaps")]
    fn a_double_free_panics() {
        let mut list = FreeList::<u64>::new(100);
        let a = list.allocate(50, 1).unwrap();
        let _b = list.allocate(50, 1).unwrap();

        list.free(a, 50);
        list.free(a, 50);
    }

    #[test]
    #[should_panic(expected = "overlaps")]
    fn freeing_a_range_that_is_partly_free_panics() {
        let mut list = FreeList::<u64>::new(100);
        let _a = list.allocate(50, 1).unwrap();

        // 50..100 is free, so freeing 40..60 would hand out the same bytes twice.
        list.free(40, 20);
    }

    #[test]
    #[should_panic(expected = "outside")]
    fn freeing_outside_the_block_panics() {
        let mut list = FreeList::<u64>::new(100);
        let _a = list.allocate(100, 1).unwrap();

        list.free(90, 20);
    }

    #[test]
    fn an_empty_block_has_nothing_to_give() {
        let mut list = FreeList::<u64>::new(0);

        assert!(list.is_unused());
        assert_eq!(list.allocate(1, 1), None);
    }

    /// Allocates and frees a lot in a pseudo-random order, and checks against a map of every
    /// byte that no two live allocations overlap and that all the offsets are aligned.
    #[test]
    #[allow(clippy::cast_possible_truncation)] // the block is 4096 bytes, offsets fit usize
    fn random_use_never_hands_out_the_same_byte_twice() {
        const BLOCK: u64 = 4096;

        let mut list = FreeList::<u64>::new(BLOCK);
        let mut used = vec![false; BLOCK as usize];
        let mut live: Vec<(u64, u64)> = Vec::new();

        // A small linear congruential generator: deterministic, so a failure can be reproduced.
        let mut state = 0x2545_f491_4f6c_dd1d_u64;
        let mut next = move |bound: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) % bound
        };

        // Miri is slow, and this checks every byte on every step.
        let steps = if cfg!(miri) { 300 } else { 5000 };
        for _ in 0..steps {
            if live.is_empty() || next(100) < 55 {
                let size = 1 + next(200);
                let alignment = 1 << next(7); // 1 to 64
                if let Some(offset) = list.allocate(size, alignment) {
                    assert_eq!(offset % alignment, 0, "misaligned allocation");
                    assert!(offset + size <= BLOCK, "allocation outside the block");
                    for byte in offset..offset + size {
                        assert!(!used[byte as usize], "byte {byte} handed out twice");
                        used[byte as usize] = true;
                    }
                    live.push((offset, size));
                }
            } else {
                let (offset, size) = live.swap_remove(next(live.len() as u64) as usize);
                for byte in offset..offset + size {
                    used[byte as usize] = false;
                }
                list.free(offset, size);
            }

            let in_use: u64 = live.iter().map(|&(_, size)| size).sum();
            assert_eq!(list.free_bytes(), BLOCK - in_use, "free bytes drifted");
        }

        // Freeing everything merges all the ranges back into one.
        for (offset, size) in live {
            list.free(offset, size);
        }
        assert!(list.is_unused());
        assert_eq!(list.largest_free(), BLOCK, "ranges were not merged");
    }
}
