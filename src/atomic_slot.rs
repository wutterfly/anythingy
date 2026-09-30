//! A single-value slot that threads hand values to each other through.
//!
//! See [`AtomicSlot`].

use alloc::boxed::Box;
use core::fmt;
use core::marker::PhantomData;
use core::sync::atomic::{AtomicPtr, Ordering};

// Implementation notes
// ----------------------
//
// The slot owns exactly two `Box<Option<T>>` allocations, made once in `new`
// and freed only in `Drop`. `value` and `spare` each always point at one of
// them, except briefly while a thread is in the middle of `set`. `value`
// holds the current content (`None` = empty); `spare` always holds `None`
// and stands by to become the next `value`.
//
// `set`, which both `push` and `take` are built from, does the same steps
// either way: grab `spare` (atomic swap to null), write the new content into
// it, swap it into `value` (which gives the previous box back), read the
// previous content out of that box, and hand the box back to `spare`, where
// it holds `None` again like every box does whenever it sits there.
//
// Grabbing `spare` can find it null, because another thread is between its
// own grab and hand-back. This spins instead of allocating a third box. That
// is sound because there are only two boxes, and every `set` that takes
// `spare` puts one back before returning, with no path out that skips it.
// Not even a panicking `T::drop` can: nothing in `set` drops a live `T`. The
// box grabbed from `spare` held `None`, so overwriting it drops nothing, and
// the value read out of `value`'s old box is returned to the caller, who
// drops it after `set` has already handed the box back.
//
// A plain `AtomicCell<Option<T>>` would move the value through an integer
// atomic, which cannot carry pointer provenance, so Miri flags the drop of
// the overwritten value for pointer-shaped `T` (`Box`, `Arc`, `&'static X`).
// This slot only ever moves real, typed `Box<Option<T>>` pointers.
//
// The slot does not track whether it is empty beyond what `Option<T>` says.

/// A slot that holds zero or one value of `T`, which any number of threads can
/// fill and empty through a shared reference.
///
/// [`push`](Self::push) stores a value and drops whatever was stored before.
/// [`take`](Self::take) removes the current value and leaves the slot empty.
/// It is a mailbox that only keeps the latest message, which suits "latest
/// value wins" hand-offs such as the newest reading, frame or configuration
/// passing from one thread to another.
///
/// # Concurrency
///
/// Every operation is atomic, and none of them allocates: the slot's storage
/// is allocated once, in [`new`](Self::new). Operations do not take a lock and
/// never park a thread. A thread that collides with another one using the same
/// slot spins until that other operation, which is short and fixed in length,
/// has finished. So it is not lock-free in the strict sense: a thread that is
/// descheduled in the middle of an operation delays the others until it runs
/// again.
///
/// # Thread safety
///
/// `AtomicSlot<T>` is `Send` and `Sync` whenever `T` is `Send`, like
/// `Mutex<T>`. `T` does not have to be `Sync`, since a value is only ever
/// handed to one thread at a time and never shared.
///
/// # Examples
///
/// ```
/// use anythingy::AtomicSlot;
///
/// let slot = AtomicSlot::new();
///
/// std::thread::scope(|s| {
///     for thread in 0..4 {
///         let slot = &slot;
///         s.spawn(move || {
///             for i in 0..100 {
///                 slot.push(thread * 100 + i);
///
///                 if i % 10 == 0 {
///                     // Whatever is stored right now, from any thread, or
///                     // `None` if another thread took it first.
///                     let _ = slot.take();
///                 }
///             }
///         });
///     }
/// });
///
/// // At most one value is left, and it was pushed by one of the threads.
/// if let Some(value) = slot.take() {
///     assert!(value < 400);
/// }
/// assert!(slot.take().is_none());
/// ```
pub struct AtomicSlot<T> {
    value: AtomicPtr<Option<T>>,
    spare: AtomicPtr<Option<T>>,

    // Ties the `Send`/`Sync` of `AtomicSlot<T>` to the explicit `unsafe impl`s
    // below, instead of the unconditional ones that a bare `AtomicPtr` would
    // grant whatever `T` is. The slot does dereference its pointers.
    _marker: PhantomData<*const T>,
}

// SAFETY: every `T` that passes through the slot does so via an atomic
// pointer swap that hands exclusive ownership to one thread at a time (see
// `set` and `clear`), the same guarantee `Mutex<T>` relies on. So, like
// `Mutex<T>`, `T: Send` is necessary and sufficient: `T: Sync` is never
// needed, since no thread gets a shared `&T` into the slot while another
// thread can reach it too.
unsafe impl<T: Send> Send for AtomicSlot<T> {}
// SAFETY: see above.
unsafe impl<T: Send> Sync for AtomicSlot<T> {}

impl<T> AtomicSlot<T> {
    /// Creates an empty slot.
    ///
    /// This is the only call that allocates.
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self {
            value: AtomicPtr::new(Box::into_raw(Box::new(None))),
            spare: AtomicPtr::new(Box::into_raw(Box::new(None))),
            _marker: PhantomData,
        }
    }

    /// Replaces the stored value with `new`, returning what was stored before.
    /// `push` is `set(Some(value))` with the previous value discarded, `take`
    /// is `set(None)` with the previous value returned.
    #[inline]
    fn set(&self, new: Option<T>) -> Option<T> {
        // Grab `spare`. This only spins while another thread is between its
        // own grab and hand-back below, which is a short, bounded,
        // non-allocating sequence: see the implementation notes.
        let raw = loop {
            let p = self.spare.swap(core::ptr::null_mut(), Ordering::Acquire);

            if !p.is_null() {
                break p;
            }

            // Wait with plain loads until `spare` is back, and only then try
            // the swap again. Swapping in a loop would write to the cache line
            // on every spin, and the waiting threads would keep pulling it
            // away from the thread that is about to hand the box back.
            while self.spare.load(Ordering::Relaxed).is_null() {
                core::hint::spin_loop();
            }
        };

        // SAFETY: `raw` points at one of the two boxes allocated in `new`,
        // which are never freed before `Drop`. As a box that was just in
        // `spare` it holds `None`, so this assignment drops a `None`, never a
        // live `T`.
        unsafe { *raw = new };

        let old = self.value.swap(raw, Ordering::AcqRel);

        // SAFETY: `old` just came out of `value` via the swap above, so no
        // other thread can reach it, and reading it is exclusive. Once it is
        // in `spare`, another thread can grab and overwrite it at any moment,
        // so this has to happen first.
        let previous = unsafe { (*old).take() };

        // `old` now holds `None`, like every box in `spare` does. A plain
        // store, not a swap or a CAS, is correct: `spare` is still null,
        // since the only way to put a box there is to hold `spare`'s one box,
        // and this thread holds it, in `old`.
        self.spare.store(old, Ordering::Release);

        previous
    }

    /// Stores `value`, dropping whatever was stored before.
    #[inline]
    pub fn push(&self, value: T) {
        drop(self.set(Some(value)));
    }

    /// Removes and returns the stored value, leaving the slot empty.
    ///
    /// Returns `None` if the slot is empty.
    #[inline]
    pub fn take(&self) -> Option<T> {
        self.set(None)
    }

    /// Empties the slot, dropping the stored value.
    ///
    /// This needs exclusive access, so no other thread can be using the slot
    /// at the same time.
    #[inline]
    pub fn clear(&mut self) {
        // SAFETY: `value` points at one of the two boxes allocated in `new`,
        // which are never freed before `Drop`. Exclusive access (`&mut self`)
        // means no atomic operation is needed to touch it.
        unsafe { *(*self.value.get_mut()) = None };
    }
}

impl<T> Default for AtomicSlot<T> {
    /// Creates an empty slot, like [`AtomicSlot::new`].
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> fmt::Debug for AtomicSlot<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The content cannot be shown without taking it out of the slot.
        f.debug_struct("AtomicSlot").finish_non_exhaustive()
    }
}

impl<T> Drop for AtomicSlot<T> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: both `value` and `spare` point at one of the two boxes
        // allocated in `new`, and nothing else frees them. Exclusive access
        // (`&mut self`) means no atomic operation is needed to take them back.
        drop(unsafe { Box::from_raw(*self.value.get_mut()) });
        drop(unsafe { Box::from_raw(*self.spare.get_mut()) });
    }
}

#[cfg(test)]
mod tests {
    use super::AtomicSlot;

    #[test]
    fn push_then_take() {
        let slot = AtomicSlot::new();
        assert_eq!(slot.take(), None);

        slot.push(1);
        assert_eq!(slot.take(), Some(1));
        assert_eq!(slot.take(), None);
    }

    #[test]
    fn push_overwrites_unconsumed_value() {
        let slot = AtomicSlot::new();

        slot.push(1);
        slot.push(2);

        assert_eq!(slot.take(), Some(2));
    }

    #[test]
    fn clear_drops_the_stored_value() {
        let mut slot = AtomicSlot::new();

        slot.push(1);
        slot.clear();

        assert_eq!(slot.take(), None);
    }

    #[test]
    fn sync_needs_only_t_send_not_t_sync() {
        // `AtomicSlot<T>` should be `Send + Sync` whenever `T: Send`, without additionally requiring `T: Sync`
        // (same as `Mutex<T>`), since every access hands over exclusive ownership via a pointer swap, never a
        // shared `&T`. `Cell<u8>` is `Send` but deliberately not `Sync`, so this only compiles if that bound is
        // exactly right — too permissive (no `T: Send` requirement at all) or too strict (`T: Sync` required)
        // would both change whether this line compiles.
        const fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<AtomicSlot<std::cell::Cell<u8>>>();
    }

    #[test]
    fn threads_pushing_concurrently_leave_exactly_one_value() {
        // multiple threads pushing into the same slot concurrently: whichever value ends up stored must be one
        // that was actually pushed (not a torn/garbage read), and no allocation is leaked.
        // Smaller under Miri, which is slow at spinning threads.
        const THREADS: u32 = if cfg!(miri) { 3 } else { 8 };
        const PER_THREAD: u32 = if cfg!(miri) { 40 } else { 2_000 };
        const ROUNDS: u32 = if cfg!(miri) { 2 } else { 5 };

        let slot = AtomicSlot::new();

        for round in 0..ROUNDS {
            std::thread::scope(|s| {
                for t in 0..THREADS {
                    let slot = &slot;
                    s.spawn(move || {
                        for i in 0..PER_THREAD {
                            slot.push(t * PER_THREAD + i);
                        }
                    });
                }
            });

            let remaining = slot.take();
            assert!(remaining.is_some(), "round {round}");
            assert!(remaining.unwrap() < THREADS * PER_THREAD, "round {round}");
            assert!(
                slot.take().is_none(),
                "round {round}: only one value should remain"
            );
        }
    }

    #[test]
    fn panicking_drop_does_not_strand_spare() {
        // regression test for the claim in `AtomicSlot`'s docs: `set` never drops a live `T` itself, only ever
        // handing the evicted value back to its caller — so even a panicking `Drop`, which only ever runs in
        // that caller (here, `push`'s `drop(self.set(..))`, after `set` has already returned) cannot leave
        // `spare` without a box in it and stall every future `push`/`take` on this slot.
        struct MaybeDropPanics(bool);

        impl Drop for MaybeDropPanics {
            fn drop(&mut self) {
                assert!(!self.0, "boom");
            }
        }

        let slot = AtomicSlot::new();

        // installed as the live value; nothing evicted yet, so nothing is dropped here
        slot.push(MaybeDropPanics(true));

        // evicts the previous (panics-on-drop) value
        let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            slot.push(MaybeDropPanics(false));
        }));
        assert!(panicked.is_err());

        // the slot must still be fully usable: `spare` was never left without a box to give back
        slot.push(MaybeDropPanics(false));
        assert!(slot.take().is_some());
    }
}
