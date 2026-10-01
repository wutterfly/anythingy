//! A thread-safe [`RefCell`](core::cell::RefCell).
//!
//! See [`AtomicRefCell`].

use crate::heap_size::HeapSize;
use core::cell::UnsafeCell;
use core::error::Error;
use core::fmt;
use core::marker::PhantomData;
use core::mem;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;
use core::sync::atomic::{AtomicIsize, Ordering};

// Implementation notes
// ----------------------
//
// The borrow state is one atomic counter: `UNUSED` (0) when nothing borrows
// the value, a positive number of readers while it is borrowed shared, and
// `WRITING` (-1) while it is borrowed exclusively. Every reference handed out
// is gated by a successful atomic transition of the counter, which proves that
// no conflicting borrow is live. That is the same guarantee `RwLock` gives,
// except that a conflict is reported instead of waited for.
//
// The reader count is bounded by `isize::MAX`. Guards can be leaked with
// `mem::forget`, and on a 32-bit target it takes only about two billion of
// them to reach the bound, so a borrow that would pass it fails instead of
// wrapping around to zero or to `WRITING`.

const UNUSED: isize = 0;
const WRITING: isize = -1;

/// A [`RefCell`](core::cell::RefCell) that can be shared between threads.
///
/// Like `RefCell`, it checks borrows at runtime: there can be any number of
/// shared borrows, made with [`borrow`](Self::borrow), or one exclusive borrow,
/// made with [`borrow_mut`](Self::borrow_mut), at a time. A borrow that
/// conflicts with another one does not wait for it, as it would with an
/// `RwLock`. The `try_` methods return an error, and the others panic.
///
/// The borrow state is one atomic counter, so the cell does not allocate, never
/// blocks a thread, and cannot be poisoned. It also works without `std`.
///
/// # Thread safety
///
/// `AtomicRefCell<T>` is `Sync` when `T` is `Send + Sync`, and `Send` when `T`
/// is `Send`, like `RwLock<T>`. Its guards can be sent to other threads, too:
/// [`AtomicRef`] is `Send` when `T` is `Sync`, and [`AtomicRefMut`] when `T` is
/// `Send`.
///
/// ```compile_fail,E0277
/// use std::cell::Cell;
/// use anythingy::AtomicRefCell;
///
/// fn assert_sync<T: Sync>() {}
/// assert_sync::<AtomicRefCell<Cell<u8>>>();
/// ```
///
/// # Examples
///
/// ```
/// use anythingy::AtomicRefCell;
///
/// let cell = AtomicRefCell::new(vec![1, 2, 3]);
///
/// {
///     // Any number of shared borrows at once.
///     let first = cell.borrow();
///     let second = cell.borrow();
///     assert_eq!(first.len(), second.len());
///
///     // But not together with an exclusive one.
///     assert!(cell.try_borrow_mut().is_err());
/// }
///
/// cell.borrow_mut().push(4);
/// assert_eq!(*cell.borrow(), [1, 2, 3, 4]);
/// ```
///
/// Sharing it between threads:
///
/// ```
/// use anythingy::AtomicRefCell;
///
/// let cell = AtomicRefCell::new(0);
///
/// std::thread::scope(|s| {
///     for _ in 0..4 {
///         s.spawn(|| {
///             for _ in 0..100 {
///                 // A writer never waits: if the cell is borrowed, try again.
///                 loop {
///                     if let Ok(mut value) = cell.try_borrow_mut() {
///                         *value += 1;
///                         break;
///                     }
///                     std::hint::spin_loop();
///                 }
///             }
///         });
///     }
/// });
///
/// assert_eq!(*cell.borrow(), 400);
/// ```
pub struct AtomicRefCell<T: ?Sized> {
    borrow: AtomicIsize,
    value: UnsafeCell<T>,
}

// SAFETY: every `&T`/`&mut T` handed out is gated by a successful atomic
// transition of `borrow`, proving no conflicting borrow is live: the same
// guarantee `RwLock` gives, with the same bounds.
unsafe impl<T: ?Sized + Send + Sync> Sync for AtomicRefCell<T> {}

impl<T> AtomicRefCell<T> {
    /// Creates a new cell that holds `value`.
    #[inline]
    #[must_use]
    pub const fn new(value: T) -> Self {
        Self {
            borrow: AtomicIsize::new(UNUSED),
            value: UnsafeCell::new(value),
        }
    }

    /// Consumes the cell and returns the value.
    #[inline]
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }

    /// Replaces the value with `t` and returns the old one.
    ///
    /// # Panics
    ///
    /// Panics if the cell is currently borrowed.
    #[inline]
    #[track_caller]
    pub fn replace(&self, t: T) -> T {
        mem::replace(&mut *self.borrow_mut(), t)
    }

    /// Replaces the value with the result of `f`, which gets a mutable
    /// reference to the old value, and returns the old value.
    ///
    /// # Panics
    ///
    /// Panics if the cell is currently borrowed.
    #[inline]
    #[track_caller]
    pub fn replace_with<F: FnOnce(&mut T) -> T>(&self, f: F) -> T {
        let mut guard = self.borrow_mut();
        let replacement = f(&mut guard);
        mem::replace(&mut *guard, replacement)
    }

    /// Swaps the values of two cells.
    ///
    /// # Panics
    ///
    /// Panics if either cell is currently borrowed, which includes swapping a
    /// cell with itself.
    #[inline]
    #[track_caller]
    pub fn swap(&self, other: &Self) {
        mem::swap(&mut *self.borrow_mut(), &mut *other.borrow_mut());
    }

    /// Takes the value out, leaving [`Default::default`] in its place.
    ///
    /// # Panics
    ///
    /// Panics if the cell is currently borrowed.
    #[inline]
    #[track_caller]
    pub fn take(&self) -> T
    where
        T: Default,
    {
        self.replace(T::default())
    }
}

impl<T: ?Sized> AtomicRefCell<T> {
    /// Borrows the value immutably, or returns an error if it is currently
    /// borrowed mutably.
    ///
    /// Any number of shared borrows can be live at once. The borrow lasts until
    /// the returned guard is dropped.
    ///
    /// # Errors
    ///
    /// Returns an error if the value is borrowed mutably.
    #[inline]
    pub fn try_borrow(&self) -> Result<AtomicRef<'_, T>, BorrowError> {
        let mut current = self.borrow.load(Ordering::Acquire);
        loop {
            // Writing, or so many readers that one more would wrap around.
            if current < UNUSED || current == isize::MAX {
                return Err(BorrowError { _private: () });
            }
            // Reserve one more reader. The exchange may fail spuriously or
            // because the count changed, so retry with what it saw.
            match self.borrow.compare_exchange_weak(
                current,
                current + 1,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // SAFETY: the exchange above proved that no writer holds
                    // the cell, and this reservation keeps one out until the
                    // returned `AtomicRef` is dropped.
                    let value = unsafe { &*self.value.get() };
                    return Ok(AtomicRef {
                        value,
                        borrow: &self.borrow,
                    });
                }
                Err(observed) => current = observed,
            }
        }
    }

    /// Borrows the value immutably.
    ///
    /// Any number of shared borrows can be live at once. The borrow lasts until
    /// the returned guard is dropped.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed mutably. For a version that
    /// does not panic, see [`try_borrow`](Self::try_borrow).
    #[inline]
    #[must_use]
    #[track_caller]
    #[allow(clippy::match_wild_err_arm, clippy::option_if_let_else)] // `expect` would print the error too, and a closure would lose `#[track_caller]`
    pub fn borrow(&self) -> AtomicRef<'_, T> {
        match self.try_borrow() {
            Ok(guard) => guard,
            Err(_) => panic!("AtomicRefCell already mutably borrowed"),
        }
    }

    /// Borrows the value mutably, or returns an error if it is currently
    /// borrowed in any way.
    ///
    /// The borrow lasts until the returned guard is dropped.
    ///
    /// # Errors
    ///
    /// Returns an error if the value is borrowed, shared or mutably.
    #[inline]
    pub fn try_borrow_mut(&self) -> Result<AtomicRefMut<'_, T>, BorrowMutError> {
        // A strong exchange: this is one exact `UNUSED` -> `WRITING` step, so
        // there is nothing to retry after a spurious failure.
        match self
            .borrow
            .compare_exchange(UNUSED, WRITING, Ordering::AcqRel, Ordering::Acquire)
        {
            Ok(_) => {
                // SAFETY: the exchange above proved that the cell was not
                // borrowed, and this reservation excludes every other borrow
                // until the returned `AtomicRefMut` is dropped. The pointer
                // comes from the `UnsafeCell`, so it is never null.
                let value = unsafe { NonNull::new_unchecked(self.value.get()) };
                Ok(AtomicRefMut {
                    value,
                    borrow: &self.borrow,
                    _marker: PhantomData,
                })
            }
            Err(_) => Err(BorrowMutError { _private: () }),
        }
    }

    /// Borrows the value mutably.
    ///
    /// The borrow lasts until the returned guard is dropped.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed, shared or mutably. For a
    /// version that does not panic, see [`try_borrow_mut`](Self::try_borrow_mut).
    #[inline]
    #[must_use]
    #[track_caller]
    #[allow(clippy::match_wild_err_arm, clippy::option_if_let_else)] // see `borrow`
    pub fn borrow_mut(&self) -> AtomicRefMut<'_, T> {
        match self.try_borrow_mut() {
            Ok(guard) => guard,
            Err(_) => panic!("AtomicRefCell already borrowed"),
        }
    }

    /// Returns a mutable reference to the value.
    ///
    /// This needs no check: `&mut self` already proves that nothing else
    /// borrows the value.
    #[inline]
    pub const fn get_mut(&mut self) -> &mut T {
        self.value.get_mut()
    }

    /// Returns a raw pointer to the value.
    ///
    /// Reading or writing through it is only sound while no borrow of the cell
    /// conflicts with the access.
    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *mut T {
        self.value.get()
    }

    /// Borrows the value without any check, and without touching the borrow
    /// state at all. No guard is returned, since there is nothing to release.
    ///
    /// # Safety
    ///
    /// No mutable reference to the value may be alive at the same time, from
    /// [`borrow_mut`](Self::borrow_mut) or from
    /// [`borrow_mut_unchecked`](Self::borrow_mut_unchecked).
    #[inline]
    #[must_use]
    pub unsafe fn borrow_unchecked(&self) -> &T {
        // SAFETY: forwarded to the caller.
        unsafe { &*self.value.get() }
    }

    /// The mutable counterpart of [`borrow_unchecked`](Self::borrow_unchecked).
    ///
    /// # Safety
    ///
    /// No other reference to the value may be alive at the same time, from
    /// any kind of borrow of the cell.
    #[inline]
    #[must_use]
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn borrow_mut_unchecked(&self) -> &mut T {
        // SAFETY: forwarded to the caller.
        unsafe { &mut *self.value.get() }
    }
}

impl<T: Default> Default for AtomicRefCell<T> {
    /// Creates a cell that holds `T::default()`.
    #[inline]
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> From<T> for AtomicRefCell<T> {
    /// Creates a cell that holds `value`, like [`AtomicRefCell::new`].
    #[inline]
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T: Clone> Clone for AtomicRefCell<T> {
    /// Clones the value into a new cell.
    ///
    /// # Panics
    ///
    /// Panics if the cell is currently borrowed mutably.
    #[inline]
    #[track_caller]
    fn clone(&self) -> Self {
        Self::new(self.borrow().clone())
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for AtomicRefCell<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("AtomicRefCell");
        match self.try_borrow() {
            Ok(value) => debug.field("value", &&*value),
            Err(_) => debug.field("value", &format_args!("<borrowed>")),
        };
        debug.finish()
    }
}

/// Compares the values. Panics if either cell is currently borrowed mutably.
impl<T: ?Sized + PartialEq> PartialEq for AtomicRefCell<T> {
    #[inline]
    #[track_caller]
    fn eq(&self, other: &Self) -> bool {
        *self.borrow() == *other.borrow()
    }
}

impl<T: ?Sized + Eq> Eq for AtomicRefCell<T> {}

/// Compares the values. Panics if either cell is currently borrowed mutably.
impl<T: ?Sized + PartialOrd> PartialOrd for AtomicRefCell<T> {
    #[inline]
    #[track_caller]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.borrow().partial_cmp(&*other.borrow())
    }
}

/// Compares the values. Panics if either cell is currently borrowed mutably.
impl<T: ?Sized + Ord> Ord for AtomicRefCell<T> {
    #[inline]
    #[track_caller]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.borrow().cmp(&*other.borrow())
    }
}

/// A shared borrow of the value in an [`AtomicRefCell`].
///
/// It gives read access through [`Deref`], and releases the borrow when it is
/// dropped.
pub struct AtomicRef<'b, T: ?Sized> {
    value: &'b T,
    borrow: &'b AtomicIsize,
}

impl<'b, T: ?Sized> AtomicRef<'b, T> {
    /// Makes another shared borrow of the same value.
    ///
    /// This is an associated function, like [`Rc::clone`](alloc::rc::Rc::clone),
    /// so that it does not hide a `clone` of the value itself.
    ///
    /// # Panics
    ///
    /// Panics if the cell already has `isize::MAX` shared borrows.
    #[inline]
    #[must_use]
    #[track_caller]
    #[allow(clippy::should_implement_trait)]
    pub fn clone(orig: &Self) -> Self {
        // The guard `orig` proves that the count is positive, and that it
        // stays so, so this only has to stop it from overflowing.
        let mut count = orig.borrow.load(Ordering::Relaxed);
        loop {
            assert!(
                count != isize::MAX,
                "too many shared borrows of an AtomicRefCell"
            );
            match orig.borrow.compare_exchange_weak(
                count,
                count + 1,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(observed) => count = observed,
            }
        }
        Self {
            value: orig.value,
            borrow: orig.borrow,
        }
    }

    /// Makes a new guard for a part of the borrowed value, like
    /// [`Ref::map`](core::cell::Ref::map).
    ///
    /// This is an associated function, so that it does not interfere with
    /// methods of the value.
    #[inline]
    pub fn map<U: ?Sized, F>(orig: Self, f: F) -> AtomicRef<'b, U>
    where
        F: FnOnce(&T) -> &U,
    {
        // `orig` is still alive while `f` runs, so a panic in `f` releases
        // the borrow as usual.
        let value = f(orig.value);
        let borrow = orig.borrow;
        mem::forget(orig);
        AtomicRef { value, borrow }
    }

    /// Makes a new guard for a part of the borrowed value, if `f` finds one.
    /// Otherwise the original guard is returned as the error.
    ///
    /// # Errors
    ///
    /// Returns the original guard if `f` returns `None`.
    #[inline]
    pub fn filter_map<U: ?Sized, F>(orig: Self, f: F) -> Result<AtomicRef<'b, U>, Self>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        match f(orig.value) {
            Some(value) => {
                let borrow = orig.borrow;
                mem::forget(orig);
                Ok(AtomicRef { value, borrow })
            }
            None => Err(orig),
        }
    }
}

impl<T: ?Sized> Deref for AtomicRef<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.value
    }
}

impl<T: ?Sized> Drop for AtomicRef<'_, T> {
    #[inline]
    fn drop(&mut self) {
        self.borrow.fetch_sub(1, Ordering::Release);
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for AtomicRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for AtomicRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

/// An exclusive borrow of the value in an [`AtomicRefCell`].
///
/// It gives read and write access through [`Deref`] and [`DerefMut`], and
/// releases the borrow when it is dropped.
pub struct AtomicRefMut<'b, T: ?Sized> {
    // A pointer and not a `&mut T`, so that `map` can hand out a reference for
    // the full lifetime without moving out of a type that has a destructor.
    value: NonNull<T>,
    borrow: &'b AtomicIsize,
    _marker: PhantomData<&'b mut T>,
}

// SAFETY: an `AtomicRefMut<T>` is an exclusive reference to a `T`, and is
// moved between threads under the same condition as `&mut T`.
unsafe impl<T: ?Sized + Send> Send for AtomicRefMut<'_, T> {}
// SAFETY: sharing an `AtomicRefMut<T>` only shares a `&T`, like `&&mut T`.
unsafe impl<T: ?Sized + Sync> Sync for AtomicRefMut<'_, T> {}

impl<'b, T: ?Sized> AtomicRefMut<'b, T> {
    /// Makes a new guard for a part of the borrowed value, like
    /// [`RefMut::map`](core::cell::RefMut::map).
    ///
    /// This is an associated function, so that it does not interfere with
    /// methods of the value.
    #[inline]
    pub fn map<U: ?Sized, F>(orig: Self, f: F) -> AtomicRefMut<'b, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let mut orig = orig;
        // SAFETY: `orig` holds the exclusive borrow of the cell and is not
        // used again, except to release it if `f` panics.
        let value = f(unsafe { orig.value.as_mut() });
        let value = NonNull::from(value);
        let borrow = orig.borrow;
        mem::forget(orig);
        AtomicRefMut {
            value,
            borrow,
            _marker: PhantomData,
        }
    }

    /// Makes a new guard for a part of the borrowed value, if `f` finds one.
    /// Otherwise the original guard is returned as the error.
    ///
    /// # Errors
    ///
    /// Returns the original guard if `f` returns `None`.
    #[inline]
    pub fn filter_map<U: ?Sized, F>(orig: Self, f: F) -> Result<AtomicRefMut<'b, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        let mut orig = orig;
        // SAFETY: as in `map`.
        match f(unsafe { orig.value.as_mut() }) {
            Some(value) => {
                let value = NonNull::from(value);
                let borrow = orig.borrow;
                mem::forget(orig);
                Ok(AtomicRefMut {
                    value,
                    borrow,
                    _marker: PhantomData,
                })
            }
            None => Err(orig),
        }
    }
}

impl<T: ?Sized> Deref for AtomicRefMut<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: the guard holds the exclusive borrow of the cell.
        unsafe { self.value.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for AtomicRefMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: the guard holds the exclusive borrow of the cell.
        unsafe { self.value.as_mut() }
    }
}

impl<T: ?Sized> Drop for AtomicRefMut<'_, T> {
    #[inline]
    fn drop(&mut self) {
        self.borrow.store(UNUSED, Ordering::Release);
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for AtomicRefMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for AtomicRefMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

/// The error of [`AtomicRefCell::try_borrow`]: the value is borrowed mutably.
#[derive(Debug)]
pub struct BorrowError {
    _private: (),
}

impl fmt::Display for BorrowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("already mutably borrowed")
    }
}

impl Error for BorrowError {}

/// The error of [`AtomicRefCell::try_borrow_mut`]: the value is already
/// borrowed.
#[derive(Debug)]
pub struct BorrowMutError {
    _private: (),
}

impl fmt::Display for BorrowMutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("already borrowed")
    }
}

impl Error for BorrowMutError {}

/// The cell keeps its value inline and allocates nothing, so this is always
/// `0`. What the value itself owns is not counted.
impl<T: ?Sized> HeapSize for AtomicRefCell<T> {
    fn heap_size(&self) -> usize {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use alloc::boxed::Box;
    use alloc::format;
    use alloc::string::{String, ToString};
    use alloc::vec::Vec;

    #[test]
    fn borrow_mut_then_borrow_fails() {
        let cell = AtomicRefCell::new(5);
        let _guard = cell.try_borrow_mut().unwrap();

        assert!(cell.try_borrow().is_err());
        assert!(cell.try_borrow_mut().is_err());
    }

    #[test]
    fn borrow_then_borrow_mut_fails() {
        let cell = AtomicRefCell::new(5);
        let _guard = cell.try_borrow().unwrap();

        assert!(cell.try_borrow_mut().is_err());
    }

    #[test]
    fn dropping_a_borrow_releases_it() {
        let cell = AtomicRefCell::new(5);
        {
            let _guard = cell.try_borrow_mut().unwrap();
        }

        assert!(cell.try_borrow_mut().is_ok());
    }

    #[test]
    fn unchecked_borrows_read_and_write_through() {
        let cell = AtomicRefCell::new(5);

        // SAFETY: nothing else borrows `cell` in this test.
        unsafe {
            assert_eq!(*cell.borrow_unchecked(), 5);
            *cell.borrow_mut_unchecked() = 9;
            assert_eq!(*cell.borrow_unchecked(), 9);
        }
    }

    #[test]
    fn many_readers_release_independently() {
        let cell = AtomicRefCell::new(5);
        let a = cell.try_borrow().unwrap();
        let b = cell.try_borrow().unwrap();
        drop(a);

        // One reader remains; still no room for a writer.
        assert!(cell.try_borrow_mut().is_err());
        drop(b);
        assert!(cell.try_borrow_mut().is_ok());
    }

    #[test]
    #[should_panic(expected = "AtomicRefCell already mutably borrowed")]
    fn borrow_panics_while_mutably_borrowed() {
        let cell = AtomicRefCell::new(5);
        let _guard = cell.borrow_mut();
        let _ = cell.borrow();
    }

    #[test]
    #[should_panic(expected = "AtomicRefCell already borrowed")]
    fn borrow_mut_panics_while_borrowed() {
        let cell = AtomicRefCell::new(5);
        let _guard = cell.borrow();
        let _ = cell.borrow_mut();
    }

    #[test]
    fn error_messages() {
        let cell = AtomicRefCell::new(5);
        let writer = cell.borrow_mut();
        assert_eq!(
            cell.try_borrow().unwrap_err().to_string(),
            "already mutably borrowed"
        );
        assert_eq!(
            cell.try_borrow_mut().unwrap_err().to_string(),
            "already borrowed"
        );
        drop(writer);

        let _reader = cell.borrow();
        assert_eq!(
            cell.try_borrow_mut().unwrap_err().to_string(),
            "already borrowed"
        );

        let error: &dyn Error = &cell.try_borrow_mut().unwrap_err();
        assert!(error.source().is_none());
    }

    #[test]
    fn get_mut_and_into_inner_skip_the_checks() {
        let mut cell = AtomicRefCell::new(String::from("a"));
        cell.get_mut().push('b');
        assert_eq!(cell.into_inner(), "ab");
    }

    #[test]
    fn as_ptr_points_at_the_value() {
        let cell = AtomicRefCell::new(7);
        // SAFETY: nothing borrows the cell.
        unsafe { *cell.as_ptr() += 1 };
        assert_eq!(*cell.borrow(), 8);
    }

    #[test]
    fn replace_swap_take() {
        let a = AtomicRefCell::new(1);
        let b = AtomicRefCell::new(2);

        assert_eq!(a.replace(10), 1);
        assert_eq!(a.replace_with(|old| *old + 5), 10);
        assert_eq!(*a.borrow(), 15);

        a.swap(&b);
        assert_eq!((*a.borrow(), *b.borrow()), (2, 15));

        assert_eq!(b.take(), 15);
        assert_eq!(*b.borrow(), 0);
    }

    #[test]
    #[should_panic(expected = "AtomicRefCell already borrowed")]
    fn swap_with_itself_panics() {
        let cell = AtomicRefCell::new(1);
        cell.swap(&cell);
    }

    #[test]
    #[should_panic(expected = "AtomicRefCell already")]
    fn replace_panics_while_borrowed() {
        let cell = AtomicRefCell::new(1);
        let _guard = cell.borrow();
        cell.replace(2);
    }

    #[test]
    fn default_from_clone_and_eq() {
        let cell: AtomicRefCell<Vec<u8>> = AtomicRefCell::default();
        assert!(cell.borrow().is_empty());

        let cell = AtomicRefCell::from(String::from("x"));
        let copy = cell.clone();
        assert_eq!(cell, copy);
        copy.borrow_mut().push('y');
        assert_ne!(cell, copy);
        assert!(cell < copy);
        assert_eq!(cell.cmp(&copy), core::cmp::Ordering::Less);
        assert_eq!(cell.partial_cmp(&cell), Some(core::cmp::Ordering::Equal));
    }

    #[test]
    #[should_panic(expected = "AtomicRefCell already mutably borrowed")]
    fn clone_panics_while_mutably_borrowed() {
        let cell = AtomicRefCell::new(1);
        let _guard = cell.borrow_mut();
        let _ = cell.clone();
    }

    #[test]
    fn debug_shows_the_value_or_borrowed() {
        let cell = AtomicRefCell::new(5);
        assert_eq!(format!("{cell:?}"), "AtomicRefCell { value: 5 }");

        let guard = cell.borrow_mut();
        assert_eq!(format!("{cell:?}"), "AtomicRefCell { value: <borrowed> }");
        assert_eq!(format!("{guard:?} {guard}"), "5 5");
        drop(guard);

        let guard = cell.borrow();
        assert_eq!(format!("{guard:?} {guard}"), "5 5");
    }

    #[test]
    fn works_with_unsized_values() {
        let array = AtomicRefCell::new([1, 2, 3]);
        let slice: &AtomicRefCell<[i32]> = &array;
        slice.borrow_mut()[0] = 10;
        assert_eq!(&*slice.borrow(), &[10, 2, 3]);

        let boxed: Box<AtomicRefCell<dyn fmt::Debug>> = Box::new(AtomicRefCell::new(5_u8));
        assert_eq!(format!("{:?}", boxed.borrow()), "5");
    }

    #[test]
    fn ref_clone_adds_a_reader() {
        let cell = AtomicRefCell::new(5);
        let first = cell.borrow();
        let second = AtomicRef::clone(&first);
        drop(first);

        assert!(cell.try_borrow_mut().is_err());
        drop(second);
        assert!(cell.try_borrow_mut().is_ok());
    }

    #[test]
    fn ref_map_and_filter_map_keep_the_borrow() {
        let cell = AtomicRefCell::new((1, String::from("a")));

        let text = AtomicRef::map(cell.borrow(), |pair| &pair.1);
        assert_eq!(&*text, "a");
        assert!(cell.try_borrow_mut().is_err());
        drop(text);
        assert!(cell.try_borrow_mut().is_ok());

        let found = AtomicRef::filter_map(cell.borrow(), |pair| Some(&pair.0));
        assert_eq!(*found.unwrap(), 1);

        let missing = AtomicRef::filter_map(cell.borrow(), |_| None::<&i32>);
        let original = missing.unwrap_err();
        assert_eq!(original.0, 1);
        assert!(cell.try_borrow_mut().is_err());
        drop(original);
        assert!(cell.try_borrow_mut().is_ok());
    }

    #[test]
    fn ref_mut_map_and_filter_map_keep_the_borrow() {
        let cell = AtomicRefCell::new((1, String::from("a")));

        let mut text = AtomicRefMut::map(cell.borrow_mut(), |pair| &mut pair.1);
        text.push('b');
        assert!(cell.try_borrow().is_err());
        drop(text);
        assert_eq!(cell.borrow().1, "ab");

        let found = AtomicRefMut::filter_map(cell.borrow_mut(), |pair| Some(&mut pair.0));
        *found.unwrap() += 1;
        assert_eq!(cell.borrow().0, 2);

        let missing = AtomicRefMut::filter_map(cell.borrow_mut(), |_| None::<&mut i32>);
        let mut original = missing.unwrap_err();
        original.0 = 7;
        assert!(cell.try_borrow().is_err());
        drop(original);
        assert_eq!(cell.borrow().0, 7);
    }

    #[test]
    fn a_panic_in_map_releases_the_borrow() {
        let cell = AtomicRefCell::new(1);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = AtomicRef::map(cell.borrow(), |_| -> &i32 { panic!("boom") });
        }));
        assert!(result.is_err());
        assert!(cell.try_borrow_mut().is_ok());

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = AtomicRefMut::map(cell.borrow_mut(), |_| -> &mut i32 { panic!("boom") });
        }));
        assert!(result.is_err());
        assert!(cell.try_borrow().is_ok());
    }

    #[test]
    fn the_reader_count_does_not_wrap_around() {
        let cell = AtomicRefCell::new(1);
        let guard = cell.borrow();

        // As if `isize::MAX - 1` more guards had been leaked.
        cell.borrow.store(isize::MAX, Ordering::Relaxed);
        assert!(cell.try_borrow().is_err());
        assert!(cell.try_borrow_mut().is_err());

        let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = AtomicRef::clone(&guard);
        }));
        assert!(panicked.is_err());
        assert_eq!(cell.borrow.load(Ordering::Relaxed), isize::MAX);

        // Put the count back to what `guard` alone accounts for.
        cell.borrow.store(1, Ordering::Relaxed);
        drop(guard);
        assert!(cell.try_borrow_mut().is_ok());
    }

    #[test]
    fn bounds_for_send_and_sync() {
        const fn assert_send<T: Send>() {}
        const fn assert_sync<T: Sync>() {}

        assert_send::<AtomicRefCell<u8>>();
        assert_sync::<AtomicRefCell<u8>>();
        // `Cell` is `Send` but not `Sync`, so only `Send` holds.
        assert_send::<AtomicRefCell<core::cell::Cell<u8>>>();
        assert_send::<AtomicRef<'static, u8>>();
        assert_sync::<AtomicRef<'static, u8>>();
        assert_send::<AtomicRefMut<'static, u8>>();
        assert_sync::<AtomicRefMut<'static, u8>>();
    }

    #[test]
    fn guards_can_be_released_from_another_thread() {
        let cell = AtomicRefCell::new(1);
        let guard = cell.borrow_mut();

        std::thread::scope(|s| {
            s.spawn(move || drop(guard));
        });
        assert!(cell.try_borrow_mut().is_ok());
    }

    #[test]
    fn threads_share_readers_and_writers() {
        // Smaller under Miri, which is slow at spinning threads.
        const WRITERS: usize = if cfg!(miri) { 2 } else { 4 };
        const INCREMENTS: usize = if cfg!(miri) { 20 } else { 1_000 };

        let cell = AtomicRefCell::new(0_usize);

        std::thread::scope(|s| {
            for _ in 0..WRITERS {
                s.spawn(|| {
                    for _ in 0..INCREMENTS {
                        loop {
                            if let Ok(mut value) = cell.try_borrow_mut() {
                                *value += 1;
                                break;
                            }
                            core::hint::spin_loop();
                        }
                    }
                });
            }
            s.spawn(|| {
                let mut last = 0;
                for _ in 0..INCREMENTS {
                    if let Ok(value) = cell.try_borrow() {
                        // The count only ever grows.
                        assert!(*value >= last);
                        last = *value;
                    }
                }
            });
        });

        assert_eq!(cell.into_inner(), WRITERS * INCREMENTS);
    }

    #[test]
    fn drops_the_value_once() {
        use alloc::sync::Arc;

        let value = Arc::new(());
        let cell = AtomicRefCell::new(Arc::clone(&value));
        drop(cell.borrow());
        drop(cell.borrow_mut());
        assert_eq!(Arc::strong_count(&value), 2);
        drop(cell);
        assert_eq!(Arc::strong_count(&value), 1);
    }

    #[test]
    fn heap_size_is_zero() {
        let cell = AtomicRefCell::new(Vec::from([1_u8; 100]));
        assert_eq!(cell.heap_size(), 0);

        // Whether the cell is borrowed does not matter.
        let _guard = cell.borrow_mut();
        assert_eq!(cell.heap_size(), 0);
    }
}
