//! A queue that many threads push events into and one consumer drains in
//! batches.
//!
//! See [`EventQueue`].

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ptr;
use std::sync::atomic::{AtomicPtr, AtomicU8, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

// Implementation notes
// ----------------------
//
// A lock-free multi-producer event queue for the "many threads produce
// events, other threads periodically drain them" pattern -- e.g. an
// event bus, where you don't need per-item pop semantics, just "give me
// everything that's happened since I last checked."
//
// Each producer thread accumulates its pushes into its own plain,
// contiguous `Vec<T>` -- not a shared structure at all, so pushing never
// synchronizes with *other producers* in any way, and iterating what a
// thread produced is a normal cache-friendly `Vec` scan rather than
// chasing pointers through a linked list of individually-allocated
// nodes. [`drain`](EventQueue::drain) walks every thread's buffer and
// swaps each one out for a fresh empty `Vec`, in a single atomic
// operation per thread.
//
// The only synchronization on the hot path is between a single thread's
// own pushes and an occasional `drain` reaching into *that specific
// thread's* buffer -- never between two producer threads, and never a
// blocking one: each per-thread buffer is guarded by a swap-based
// ticket (see `ThreadBuffer`) rather than a `Mutex`, so contention
// (which only happens if a drain lands on the exact instant a push is
// in progress) resolves with a few spins, never OS-level parking.
//
// Finding a thread's buffer, and registering a new one the first time a
// thread pushes to a given queue, uses a `thread_local!` cache plus a
// lock-free append-only list of every buffer that's ever been created
// for this queue (never unlinked, so no reclamation hazard: `drain`
// walking the list concurrently with a new thread appending to it is
// exactly as safe as any other lock-free append-only list).
//
// Buffers are *recycled*, not removed. When a producer thread exits, its
// buffer is marked free (by a thread-local guard, off the hot path) and
// the next thread to push claims it instead of allocating a new one, so
// the list -- and the cost of `drain`, `len` and `is_empty`, which walk
// all of it -- is bounded by the peak number of *concurrently live*
// producers, not by how many threads have ever pushed. Events a
// finished thread left undrained stay in its buffer for the next
// `drain`, ahead of whatever the buffer's next owner pushes.
//
// Cross-thread event ordering in `drain`'s output follows *reverse
// creation order* of the buffers (the list is prepend-only, so the most
// recently created buffer comes first), not global push time -- each
// thread's own events stay in the order it pushed them, but if thread A
// pushed at time 1 and thread B pushed at time 2, they may come back in
// either relative order. If you need a single global order across all
// producers, this isn't the right structure. (One caveat on the
// per-thread guarantee: a thread that pushes from another
// `thread_local!` destructor during its own teardown may find its buffer
// already recycled, and then its final events can interleave with the
// next owner's. This is memory-safe, and only affects ordering in that
// corner.)
//
// The thread-local cache holds a plain, non-owning raw pointer to the
// buffer, not an `Arc`/`Weak` -- see `EventQueue::thread_buffer` for
// why that's sound. This is what keeps `push` down to two atomic
// operations (the buffer's own acquire/release swap) instead of paying
// for reference counting on every call.

/// One producer thread's accumulated, not-yet-drained events. Guarded by
/// a swap-to-null "ticket": whoever holds the non-null pointer has
/// exclusive access, and puts a (possibly different) vec back when done.
/// Cheaper and simpler than a `Mutex`, and never parks a thread -- the
/// only contention is a push racing a drain of this exact buffer, which
/// resolves in a handful of spins.
struct ThreadBuffer<T> {
    slot: AtomicPtr<Vec<T>>,
}

unsafe impl<T: Send> Send for ThreadBuffer<T> {}
unsafe impl<T: Send> Sync for ThreadBuffer<T> {}

impl<T> ThreadBuffer<T> {
    fn new() -> Self {
        Self {
            slot: AtomicPtr::new(Box::into_raw(Box::new(Vec::new()))),
        }
    }

    fn push(&self, value: T) {
        loop {
            let ptr = self.slot.swap(ptr::null_mut(), Ordering::Acquire);
            if ptr.is_null() {
                std::hint::spin_loop();
                continue;
            }
            let mut vec = unsafe { Box::from_raw(ptr) };
            vec.push(value);
            self.slot.store(Box::into_raw(vec), Ordering::Release);
            return;
        }
    }

    /// Swaps out whatever has accumulated for a fresh empty `Vec`.
    fn take(&self) -> Vec<T> {
        loop {
            let ptr = self.slot.swap(ptr::null_mut(), Ordering::Acquire);
            if ptr.is_null() {
                std::hint::spin_loop();
                continue;
            }
            let contents = *unsafe { Box::from_raw(ptr) };
            self.slot
                .store(Box::into_raw(Box::new(Vec::new())), Ordering::Release);
            return contents;
        }
    }

    /// Peeks the current length without taking ownership. Pays the same
    /// swap-and-restore cost as `push`/`take`, which is fine since this
    /// is only used by [`EventQueue::len`]/[`EventQueue::is_empty`], not
    /// on any per-push hot path.
    fn peek_len(&self) -> usize {
        loop {
            let ptr = self.slot.swap(ptr::null_mut(), Ordering::Acquire);
            if ptr.is_null() {
                std::hint::spin_loop();
                continue;
            }
            let len = unsafe { (*ptr).len() };
            self.slot.store(ptr, Ordering::Release);
            return len;
        }
    }
}

impl<T> Drop for ThreadBuffer<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(*self.slot.get_mut())) };
    }
}

/// `RegistryNode::state` value: no live thread owns this node, so a newly
/// registering thread may claim it. Whatever events are still in its
/// buffer stay there until the next `drain`.
const NODE_FREE: u8 = 0;
/// `RegistryNode::state` value: some live thread is pushing into this node.
const NODE_OWNED: u8 = 1;

/// Append-only, never-freed-until-the-queue-drops linked list of every
/// `ThreadBuffer` created for a given queue. Nodes are only ever added at
/// the front (via CAS) and never unlinked, so `drain` walking the list
/// concurrently with a new thread registering is safe by the same
/// reasoning as any lock-free, append-only structure: nothing is ever
/// mutated or freed out from under a concurrent reader. The buffer lives
/// inline (not boxed separately) since the whole node is already one heap
/// allocation and never moves after being linked in.
///
/// Nodes are *recycled* rather than removed: when a thread exits, its
/// node's `state` goes back to [`NODE_FREE`] and the next thread to
/// register claims it with a CAS instead of allocating a new one. That
/// bounds the list by the peak number of concurrently live producers,
/// not by the number of threads that ever pushed, without needing any
/// memory-reclamation scheme.
struct RegistryNode<T> {
    state: AtomicU8,
    buffer: ThreadBuffer<T>,
    next: *mut Self,
}

/// Liveness handle shared between a queue and the thread-exit guards that
/// point into its nodes (see [`Guard`]). It is deliberately independent of
/// `T`, so thread-local storage can hold it for any queue without
/// requiring `T: 'static`, and it never owns any events, so a lingering
/// guard can never delay (or move to another thread) a `T`'s destructor.
///
/// The mutex is what makes a guard's raw pointer into a node safe to
/// dereference: the queue flips `alive` to `false` under the lock *before*
/// freeing any node, and a guard only touches its node while holding the
/// lock and seeing `alive == true`. Both happen on cold paths (thread
/// exit, queue drop), never in `push`.
struct QueueLife {
    alive: Mutex<bool>,
}

impl QueueLife {
    fn lock(&self) -> MutexGuard<'_, bool> {
        // Nothing done under this lock can panic, but don't turn a
        // poisoned lock into a panic inside a TLS destructor if it ever did.
        self.alive.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// One thread's claim on one node of one queue. Lives in the thread's
/// [`GUARDS`], and gives the node back (marks it [`NODE_FREE`]) when the
/// thread exits -- or earlier, once the queue is known to be gone.
///
/// Type-erased (`T` only ever appears behind the raw pointers) so a single
/// thread-local can hold guards for every `EventQueue<T>`, for any `T`.
struct Guard {
    life: Arc<QueueLife>,
    /// Points at the node's `state`. Only dereferenced under `life`'s lock
    /// while the queue is still alive.
    state: *const AtomicU8,
    /// Points at the node's `ThreadBuffer<T>`; cast back to the right `T`
    /// by the queue whose unique id keys this guard.
    buffer: *const (),
}

impl Guard {
    fn queue_is_alive(&self) -> bool {
        *self.life.lock()
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        let alive = self.life.lock();
        if *alive {
            // SAFETY: the queue can't free its nodes while we hold the
            // lock with `alive == true`, so `state` is still valid.
            unsafe { (*self.state).store(NODE_FREE, Ordering::Release) };
        }
    }
}

/// A thread's guards for every live queue it has pushed to, keyed by queue
/// id. This is what lets a thread find its own node again after
/// [`LOCAL_CACHE`] evicted the entry, without walking the registry (which
/// can no longer identify "my" node -- nodes aren't tied to a thread id).
/// Dropped at thread exit, which releases every node the thread held.
struct Guards {
    by_queue: BTreeMap<u64, Guard>,
    /// Size at which the next registration prunes guards of dropped
    /// queues; doubled after each prune so the total cost stays amortized
    /// O(1) per registration, and the map stays proportional to the number
    /// of *live* queues this thread uses.
    prune_at: usize,
}

impl Guards {
    const MIN_PRUNE_AT: usize = 16;

    const fn new() -> Self {
        Self {
            by_queue: BTreeMap::new(),
            prune_at: Self::MIN_PRUNE_AT,
        }
    }

    fn insert(&mut self, id: u64, guard: Guard) {
        if self.by_queue.len() >= self.prune_at {
            self.by_queue.retain(|_, g| g.queue_is_alive());
            self.prune_at = (self.by_queue.len() * 2).max(Self::MIN_PRUNE_AT);
        }
        self.by_queue.insert(id, guard);
    }
}

/// Global, monotonically increasing counter handing out a unique ID to
/// every `EventQueue` ever created (across all `T`, since a single
/// `thread_local!` cache serves every queue instance). Used instead of
/// the queue's address to detect a stale thread-local cache entry, so
/// that check is a plain integer comparison instead of the atomic
/// refcount bump an `Arc`/`Weak`-based check would need -- see
/// `EventQueue::thread_buffer`.
static NEXT_QUEUE_ID: AtomicU64 = AtomicU64::new(0);

/// A queue that many threads can push events into, and that is drained in
/// batches.
///
/// It fits the pattern "many threads produce events, another thread
/// periodically collects everything that happened since it last looked":
/// an event bus, a log or metrics sink, input handed to a single consumer once
/// per frame. There is no `pop`: [`drain`](Self::drain) takes all pending
/// events, from every thread, in one call.
///
/// Pushing takes `&self`, is lock-free, and does not wait for other
/// producers, so a queue can be shared by reference or in an `Arc`. A queue
/// is `Send` and `Sync` whenever `T` is `Send`.
///
/// # Ordering
///
/// The events a thread pushes come out of [`drain`](Self::drain) in the order
/// that thread pushed them. The order *between* threads is unspecified: if one
/// thread pushed before another, their events may still come back in either
/// order. If you need one global order across all producers, use a channel or
/// a `Mutex<Vec<T>>` instead.
///
/// Events a thread pushes while it is shutting down (from a thread-local
/// destructor) are delivered, but may not keep their order relative to that
/// thread's earlier events.
///
/// # Cost
///
/// `push` is cheap and does not depend on the number of threads.
/// [`drain`](Self::drain), [`len`](Self::len) and
/// [`is_empty`](Self::is_empty) do work proportional to the number of threads
/// that push to the queue at the same time. Events left behind by a thread
/// that has exited stay in the queue until the next `drain`.
///
/// # Examples
///
/// ```
/// use std::thread;
///
/// use anythingy::EventQueue;
///
/// let queue = EventQueue::new();
///
/// thread::scope(|scope| {
///     for worker in 0..3 {
///         let queue = &queue;
///         scope.spawn(move || queue.push(format!("worker {worker} finished")));
///     }
/// });
///
/// assert_eq!(queue.len(), 3);
/// let events = queue.drain();
/// assert_eq!(events.len(), 3);
/// assert!(queue.is_empty());
/// ```
pub struct EventQueue<T> {
    id: u64,
    life: Arc<QueueLife>,
    registry_head: AtomicPtr<RegistryNode<T>>,
}

unsafe impl<T: Send> Send for EventQueue<T> {}
unsafe impl<T: Send> Sync for EventQueue<T> {}

/// Cap on [`LOCAL_CACHE`]'s size. Bounds every lookup to at most this many
/// comparisons (plus an LRU shuffle on a hit), regardless of how many
/// distinct `EventQueue` instances a given thread has *ever* pushed to --
/// see `EventQueue::thread_buffer` for why that bound matters.
const LOCAL_CACHE_CAP: usize = 32;

thread_local! {
    /// Per-thread cache of `(queue id, raw pointer to that thread's
    /// buffer for this queue)`, ordered least- to most-recently-used and
    /// capped at [`LOCAL_CACHE_CAP`] entries. A single `thread_local!`
    /// serves every `EventQueue<T>` instance and every `T`; a thread
    /// steadily using a handful of queues settles into just those few
    /// entries, so a linear scan beats a hash map here.
    ///
    /// Holds non-owning raw pointers, not `Arc`/`Weak`: see
    /// `EventQueue::thread_buffer` for why that's sound. Since nothing
    /// here owns anything, there's no cleanup to do when a thread exits,
    /// an entry goes stale, or an entry is evicted -- it's just a few
    /// inert bytes either way. The authoritative record of which node a
    /// thread owns is [`GUARDS`].
    static LOCAL_CACHE: RefCell<Vec<(u64, *const ())>> = const { RefCell::new(Vec::new()) };

    /// The thread's ownership claims on registry nodes; see [`Guards`].
    /// Consulted only on a [`LOCAL_CACHE`] miss (first push to a queue, or
    /// after eviction), never on the hot path.
    static GUARDS: RefCell<Guards> = const { RefCell::new(Guards::new()) };
}

impl<T: Send> EventQueue<T> {
    /// Creates an empty queue.
    pub fn new() -> Self {
        Self {
            id: NEXT_QUEUE_ID.fetch_add(1, Ordering::Relaxed),
            life: Arc::new(QueueLife {
                alive: Mutex::new(true),
            }),
            registry_head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// Claims a free node from the registry (one whose previous thread has
    /// exited), or links in a brand-new one if there isn't any. The
    /// returned node is marked [`NODE_OWNED`] and belongs to the caller.
    fn claim_node(&self) -> *const RegistryNode<T> {
        let mut node = self.registry_head.load(Ordering::Acquire);
        while !node.is_null() {
            let n = unsafe { &*node };
            if n.state.load(Ordering::Relaxed) == NODE_FREE
                && n.state
                    .compare_exchange(NODE_FREE, NODE_OWNED, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
            {
                return node;
            }
            node = n.next;
        }

        let new_node = Box::into_raw(Box::new(RegistryNode {
            state: AtomicU8::new(NODE_OWNED),
            buffer: ThreadBuffer::new(),
            next: ptr::null_mut(),
        }));
        let mut head = self.registry_head.load(Ordering::Relaxed);
        loop {
            unsafe { (*new_node).next = head };
            match self.registry_head.compare_exchange_weak(
                head,
                new_node,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => return new_node,
                Err(actual) => head = actual,
            }
        }
    }

    /// Finds the calling thread's node for this queue, claiming one (and
    /// recording a [`Guard`] so it's released when the thread exits) if
    /// this thread doesn't have one yet.
    ///
    /// Looking up an existing node first (rather than unconditionally
    /// claiming) is what makes it safe for [`thread_buffer`]'s cache to
    /// evict entries: eviction only costs falling back to this lookup,
    /// never a second node for the same (thread, queue) pair -- which
    /// would silently reorder that thread's own events, since `drain`
    /// visits nodes in list order.
    ///
    /// If thread-local storage is already gone (this is running from some
    /// other TLS destructor during thread teardown) there is nowhere to
    /// record a guard, so the node is claimed unguarded: it stays owned
    /// until the queue drops instead of being recycled. Memory-safe, and
    /// only costs one node's worth of reuse.
    ///
    /// [`thread_buffer`]: Self::thread_buffer
    fn lookup_or_register_thread_buffer(&self) -> *const ThreadBuffer<T> {
        let registered = GUARDS.try_with(|guards| {
            let mut guards = guards.borrow_mut();
            if let Some(guard) = guards.by_queue.get(&self.id) {
                return guard.buffer.cast::<ThreadBuffer<T>>();
            }
            let node = self.claim_node();
            let buffer: *const ThreadBuffer<T> = unsafe { &raw const (*node).buffer };
            guards.insert(
                self.id,
                Guard {
                    life: Arc::clone(&self.life),
                    state: unsafe { &raw const (*node).state },
                    buffer: buffer.cast(),
                },
            );
            buffer
        });
        registered.unwrap_or_else(|_| unsafe { &raw const (*self.claim_node()).buffer })
    }

    /// Finds (or lazily creates) the calling thread's buffer for this
    /// queue.
    ///
    /// Returns a raw, non-owning pointer, cached as such in thread-local
    /// storage rather than an `Arc`/`Weak`. This is sound because: (1)
    /// `push`/`len` only ever run while the caller holds a live `&self`,
    /// which proves this `EventQueue` -- and therefore its registry, and
    /// every buffer the registry has ever linked in -- is still alive;
    /// and (2) the cache entry is keyed by `self.id`, a value from a
    /// global counter that's never reused, not by `self`'s address, so a
    /// *different*, later queue that happens to land at the same address
    /// as a since-dropped one can never be confused with a stale cache
    /// entry (the id simply won't match, and we look up or register a
    /// fresh buffer instead). Between those two, a cache hit always
    /// points at a currently-live buffer of the currently-live queue
    /// being called -- no refcounting needed to prove it.
    ///
    /// Node recycling doesn't affect that argument: a node is never freed
    /// while its queue lives, only handed to another thread. If a thread
    /// pushes through a cache entry after its node was recycled (only
    /// possible from another TLS destructor during thread teardown), two
    /// threads briefly share one buffer, which the buffer's ticket
    /// handles like any other push/push contention.
    fn thread_buffer(&self) -> *const ThreadBuffer<T> {
        // `try_with`, not `with`: a push made from another `thread_local!`'s
        // destructor can run after `LOCAL_CACHE` itself has been torn down,
        // and `with` would panic there (aborting the process, since it's
        // inside a TLS destructor). In that case the cache is just skipped
        // and the node is found via `lookup_or_register_thread_buffer`,
        // which is always correct -- the cache is purely an optimization.
        LOCAL_CACHE
            .try_with(|cache| self.thread_buffer_cached(cache))
            .unwrap_or_else(|_| self.lookup_or_register_thread_buffer())
    }

    fn thread_buffer_cached(
        &self,
        cache: &RefCell<Vec<(u64, *const ())>>,
    ) -> *const ThreadBuffer<T> {
        let mut cache = cache.borrow_mut();
        if let Some(pos) = cache.iter().position(|(id, _)| *id == self.id) {
            // Move to the end (most-recently-used) so a thread that's
            // actively alternating between a handful of queues keeps
            // all of them cheap to find, not just the last one used.
            let entry = cache.remove(pos);
            let ptr = entry.1;
            cache.push(entry);
            return ptr.cast::<ThreadBuffer<T>>();
        }
        let ptr = self.lookup_or_register_thread_buffer();
        if cache.len() >= LOCAL_CACHE_CAP {
            // Evict the least-recently-used entry. Bounds every
            // lookup to at most `LOCAL_CACHE_CAP` comparisons
            // regardless of how many distinct queues this thread has
            // *ever* touched -- without this, a thread that creates
            // and drops many short-lived queues over its life would
            // accumulate one entry per queue forever, turning every
            // future push into a scan over that whole history.
            cache.remove(0);
        }
        cache.push((self.id, ptr.cast::<()>()));
        ptr
    }

    /// Adds an event to the queue.
    ///
    /// This never blocks on other producers. It may be called from any number
    /// of threads at once, and concurrently with [`drain`](Self::drain).
    pub fn push(&self, value: T) {
        unsafe { (*self.thread_buffer()).push(value) };
    }

    /// Removes and returns every event pushed so far, by every thread.
    ///
    /// Each thread's events are in the order it pushed them; see the
    /// [type-level notes on ordering](EventQueue#ordering) for what is not
    /// guaranteed between threads. Events pushed while `drain` runs are
    /// returned by this call or by the next one.
    pub fn drain(&self) -> Vec<T> {
        let mut all = Vec::new();
        let mut node = self.registry_head.load(Ordering::Acquire);
        while !node.is_null() {
            let n = unsafe { &*node };
            all.extend(n.buffer.take());
            node = n.next;
        }
        all
    }

    /// Returns the number of events currently in the queue.
    ///
    /// Events pushed concurrently may or may not be counted, so treat the
    /// result as a snapshot. This visits every pushing thread's buffer, so it
    /// is meant for occasional checks rather than for performance-critical code.
    pub fn len(&self) -> usize {
        let mut total = 0;
        let mut node = self.registry_head.load(Ordering::Acquire);
        while !node.is_null() {
            let n = unsafe { &*node };
            total += n.buffer.peek_len();
            node = n.next;
        }
        total
    }

    /// Returns `true` if the queue holds no events. A snapshot, like
    /// [`len`](Self::len).
    pub fn is_empty(&self) -> bool {
        let mut node = self.registry_head.load(Ordering::Acquire);
        while !node.is_null() {
            let n = unsafe { &*node };
            if n.buffer.peek_len() > 0 {
                return false;
            }
            node = n.next;
        }
        true
    }

    /// Number of nodes ever linked into the registry (test-only).
    #[cfg(test)]
    fn registry_len(&self) -> usize {
        let mut count = 0;
        let mut node = self.registry_head.load(Ordering::Acquire);
        while !node.is_null() {
            count += 1;
            node = unsafe { (*node).next };
        }
        count
    }
}

impl<T: Send> Default for EventQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for EventQueue<T> {
    fn drop(&mut self) {
        // Tell every thread-exit guard that these nodes are about to go
        // away. Taking the lock also waits out any guard that's in the
        // middle of touching one, so after this nothing can reach a node.
        *self.life.lock() = false;

        let mut node = *self.registry_head.get_mut();
        while !node.is_null() {
            let boxed = unsafe { Box::from_raw(node) };
            node = boxed.next;
            // `boxed.buffer` (a `ThreadBuffer<T>`) drops here, freeing
            // whatever vec it's currently holding.
        }
    }
}

#[cfg(test)]
mod tests {
    // Test values are small and narrowed on purpose, and helper types are
    // declared next to the test that uses them.
    #![allow(clippy::cast_possible_truncation, clippy::items_after_statements)]
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering as O};

    #[test]
    fn drain_returns_all_pushed_from_one_thread() {
        let q = EventQueue::new();
        for i in 0..10 {
            q.push(i);
        }
        assert_eq!(q.drain(), (0..10).collect::<Vec<_>>());
    }

    #[test]
    fn drain_empties_the_queue() {
        let q = EventQueue::new();
        q.push(1);
        assert_eq!(q.drain(), vec![1]);
        assert_eq!(q.drain(), Vec::<i32>::new());
        assert!(q.is_empty());
    }

    #[test]
    fn len_tracks_pushes_and_drains() {
        let q = EventQueue::new();
        assert_eq!(q.len(), 0);
        q.push(1);
        q.push(2);
        assert_eq!(q.len(), 2);
        q.drain();
        assert_eq!(q.len(), 0);
    }

    #[test]
    fn dropping_queue_drops_undrained_events() {
        let counter = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, O::SeqCst);
            }
        }

        {
            let q = EventQueue::new();
            for _ in 0..5 {
                q.push(DropCounter(counter.clone()));
            }
        }
        assert_eq!(counter.load(O::SeqCst), 5);
    }

    #[test]
    fn reused_queue_address_does_not_confuse_the_cache() {
        // Regression test for the hazard the id-based cache exists to
        // rule out: a new queue landing at the same address as a
        // previously dropped one must never be served a stale cached
        // pointer from a thread that used the old one.
        for round in 0..64 {
            let q = EventQueue::new();
            q.push(round);
            assert_eq!(q.drain(), vec![round]);
        }
    }

    #[test]
    fn local_cache_stays_bounded_across_many_queues() {
        // Regression test for the bug the LRU cap exists to fix: without
        // it, one thread creating many short-lived queues (exactly what
        // this loop does) accumulates one permanent cache entry per
        // queue, turning every future push into a scan over that whole
        // history. Correctness-wise this must still behave identically
        // either way; this just exercises far more distinct queues than
        // `LOCAL_CACHE_CAP` from a single thread to make sure eviction
        // doesn't break anything.
        for round in 0..(LOCAL_CACHE_CAP * 10) {
            let q = EventQueue::new();
            for i in 0..5 {
                q.push((round, i));
            }
            assert_eq!(q.drain(), (0..5).map(|i| (round, i)).collect::<Vec<_>>());
        }
    }

    #[test]
    fn local_cache_lru_keeps_alternating_queues_findable() {
        // A thread alternating between more queues than fit in the cache
        // at once must still find the right buffer for each -- eviction
        // must not corrupt lookups for queues still in active use.
        let queues: Vec<EventQueue<usize>> = (0..(LOCAL_CACHE_CAP + 3))
            .map(|_| EventQueue::new())
            .collect();

        for round in 0..20 {
            for q in &queues {
                q.push(round);
            }
        }

        for q in &queues {
            assert_eq!(q.drain(), (0..20).collect::<Vec<_>>());
        }
    }

    #[test]
    fn push_from_a_thread_local_destructor_does_not_abort() {
        // Regression test: `A`'s destructor is registered before
        // `LOCAL_CACHE` is first touched, so it runs after `LOCAL_CACHE`
        // has been destroyed. Pushing from it used to panic inside a TLS
        // destructor, aborting the whole process.
        struct PushOnDrop(&'static EventQueue<u32>);
        impl Drop for PushOnDrop {
            fn drop(&mut self) {
                self.0.push(1);
            }
        }
        thread_local! {
            static A: RefCell<Option<PushOnDrop>> = const { RefCell::new(None) };
        }

        // The thread-local needs a `'static` queue; reclaim the box once the
        // thread (and so its destructor) has finished, so nothing leaks.
        let raw = Box::into_raw(Box::new(EventQueue::new()));
        // SAFETY: `raw` outlives the spawned thread, which is joined below
        // before the box is reclaimed.
        let q: &'static EventQueue<u32> = unsafe { &*raw };
        std::thread::spawn(move || {
            A.with(|a| *a.borrow_mut() = Some(PushOnDrop(q)));
            q.push(0);
        })
        .join()
        .unwrap();

        let queue = unsafe { Box::from_raw(raw) };
        let mut got = queue.drain();
        got.sort_unstable();
        assert_eq!(got, vec![0, 1]);
    }

    #[test]
    fn sequential_threads_recycle_one_node() {
        // `JoinHandle::join`, not `thread::scope`: a scope is released as
        // soon as the closure returns, which is *before* the thread's TLS
        // destructors (and so its node guard) have run. Joining the
        // thread itself waits for those too.
        let q = Arc::new(EventQueue::new());
        for t in 0..200u32 {
            let q = Arc::clone(&q);
            std::thread::spawn(move || q.push(t)).join().unwrap();
        }
        // Each thread fully exited before the next started, so they all
        // reuse the first thread's node instead of linking in 200 of them.
        assert_eq!(q.registry_len(), 1);
        // Leftover events from finished threads survive, in ownership order.
        assert_eq!(q.drain(), (0..200).collect::<Vec<_>>());
    }

    #[test]
    fn registry_is_bounded_by_peak_concurrency() {
        const THREADS: usize = 4;
        let q = Arc::new(EventQueue::new());
        for _ in 0..25 {
            let barrier = Arc::new(std::sync::Barrier::new(THREADS));
            let handles: Vec<_> = (0..THREADS)
                .map(|_| {
                    let q = Arc::clone(&q);
                    let barrier = Arc::clone(&barrier);
                    std::thread::spawn(move || {
                        q.push(0u8);
                        // Keep all threads alive together so none can
                        // exit (and free its node) before the others push.
                        barrier.wait();
                    })
                })
                .collect();
            for h in handles {
                h.join().unwrap();
            }
            q.drain();
        }
        assert!(
            q.registry_len() <= THREADS,
            "registry grew to {}",
            q.registry_len()
        );
    }

    #[test]
    fn drain_after_thread_exit_still_sees_its_events() {
        let q = EventQueue::new();
        std::thread::scope(|scope| {
            scope.spawn(|| {
                q.push(1);
                q.push(2);
            });
        });
        assert_eq!(q.len(), 2);
        assert_eq!(q.drain(), vec![1, 2]);
    }

    #[test]
    fn queue_dropped_before_its_thread_exits() {
        // The thread's exit guard outlives the queue here: the queue is
        // dropped when the closure ends, before the thread's TLS
        // destructors run. The guard must notice and not touch the freed
        // node (Miri checks this).
        let counter = Arc::new(AtomicUsize::new(0));
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, O::SeqCst);
            }
        }

        let q = EventQueue::new();
        let c = Arc::clone(&counter);
        std::thread::spawn(move || {
            q.push(DropCounter(c));
        })
        .join()
        .unwrap();
        assert_eq!(counter.load(O::SeqCst), 1);
    }

    #[test]
    fn many_queues_per_thread_prune_dead_guards() {
        // More short-lived queues than `Guards::MIN_PRUNE_AT`, so pruning
        // of guards for dropped queues runs, while a long-lived queue's
        // guard must survive it.
        let keep = EventQueue::new();
        keep.push(usize::MAX);
        for i in 0..(Guards::MIN_PRUNE_AT * 8) {
            let q = EventQueue::new();
            q.push(i);
            assert_eq!(q.drain(), vec![i]);
        }
        keep.push(usize::MAX - 1);
        assert_eq!(keep.drain(), vec![usize::MAX, usize::MAX - 1]);
        assert_eq!(keep.registry_len(), 1);
    }

    #[test]
    fn thread_churn_with_concurrent_drains_loses_nothing() {
        const WAVES: u64 = if cfg!(miri) { 4 } else { 200 };
        const THREADS: u64 = if cfg!(miri) { 3 } else { 6 };
        const PER_THREAD: u64 = if cfg!(miri) { 5 } else { 50 };

        let q = EventQueue::new();
        let done = std::sync::atomic::AtomicBool::new(false);
        let mut got: Vec<u64> = Vec::new();

        std::thread::scope(|scope| {
            let drainer = scope.spawn(|| {
                let mut got = Vec::new();
                while !done.load(O::SeqCst) {
                    got.extend(q.drain());
                }
                got.extend(q.drain());
                got
            });

            for wave in 0..WAVES {
                std::thread::scope(|producers| {
                    for t in 0..THREADS {
                        let q = &q;
                        producers.spawn(move || {
                            for i in 0..PER_THREAD {
                                q.push((wave * THREADS + t) * PER_THREAD + i);
                            }
                        });
                    }
                });
            }
            done.store(true, O::SeqCst);
            got = drainer.join().unwrap();
        });

        got.sort_unstable();
        let expected: Vec<u64> = (0..WAVES * THREADS * PER_THREAD).collect();
        assert_eq!(got, expected);
    }

    #[test]
    fn each_thread_keeps_its_own_push_order() {
        const PER_THREAD: usize = 5_000;
        let q = Arc::new(EventQueue::new());

        std::thread::scope(|scope| {
            for t in 0..4usize {
                let q = Arc::clone(&q);
                scope.spawn(move || {
                    for i in 0..PER_THREAD {
                        q.push((t, i));
                    }
                });
            }
        });

        let all = q.drain();
        assert_eq!(all.len(), 4 * PER_THREAD);

        let mut last_per_thread: [Option<usize>; 4] = [None; 4];
        for (t, i) in all {
            if let Some(last) = last_per_thread[t] {
                assert!(i > last, "thread {t}'s events came back out of order");
            }
            last_per_thread[t] = Some(i);
        }
    }

    #[test]
    fn mpmc_stress_no_lost_or_duplicated_events() {
        // Scaled down under Miri, which is orders of magnitude slower.
        const PRODUCERS: u64 = if cfg!(miri) { 3 } else { 8 };
        const PER_PRODUCER: u64 = if cfg!(miri) { 50 } else { 20_000 };
        const DRAINERS: u64 = if cfg!(miri) { 2 } else { 4 };

        let queue = Arc::new(EventQueue::new());
        let collected: Arc<std::sync::Mutex<Vec<u64>>> =
            Arc::new(std::sync::Mutex::new(Vec::new()));
        let producers_done = Arc::new(AtomicUsize::new(0));

        std::thread::scope(|scope| {
            for p in 0..PRODUCERS {
                let queue = Arc::clone(&queue);
                let producers_done = Arc::clone(&producers_done);
                scope.spawn(move || {
                    for i in 0..PER_PRODUCER {
                        queue.push(p * PER_PRODUCER + i);
                    }
                    producers_done.fetch_add(1, O::SeqCst);
                });
            }

            for _ in 0..DRAINERS {
                let queue = Arc::clone(&queue);
                let collected = Arc::clone(&collected);
                let producers_done = Arc::clone(&producers_done);
                scope.spawn(move || {
                    loop {
                        let batch = queue.drain();
                        if !batch.is_empty() {
                            collected.lock().unwrap().extend(batch);
                        } else if producers_done.load(O::SeqCst) == PRODUCERS as usize {
                            let last = queue.drain();
                            if !last.is_empty() {
                                collected.lock().unwrap().extend(last);
                            }
                            break;
                        }
                    }
                });
            }
        });

        let mut got = Arc::try_unwrap(collected).unwrap().into_inner().unwrap();
        got.sort_unstable();
        let expected: Vec<u64> = (0..PRODUCERS * PER_PRODUCER).collect();
        assert_eq!(got, expected);
    }
}
