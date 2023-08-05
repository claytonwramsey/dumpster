/*
   dumpster, a cycle-tracking garbage collector for Rust.
   Copyright (C) 2023 Clayton Ramsey.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

//! Thread-safe shared garbage collection.

mod collect;
mod ptr;
#[cfg(test)]
mod tests;

use std::{
    alloc::{dealloc, Layout},
    borrow::Borrow,
    cell::{Cell, UnsafeCell},
    ops::Deref,
    ptr::{addr_of, drop_in_place},
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{Collectable, Visitor};

use self::{
    collect::{CLEANING, DUMPSTER},
    ptr::Tagged,
};

#[derive(Debug)]
/// A thread-safe garbage-collected pointer.
///
/// This pointer can be duplicated and then shared across threads.
/// Garbage collection is performed concurrently.
///
/// # Examples
///
/// ```
/// use dumpster::sync::Gc;
/// use std::sync::atomic::{AtomicUsize, Ordering};
///
/// let shared = Gc::new(AtomicUsize::new(0));
///
/// std::thread::scope(|s| {
///     s.spawn(|| {
///         let other_gc = shared.clone();
///         other_gc.store(1, Ordering::Relaxed);
///     });
///
///     shared.store(2, Ordering::Relaxed);
/// });
///
/// println!("{}", shared.load(Ordering::Relaxed));
/// ```
pub struct Gc<T: Collectable + Sync + ?Sized + 'static>(UnsafeCell<Tagged<T>>);

#[repr(C)]
/// The backing allocation for a [`Gc`].
struct GcBox<T>
where
    T: Collectable + Sync + ?Sized,
{
    /// The "strong" count, which is the number of extant `Gc`s to this allocation.
    /// If the strong count is zero, a value contained in the allocation may be dropped, but the
    /// allocation itself must still be valid.
    strong: AtomicUsize,
    /// The "weak" count, which is the number of references to this allocation stored in to-collect
    /// buffers by the collection algorithm.
    /// If the weak count is zero, the allocation may be destroyed.
    weak: AtomicUsize,
    /// The current generation number of the allocation.
    /// The generation number is incremented or decremented every time a strong reference is added
    /// to or removed from the allocation.
    generation: AtomicUsize,
    /// The actual data stored in the allocation.
    value: T,
}

unsafe impl<T> Send for Gc<T> where T: Collectable + Sync + ?Sized {}
unsafe impl<T> Sync for Gc<T> where T: Collectable + Sync + ?Sized {}

/// Collect all unreachable thread-safe [`Gc`]s on the heap.
///
/// This function may return while some `Gc`s created by this thread but which are unreachable have
/// still not been collected, due to concurrency.
/// For a blocking version, refer to [`collect_await`].
pub fn collect() {
    DUMPSTER.collect_all();
}

/// Collect all unreachable thread-safe [`Gc`]s on the heap, blocking until no more collection
/// operations are occurring.
pub fn collect_await() {
    collect();
    DUMPSTER.await_collection_end();
}

/// Information passed to a [`CollectCondition`] used to determine whether the garbage collector
/// should start collecting.
pub struct CollectInfo {
    /// Dummy value so this is a private structure.
    _private: (),
}

/// A function which determines whether the garbage collector should start collecting.
/// This function primarily exists so that it can be used with [`set_collect_condition`].
///
/// # Examples
///
/// ```rust
/// use dumpster::sync::{set_collect_condition, CollectInfo};
///
/// fn always_collect(_: &CollectInfo) -> bool {
///     true
/// }
/// ```
pub type CollectCondition = fn(&CollectInfo) -> bool;

#[must_use]
/// The default collection condition used by the garbage collector.
///
/// There are no guarantees about what this function returns, other than that it will return `true`
/// with sufficient frequency to ensure that all `Gc` operations are amortized _O(1)_ in runtime.
///
/// # Examples
///
/// ```rust
/// use dumpster::sync::{default_collect_condition, set_collect_condition};
///
/// set_collect_condition(default_collect_condition)
/// ```
pub fn default_collect_condition(info: &CollectInfo) -> bool {
    info.n_gcs_dropped_since_last_collect() > info.n_gcs_existing()
}

#[allow(clippy::missing_panics_doc)]
/// Set the function which determines whether the garbage collector should be run.
///
/// `f` will be periodically called by the garbage collector to determine whether it should perform
/// a full sweep of the heap.
/// When `f` returns true, a sweep will begin.
///
/// # Examples
///
/// ```
/// use dumpster::sync::{set_collect_condition, CollectInfo};
///
/// /// This function will make sure a GC sweep never happens unless directly activated.
/// fn never_collect(_: &CollectInfo) -> bool {
///     false
/// }
///
/// set_collect_condition(never_collect);
/// ```
pub fn set_collect_condition(f: CollectCondition) {
    *DUMPSTER.collect_condition.write().unwrap() = f;
}

impl<T> Gc<T>
where
    T: Collectable + Sync + ?Sized,
{
    /// Construct a new garbage-collected value.
    pub fn new(value: T) -> Gc<T>
    where
        T: Sized,
    {
        DUMPSTER.notify_created_gc();
        Gc(UnsafeCell::new(Tagged::new(
            Box::leak(Box::new(GcBox {
                strong: AtomicUsize::new(1),
                weak: AtomicUsize::new(0),
                generation: AtomicUsize::new(0),
                value,
            }))
            .into(),
            false,
        )))
    }
}

impl<T> Clone for Gc<T>
where
    T: Collectable + Sync + ?Sized,
{
    /// Clone a garbage-collected reference.
    /// This does not clone the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::sync::Gc;
    /// use std::sync::atomic::{AtomicU8, Ordering};
    ///
    /// let gc1 = Gc::new(AtomicU8::new(0));
    /// let gc2 = gc1.clone();
    ///
    /// gc1.store(1, Ordering::Relaxed);
    /// assert_eq!(gc2.load(Ordering::Relaxed), 1);
    /// ```
    fn clone(&self) -> Gc<T> {
        let box_ref = unsafe { (*self.0.get()).as_ref() };
        // increment strong count before generation to ensure sweeper never underestimates ref count
        box_ref.strong.fetch_add(1, Ordering::Relaxed);
        box_ref.generation.fetch_add(1, Ordering::Relaxed);
        DUMPSTER.notify_created_gc();
        DUMPSTER.mark_clean(box_ref);
        Gc(UnsafeCell::new(Tagged::new(
            unsafe { (*self.0.get()).as_nonnull() },
            false,
        )))
    }
}

impl<T> Drop for Gc<T>
where
    T: Collectable + Sync + ?Sized,
{
    fn drop(&mut self) {
        if CLEANING.with(Cell::get) {
            return;
        }
        let box_ref = unsafe { (*self.0.get()).as_ref() };
        // decrement strong count after generation to ensure sweeper never underestimates ref count
        box_ref.generation.fetch_sub(1, Ordering::Relaxed);
        box_ref.weak.fetch_add(1, Ordering::Acquire); // ensures that this allocation wasn't freed
                                                      // while we weren't looking
        match box_ref.strong.fetch_sub(1, Ordering::Release) {
            0 => unreachable!("strong cannot reach zero while a Gc to it exists"),
            1 => {
                DUMPSTER.mark_clean(box_ref);
                if box_ref.weak.fetch_sub(1, Ordering::Relaxed) == 1 {
                    // destroyed the last weak reference! we can safely deallocate this
                    let layout = Layout::for_value(box_ref);
                    unsafe {
                        let mut nn = (*self.0.get()).as_nonnull();
                        drop_in_place(nn.as_mut());
                        dealloc(nn.as_ptr().cast(), layout);
                    }
                }
            }
            _ => {
                DUMPSTER.mark_dirty(unsafe { (*self.0.get()).as_nonnull() });
                box_ref.weak.fetch_sub(1, Ordering::Relaxed);
            }
        }
        DUMPSTER.notify_dropped_gc();
    }
}

impl CollectInfo {
    /// Get the number of times that a [`Gc`] has been dropped since the last time a collection
    /// operation was performed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::sync::{set_collect_condition, CollectInfo};
    ///
    /// // Collection condition for whether many Gc's have been dropped.
    /// fn have_many_gcs_dropped(info: &CollectInfo) -> bool {
    ///     info.n_gcs_dropped_since_last_collect() > 100
    /// }
    ///
    /// set_collect_condition(have_many_gcs_dropped);
    /// ```
    pub fn n_gcs_dropped_since_last_collect(&self) -> usize {
        DUMPSTER.n_gcs_dropped.load(Ordering::Relaxed)
    }

    /// Get the total number of [`Gc`]s which currently exist.
    pub fn n_gcs_existing(&self) -> usize {
        DUMPSTER.n_gcs_existing.load(Ordering::Relaxed)
    }
}

unsafe impl<T: Collectable + Sync + ?Sized> Collectable for Gc<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        visitor.visit_sync(self);
        Ok(())
    }
}

impl<T: Collectable + Sync + ?Sized> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &(*self.0.get()).as_ref().value }
    }
}

impl<T: Collectable + ?Sized + Sync> AsRef<T> for Gc<T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: Collectable + ?Sized + Sync> Borrow<T> for Gc<T> {
    fn borrow(&self) -> &T {
        self.as_ref()
    }
}

impl<T: Collectable + ?Sized + Sync> std::fmt::Pointer for Gc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Pointer::fmt(&addr_of!(**self), f)
    }
}

#[cfg(feature = "coerce-unsized")]
impl<T, U> std::ops::CoerceUnsized<Gc<U>> for Gc<T>
where
    T: std::marker::Unsize<U> + Collectable + Sync + ?Sized,
    U: Collectable + Sync + ?Sized,
{
}
