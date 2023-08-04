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
#[cfg(test)]
mod tests;

use std::{
    alloc::{dealloc, Layout},
    borrow::Borrow,
    cell::Cell,
    ops::Deref,
    ptr::{addr_of, drop_in_place, NonNull},
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{Collectable, Visitor};

use self::collect::{CLEANING, DUMPSTER};

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
pub struct Gc<T>
where
    T: Collectable + Sync + ?Sized + 'static,
{
    /// A pointer to the heap allocation containing the data under concern.
    /// The pointee box should never be mutated.
    ///
    /// This pointer will only be null if it has been 'destroyed' and is about to be cleaned up.
    /// I do not use `Option<NonNull<T>` because it doesn't implement `CoerceUnsized`.
    ptr: NonNull<GcBox<T>>,
}

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
        Gc {
            ptr: Box::leak(Box::new(GcBox {
                strong: AtomicUsize::new(1),
                weak: AtomicUsize::new(0),
                generation: AtomicUsize::new(0),
                value,
            }))
            .into(),
        }
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
        let box_ref = unsafe { self.ptr.as_ref() };
        // increment strong count before generation to ensure sweeper never underestimates ref count
        box_ref.strong.fetch_add(1, Ordering::Relaxed);
        box_ref.generation.fetch_add(1, Ordering::Relaxed);
        DUMPSTER.notify_created_gc();
        DUMPSTER.mark_clean(box_ref);
        Gc { ptr: self.ptr }
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
        let box_ref = unsafe { self.ptr.as_ref() };
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
                        drop_in_place(self.ptr.as_mut());
                        dealloc(self.ptr.as_ptr().cast(), layout);
                    }
                }
            }
            _ => {
                DUMPSTER.mark_dirty(self.ptr);
                box_ref.weak.fetch_sub(1, Ordering::Relaxed);
            }
        }
        DUMPSTER.notify_dropped_gc();
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
        unsafe { &self.ptr.as_ref().value }
    }
}

impl<T: Collectable + ?Sized + Sync> AsRef<T> for Gc<T> {
    fn as_ref(&self) -> &T {
        unsafe { addr_of!(self.ptr.as_ref().value).as_ref().unwrap() }
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
