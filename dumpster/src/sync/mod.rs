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
    marker::Unsize,
    ops::{CoerceUnsized, Deref},
    ptr::{addr_of, addr_of_mut, drop_in_place, NonNull},
    sync::Mutex,
};

use crate::{Collectable, Visitor};

use self::collect::{CLEANING, DUMPSTER};

/// A thread-safe garbage-collected pointer.
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

#[derive(Debug)]
/// The reference counts for an allocation.
struct RefCounts {
    /// The "strong" count, which is the number of extant `Gc`s to this allocation.
    /// If the strong count is zero, a value contained in the allocation may be dropped, but the
    /// allocation itself must still be valid.
    strong: usize,
    /// The "weak" count, which is the number of references to this allocation stored in to-collect
    /// buffers by the collection algorithm.
    /// If the weak count is zero, the allocation may be destroyed.
    weak: usize,
}

#[repr(C)]
/// The backing allocation for a [`Gc`].
struct GcBox<T>
where
    T: Collectable + Sync + ?Sized,
{
    /// The reference count for this allocation.
    ///
    /// We use a mutex instead of an atomic here for algorithmic reasons - it allows us to achieve
    /// mutual exclusion when searching for cycles, preventing a malicious thread from fooling us
    /// into believing that an allocation is unreachable (therefore, preventing us from
    /// accidentally UAFing)
    ref_count: Mutex<RefCounts>,
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
                ref_count: Mutex::new(RefCounts { strong: 1, weak: 0 }),
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
        unsafe {
            let mut ref_count_guard = self.ptr.as_ref().ref_count.lock().unwrap();
            ref_count_guard.strong += 1;
            DUMPSTER.notify_created_gc();
            // If we can clone a Gc pointing to this allocation, it must be accessible
            DUMPSTER.mark_clean(self.ptr, &mut ref_count_guard);
        }
        Gc { ptr: self.ptr }
    }
}

impl<T> Drop for Gc<T>
where
    T: Collectable + Sync + ?Sized,
{
    fn drop(&mut self) {
        if !CLEANING.with(Cell::get) {
            unsafe {
                // this block ensures that `count_handle` is dropped before `notify_dropped_gc`
                let mut count_handle = self.ptr.as_ref().ref_count.lock().unwrap();
                match count_handle.strong {
                    0 => (),
                    1 => {
                        count_handle.strong = 0;

                        DUMPSTER.mark_clean(self.ptr, &mut count_handle);
                        if count_handle.weak == 0 {
                            drop(count_handle); // must drop handle before dropping the mutex

                            let layout = Layout::for_value(self.ptr.as_ref());
                            drop_in_place(addr_of_mut!(self.ptr.as_mut().value));
                            dealloc(self.ptr.as_ptr().cast(), layout);
                        }
                    }
                    n => {
                        count_handle.strong = n - 1;
                        DUMPSTER.mark_dirty(self.ptr, &mut count_handle);
                        drop(count_handle);
                    }
                }
                DUMPSTER.notify_dropped_gc();
            }
        }
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

impl<T, U> CoerceUnsized<Gc<U>> for Gc<T>
where
    T: Unsize<U> + Collectable + Sync + ?Sized,
    U: Collectable + Sync + ?Sized,
{
}
