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

//! Thread-local garbage collection.

use std::{
    alloc::{dealloc, Layout},
    borrow::Borrow,
    cell::Cell,
    ops::Deref,
    ptr::{addr_of, addr_of_mut, drop_in_place, NonNull},
};

use crate::{Collectable, Destroyer, Visitor};

use self::collect::{Dumpster, DUMPSTER};

mod collect;
#[cfg(test)]
mod tests;

#[derive(Debug)]
/// A garbage-collected pointer.
///
/// This garbage-collected pointer may be used for data which is not safe to share across threads
/// (such as a [`RefCell`]).
/// It can also be used for variably sized data.
///
/// # Examples
///
/// ```
/// use dumpster::unsync::Gc;
///
/// let x: Gc<u8> = Gc::new(3);
///
/// println!("{}", *x); // prints '3'
///                     // x is then freed automatically!
/// ```
pub struct Gc<T: Collectable + ?Sized + 'static> {
    /// A pointer to the heap allocation containing the data under concern.
    /// The pointee box should never be mutated.
    ptr: Option<NonNull<GcBox<T>>>,
}

/// Collect all existing unreachable allocations.
///
/// This only collects the allocations local to the caller's thread.
pub fn collect() {
    DUMPSTER.with(Dumpster::collect_all);
}

#[repr(C)]
/// The underlying heap allocation for a [`Gc`].
struct GcBox<T: Collectable + ?Sized> {
    /// The number of extant references to this garbage-collected data.
    /// If the stored reference count is zero, then this value is a "zombie" - in the process of
    /// being dropped - and should not be dropped again.
    ref_count: Cell<usize>,
    /// The stored value inside this garbage-collected box.
    value: T,
}

impl<T: Collectable + ?Sized> Gc<T> {
    /// Construct a new garbage-collected allocation, with `value` as its value.
    pub fn new(value: T) -> Gc<T>
    where
        T: Sized,
    {
        DUMPSTER.with(Dumpster::notify_created_gc);
        Gc {
            ptr: Some(NonNull::from(Box::leak(Box::new(GcBox {
                ref_count: Cell::new(1),
                value,
            })))),
        }
    }
}

impl<T: Collectable + ?Sized> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            &self
                .ptr
                .expect("Dereferenced Gc during Drop")
                .as_ref()
                .value
        }
    }
}

impl<T: Collectable + ?Sized> Clone for Gc<T> {
    #[allow(clippy::clone_on_copy)]
    /// Create a duplicate reference to the same data pointed to by `self`.
    /// This does not duplicate the data.
    fn clone(&self) -> Self {
        unsafe {
            let box_ref = self.ptr.unwrap().as_ref();
            box_ref.ref_count.set(box_ref.ref_count.get() + 1);
        }
        DUMPSTER.with(|d| {
            d.notify_created_gc();
            d.mark_cleaned(self.ptr.unwrap());
        });
        Self {
            ptr: self.ptr.clone(),
        }
    }
}

impl<T: Collectable + ?Sized> Drop for Gc<T> {
    /// Destroy this garbage-collected pointer.
    ///
    /// If this is the last reference which can reach the pointed-to data, the allocation that it
    /// points to will be destroyed.
    fn drop(&mut self) {
        if let Some(mut ptr) = self.ptr {
            DUMPSTER.with(|d| {
                unsafe {
                    let box_ref = ptr.as_ref();
                    match box_ref.ref_count.get() {
                        0 => (), // allocation is already being destroyed
                        1 => {
                            d.mark_cleaned(ptr);
                            // this was the last reference, drop unconditionally
                            drop_in_place(addr_of_mut!(ptr.as_mut().value));
                            // note: `box_ref` is no longer usable
                            dealloc(ptr.as_ptr().cast::<u8>(), Layout::for_value(ptr.as_ref()));
                        }
                        n => {
                            // decrement the ref count - but another reference to this data still
                            // lives
                            box_ref.ref_count.set(n - 1);
                            // remaining references could be a cycle - therefore, mark it as dirty
                            // so we can check later
                            d.mark_dirty(ptr);
                        }
                    }
                    // Notify that a GC has been dropped, potentially triggering a sweep
                    d.notify_dropped_gc();
                }
            });
        }
    }
}

unsafe impl<T: Collectable + ?Sized> Collectable for Gc<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        visitor.visit_unsync(self);
        Ok(())
    }

    unsafe fn destroy_gcs<D: Destroyer>(&mut self, visitor: &mut D) {
        visitor.visit_unsync(self);
    }
}

impl<T: Collectable + ?Sized> AsRef<T> for Gc<T> {
    fn as_ref(&self) -> &T {
        unsafe { addr_of!(self.ptr.unwrap().as_ref().value).as_ref().unwrap() }
    }
}

impl<T: Collectable + ?Sized> Borrow<T> for Gc<T> {
    fn borrow(&self) -> &T {
        self.as_ref()
    }
}

impl<T: Collectable + Default> Default for Gc<T> {
    fn default() -> Self {
        Gc::new(T::default())
    }
}
