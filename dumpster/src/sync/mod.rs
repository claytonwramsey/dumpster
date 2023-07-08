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
    marker::PhantomData,
    ops::Deref,
    ptr::{addr_of_mut, drop_in_place, NonNull},
    sync::Mutex,
};

use crate::{Collectable, Destroyer, Visitor};

use self::collect::DUMPSTER;

/// A thread-safe garbage-collected pointer.
pub struct Gc<T>
where
    T: Collectable + Sync + ?Sized,
{
    /// A pointer to the heap allocation containing the data under concern.
    /// The pointee box should never be mutated.
    ptr: Option<NonNull<GcBox<T>>>,
    /// Phantom data to ensure correct lifetime analysis.
    _phantom: PhantomData<T>,
}

#[repr(C)]
struct GcBox<T>
where
    T: Collectable + Sync + ?Sized,
{
    ref_count: Mutex<usize>,
    value: T,
}

unsafe impl<T> Send for Gc<T> where T: Collectable + Sync + ?Sized {}
unsafe impl<T> Sync for Gc<T> where T: Collectable + Sync + ?Sized {}

/// Collect all unreachable thread-safe [`Gc`]s on the heap.
pub fn collect() {
    DUMPSTER.collect_all();
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
            ptr: Some(NonNull::from(Box::leak(Box::new(GcBox {
                ref_count: Mutex::new(1),
                value,
            })))),
            _phantom: PhantomData,
        }
    }
}

impl<T> Clone for Gc<T>
where
    T: Collectable + Sync + ?Sized,
{
    fn clone(&self) -> Gc<T> {
        unsafe {
            *self.ptr.unwrap().as_ref().ref_count.lock().unwrap() += 1;
        }
        Gc {
            ptr: self.ptr,
            _phantom: PhantomData,
        }
    }
}

impl<T> Drop for Gc<T>
where
    T: Collectable + Sync + ?Sized,
{
    fn drop(&mut self) {
        unsafe {
            if let Some(mut ptr) = self.ptr {
                {
                    // this block ensures that `count_handle` is dropped before `notify_dropped_gc`
                    let mut count_handle = ptr.as_ref().ref_count.lock().unwrap();
                    match *count_handle {
                        0 => (), // value already being dropped
                        1 => {
                            *count_handle = 0;
                            drop(count_handle); // must drop handle before dropping the mutex

                            DUMPSTER.mark_clean(ptr);

                            drop_in_place(addr_of_mut!(ptr.as_mut().value));
                            dealloc(ptr.as_ptr().cast(), Layout::for_value(ptr.as_ref()));
                        }
                        n => {
                            *count_handle = n - 1;
                            DUMPSTER.mark_dirty(ptr);
                        }
                    }
                }
                DUMPSTER.notify_dropped_gc();
            }
        }
    }
}

unsafe impl<T: Collectable + Sync + ?Sized> Collectable for Gc<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) {
        visitor.visit_sync(self);
    }

    unsafe fn destroy_gcs<D: Destroyer>(&mut self, destroyer: &mut D) {
        destroyer.visit_sync(self);
    }
}

impl<T: Collectable + Sync + ?Sized> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.ptr.unwrap().as_ref().value }
    }
}
