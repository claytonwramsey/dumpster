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

use std::{marker::PhantomData, ptr::{NonNull, drop_in_place, addr_of_mut}, sync::Mutex, alloc::{dealloc, Layout}};

use crate::Collectable;

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

/// Collect all unreachable [`Gc`]s on the heap.
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
                let mut count_handle = ptr.as_ref().ref_count.lock().unwrap();
                match *count_handle {
                    0 => (), // value already being dropped
                    1 => {
                        *count_handle = 0;
                        drop(count_handle); // must drop handle before dropping the mutex
                        drop_in_place(addr_of_mut!(ptr.as_mut().value));
                        dealloc(ptr.as_ptr().cast(), Layout::for_value(ptr.as_ref()));
                    },
                    n => {
                        *count_handle = n - 1;
                        // todo!();
                    }
                }
            }
        }
    }
}