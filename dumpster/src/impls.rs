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

//! Implementations of [`Collectable`] for common data types.

use std::{
    cell::RefCell,
    collections::{BinaryHeap, HashSet, LinkedList, VecDeque},
};

use crate::Gc;

use super::{AllocationId, Collectable, RefGraph};

unsafe impl<T: Collectable + ?Sized> Collectable for Gc<T> {
    fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
        let next_id = Gc::id(self);
        ref_graph.add_ref(self_ref, next_id);
        ref_graph.add_allocation(next_id, unsafe { &self.ptr.unwrap().as_ref().value });
    }

    unsafe fn destroy_gcs(&mut self) {
        // do not delegate to pointee
        self.ptr = None;
    }
}

unsafe impl<'a, T> Collectable for &'a T {
    fn add_to_ref_graph(&self, _: AllocationId, _: &mut RefGraph) {}
    unsafe fn destroy_gcs(&mut self) {}
}

unsafe impl<T: Collectable + ?Sized> Collectable for RefCell<T> {
    fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
        self.borrow().add_to_ref_graph(self_ref, ref_graph);
    }

    unsafe fn destroy_gcs(&mut self) {
        self.borrow_mut().destroy_gcs();
    }
}

unsafe impl<T: Collectable> Collectable for Option<T> {
    fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
        if let Some(v) = self {
            v.add_to_ref_graph(self_ref, ref_graph);
        }
    }

    unsafe fn destroy_gcs(&mut self) {
        if let Some(x) = self.as_mut() {
            x.destroy_gcs();
        }
    }
}

/// Implement [`Collectable`] for a collection data structure which has some method `iter()` that
/// iterates over all elements of the data structure and `iter_mut()` which does the same over
/// mutable references.
macro_rules! collectable_collection_impl {
    ($x: ty) => {
        unsafe impl<T: Collectable> Collectable for $x {
            #[inline]
            fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
                self.iter()
                    .for_each(|elem| elem.add_to_ref_graph(self_ref, ref_graph));
            }

            #[inline]
            unsafe fn destroy_gcs(&mut self) {
                self.iter_mut().for_each(|x| x.destroy_gcs());
            }
        }
    };
}

collectable_collection_impl!(Vec<T>);
collectable_collection_impl!(VecDeque<T>);
collectable_collection_impl!(LinkedList<T>);

/// Implement [`Collectable`] for a set-like data structure which freezes its elements.
macro_rules! collectable_set_impl {
    ($x: ty) => {
        unsafe impl<T: Collectable> Collectable for $x {
            #[inline]
            fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
                self.iter()
                    .for_each(|elem| elem.add_to_ref_graph(self_ref, ref_graph));
            }

            #[inline]
            unsafe fn destroy_gcs(&mut self) {
                self.drain().for_each(|mut x| x.destroy_gcs());
            }
        }
    };
}

collectable_set_impl!(HashSet<T>);
collectable_set_impl!(BinaryHeap<T>);
// collectable_set_impl!(BTreeSet<T>); // awaiting stabilization of `drain` on `BTreeSet`

/// Implement [`Collectable`] for a trivially-collected type which contains no  [`Gc`]s in its
/// fields.
macro_rules! collectable_trivial_impl {
    ($x: ty) => {
        unsafe impl Collectable for $x {
            #[inline]
            fn add_to_ref_graph(&self, _: AllocationId, _: &mut RefGraph) {}
            #[inline]
            unsafe fn destroy_gcs(&mut self) {}
        }
    };
}

collectable_trivial_impl!(());

collectable_trivial_impl!(u8);
collectable_trivial_impl!(u16);
collectable_trivial_impl!(u32);
collectable_trivial_impl!(u64);
collectable_trivial_impl!(u128);
collectable_trivial_impl!(usize);

collectable_trivial_impl!(i8);
collectable_trivial_impl!(i16);
collectable_trivial_impl!(i32);
collectable_trivial_impl!(i64);
collectable_trivial_impl!(i128);
collectable_trivial_impl!(isize);

collectable_trivial_impl!(f32);
collectable_trivial_impl!(f64);
