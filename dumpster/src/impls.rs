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

use std::cell::RefCell;

use crate::Gc;

use super::{AllocationId, Collectable, RefGraph};

unsafe impl<T: Collectable + ?Sized> Collectable for Gc<T> {
    fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
        let next_id = Gc::id(self);
        ref_graph.add_ref(self_ref, next_id);
        ref_graph.add_allocation(next_id, unsafe { &self.ptr.as_ref().value });
    }
}

unsafe impl<'a, T> Collectable for &'a T {
    fn add_to_ref_graph(&self, _: AllocationId, _: &mut RefGraph) {}
}

unsafe impl<T: Collectable + ?Sized> Collectable for RefCell<T> {
    fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
        self.borrow().add_to_ref_graph(self_ref, ref_graph);
    }
}

unsafe impl<T: Collectable> Collectable for Option<T> {
    fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
        if let Some(v) = self {
            v.add_to_ref_graph(self_ref, ref_graph);
        }
    }
}

unsafe impl<T: Collectable> Collectable for Vec<T> {
    fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
        self.iter()
            .for_each(|elem| elem.add_to_ref_graph(self_ref, ref_graph));
    }
}

/// Implement [`Collectable`] for a trivially-collected type which contains no  [`Gc`]s in its
/// fields.
macro_rules! collectable_trivial_impl {
    ($x: ty) => {
        unsafe impl Collectable for $x {
            #[inline]
            fn add_to_ref_graph(&self, _: AllocationId, _: &mut RefGraph) {}
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
