//! Implementations of [`Collectable`] for common data types.

use std::cell::RefCell;

use crate::Gc;

use super::{AllocationId, Collectable, RefGraph};

unsafe impl<T: Collectable + ?Sized> Collectable for Gc<T> {
    fn add_to_ref_graph<const IS_ALLOCATION: bool>(
        &self,
        self_ref: AllocationId,
        ref_graph: &mut RefGraph,
    ) {
        if IS_ALLOCATION && ref_graph.mark_visited(self_ref) {
            return;
        }
        let next_id = Gc::id(self);
        ref_graph.add_ref(self_ref, next_id);
        unsafe {
            self.ptr
                .as_ref()
                .value
                .add_to_ref_graph::<true>(next_id, ref_graph);
        }
    }
}

unsafe impl<T: Collectable + ?Sized> Collectable for RefCell<T> {
    fn add_to_ref_graph<const IS_ALLOCATION: bool>(
        &self,
        self_ref: AllocationId,
        ref_graph: &mut RefGraph,
    ) {
        if IS_ALLOCATION && ref_graph.mark_visited(self_ref) {
            return;
        }
        self.borrow().add_to_ref_graph::<false>(self_ref, ref_graph);
    }
}

unsafe impl<T: Collectable> Collectable for Option<T> {
    fn add_to_ref_graph<const IS_ALLOCATION: bool>(
        &self,
        self_ref: AllocationId,
        ref_graph: &mut RefGraph,
    ) {
        if IS_ALLOCATION && ref_graph.mark_visited(self_ref) {
            return;
        }
        if let Some(v) = self {
            v.add_to_ref_graph::<false>(self_ref, ref_graph);
        }
    }
}

/// Implement [`Collectable`] for a trivially-collected type which contains no  [`Gc`]s in its
/// fields.
macro_rules! collectable_trivial_impl {
    ($x: ty) => {
        unsafe impl Collectable for $x {
            #[inline]
            fn add_to_ref_graph<const IS_ALLOCATION: bool>(
                &self,
                id: AllocationId,
                ref_graph: &mut RefGraph,
            ) {
                if IS_ALLOCATION {
                    ref_graph.mark_visited(id);
                }
            }
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
