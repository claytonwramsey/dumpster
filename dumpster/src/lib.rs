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

#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]

use std::{
    alloc::{dealloc, Layout},
    cell::Cell,
    collections::{HashMap, HashSet},
    marker::PhantomData,
    ops::Deref,
    ptr::{self, NonNull},
};

#[cfg(test)]
mod tests;

mod impls;

/// The trait that any garbage-collectable data must implement.
///
/// This trait should usually be implemented by using `#[derive(Collectable)]`, using the macro from
/// the crate `dumpster_derive`.
/// Only data structures using raw pointers or other magic should manually implement `Collectable`.
///
/// # Safety
///
/// A collectable data type must call `add_to_ref_graph` on all values which it owns with the same
/// arguments that were passed to it.
/// Additionally, when a collectable type is dropped (via its implementation in [`Drop`]), it must
/// not access any of the data behind its [`Gc`] fields, because those values may have already been
/// dropped.
///
/// # Examples
///
/// A data structure which contains no `Gc`s is quite simple:
///
/// ```
/// use dumpster::{AllocationId, Collectable, RefGraph};
///
/// struct Foo;
///
/// unsafe impl Collectable for Foo {
///     fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {}
///     unsafe fn destroy_gcs(&mut self) {}
/// }
///
/// # use dumpster::Gc;
/// # let gc1 = Gc::new(Foo);
/// # drop(gc1);
/// ```
///
/// If a field of your structure is a `Gc`, it should delegate to that field as such:
///
/// ```
/// use dumpster::{AllocationId, Collectable, RefGraph};
///
/// struct Bar(Gc<()>);
///
/// unsafe impl Collectable for Bar {
///     fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph) {
///         // `self.0` is a field, so we delegate down to it.
///         self.0.add_to_ref_graph(self_ref, ref_graph);
///     }
///
///     unsafe fn destroy_gcs(&mut self) {
///         // likewise, delegate down for `destroy_gcs`
///         self.0.destroy_gcs();
///     }
/// }
/// # use dumpster::Gc;
/// # let gc1 = Gc::new(Bar(Gc::new(())));
/// # drop(gc1);
/// ```
pub unsafe trait Collectable {
    /// Construct a reference graph by adding all references as edges to `ref_graph`.
    /// Downstream implementors need not do anything other than delegate to all fields of this data
    /// structure.
    fn add_to_ref_graph(&self, self_ref: AllocationId, ref_graph: &mut RefGraph);

    /// Destroy all `Gc` pointers owned by this value without calling `Drop`.
    ///
    /// This function may only be called just before this value is dropped.
    /// Implementors should simply delegate to calling `destroy_gcs` on all of its fields.
    ///
    /// After this function has been called on a [`Gc`], it is rendered unusable.
    ///
    /// # Safety
    ///
    /// After `destroy_gcs` is called on this value, any `Gc` owned by this data structure may not
    /// be dereferenced.
    ///
    /// `destroy_gcs` should only be called by the `dumpster` crate (i.e. not by any downstream
    /// consumer).
    unsafe fn destroy_gcs(&mut self);
}

/// A garbage-collected pointer.
pub struct Gc<T: Collectable + ?Sized> {
    /// A pointer to the heap allocation containing the data under concern.
    /// The pointee box should never be mutated.
    ptr: Option<NonNull<GcBox<T>>>,
    /// Phantom data to ensure correct lifetime analysis.
    _phantom: PhantomData<T>,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A unique identifier for an allocated garbage-collected block.
///
/// It contains a pointer to the reference count of the allocation.
pub struct AllocationId(NonNull<Cell<usize>>);

/// A reference graph of garbage-collected values.
///
/// This graph is built during cycle detection to find allocations which are unreachable and can
/// be freed.
pub struct RefGraph {
    /// A map from each allocation to all allocations which we could find that referenced it.
    parent_map: HashMap<AllocationId, Vec<AllocationId>>,
    /// The set of allocations that have already been visited while searching for cycles.
    visited: HashSet<AllocationId>,
}

impl<T: Collectable + ?Sized> Gc<T> {
    /// Construct a new garbage-collected allocation, with `value` as its value.
    pub fn new(value: T) -> Gc<T>
    where
        T: Sized,
    {
        Gc {
            ptr: Some(NonNull::from(Box::leak(Box::new(GcBox {
                ref_count: Cell::new(1),
                value,
            })))),
            _phantom: PhantomData,
        }
    }

    #[must_use]
    /// Get a unique ID for the data pointed to by this garbage-collected pointer.
    ///
    /// This is used by `dumpster` directly for generating a reference graph.
    fn id(gc: &Gc<T>) -> AllocationId {
        unsafe { gc.ptr.unwrap().as_ref().id() }
    }
}

impl<T: Collectable + ?Sized> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.ptr.unwrap().as_ref().value }
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
        Self {
            ptr: self.ptr.clone(),
            _phantom: PhantomData,
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
            let box_ref = unsafe { ptr.as_ref() };
            let old_ref_count = box_ref.ref_count.get();
            if old_ref_count == 0 {
                return;
            }
            box_ref.ref_count.set(old_ref_count - 1);
            if old_ref_count == 1 || box_ref.is_orphaned() {
                box_ref.ref_count.set(0);
                unsafe {
                    ptr::drop_in_place(ptr.as_mut());
                    dealloc(ptr.as_ptr().cast::<u8>(), Layout::for_value(ptr.as_ref()));
                };
            }
        }
    }
}

impl<T: Collectable + ?Sized> GcBox<T> {
    /// Get a unique ID for this allocation.
    fn id(&self) -> AllocationId {
        AllocationId(NonNull::from(&self.ref_count))
    }

    /// Determine whether this `GcBox` exists only because it is part of an orphaned cycle.
    fn is_orphaned(&self) -> bool {
        fn all_accounted_ancestors(
            id: AllocationId,
            parent_map: &mut HashMap<AllocationId, Vec<AllocationId>>,
        ) -> bool {
            match parent_map.remove(&id) {
                // we have already visited this node and verified its ancestors are accounted for
                None => true,
                Some(v) => {
                    if v.len() != unsafe { id.0.as_ref() }.get() {
                        // mismatched ref count and number of found parents
                        return false;
                    }
                    for next_parent in v {
                        if !all_accounted_ancestors(next_parent, parent_map) {
                            return false;
                        }
                    }
                    true
                }
            }
        }

        let mut ref_graph = RefGraph {
            parent_map: HashMap::new(),
            visited: HashSet::new(),
        };
        ref_graph.add_allocation(self.id(), &self.value);

        all_accounted_ancestors(self.id(), &mut ref_graph.parent_map)
    }
}

impl RefGraph {
    fn add_ref(&mut self, from: AllocationId, to: AllocationId) {
        self.parent_map.entry(to).or_insert(Vec::new()).push(from);
        self.visited.insert(from);
    }

    fn add_allocation<T: Collectable + ?Sized>(&mut self, id: AllocationId, value: &T) {
        if self.mark_visited(id) {
            return;
        }
        value.add_to_ref_graph(id, self);
    }

    fn mark_visited(&mut self, allocation: AllocationId) -> bool {
        let already_visited = !self.visited.insert(allocation);
        self.parent_map.entry(allocation).or_insert(Vec::new());
        already_visited
    }
}
