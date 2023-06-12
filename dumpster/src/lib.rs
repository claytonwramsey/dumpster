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
/// This trait should usually be implemented by using `#[derive(Collectable)]`.
/// Only data structures using raw pointers or other magic should manually implement `Collectable`.
///
/// # Safety
///
/// A collectable data type must correctly be able to add itself and its references to the reference
/// graph.
/// It must also make sure to check whether it has already been visited to prevent infinite loops.
/// Lastly, when a collectable type is dropped (via its implementation in [`Drop`]), it must not
/// access any of the data behind its [`Gc`] fields, because those values may have already been
/// dropped.
pub unsafe trait Collectable {
    fn add_to_ref_graph<const IS_ALLOCATION: bool>(
        &self,
        self_ref: AllocationId,
        ref_graph: &mut RefGraph,
    );
}

/// A garbage-collected pointer.
pub struct Gc<T: Collectable + ?Sized> {
    /// A pointer to the heap allocation containing the data under concern.
    /// The pointee box should never be mutated.
    ptr: NonNull<GcBox<T>>,
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
///
/// # Examples
///
/// ```
/// use dumpster::{AllocationId, Gc};
///
/// let gc1 = Gc::new(1);
/// let gc2 = Gc::clone(&gc1);
/// let gc3 = Gc::new(1);
///
/// let id1: AllocationId = Gc::id(&gc1);
/// let id2: AllocationId = Gc::id(&gc2);
/// let id3: AllocationId = Gc::id(&gc3);
///
/// assert_eq!(id1, id2);
/// assert!(id1 != id3);
/// ```
pub struct AllocationId(NonNull<Cell<usize>>);

/// A reference graph of garbage-collected values.
///
/// This graph is built during cycle detection to find allocations which are unreachable and can
/// be freed.
pub struct RefGraph {
    /// A map from each allocation to all allocations which we could find that referenced it.
    parent_map: HashMap<AllocationId, Vec<AllocationId>>,
    visited: HashSet<AllocationId>,
}

impl<T: Collectable + ?Sized> Gc<T> {
    /// Construct a new garbage-collected allocation, with `value` as its value.
    pub fn new(value: T) -> Gc<T>
    where
        T: Sized,
    {
        Gc {
            ptr: NonNull::from(Box::leak(Box::new(GcBox {
                ref_count: Cell::new(1),
                value,
            }))),
            _phantom: PhantomData,
        }
    }

    /// Get a unique ID for the data pointed to by this garbage-collected pointer.
    ///
    /// This is used especially for the implementation of [`Collectable::add_to_parent_map`].
    pub fn id(gc: &Gc<T>) -> AllocationId {
        unsafe { gc.ptr.as_ref().id() }
    }
}

impl<T: Collectable + ?Sized> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.ptr.as_ref().value }
    }
}

impl<T: Collectable + ?Sized> Clone for Gc<T> {
    #[allow(clippy::clone_on_copy)]
    /// Create a duplicate reference to the same data pointed to by `self`.
    /// This does not duplicate the data.
    fn clone(&self) -> Self {
        unsafe {
            let box_ref = self.ptr.as_ref();
            box_ref.ref_count.set(box_ref.ref_count.get() + 1);
        }
        Self {
            ptr: self.ptr.clone(),
            _phantom: self._phantom.clone(),
        }
    }
}

impl<T: Collectable + ?Sized> Drop for Gc<T> {
    /// Destroy this garbage-collected pointer.
    ///
    /// If this is the last reference which can reach the pointed-to data,
    fn drop(&mut self) {
        let box_ref = unsafe { self.ptr.as_ref() };
        println!("drop a gc with ref count {}", box_ref.ref_count.get());
        let old_ref_count = box_ref.ref_count.get();
        if old_ref_count == 0 {
            return;
        }
        box_ref.ref_count.set(old_ref_count - 1);
        if old_ref_count == 1 || box_ref.is_orphaned() {
            box_ref.ref_count.set(0);
            unsafe {
                ptr::drop_in_place(self.ptr.as_mut());
                dealloc(
                    self.ptr.as_ptr() as *mut u8,
                    Layout::for_value(self.ptr.as_ref()),
                )
            };
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
        let mut ref_graph = RefGraph {
            parent_map: HashMap::new(),
            visited: HashSet::new(),
        };
        self.value
            .add_to_ref_graph::<true>(self.id(), &mut ref_graph);

        println!("final ref graph: {:?}", ref_graph.parent_map);

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

        all_accounted_ancestors(self.id(), &mut ref_graph.parent_map)
    }
}

impl RefGraph {
    pub fn add_ref(&mut self, pointer: AllocationId, pointee: AllocationId) {
        self.parent_map
            .entry(pointee)
            .or_insert(Vec::new())
            .push(pointer);
        self.visited.insert(pointer);
    }

    pub fn mark_visited(&mut self, allocation: AllocationId) -> bool {
        let already_visited = !self.visited.insert(allocation);
        self.parent_map.entry(allocation).or_insert(Vec::new());
        already_visited
    }
}
