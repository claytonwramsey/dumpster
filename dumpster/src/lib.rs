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
    collections::{hash_map::Entry, HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
    num::NonZeroUsize,
    ops::Deref,
    ptr::{drop_in_place, NonNull},
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
///     fn add_to_ref_graph(&self, _: &mut RefGraph) {}
///     fn sweep(&self, _: bool, _: &mut RefGraph) {}
///     unsafe fn destroy_gcs(&mut self, _: &mut RefGraph) {}
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
///     fn add_to_ref_graph(&self, ref_graph: &mut RefGraph) {
///         // `self.0` is a field, so we delegate down to it.
///         self.0.add_to_ref_graph(ref_graph);
///     }
///
///     fn sweep(&self, is_accessible: bool, ref_graph: &mut RefGraph) {
///         self.0.sweep(is_accessible, ref_graph);
///     }
///
///     unsafe fn destroy_gcs(&mut self, ref_graph: &mut RefGraph) {
///         // likewise, delegate down for `destroy_gcs`
///         self.0.destroy_gcs(ref_graph);
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
    fn add_to_ref_graph(&self, ref_graph: &mut RefGraph);

    /// Perform the sweep step in a mark-sweep garbage collection.
    /// User implementations need not do anything except delegate to their fields.
    fn sweep(&self, is_accessible: bool, ref_graph: &mut RefGraph);

    /// Destroy all `Gc` pointers owned by this value without calling `Drop`.
    ///
    /// This function may only be called just before this value is dropped.
    /// Implementors should simply delegate to calling `destroy_gcs` on all of its fields.
    ///
    /// After this function has been called on a [`Gc`], it will be rendered unusable.
    ///
    /// # Safety
    ///
    /// After `destroy_gcs` is called on this value, any `Gc` owned by this data structure may not
    /// be dereferenced.
    ///
    /// `destroy_gcs` should only be called by the `dumpster` crate (i.e. not by any downstream
    /// consumer).
    unsafe fn destroy_gcs(&mut self, ref_graph: &mut RefGraph);
}

#[derive(Debug)]
/// A garbage-collected pointer.
/// 
/// # Examples
/// 
/// ```
/// use dumpster::Gc;
/// 
/// let x: Gc<u8> = Gc::new(3);
/// 
/// println!("{}", *x); // prints '3'
/// // x is then freed automatically!
/// ```
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
struct AllocationId(NonNull<Cell<usize>>);

/// A reference graph of garbage-collected values.
///
/// This graph is built during cycle detection to find allocations which are unreachable and can
/// be freed.
pub struct RefGraph {
    /// A map from each allocation to what is known about it.
    allocations: HashMap<AllocationId, AllocationInfo>,
    /// The set of allocations that have already been visited while searching for cycles.
    visited: HashSet<AllocationId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// The set of states that we can know about an allocation's reachability.
enum AllocationInfo {
    /// The allocation has been proven reachable and is not safe to free.
    Reachable,
    /// The allocation's reachability is unknown.
    /// Field 0 of this case is the number of located references to this allocation.
    Unknown(NonZeroUsize),
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
        unsafe { &self.ptr.expect("Dereferenced Gc during Drop").as_ref().value }
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
            unsafe {
                let box_ref = ptr.as_ref();
                match box_ref.ref_count.get() {
                    0 => (), // allocation is already being destroyed
                    1 => {
                        // this was the last reference, drop unconditionally
                        drop_in_place(ptr.as_mut());
                        // note: `box_ref` is no longer usable
                        dealloc(ptr.as_ptr().cast::<u8>(), Layout::for_value(ptr.as_ref()));
                    }
                    n => {
                        // search through to see if we need to deallocate anything inaccessible
                        box_ref.ref_count.set(n - 1);

                        // build the reference graph
                        let mut ref_graph = RefGraph {
                            allocations: HashMap::new(),
                            visited: HashSet::new(),
                        };
                        ref_graph.mark_visited(box_ref.id());
                        box_ref.value.add_to_ref_graph(&mut ref_graph);

                        // `ref_graph` now has the full internal reference graph.
                        // perform a mark-sweep to detect all unreachable allocations.
                        ref_graph.visited.clear();
                        ref_graph.mark_visited(box_ref.id());
                        box_ref.value.sweep(false, &mut ref_graph);

                        // `ref_graph` has now found which allocations are reachable and which are
                        // not. Destroy the GCs.
                        if matches!(
                            ref_graph.allocations.get(&Gc::id(self)),
                            Some(AllocationInfo::Unknown(_))
                        ) {
                            self.ptr = None;
                            box_ref.ref_count.set(0);
                            ref_graph.visited.clear();
                            ref_graph.mark_visited(box_ref.id());
                            ptr.as_mut().value.destroy_gcs(&mut ref_graph);
                            drop_in_place(ptr.as_mut());
                            dealloc(ptr.as_ptr().cast::<u8>(), Layout::for_value(ptr.as_ref()));
                        }
                    }
                }
            }
        }
    }
}

unsafe impl<T: Collectable + ?Sized> Collectable for Gc<T> {
    fn add_to_ref_graph(&self, ref_graph: &mut RefGraph) {
        let next_id = Gc::id(self);
        ref_graph.add_ref(next_id);
        if !ref_graph.mark_visited(next_id) {
            let deref: &T = self;
            deref.add_to_ref_graph(ref_graph);
        }
    }

    fn sweep(&self, is_accessible: bool, ref_graph: &mut RefGraph) {
        let next_id = Gc::id(self);
        let deref: &T = self;
        if let AllocationInfo::Unknown(n_refs_found) = ref_graph.allocations[&next_id] {
            if is_accessible
                || usize::from(n_refs_found) < unsafe { self.ptr.unwrap().as_ref().ref_count.get() }
            {
                // we proved that the pointed-to allocation was reachable!
                ref_graph
                    .allocations
                    .insert(next_id, AllocationInfo::Reachable);
                // ignore visited qualifier because this is a change of state
                deref.sweep(true, ref_graph);
            } else if !ref_graph.mark_visited(next_id) {
                // unable to prove this allocation was reachable - keep looking
                deref.sweep(false, ref_graph);
            }
        }
    }

    unsafe fn destroy_gcs(&mut self, ref_graph: &mut RefGraph) {
        if let Some(mut ptr) = self.ptr {
            let next_id = Gc::id(self);
            let old_ref_count = ptr.as_ref().ref_count.get();
            self.ptr = None;
            if !ref_graph.mark_visited(next_id)
                && !matches!(ref_graph.allocations[&next_id], AllocationInfo::Reachable)
                && old_ref_count != 0
            {
                ptr.as_ref().ref_count.set(0);
                ptr.as_mut().value.destroy_gcs(ref_graph);
                drop_in_place(ptr.as_mut());
                dealloc(ptr.as_ptr().cast::<u8>(), Layout::for_value(ptr.as_ref()));
            }
        }
    }
}

impl<T: Collectable + ?Sized> GcBox<T> {
    /// Get a unique ID for this allocation.
    fn id(&self) -> AllocationId {
        AllocationId(NonNull::from(&self.ref_count))
    }
}

impl RefGraph {
    fn add_ref(&mut self, to: AllocationId) {
        match self.allocations.entry(to) {
            Entry::Occupied(ref mut o) => {
                let AllocationInfo::Unknown(ref mut count) = o.get_mut() else {unreachable!();};
                *count = count.saturating_add(1);
            }
            Entry::Vacant(v) => {
                v.insert(AllocationInfo::Unknown(NonZeroUsize::new(1).unwrap()));
            }
        }
    }

    /// Mark this allocation as having been visited.
    /// Returns `true` if the allocation has been visited before, and `false` if not.
    fn mark_visited(&mut self, allocation: AllocationId) -> bool {
        !self.visited.insert(allocation)
    }
}
