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

//! Implementations of the single-threaded garbage-collection logic.

use std::{
    alloc::{dealloc, Layout},
    cell::{Cell, RefCell},
    collections::{hash_map::Entry, HashMap, HashSet},
    num::NonZeroUsize,
    ops::Deref,
    ptr::{drop_in_place, NonNull},
};

use crate::{unsync::Gc, Collectable, ErasedPtr, Visitor};

use super::GcBox;

thread_local! {
    /// The global collection of allocation information for this thread.
    pub(super) static DUMPSTER: Dumpster = Dumpster {
        to_collect: RefCell::new(HashMap::new()),
        n_ref_drops: Cell::new(0),
        n_refs_living: Cell::new(0),
        collecting: Cell::new(false),
    };
}

/// A dumpster is a collection of all the garbage that may or may not need to be cleaned up.
/// It also contains information relevant to when a sweep should be triggered.
pub(super) struct Dumpster {
    /// A map from allocation IDs for allocations which may need to be collected to pointers to
    /// their allocations.
    to_collect: RefCell<HashMap<AllocationId, Cleanup>>,
    /// The number of times a reference has been dropped since the last collection was triggered.
    n_ref_drops: Cell<usize>,
    /// The number of references that currently exist in the entire heap and stack.
    n_refs_living: Cell<usize>,
    /// Whether the current thread is running a cleanup process.
    collecting: Cell<bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A unique identifier for an allocated garbage-collected block.
///
/// It contains a pointer to the reference count of the allocation.
struct AllocationId(pub NonNull<Cell<NonZeroUsize>>);

impl<T> From<NonNull<GcBox<T>>> for AllocationId
where
    T: Collectable + ?Sized,
{
    /// Get an allocation ID from a pointer to an allocation.
    fn from(value: NonNull<GcBox<T>>) -> Self {
        AllocationId(value.cast())
    }
}

#[derive(Debug)]
/// The necessary information required to collect some garbage-collected data.
/// This data is stored in a map from allocation IDs to the necessary cleanup operation.
struct Cleanup {
    /// The function which is called to build the reference graph and find all allocations
    /// reachable from this allocation.
    build_graph_fn: unsafe fn(ErasedPtr, &mut Dfs),
    /// The function which is called to sweep out and mark allocations reachable from this
    /// allocation as reachable.
    sweep_fn: unsafe fn(ErasedPtr, &mut Sweep),
    /// A function used for dropping the allocation.
    drop_fn: unsafe fn(ErasedPtr, &mut DropAlloc<'_>),
    /// An erased pointer to the allocation.
    ptr: ErasedPtr,
}

impl Cleanup {
    /// Construct a new cleanup for an allocation.
    fn new<T: Collectable + ?Sized>(box_ptr: NonNull<GcBox<T>>) -> Cleanup {
        Cleanup {
            build_graph_fn: apply_visitor::<T, Dfs>,
            sweep_fn: apply_visitor::<T, Sweep>,
            drop_fn: drop_assist::<T>,
            ptr: ErasedPtr::new(box_ptr),
        }
    }
}

/// Apply a visitor to some erased pointer.
///
/// # Safety
///
/// `T` must be the same type that `ptr` was created with via [`ErasedPtr::new`].
unsafe fn apply_visitor<T: Collectable + ?Sized, V: Visitor>(ptr: ErasedPtr, visitor: &mut V) {
    let specified: NonNull<GcBox<T>> = ptr.specify();
    let _ = specified.as_ref().value.accept(visitor);
}

impl Dumpster {
    /// Collect all unreachable allocations that this dumpster is responsible for.
    pub fn collect_all(&self) {
        self.n_ref_drops.set(0);

        unsafe {
            let mut ref_graph_build = Dfs {
                visited: HashSet::with_capacity(self.to_collect.borrow().len()),
                ref_state: HashMap::with_capacity(self.to_collect.borrow().len()),
            };

            for (k, v) in &*self.to_collect.borrow() {
                if !ref_graph_build.visited.contains(k) {
                    ref_graph_build.visited.insert(*k);
                    (v.build_graph_fn)(v.ptr, &mut ref_graph_build);
                }
            }

            let mut sweep = Sweep {
                visited: HashSet::with_capacity(ref_graph_build.visited.len()),
            };
            for (id, reachability) in ref_graph_build
                .ref_state
                .iter()
                .filter(|(_, reachability)| reachability.n_unaccounted != 0)
            {
                sweep.visited.insert(*id);
                (reachability.sweep_fn)(reachability.ptr, &mut sweep);
            }

            // any allocations which we didn't find must also be roots
            for (id, cleanup) in self
                .to_collect
                .borrow()
                .iter()
                .filter(|(id, _)| !ref_graph_build.ref_state.contains_key(id))
            {
                sweep.visited.insert(*id);
                (cleanup.sweep_fn)(cleanup.ptr, &mut sweep);
            }

            ref_graph_build.visited.clear();
            let mut decrementer = DropAlloc {
                visited: ref_graph_build.visited,
                reachable: &sweep.visited,
            };

            self.collecting.set(true);
            for cleanup in self
                .to_collect
                .borrow_mut()
                .drain()
                .filter_map(|(id, cleanup)| (!sweep.visited.contains(&id)).then_some(cleanup))
            {
                (cleanup.drop_fn)(cleanup.ptr, &mut decrementer);
            }
            self.collecting.set(false);
        }
    }

    /// Mark an allocation as "dirty," implying that it may need to be swept through later to find
    /// out if it has any references pointing to it.
    pub fn mark_dirty<T: Collectable + ?Sized>(&self, box_ptr: NonNull<GcBox<T>>) {
        self.to_collect
            .borrow_mut()
            .entry(AllocationId::from(box_ptr))
            .or_insert_with(|| Cleanup::new(box_ptr));
    }

    /// Mark an allocation as "cleaned," implying that the allocation is about to be destroyed and
    /// therefore should not be cleaned up later.
    pub fn mark_cleaned<T: Collectable + ?Sized>(&self, box_ptr: NonNull<GcBox<T>>) {
        self.to_collect
            .borrow_mut()
            .remove(&AllocationId::from(box_ptr));
    }

    /// Notify the dumpster that a garbage-collected pointer has been dropped.
    ///
    /// This may trigger a sweep of the heap, but is guaranteed to be amortized to _O(1)_.
    pub fn notify_dropped_gc(&self) {
        self.n_ref_drops.set(self.n_ref_drops.get() + 1);
        let old_refs_living = self.n_refs_living.get();
        assert_ne!(
            old_refs_living, 0,
            "underflow on unsync::Gc number of living Gcs"
        );
        self.n_refs_living.set(old_refs_living - 1);

        // check if it's been a long time since the last time we collected all
        // the garbage.
        // if so, go and collect it all again (amortized O(1))
        if self.n_ref_drops.get() << 1 >= self.n_refs_living.get() {
            self.collect_all();
        }
    }

    /// Notify the dumpster that a new [`Gc`] has been created.
    pub fn notify_created_gc(&self) {
        self.n_refs_living.set(self.n_refs_living.get() + 1);
    }

    /// Determine whether this dumpster is currently running a collection process.
    pub fn collecting(&self) -> bool {
        self.collecting.get()
    }
}

impl Drop for Dumpster {
    fn drop(&mut self) {
        // cleanup any leftover allocations
        self.collect_all();
    }
}

/// The data required to construct the graph of reachable allocations.
struct Dfs {
    /// The set of allocations which have already been visited.
    visited: HashSet<AllocationId>,
    /// A map from allocation identifiers to information about their reachability.
    ref_state: HashMap<AllocationId, Reachability>,
}

#[derive(Debug)]
/// Information about the reachability of a structure.
struct Reachability {
    /// The number of unaccounted-for references to this allocation.
    /// If this number is 0, the reference is not a root.
    n_unaccounted: usize,
    /// An erased pointer to the allocation under concern.
    ptr: ErasedPtr,
    /// A function used to sweep from `ptr` if this allocation is proven reachable.
    sweep_fn: unsafe fn(ErasedPtr, &mut Sweep),
}

impl Visitor for Dfs {
    fn visit_sync<T>(&mut self, _: &crate::sync::Gc<T>)
    where
        T: Collectable + Sync + ?Sized,
    {
        // because `Gc` is `!Sync`, we know we won't find a `Gc` this way and can return
        // immediately.
    }

    fn visit_unsync<T>(&mut self, gc: &Gc<T>)
    where
        T: Collectable + ?Sized,
    {
        let next_id = AllocationId::from(gc.ptr);
        match self.ref_state.entry(next_id) {
            Entry::Occupied(ref mut o) => {
                o.get_mut().n_unaccounted -= 1;
            }
            Entry::Vacant(v) => {
                v.insert(Reachability {
                    n_unaccounted: unsafe { next_id.0.as_ref().get().get() - 1 },
                    ptr: ErasedPtr::new(gc.ptr),
                    sweep_fn: apply_visitor::<T, Sweep>,
                });
            }
        }
        if self.visited.insert(next_id) {
            gc.deref().accept(self).unwrap();
        }
    }
}

/// A sweep, which marks allocations as reachable.
struct Sweep {
    /// The set of allocations which have been marked as reachable.
    visited: HashSet<AllocationId>,
}

impl Visitor for Sweep {
    fn visit_sync<T>(&mut self, _: &crate::sync::Gc<T>)
    where
        T: Collectable + Sync + ?Sized,
    {
        // because `Gc` is `!Sync`, we know we won't find a `Gc` this way and can return
        // immediately.
    }

    fn visit_unsync<T>(&mut self, gc: &Gc<T>)
    where
        T: Collectable + ?Sized,
    {
        if self.visited.insert(AllocationId::from(gc.ptr)) {
            gc.deref().accept(self).unwrap();
        }
    }
}

/// A visitor for dropping allocations.
struct DropAlloc<'a> {
    /// The set of unreachable allocations we've already visited.
    visited: HashSet<AllocationId>,
    /// The set of unreachable allocations.
    reachable: &'a HashSet<AllocationId>,
}

impl Visitor for DropAlloc<'_> {
    fn visit_sync<T>(&mut self, _: &crate::sync::Gc<T>)
    where
        T: Collectable + Sync + ?Sized,
    {
        // do nothing
    }

    fn visit_unsync<T>(&mut self, gc: &Gc<T>)
    where
        T: Collectable + ?Sized,
    {
        let id = AllocationId::from(gc.ptr);
        if self.reachable.contains(&id) {
            unsafe {
                let cell_ref = id.0.as_ref();
                cell_ref.set(NonZeroUsize::new(cell_ref.get().get() - 1).unwrap());
            }
        } else if self.visited.insert(id) {
            (**gc).accept(self).unwrap();
            unsafe {
                let layout = Layout::for_value(gc.ptr.as_ref());
                drop_in_place(gc.ptr.as_ptr());
                dealloc(gc.ptr.as_ptr().cast(), layout);
            }
        }
    }
}

/// Decrement the outbound reference counts for any reachable allocations which this allocation can
/// find.
/// Also, drop the allocation when done.
unsafe fn drop_assist<T: Collectable + ?Sized>(ptr: ErasedPtr, visitor: &mut DropAlloc<'_>) {
    if visitor
        .visited
        .insert(AllocationId::from(ptr.specify::<GcBox<T>>()))
    {
        ptr.specify::<GcBox<T>>()
            .as_ref()
            .value
            .accept(visitor)
            .unwrap();

        let mut_spec = ptr.specify::<GcBox<T>>().as_mut();
        let layout = Layout::for_value(mut_spec);
        drop_in_place(mut_spec);
        dealloc((mut_spec as *mut GcBox<T>).cast(), layout);
    }
}
