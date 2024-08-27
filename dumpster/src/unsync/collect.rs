/*
    dumpster, acycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! Implementations of the single-threaded garbage-collection logic.

use std::{
    alloc::{dealloc, Layout},
    cell::{Cell, RefCell},
    collections::{hash_map::Entry, HashMap, HashSet},
    num::NonZeroUsize,
    ptr::{drop_in_place, NonNull},
};

use crate::{
    ptr::Erased,
    unsync::{default_collect_condition, CollectInfo, Gc},
    Trace, Visitor,
};

use super::{CollectCondition, GcBox};

thread_local! {
    /// Whether the current thread is running a cleanup process.
    pub(super) static COLLECTING: Cell<bool> = const { Cell::new(false) };
    /// The global collection of allocation information for this thread.
    pub(super) static DUMPSTER: Dumpster = Dumpster {
        to_collect: RefCell::new(HashMap::new()),
        n_ref_drops: Cell::new(0),
        n_refs_living: Cell::new(0),
        collect_condition: Cell::new(default_collect_condition),
    };
}

/// A dumpster is a collection of all the garbage that may or may not need to be cleaned up.
/// It also contains information relevant to when a cleanup should be triggered.
pub(super) struct Dumpster {
    /// A map from allocation IDs for allocations which may need to be collected to pointers to
    /// their allocations.
    to_collect: RefCell<HashMap<AllocationId, Cleanup>>,
    /// The number of times a reference has been dropped since the last collection was triggered.
    pub n_ref_drops: Cell<usize>,
    /// The number of references that currently exist in the entire heap and stack.
    pub n_refs_living: Cell<usize>,
    /// The function for determining whether a collection should be run.
    pub collect_condition: Cell<CollectCondition>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A unique identifier for an allocated garbage-collected block.
///
/// It contains a pointer to the reference count of the allocation.
struct AllocationId(pub NonNull<Cell<NonZeroUsize>>);

impl<T> From<NonNull<GcBox<T>>> for AllocationId
where
    T: Trace + ?Sized,
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
    dfs_fn: unsafe fn(Erased, &mut Dfs),
    /// The function which is called to mark descendants of this allocation as reachable.
    mark_fn: unsafe fn(Erased, &mut Mark),
    /// A function used for dropping the allocation.
    drop_fn: unsafe fn(Erased, &mut DropAlloc<'_>),
    /// An erased pointer to the allocation.
    ptr: Erased,
}

impl Cleanup {
    /// Construct a new cleanup for an allocation.
    fn new<T: Trace + ?Sized>(box_ptr: NonNull<GcBox<T>>) -> Cleanup {
        Cleanup {
            dfs_fn: apply_visitor::<T, Dfs>,
            mark_fn: apply_visitor::<T, Mark>,
            drop_fn: drop_assist::<T>,
            ptr: Erased::new(box_ptr),
        }
    }
}

/// Apply a visitor to some erased pointer.
///
/// # Safety
///
/// `T` must be the same type that `ptr` was created with via [`ErasedPtr::new`].
unsafe fn apply_visitor<T: Trace + ?Sized, V: Visitor>(ptr: Erased, visitor: &mut V) {
    let specified: NonNull<GcBox<T>> = ptr.specify();
    let _ = specified.as_ref().value.accept(visitor);
}

impl Dumpster {
    /// Collect all unreachable allocations that this dumpster is responsible for.
    pub fn collect_all(&self) {
        self.n_ref_drops.set(0);

        unsafe {
            let mut dfs = Dfs {
                visited: HashSet::with_capacity(self.to_collect.borrow().len()),
                ref_graph: HashMap::with_capacity(self.to_collect.borrow().len()),
            };

            for (k, v) in &*self.to_collect.borrow() {
                if dfs.visited.insert(*k) {
                    (v.dfs_fn)(v.ptr, &mut dfs);
                }
            }

            let mut mark = Mark {
                visited: HashSet::with_capacity(dfs.visited.len()),
            };
            for (id, reachability) in dfs
                .ref_graph
                .iter()
                .filter(|(_, reachability)| reachability.n_unaccounted != 0)
            {
                mark.visited.insert(*id);
                (reachability.mark_fn)(reachability.ptr, &mut mark);
            }

            // any allocations which we didn't find must also be roots
            for (id, cleanup) in self
                .to_collect
                .borrow()
                .iter()
                .filter(|(id, _)| !dfs.ref_graph.contains_key(id))
            {
                mark.visited.insert(*id);
                (cleanup.mark_fn)(cleanup.ptr, &mut mark);
            }

            dfs.visited.clear();
            let mut decrementer = DropAlloc {
                visited: dfs.visited,
                reachable: &mark.visited,
            };

            COLLECTING.with(|c| c.set(true));
            for cleanup in self
                .to_collect
                .borrow_mut()
                .drain()
                .filter_map(|(id, cleanup)| (!mark.visited.contains(&id)).then_some(cleanup))
            {
                (cleanup.drop_fn)(cleanup.ptr, &mut decrementer);
            }
            COLLECTING.with(|c| c.set(false));
        }
    }

    /// Mark an allocation as "dirty," implying that it may need to be swept through later to find
    /// out if it has any references pointing to it.
    pub fn mark_dirty<T: Trace + ?Sized>(&self, box_ptr: NonNull<GcBox<T>>) {
        self.to_collect
            .borrow_mut()
            .entry(AllocationId::from(box_ptr))
            .or_insert_with(|| Cleanup::new(box_ptr));
    }

    /// Mark an allocation as "cleaned," implying that the allocation is about to be destroyed and
    /// therefore should not be cleaned up later.
    pub fn mark_cleaned<T: Trace + ?Sized>(&self, box_ptr: NonNull<GcBox<T>>) {
        self.to_collect
            .borrow_mut()
            .remove(&AllocationId::from(box_ptr));
    }

    /// Notify the dumpster that a garbage-collected pointer has been dropped.
    ///
    /// This may trigger a cleanup of the heap, but is guaranteed to be amortized to _O(1)_.
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
        if (self.collect_condition.get())(&CollectInfo { _private: () }) {
            self.collect_all();
        }
    }

    /// Notify the dumpster that a new [`Gc`] has been created.
    pub fn notify_created_gc(&self) {
        self.n_refs_living.set(self.n_refs_living.get() + 1);
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
    ref_graph: HashMap<AllocationId, Reachability>,
}

#[derive(Debug)]
/// Information about the reachability of a structure.
struct Reachability {
    /// The number of unaccounted-for references to this allocation.
    /// If this number is 0, the reference is not a root.
    n_unaccounted: usize,
    /// An erased pointer to the allocation under concern.
    ptr: Erased,
    /// A function used to mark descendants of this allocation as accessible.
    mark_fn: unsafe fn(Erased, &mut Mark),
}

impl Visitor for Dfs {
    fn visit_sync<T>(&mut self, _: &crate::sync::Gc<T>)
    where
        T: Trace + Send + Sync + ?Sized,
    {
        // because `Gc` is `!Sync`, we know we won't find a `Gc` this way and can return
        // immediately.
    }

    fn visit_unsync<T>(&mut self, gc: &Gc<T>)
    where
        T: Trace + ?Sized,
    {
        let ptr = gc.ptr.get().unwrap();
        let next_id = AllocationId::from(ptr);
        match self.ref_graph.entry(next_id) {
            Entry::Occupied(ref mut o) => {
                o.get_mut().n_unaccounted -= 1;
            }
            Entry::Vacant(v) => {
                v.insert(Reachability {
                    n_unaccounted: unsafe { next_id.0.as_ref().get().get() - 1 },
                    ptr: Erased::new(ptr),
                    mark_fn: apply_visitor::<T, Mark>,
                });
            }
        }
        if self.visited.insert(next_id) {
            let _ = unsafe { ptr.as_ref() }.value.accept(self);
        }
    }
}

/// A mark traversal, which marks allocations as reachable.
struct Mark {
    /// The set of allocations which have been marked as reachable.
    visited: HashSet<AllocationId>,
}

impl Visitor for Mark {
    fn visit_sync<T>(&mut self, _: &crate::sync::Gc<T>)
    where
        T: Trace + Send + Sync + ?Sized,
    {
        // because `Gc` is `!Sync`, we know we won't find a `Gc` this way and can return
        // immediately.
    }

    fn visit_unsync<T>(&mut self, gc: &Gc<T>)
    where
        T: Trace + ?Sized,
    {
        let ptr = gc.ptr.get().unwrap();
        if self.visited.insert(AllocationId::from(ptr)) {
            let _ = unsafe { ptr.as_ref().value.accept(self) };
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
        T: Trace + Send + Sync + ?Sized,
    {
        // do nothing
    }

    fn visit_unsync<T>(&mut self, gc: &Gc<T>)
    where
        T: Trace + ?Sized,
    {
        let ptr = gc.ptr.get().unwrap();
        let id = AllocationId::from(ptr);
        if self.reachable.contains(&id) {
            unsafe {
                let cell_ref = &ptr.as_ref().ref_count;
                cell_ref.set(NonZeroUsize::new(cell_ref.get().get() - 1).unwrap());
            }
            return;
        }
        gc.ptr.set(gc.ptr.get().as_null());
        if self.visited.insert(id) {
            unsafe {
                ptr.as_ref().value.accept(self).unwrap();
                let layout = Layout::for_value(ptr.as_ref());
                drop_in_place(ptr.as_ptr());
                dealloc(ptr.as_ptr().cast(), layout);
            }
        }
    }
}

/// Decrement the outbound reference counts for any reachable allocations which this allocation can
/// find.
/// Also, drop the allocation when done.
unsafe fn drop_assist<T: Trace + ?Sized>(ptr: Erased, visitor: &mut DropAlloc<'_>) {
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
        dealloc(std::ptr::from_mut::<GcBox<T>>(mut_spec).cast(), layout);
    }
}
