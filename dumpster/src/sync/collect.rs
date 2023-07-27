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

//! A synchronized collection algorithm.

use std::{
    alloc::{dealloc, Layout},
    cell::Cell,
    collections::{hash_map::Entry, HashMap},
    mem::{replace, swap, take},
    ptr::{drop_in_place, NonNull},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Mutex, MutexGuard, RwLock, TryLockError,
    },
};

use chashmap::CHashMap;

use once_cell::sync::Lazy;

use crate::{Collectable, OpaquePtr, Visitor};

use super::{Gc, GcBox};

/// The global collection of allocations to clean up.
// wishing dreams: chashmap gets a const new function so that we can remove the once cell
pub(super) static DUMPSTER: Dumpster = Dumpster {
    to_clean: Lazy::new(|| RwLock::new(CHashMap::new())),
    collecting_lock: RwLock::new(()),
    n_gcs_dropped: AtomicUsize::new(0),
    n_gcs_existing: AtomicUsize::new(0),
};

thread_local! {
    /// Whether the currently-running thread is doing a cleanup.
    pub(super) static CLEANING: Cell<bool> = Cell::new(false);
}

/// A structure containing the global information for the garbage collector.
pub(super) struct Dumpster {
    /// A lookupt table for the allocations which may need to be cleaned up later.
    to_clean: Lazy<RwLock<CHashMap<AllocationId, Cleanup>>>,
    /// A lock used for synchronizing threads that are awaiting completion of a collection process.
    /// This lock should be acquired for reads by threads running a collection and for writes by
    /// threads awaiting collection completion.
    collecting_lock: RwLock<()>,
    /// The number of [`Gc`]s dropped since the last time [`Dumpster::collect_all()`] was called.
    n_gcs_dropped: AtomicUsize,
    /// The number of [`Gc`]s currently existing (which have not had their internals replaced with
    /// `None`).
    n_gcs_existing: AtomicUsize,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
/// A unique identifier for an allocation.
struct AllocationId(NonNull<Mutex<usize>>);

unsafe impl Send for AllocationId {}
unsafe impl Sync for AllocationId {}

impl<T> From<NonNull<GcBox<T>>> for AllocationId
where
    T: Collectable + Sync + ?Sized,
{
    fn from(value: NonNull<GcBox<T>>) -> Self {
        unsafe { AllocationId(NonNull::from(&value.as_ref().ref_count)) }
    }
}

/// A function which can be used to create a reference graph.
type BuildFn = unsafe fn(
    OpaquePtr,
    AllocationId,
    &mut HashMap<AllocationId, Node>,
    &mut HashMap<AllocationId, MutexGuard<'static, usize>>,
);

#[derive(Debug)]
/// The information which describes an allocation that may need to be cleaned up later.
struct Cleanup {
    /// A pointer to the allocation to be cleaned up.
    ptr: OpaquePtr,
    /// The function which can be used to build a reference graph.
    /// This function is safe to call on `ptr`.
    build_fn: BuildFn,
}

#[derive(Debug)]
/// A node in the reference graph, which is constructed while searching for unreachable allocations.
enum Node {
    /// The information describing an allocation whose accessibility is unknown.
    Unknown {
        /// The IDs for the allocations directly accessible from this allocation.
        children: Vec<AllocationId>,
        /// The number of references in the reference count for this allocation which are
        /// "unaccounted," which have not been found while constructing the graph.
        /// It is the difference between the allocations indegree in the "true" reference graph vs
        /// the one we are currently building.
        n_unaccounted: usize,
        /// A function used to destroy the allocation.
        destroy_fn: unsafe fn(OpaquePtr),
        /// A function used to decrement outbound reference counts to reachable nodes.
        decrement_fn: unsafe fn(OpaquePtr, &HashMap<AllocationId, Node>),
        /// A pointer to the allocation.
        ptr: OpaquePtr,
    },
    /// The allocation here is reachable.
    /// No further information is needed.
    Reachable,
}

impl Dumpster {
    /// Search through the set of existing allocations which have been marked inacessible, and see
    /// if they are inaccessible.
    /// If so, drop those allocations.
    pub fn collect_all(&self) {
        let collecting_guard = self.collecting_lock.read().unwrap();
        self.n_gcs_dropped.store(0, Ordering::Relaxed);
        let to_collect = take(&mut *self.to_clean.write().unwrap());
        let mut ref_graph = HashMap::new();
        let mut guards = HashMap::new();

        for (id, cleanup) in to_collect {
            unsafe { (cleanup.build_fn)(cleanup.ptr, id, &mut ref_graph, &mut guards) };
        }

        drop(guards);
        let root_ids = ref_graph
            .iter()
            .filter_map(|(&k, v)| match v {
                Node::Reachable => Some(k),
                Node::Unknown { n_unaccounted, .. } => (*n_unaccounted > 0).then_some(k),
            })
            .collect::<Vec<_>>();
        for root_id in root_ids {
            sweep(root_id, &mut ref_graph);
        }

        for (decrement_fn, &ptr) in ref_graph.iter().filter_map(|(_, v)| match v {
            Node::Reachable => None,
            Node::Unknown {
                decrement_fn, ptr, ..
            } => Some((decrement_fn, ptr)),
        }) {
            unsafe { decrement_fn(ptr, &ref_graph) };
        }

        CLEANING.with(|c| c.set(true));
        for (destroy_fn, ptr) in ref_graph.into_iter().filter_map(|(_, v)| match v {
            Node::Reachable => None,
            Node::Unknown {
                destroy_fn, ptr, ..
            } => Some((destroy_fn, ptr)),
        }) {
            unsafe { destroy_fn(ptr) };
        }
        CLEANING.with(|c| c.set(false));
        drop(collecting_guard);
    }

    /// Block this thread until all threads which are currently running a collection have finished.
    pub fn await_collection_end(&self) {
        drop(self.collecting_lock.write().unwrap());
    }

    /// Notify this dumpster that a `Gc` was destroyed, and update the tracking count for the number
    /// of dropped and existing `Gc`s.
    ///
    /// This may trigger a linear-time cleanup of all allocations, but this will be guaranteed to
    /// occur with less-than-linear frequency, so it's always O(1).
    pub fn notify_dropped_gc(&self) {
        let prev_gcs_dropped = self.n_gcs_dropped.fetch_add(1, Ordering::Relaxed);
        let prev_gcs_existing = self.n_gcs_existing.fetch_sub(1, Ordering::Relaxed);
        assert_ne!(prev_gcs_existing, 0, "underflow on number of existing GCs");

        if prev_gcs_dropped >= prev_gcs_existing >> 1 && prev_gcs_dropped > 0 {
            self.collect_all();
        }
    }

    /// Notify this dumpster that a `Gc` was created, and increment the number of total existing
    /// `Gc`s.
    pub fn notify_created_gc(&self) {
        self.n_gcs_existing.fetch_add(1, Ordering::Relaxed);
    }

    /// Mark an allocation as "dirty," implying that it may or may not be inaccessible and need to
    /// be cleaned up.
    pub fn mark_dirty<T>(&self, allocation: NonNull<GcBox<T>>)
    where
        T: Collectable + Sync + ?Sized,
    {
        self.to_clean
            .read()
            .unwrap()
            .insert(AllocationId::from(allocation), Cleanup::new(allocation));
    }

    /// Mark an allocation as "clean," implying that it has already been cleaned up and does not
    /// need to be cleaned again.
    pub fn mark_clean<T>(&self, allocation: NonNull<GcBox<T>>)
    where
        T: Collectable + Sync + ?Sized,
    {
        self.to_clean
            .read()
            .unwrap()
            .remove(&AllocationId::from(allocation));
    }
}

impl Cleanup {
    /// Construct a new Cleanup from the allocation needed to clean it up.
    fn new<T>(ptr: NonNull<GcBox<T>>) -> Cleanup
    where
        T: Collectable + Sync + ?Sized,
    {
        Cleanup {
            ptr: OpaquePtr::new(ptr),
            build_fn: build_ref_graph::<T>,
        }
    }
}

/// Build out a part of the reference graph, making note of all allocations which are reachable from
/// the one described in `ptr`.
///
/// # Inputs
///
/// - `ptr`: A pointer to the allocation that we should start constructing from.
/// - `starting_id`: The ID of the allocation pointed to by `ptr`.
/// - `ref_graph`: A lookup from allocation IDs to node information about that allocation.
/// - `guards`: A lookup from allocation IDs to the mutex guards they control. This prevents data
///   races during reference graph construction.
///
/// # Effects
///
/// `ref_graph` will be expanded to include all allocations reachable from `ptr`.
/// Any allocation which is of "unknown" status will also receive a mutex guard in `guards`.
///
/// # Safety
///
/// `ptr` must have been created as a pointer to a `GcBox<T>`.
/// `starting_id` must refer to the reference count for the allocation pointed to by `ptr`.
unsafe fn build_ref_graph<T: Collectable + Sync + ?Sized>(
    ptr: OpaquePtr,
    starting_id: AllocationId,
    ref_graph: &mut HashMap<AllocationId, Node>,
    guards: &mut HashMap<AllocationId, MutexGuard<'static, usize>>,
) {
    if let Entry::Vacant(v) = ref_graph.entry(starting_id) {
        match unsafe { starting_id.0.as_ref().try_lock() } {
            Ok(guard) => {
                v.insert(Node::Unknown {
                    children: Vec::new(),
                    n_unaccounted: *guard,
                    destroy_fn: destroy_opaque::<T>,
                    decrement_fn: decrement_reachable_count::<T>,
                    ptr,
                });
                guards.insert(starting_id, guard);

                if ptr
                    .specify::<GcBox<T>>()
                    .as_ref()
                    .value
                    .accept(&mut BuildRefGraph {
                        ref_graph,
                        current_id: starting_id,
                        guards,
                    })
                    .is_err()
                {
                    let Node::Unknown { children, .. } =
                        replace(ref_graph.get_mut(&starting_id).unwrap(), Node::Reachable)
                    else {
                        panic!("initial allocaiton magically marked as reachable by other thread?");
                    };

                    for child in children {
                        sweep(child, ref_graph);
                    }
                }
            }
            Err(TryLockError::WouldBlock) => {
                v.insert(Node::Reachable);
            }
            _ => {
                panic!("poisoned lock in Gc!");
            }
        }
    }
}

#[derive(Debug)]
/// The visitor structure used for building the found-reference-graph of allocations.
struct BuildRefGraph<'a> {
    /// The reference graph.
    /// Each allocation is assigned a node.
    ref_graph: &'a mut HashMap<AllocationId, Node>,
    /// The allocation ID currently being visited.
    /// Used for knowing which node is the parent of another.
    current_id: AllocationId,
    /// The currently-held mutex guards as we construct the graph.
    /// If an allocation has an entry in the reference graph, it should also be covered by a
    /// guard.
    guards: &'a mut HashMap<AllocationId, MutexGuard<'static, usize>>,
}

impl<'a> Visitor for BuildRefGraph<'a> {
    fn visit_sync<T>(&mut self, gc: &Gc<T>)
    where
        T: Collectable + Sync + ?Sized,
    {
        let mut new_id = AllocationId::from(gc.ptr);
        let Node::Unknown {
            ref mut children, ..
        } = self.ref_graph.get_mut(&self.current_id).unwrap()
        else {
            // this node has been proven reachable by something higher up. No need to keep building
            // its ref graph
            return;
        };
        children.push(new_id);

        match self.ref_graph.entry(new_id) {
            Entry::Occupied(mut o) => match o.get_mut() {
                Node::Unknown {
                    ref mut n_unaccounted,
                    ..
                } => {
                    *n_unaccounted -= 1;
                }
                Node::Reachable => (),
            },
            Entry::Vacant(v) => {
                // This allocation has never been visited by the reference graph builder.
                // Attempt to acquire its lock.
                match unsafe { new_id.0.as_ref().try_lock() } {
                    Ok(guard) => {
                        // This allocation is not currently being inspected by anything else and
                        // is therefore of unknown reachability.

                        let _ = v.insert(Node::Unknown {
                            children: Vec::new(),
                            n_unaccounted: *guard - 1,
                            destroy_fn: destroy_opaque::<T>,
                            decrement_fn: decrement_reachable_count::<T>,
                            ptr: OpaquePtr::new(gc.ptr),
                        });
                        self.guards.insert(new_id, guard);

                        // Save the previously visited ID, then carry on to the next one
                        swap(&mut new_id, &mut self.current_id);

                        if (**gc).accept(self).is_err() {
                            // On failure, this means `**gc` is accessible, and should be marked
                            // as such
                            sweep_delete_guards(new_id, self.ref_graph, self.guards);
                        }

                        // Restore current_id and carry on
                        swap(&mut new_id, &mut self.current_id);
                    }
                    Err(TryLockError::WouldBlock) => {
                        // This allocation is currently being inspected by another thread and is
                        // therefore reachable.
                        v.insert(Node::Reachable);
                    }
                    _ => {
                        panic!("poisoned lock in Gc!");
                    }
                };
            }
        };
    }

    fn visit_unsync<T>(&mut self, _: &crate::unsync::Gc<T>)
    where
        T: Collectable + ?Sized,
    {
        panic!("A `dumpster::sync::Gc` may not own a `dumpster::unsync::Gc` because `dumpster::unsync::Gc` is `Sync`");
    }
}

/// Sweep through the reference graph, marking `root` and any allocations reachable from `root` as
/// reachable.
///
/// Removes the mutex guard associated with each of those allocations as well.
fn sweep_delete_guards(
    root: AllocationId,
    graph: &mut HashMap<AllocationId, Node>,
    guards: &mut HashMap<AllocationId, MutexGuard<'static, usize>>,
) {
    let node = graph.get_mut(&root).unwrap();
    if let Node::Unknown { children, .. } = replace(node, Node::Reachable) {
        guards.remove(&root);
        for child in children {
            sweep_delete_guards(child, graph, guards);
        }
    }
}

/// Sweep through the reference graph, marking `root` and any allocations reachable from `root` as
/// reachable.
fn sweep(root: AllocationId, graph: &mut HashMap<AllocationId, Node>) {
    let node = graph.get_mut(&root).unwrap();
    if let Node::Unknown { children, .. } = replace(node, Node::Reachable) {
        for child in children {
            sweep(child, graph);
        }
    }
}

/// Destroy an allocation, obliterating its GCs, dropping it, and deallocating it.
///
/// # Safety
///
/// `ptr` must have been created from a pointer to a `GcBox<T>`.
unsafe fn destroy_opaque<T: Collectable + Sync + ?Sized>(ptr: OpaquePtr) {
    let specified = ptr.specify::<GcBox<T>>().as_mut();
    let layout = Layout::for_value(specified);
    drop_in_place(specified);
    dealloc((specified as *mut GcBox<T>).cast(), layout);
}

impl Drop for Dumpster {
    fn drop(&mut self) {
        self.collect_all();
    }
}

/// Decrement the reference count all reachable allocations pointed to by the value stored in `ptr`.
unsafe fn decrement_reachable_count<T: Collectable + Sync + ?Sized>(
    ptr: OpaquePtr,
    ref_graph: &HashMap<AllocationId, Node>,
) {
    /// A visitor for decrementing the reference count of pointees.
    struct DecrementOutboundReferenceCounts<'a> {
        /// The reference graph.
        /// Must have been populated with reachabiltiy already.
        ref_graph: &'a HashMap<AllocationId, Node>,
    }

    impl Visitor for DecrementOutboundReferenceCounts<'_> {
        fn visit_sync<T>(&mut self, gc: &crate::sync::Gc<T>)
        where
            T: Collectable + Sync + ?Sized,
        {
            unsafe {
                let id = AllocationId::from(gc.ptr);
                if let Node::Reachable = self.ref_graph[&id] {
                    // We know that this node is a root or reachable from a root, so we need not
                    // bother adding it to a collection queue.
                    // We also know this won't zero out the reference count or underflow for the
                    // same reason.
                    *id.0.as_ref().lock().unwrap() -= 1;
                }
            }
        }

        fn visit_unsync<T>(&mut self, _: &crate::unsync::Gc<T>)
        where
            T: Collectable + ?Sized,
        {
            unreachable!("no unsync members of sync Gc possible!");
        }
    }

    ptr.specify::<GcBox<T>>()
        .as_ref()
        .value
        .accept(&mut DecrementOutboundReferenceCounts { ref_graph })
        .expect("allocation assumed to be unreachable but somehow was accessed");
}
