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
    cell::{Cell, RefCell, UnsafeCell},
    collections::{hash_map::Entry, HashMap, HashSet},
    mem::{replace, swap, take, transmute},
    ptr::{drop_in_place, NonNull},
    sync::{
        atomic::{AtomicPtr, AtomicUsize, Ordering},
        Mutex, RwLock,
    },
};

use once_cell::sync::Lazy;

use crate::{Collectable, ErasedPtr, Visitor};

use super::{default_collect_condition, CollectCondition, CollectInfo, Gc, GcBox};

/// The garbage truck, which is a global data structure containing information about allocations
/// which might need to be collected.
struct GarbageTruck {
    /// The contents of the garbage truck, containing all the allocations which need to be
    /// collected and have already been delivered by a [`Dumpster`].
    contents: Mutex<HashMap<AllocationId, TrashCan>>,
    /// A lock used for synchronizing threads that are awaiting completion of a collection process.
    /// This lock should be acquired for reads by threads running a collection and for writes by
    /// threads awaiting collection completion.
    collecting_lock: RwLock<()>,
    /// The number of [`Gc`]s dropped since the last time [`Dumpster::collect_all()`] was called.
    n_gcs_dropped: AtomicUsize,
    /// The number of [`Gc`]s currently existing (which have not had their internals replaced with
    /// `None`).
    n_gcs_existing: AtomicUsize,
    /// The function which determines whether a collection should be triggerd.
    /// This pointer value should always be cast to a [`CollectCondition`], but since `AtomicPtr`
    /// doesn't handle function pointers correctly, we just cast to `*mut ()`.
    collect_condition: AtomicPtr<()>,
}

/// A structure containing the global information for the garbage collector.
struct Dumpster {
    /// A lookupt table for the allocations which may need to be cleaned u later.
    contents: RefCell<HashMap<AllocationId, TrashCan>>,
    /// The number of times an allocation on this thread has been dropped.
    n_drops: Cell<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
/// A unique identifier for an allocation.
struct AllocationId(NonNull<GcBox<()>>);

#[derive(Debug)]
/// The information which describes an allocation that may need to be cleaned up later.
struct TrashCan {
    /// A pointer to the allocation to be cleaned up.
    ptr: ErasedPtr,
    /// The function which can be used to tag the allocation and all its descendants prior to a
    /// DFS. this function is safe to call on `ptr`.
    tag_fn: unsafe fn(ErasedPtr, &mut HashSet<AllocationId>),
    /// The function which can be used to build a reference graph.
    /// This function is safe to call on `ptr`.
    dfs_fn: unsafe fn(ErasedPtr, &mut HashMap<AllocationId, AllocationInfo>),
}

#[derive(Debug)]
/// A node in the reference graph, which is constructed while searching for unreachable allocations.
struct AllocationInfo {
    /// An erased pointer to the allocation.
    ptr: ErasedPtr,
    /// Function for dropping the allocation when its weak and strong count hits zero.
    /// Should have the same behavior as dropping a Gc normally to a reference count of zero.
    weak_drop_fn: unsafe fn(ErasedPtr),
    /// Information about this allocation's reachability.
    reachability: Reachability,
}

#[derive(Debug)]
/// The state of whether an allocation is reachable or of unknown reachability.
enum Reachability {
    /// The information describing an allocation whose accessibility is unknown.
    Unknown {
        /// The IDs for the allocations directly accessible from this allocation.
        children: Vec<AllocationId>,
        /// The number of references in the reference count for this allocation which are
        /// "unaccounted," which have not been found while constructing the graph.
        /// It is the difference between the allocations indegree in the "true" reference graph vs
        /// the one we are currently building.
        n_unaccounted: usize,
        /// The last recorded generation of this allocation from when the reachability was created.
        /// If the generation does not match the allocation, that means it's accessible.
        generation: usize,
        /// A function used to destroy the allocation.
        destroy_fn: unsafe fn(ErasedPtr, &HashMap<AllocationId, AllocationInfo>),
    },
    /// The allocation here is reachable.
    /// No further information is needed.
    Reachable,
}

/// The global garbage truck.
/// All [`TrashCans`] should eventually end up in here.
static GARBAGE_TRUCK: Lazy<GarbageTruck> = Lazy::new(|| GarbageTruck {
    contents: Mutex::new(HashMap::new()),
    collecting_lock: RwLock::new(()),
    n_gcs_dropped: AtomicUsize::new(0),
    n_gcs_existing: AtomicUsize::new(0),
    collect_condition: AtomicPtr::new(default_collect_condition as *mut ()),
});

thread_local! {
    /// The dumpster for this thread.
    /// Allocations which are "dirty" will be transferred to this dumpster before being moved into
    /// the garbage truck for final collection.
    static DUMPSTER: Dumpster = Dumpster {
        contents: RefCell::new(HashMap::new()),
        n_drops: Cell::new(0),
    };

    /// Whether the currently-running thread is doing a cleanup.
    /// This cannot be stored in `DUMPSTER` because otherwise it would cause weird use-after-drop
    /// behavior.
    static CLEANING: Cell<bool> = const { Cell::new(false) };
}

#[allow(clippy::module_name_repetitions)]
/// Collect all allocations in the garbage truck (but not necessarily the dumpster), then await
/// completion of the collection.
/// Ensures that all allocations dropped on the calling thread are cleaned up
pub fn collect_all_await() {
    DUMPSTER.with(|d| d.deliver_to(&GARBAGE_TRUCK));
    GARBAGE_TRUCK.collect_all();
    drop(GARBAGE_TRUCK.collecting_lock.read().unwrap());
}

/// Notify that a `Gc` was destroyed, and update the tracking count for the number of dropped and
/// existing `Gc`s.
///
/// This may trigger a linear-time cleanup of all allocations, but this will be guaranteed to
/// occur with less-than-linear frequency, so it's always O(1).
pub fn notify_dropped_gc() {
    GARBAGE_TRUCK.n_gcs_existing.fetch_sub(1, Ordering::Relaxed);
    GARBAGE_TRUCK.n_gcs_dropped.fetch_add(1, Ordering::Relaxed);
    DUMPSTER.with(|dumpster| {
        dumpster.n_drops.set(dumpster.n_drops.get() + 1);
        if dumpster.is_full() {
            dumpster.deliver_to(&GARBAGE_TRUCK);
        }
    });

    if (unsafe {
        transmute::<_, CollectCondition>(GARBAGE_TRUCK.collect_condition.load(Ordering::Relaxed))
    })(&CollectInfo { _private: () })
    {
        GARBAGE_TRUCK.collect_all();
    }
}

/// Notify that a [`Gc`] was created, and increment the number of total existing `Gc`s.
pub fn notify_created_gc() {
    GARBAGE_TRUCK.n_gcs_existing.fetch_add(1, Ordering::Relaxed);
}

/// Mark an allocation as "dirty," implying that it may or may not be inaccessible and need to
/// be cleaned up.
pub(super) fn mark_dirty<T>(allocation: NonNull<GcBox<T>>)
where
    T: Collectable + Sync + ?Sized,
{
    let box_ref = unsafe { allocation.as_ref() };
    DUMPSTER.with(|dumpster| {
        if dumpster
            .contents
            .borrow_mut()
            .insert(
                AllocationId::from(box_ref),
                TrashCan {
                    ptr: ErasedPtr::new(allocation),
                    tag_fn: tag_all::<T>,
                    dfs_fn: dfs::<T>,
                },
            )
            .is_none()
        {
            box_ref.weak.fetch_add(1, Ordering::Acquire);
        }
    });
}

/// Mark an allocation as "clean," implying that it has already been cleaned up and does not
/// need to be cleaned again.
pub(super) fn mark_clean<T>(allocation: &GcBox<T>)
where
    T: Collectable + Sync + ?Sized,
{
    DUMPSTER.with(|dumpster| {
        if dumpster
            .contents
            .borrow_mut()
            .remove(&AllocationId::from(allocation))
            .is_some()
        {
            allocation.weak.fetch_sub(1, Ordering::Release);
        }
    });
}

#[allow(clippy::missing_panics_doc)]
/// Set the function which determines whether the garbage collector should be run.
///
/// `f` will be periodically called by the garbage collector to determine whether it should perform
/// a full traversal of the heap.
/// When `f` returns true, a traversal will begin.
///
/// # Examples
///
/// ```
/// use dumpster::sync::{set_collect_condition, CollectInfo};
///
/// /// This function will make sure a GC traversal never happens unless directly activated.
/// fn never_collect(_: &CollectInfo) -> bool {
///     false
/// }
///
/// set_collect_condition(never_collect);
/// ```
pub fn set_collect_condition(f: CollectCondition) {
    GARBAGE_TRUCK
        .collect_condition
        .store(f as *mut (), Ordering::Relaxed);
}

/// Determine whether this thread is currently cleaning.
pub fn currently_cleaning() -> bool {
    CLEANING.with(Cell::get)
}

/// Get the number of `[Gc]`s dropped since the last collection.
pub fn n_gcs_dropped() -> usize {
    GARBAGE_TRUCK.n_gcs_dropped.load(Ordering::Relaxed)
}

/// Get the number of `[Gc]`s currently existing in the entire program.
pub fn n_gcs_existing() -> usize {
    GARBAGE_TRUCK.n_gcs_existing.load(Ordering::Relaxed)
}

impl Dumpster {
    /// Deliver all [`TrashCans`] contained by this dumpster to the garbage collect, removing them
    /// from the local dumpster storage and adding them to the global truck.
    fn deliver_to(&self, garbage_truck: &GarbageTruck) {
        self.n_drops.set(0);
        let mut guard = garbage_truck.contents.lock().unwrap();
        for (id, can) in self.contents.borrow_mut().drain() {
            if guard.insert(id, can).is_some() {
                unsafe {
                    id.0.as_ref().weak.fetch_sub(1, Ordering::Relaxed);
                }
            }
        }
    }

    /// Determine whether this dumpster is full (and therefore should have its contents delivered to
    /// the garbage truck).
    fn is_full(&self) -> bool {
        self.contents.borrow().len() > 100_000 || self.n_drops.get() > 100_000
    }
}

impl GarbageTruck {
    #[allow(clippy::module_name_repetitions)]
    /// Search through the set of existing allocations which have been marked inacessible, and see
    /// if they are inaccessible.
    /// If so, drop those allocations.
    fn collect_all(&self) {
        let collecting_guard = self.collecting_lock.write().unwrap();
        self.n_gcs_dropped.store(0, Ordering::Relaxed);
        let to_collect = take(&mut *self.contents.lock().unwrap());
        let mut visited = HashSet::with_capacity(to_collect.len());

        let to_dfs = to_collect
            .into_values()
            .map(|cleanup| {
                unsafe {
                    (cleanup.tag_fn)(cleanup.ptr, &mut visited);
                }
                (cleanup.ptr, cleanup.dfs_fn)
            })
            .collect::<Vec<_>>();

        let mut ref_graph = HashMap::with_capacity(visited.len());

        for (ptr, dfs_fn) in to_dfs {
            unsafe { dfs_fn(ptr, &mut ref_graph) };
        }

        let root_ids = ref_graph
            .iter()
            .filter_map(|(&k, v)| match v.reachability {
                Reachability::Reachable => Some(k),
                Reachability::Unknown { n_unaccounted, .. } => (n_unaccounted > 0
                    || unsafe { k.0.as_ref().weak.load(Ordering::Relaxed) > 1 })
                .then_some(k),
            })
            .collect::<Vec<_>>();
        for root_id in root_ids {
            mark(root_id, &mut ref_graph);
        }

        CLEANING.with(|c| c.set(true));
        // set of allocations which must be destroyed because we were the last weak pointer to it
        let mut weak_destroys = Vec::new();
        for (id, node) in &ref_graph {
            let header_ref = unsafe { id.0.as_ref() };
            match node.reachability {
                Reachability::Unknown { destroy_fn, .. } => unsafe {
                    destroy_fn(node.ptr, &ref_graph);
                },
                Reachability::Reachable => {
                    if header_ref.weak.fetch_sub(1, Ordering::Release) == 1
                        && header_ref.strong.load(Ordering::Acquire) == 0
                    {
                        // we are the last reference to the allocation.
                        // mark to be cleaned up later
                        // no real synchronization loss to storing the guard because we had the last
                        // reference anyway
                        weak_destroys.push((node.weak_drop_fn, node.ptr));
                    }
                }
            };
        }
        CLEANING.with(|c| c.set(false));
        for (drop_fn, ptr) in weak_destroys {
            unsafe {
                drop_fn(ptr);
            }
        }
        drop(collecting_guard);
    }
}

/// Tag all allocations reachable from `ptr` as being part of a traversal (i.e. setting their tag to
/// `true`).
unsafe fn tag_all<T: Collectable + Sync + ?Sized>(
    ptr: ErasedPtr,
    visited: &mut HashSet<AllocationId>,
) {
    /// A visitor for tagging all `Gc`s reachable from one allocation.
    struct TagAll<'a> {
        /// The set of allocations already visited.
        visited: &'a mut HashSet<AllocationId>,
    }

    impl Visitor for TagAll<'_> {
        fn visit_sync<T>(&mut self, gc: &Gc<T>)
        where
            T: Collectable + Sync + ?Sized,
        {
            let tagged_ptr = UnsafeCell::raw_get(&gc.0);
            let tagged = unsafe { *tagged_ptr };
            unsafe { tagged_ptr.write(tagged.with_tag(true)) };
            let box_ref = unsafe { tagged.as_ref() };
            if self.visited.insert(AllocationId::from(box_ref)) {
                let _ = box_ref.value.accept(self);
            }
        }

        fn visit_unsync<T>(&mut self, _: &crate::unsync::Gc<T>)
        where
            T: Collectable + ?Sized,
        {
            unreachable!()
        }
    }

    let box_ref = unsafe { ptr.specify::<GcBox<T>>().as_ref() };
    if visited.insert(AllocationId::from(box_ref)) {
        let _ = box_ref.value.accept(&mut TagAll { visited });
    }
}

/// Build out a part of the reference graph, making note of all allocations which are reachable from
/// the one described in `ptr`.
///
/// # Inputs
///
/// - `ptr`: A pointer to the allocation that we should start constructing from.
/// - `ref_graph`: A lookup from allocation IDs to node information about that allocation.
///
/// # Effects
///
/// `ref_graph` will be expanded to include all allocations reachable from `ptr`.
///
/// # Safety
///
/// `ptr` must have been created as a pointer to a `GcBox<T>`.
unsafe fn dfs<T: Collectable + Sync + ?Sized>(
    ptr: ErasedPtr,
    ref_graph: &mut HashMap<AllocationId, AllocationInfo>,
) {
    let box_ref = unsafe { ptr.specify::<GcBox<T>>().as_ref() };
    let starting_id = AllocationId::from(box_ref);
    let Entry::Vacant(v) = ref_graph.entry(starting_id) else {
        // the weak count was incremented by another DFS operation elsewhere.
        // Decrement it to have only one from us.
        box_ref.weak.fetch_sub(1, Ordering::Relaxed);
        return;
    };
    let strong_count = box_ref.strong.load(Ordering::Acquire);
    let generation = box_ref.generation.load(Ordering::Acquire);
    v.insert(AllocationInfo {
        ptr,
        weak_drop_fn: drop_weak_zero::<T>,
        reachability: Reachability::Unknown {
            children: Vec::new(),
            n_unaccounted: strong_count,
            generation,
            destroy_fn: destroy_erased::<T>,
        },
    });

    if box_ref
        .value
        .accept(&mut Dfs {
            ref_graph,
            current_id: starting_id,
        })
        .is_err()
    {
        // box_ref.value was accessed while we worked
        // mark this allocation as reachable
        mark(starting_id, ref_graph);
    }
}

#[derive(Debug)]
/// The visitor structure used for building the found-reference-graph of allocations.
struct Dfs<'a> {
    /// The reference graph.
    /// Each allocation is assigned a node.
    ref_graph: &'a mut HashMap<AllocationId, AllocationInfo>,
    /// The allocation ID currently being visited.
    /// Used for knowing which node is the parent of another.
    current_id: AllocationId,
}

impl<'a> Visitor for Dfs<'a> {
    fn visit_sync<T>(&mut self, gc: &Gc<T>)
    where
        T: Collectable + Sync + ?Sized,
    {
        let tagged_ptr = UnsafeCell::raw_get(&gc.0);
        let tagged = unsafe { *tagged_ptr };
        let box_ref = unsafe { tagged.as_ref() };
        unsafe {
            *tagged_ptr = tagged.with_tag(false);
        }

        let mut new_id = AllocationId::from(box_ref);
        if !tagged.tagged() {
            // This pointer is tagged, so the allocation containing it must be accessible. Mark!
            mark(self.current_id, self.ref_graph);
            return;
        }

        let Reachability::Unknown {
            ref mut children, ..
        } = self
            .ref_graph
            .get_mut(&self.current_id)
            .unwrap()
            .reachability
        else {
            // this node has been proven reachable by something higher up. No need to keep building
            // its ref graph
            return;
        };
        children.push(new_id);

        match self.ref_graph.entry(new_id) {
            Entry::Occupied(mut o) => match o.get_mut().reachability {
                Reachability::Unknown {
                    ref mut n_unaccounted,
                    generation,
                    ..
                } => {
                    if generation == box_ref.generation.load(Ordering::Acquire) {
                        *n_unaccounted -= 1;
                    } else {
                        // generation has changed under our feet
                        // that means it's reachable
                        let Reachability::Unknown { children, .. } =
                            replace(&mut o.get_mut().reachability, Reachability::Reachable)
                        else {
                            unreachable!();
                        };
                        for child in children {
                            mark(child, self.ref_graph);
                        }
                    }
                }
                Reachability::Reachable => (),
            },
            Entry::Vacant(v) => {
                // This allocation has never been visited by the reference graph builder
                let strong_count = box_ref.strong.load(Ordering::Acquire);
                let generation = box_ref.generation.load(Ordering::Acquire);
                box_ref.weak.fetch_add(1, Ordering::Acquire);
                v.insert(AllocationInfo {
                    ptr: ErasedPtr::new(unsafe { (*gc.0.get()).as_nonnull() }),
                    weak_drop_fn: drop_weak_zero::<T>,
                    reachability: Reachability::Unknown {
                        children: Vec::new(),
                        n_unaccounted: strong_count - 1,
                        generation,
                        destroy_fn: destroy_erased::<T>,
                    },
                });

                // Save the previously visited ID, then carry on to the next one
                swap(&mut new_id, &mut self.current_id);

                if box_ref.value.accept(self).is_err() {
                    // On failure, this means `**gc` is accessible, and should be marked
                    // as such
                    mark(new_id, self.ref_graph);
                }

                // Restore current_id and carry on
                swap(&mut new_id, &mut self.current_id);
            }
        };
    }

    fn visit_unsync<T>(&mut self, _: &crate::unsync::Gc<T>)
    where
        T: Collectable + ?Sized,
    {
        unreachable!("sync Gc cannot own an unsync Gc");
    }
}

/// Traverse the reference graph, marking `root` and any allocations reachable from `root` as
/// reachable.
fn mark(root: AllocationId, graph: &mut HashMap<AllocationId, AllocationInfo>) {
    let node = graph.get_mut(&root).unwrap();
    if let Reachability::Unknown { children, .. } =
        replace(&mut node.reachability, Reachability::Reachable)
    {
        for child in children {
            mark(child, graph);
        }
    }
}

/// Destroy an allocation, obliterating its GCs, dropping it, and deallocating it.
///
/// # Safety
///
/// `ptr` must have been created from a pointer to a `GcBox<T>`.
unsafe fn destroy_erased<T: Collectable + Sync + ?Sized>(
    ptr: ErasedPtr,
    graph: &HashMap<AllocationId, AllocationInfo>,
) {
    /// A visitor for decrementing the reference count of pointees.
    struct DecrementOutboundReferenceCounts<'a> {
        /// The reference graph.
        /// Must have been populated with reachabiltiy already.
        graph: &'a HashMap<AllocationId, AllocationInfo>,
    }

    impl Visitor for DecrementOutboundReferenceCounts<'_> {
        fn visit_sync<T>(&mut self, gc: &crate::sync::Gc<T>)
        where
            T: Collectable + Sync + ?Sized,
        {
            let id = AllocationId::from(unsafe { (*UnsafeCell::raw_get(&gc.0)).as_nonnull() });
            if matches!(self.graph[&id].reachability, Reachability::Reachable) {
                unsafe {
                    id.0.as_ref().strong.fetch_sub(1, Ordering::Relaxed);
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

    let specified = ptr.specify::<GcBox<T>>().as_mut();
    specified
        .value
        .accept(&mut DecrementOutboundReferenceCounts { graph })
        .expect("allocation assumed to be unreachable but somehow was accessed");
    let layout = Layout::for_value(specified);
    drop_in_place(specified);
    dealloc((specified as *mut GcBox<T>).cast(), layout);
}

/// Function for handling dropping an allocation when its weak and strong reference count reach
/// zero.
///
/// # Safety
///
/// `ptr` must have been created as a pointer to a `GcBox<T>`.
unsafe fn drop_weak_zero<T: Collectable + Sync + ?Sized>(ptr: ErasedPtr) {
    let mut specified = ptr.specify::<GcBox<T>>();
    assert!(specified.as_ref().weak.load(Ordering::Relaxed) == 0);

    let layout = Layout::for_value(specified.as_ref());
    drop_in_place(specified.as_mut());
    dealloc(specified.as_ptr().cast(), layout);
}

unsafe impl Send for AllocationId {}
unsafe impl Sync for AllocationId {}

impl<T> From<&GcBox<T>> for AllocationId
where
    T: Collectable + Sync + ?Sized,
{
    fn from(value: &GcBox<T>) -> Self {
        AllocationId(NonNull::from(value).cast())
    }
}

impl<T> From<NonNull<GcBox<T>>> for AllocationId
where
    T: Collectable + Sync + ?Sized,
{
    fn from(value: NonNull<GcBox<T>>) -> Self {
        AllocationId(value.cast())
    }
}

impl Drop for Dumpster {
    fn drop(&mut self) {
        self.deliver_to(&GARBAGE_TRUCK);
        // collect_all();
    }
}

impl Drop for GarbageTruck {
    fn drop(&mut self) {
        GARBAGE_TRUCK.collect_all();
    }
}
