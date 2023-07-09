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
    collections::{hash_map::Entry, HashMap, HashSet},
    mem::{swap, take},
    num::NonZeroUsize,
    ptr::{drop_in_place, NonNull},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Mutex, MutexGuard, RwLock,
    },
};

use chashmap::CHashMap;

use once_cell::sync::Lazy;

use crate::{Collectable, Destroyer, OpaquePtr, Visitor};

use super::{Gc, GcBox};

/// The global collection of allocations to clean up.
// wishing dreams: chashmap gets a const new function so that we can remove the once cell
pub(super) static DUMPSTER: Dumpster = Dumpster {
    to_clean: Lazy::new(|| RwLock::new(CHashMap::new())),
    n_gcs_dropped: AtomicUsize::new(0),
    n_gcs_existing: AtomicUsize::new(0),
};

pub(super) struct Dumpster {
    to_clean: Lazy<RwLock<CHashMap<AllocationId, Cleanup>>>,
    n_gcs_dropped: AtomicUsize,
    n_gcs_existing: AtomicUsize,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
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

type BuildFn = unsafe fn(
    OpaquePtr,
    AllocationId,
    &mut HashMap<AllocationId, Node>,
    &mut Vec<MutexGuard<'static, usize>>,
);

struct Cleanup {
    ptr: OpaquePtr,
    build_fn: BuildFn,
}

#[derive(Debug)]
struct Node {
    children: Vec<AllocationId>,
    true_ref_count: NonZeroUsize,
    found_ref_count: usize,
    destroy_fn: unsafe fn(OpaquePtr),
    ptr: OpaquePtr,
}

impl Dumpster {
    /// Search through the set of existing allocations which have been marked inacessible, and see
    /// if they are inaccessible.
    /// If so, drop those allocations.
    pub fn collect_all(&self) {
        let to_collect = take(&mut *self.to_clean.write().unwrap());
        let mut ref_graph = HashMap::new();
        let mut guards = Vec::new();

        for (id, cleanup) in to_collect {
            unsafe { (cleanup.build_fn)(cleanup.ptr, id, &mut ref_graph, &mut guards) };
        }

        drop(guards);
        println!("{ref_graph:?}");

        let mut reachable = HashSet::new();
        for &root_id in ref_graph
            .iter()
            .filter_map(|(k, v)| (v.true_ref_count.get() != v.found_ref_count).then_some(k))
        {
            sweep(root_id, &ref_graph, &mut reachable);
        }

        for node in ref_graph
            .into_iter()
            .filter_map(|(k, v)| (!reachable.contains(&k)).then_some(v))
        {
            unsafe { (node.destroy_fn)(node.ptr) };
        }
    }

    /// Notify this dumpster that a `Gc` was destroyed, and update the tracking count for the number
    /// of dropped and existing `Gc`s.
    ///
    /// This may trigger a linear-time cleanup of all allocations, but this will be guaranteed to
    /// occur with less-than-linear frequency, so it's always O(1).
    pub fn notify_dropped_gc(&self) {
        let prev_gcs_dropped = self.n_gcs_dropped.fetch_add(1, Ordering::Relaxed);
        let prev_gcs_existing = self.n_gcs_existing.fetch_sub(1, Ordering::Relaxed);

        if prev_gcs_dropped >= prev_gcs_existing >> 1 {
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

unsafe fn build_ref_graph<T: Collectable + Sync + ?Sized>(
    ptr: OpaquePtr,
    starting_id: AllocationId,
    ref_graph: &mut HashMap<AllocationId, Node>,
    guards: &mut Vec<MutexGuard<'static, usize>>,
) {
    #[derive(Debug)]
    /// The visitor structure used for building the found-reference-graph of allocations.
    struct BuildRefGraph<'a> {
        /// The reference graph.
        /// Each allocation is assigned a node.
        ref_graph: &'a mut HashMap<AllocationId, Node>,
        /// The allocation ID currently being visited.
        ///
        /// At the start of the graph-building process, `current_id` is `None`.
        /// However, as we depth-first-search through the graph, we keep track of what allocation
        /// we most recently visited so that we can correctly mark the children of a node.
        current_id: AllocationId,
        /// The currently-held mutex guards as we construct graph.
        /// Immediately after we finish our search, we should clear this vector to let other
        /// threads get back to their work.
        ///
        /// Although these guards have `'static` lifetime as declared, this is a workaround because
        /// our allocations' lifetimes interact poorly under the hood with Rust's lifetime
        /// system. These guards must be dropped _before_ we start dropping allocations to
        /// prevent disaster.
        guards: &'a mut Vec<MutexGuard<'static, usize>>,
    }

    impl<'a> Visitor for BuildRefGraph<'a> {
        fn visit_sync<T>(&mut self, gc: &Gc<T>)
        where
            T: Collectable + Sync + ?Sized,
        {
            let mut new_id = AllocationId::from(gc.ptr.unwrap());
            self.ref_graph
                .get_mut(&self.current_id)
                .unwrap()
                .children
                .push(new_id);

            match self.ref_graph.entry(new_id) {
                Entry::Occupied(mut o) => {
                    o.get_mut().found_ref_count += 1;
                }
                Entry::Vacant(v) => {
                    let guard = unsafe { new_id.0.as_ref().lock().unwrap() };
                    let true_ref_count = NonZeroUsize::new(*guard).unwrap();
                    self.guards.push(guard);
                    v.insert(Node {
                        children: Vec::new(),
                        true_ref_count,
                        found_ref_count: 1,
                        destroy_fn: destroy_gcs::<T>,
                        ptr: OpaquePtr::new(gc.ptr.unwrap()),
                    });

                    // Save the previously visited ID, then carry on to the next one
                    swap(&mut new_id, &mut self.current_id);

                    (*gc).accept(self);

                    // Restore current_id and carry on
                    swap(&mut new_id, &mut self.current_id);
                }
            }
        }

        fn visit_unsync<T>(&mut self, _: &crate::unsync::Gc<T>)
        where
            T: Collectable + ?Sized,
        {
            panic!("A `dumpster::sync::Gc` may not own a `dumpster::unsync::Gc` because `dumpster::unsync::Gc` is `Sync`");
        }
    }

    if let Entry::Vacant(v) = ref_graph.entry(starting_id) {
        let guard = unsafe { starting_id.0.as_ref().lock().unwrap() };

        v.insert(Node {
            children: Vec::new(),
            found_ref_count: 0,
            true_ref_count: NonZeroUsize::new(*guard).unwrap(),
            destroy_fn: destroy_gcs::<T>,
            ptr,
        });

        guards.push(guard);
    }

    ptr.specify::<GcBox<T>>()
        .as_ref()
        .value
        .accept(&mut BuildRefGraph {
            ref_graph,
            current_id: starting_id,
            guards,
        });
}

fn sweep(
    root: AllocationId,
    graph: &HashMap<AllocationId, Node>,
    reachable: &mut HashSet<AllocationId>,
) {
    if reachable.insert(root) {
        graph[&root]
            .children
            .iter()
            .for_each(|&rt| sweep(rt, graph, reachable));
    }
}

/// Destroy all `Gc`s owned by a value.
///
/// # Safety
///
/// `ptr` must have been created from a pointer to a `GcBox<T>`.
unsafe fn destroy_gcs<T: Collectable + Sync + ?Sized>(ptr: OpaquePtr) {
    struct DestroyGcs;

    impl Destroyer for DestroyGcs {
        fn visit_sync<T>(&mut self, gc: &mut Gc<T>)
        where
            T: Collectable + Sync + ?Sized,
        {
            gc.ptr = None;
        }

        fn visit_unsync<T>(&mut self, _: &mut crate::unsync::Gc<T>)
        where
            T: Collectable + ?Sized,
        {
            panic!("A `dumpster::sync::Gc` may not own a `dumpster::unsync::Gc` because `dumpster::unsync::Gc` is `Sync`");
        }
    }

    let specified = ptr.specify::<GcBox<T>>().as_mut();
    specified.value.destroy_gcs(&mut DestroyGcs);
    let layout = Layout::for_value(specified);
    drop_in_place(specified);
    dealloc((specified as *mut GcBox<T>).cast(), layout);
}
