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
    collections::{hash_map::Entry, HashMap},
    mem::{replace, swap, take},
    num::NonZeroUsize,
    ptr::{drop_in_place, NonNull},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Mutex, MutexGuard, RwLock, TryLockError,
    },
};

use chashmap::CHashMap;

use once_cell::sync::Lazy;

use crate::{Collectable, OpaquePtr, Visitor};

use super::{DestroyGcs, Gc, GcBox};

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
struct AllocationId(NonNull<Mutex<NonZeroUsize>>);

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
    &mut HashMap<AllocationId, MutexGuard<'static, NonZeroUsize>>,
);

struct Cleanup {
    ptr: OpaquePtr,
    build_fn: BuildFn,
}

#[derive(Debug)]
enum Node {
    Unknown {
        children: Vec<AllocationId>,
        n_unaccounted: usize,
        destroy_fn: unsafe fn(OpaquePtr),
        ptr: OpaquePtr,
    },
    Reachable,
}

impl Dumpster {
    /// Search through the set of existing allocations which have been marked inacessible, and see
    /// if they are inaccessible.
    /// If so, drop those allocations.
    pub fn collect_all(&self) {
        let to_collect = take(&mut *self.to_clean.write().unwrap());
        let mut ref_graph = HashMap::new();
        let mut guards = HashMap::new();

        for (id, cleanup) in to_collect {
            unsafe { (cleanup.build_fn)(cleanup.ptr, id, &mut ref_graph, &mut guards) };
        }

        drop(guards);
        println!("{ref_graph:#?}");
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

        for (destroy_fn, ptr) in ref_graph.into_iter().filter_map(|(_, v)| match v {
            Node::Reachable => None,
            Node::Unknown {
                destroy_fn, ptr, ..
            } => Some((destroy_fn, ptr)),
        }) {
            unsafe { destroy_fn(ptr) };
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
    guards: &mut HashMap<AllocationId, MutexGuard<'static, NonZeroUsize>>,
) {
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
        guards: &'a mut HashMap<AllocationId, MutexGuard<'static, NonZeroUsize>>,
    }

    impl<'a> Visitor for BuildRefGraph<'a> {
        fn visit_sync<T>(&mut self, gc: &Gc<T>) -> Result<(), ()>
        where
            T: Collectable + Sync + ?Sized,
        {
            let mut new_id = AllocationId::from(gc.ptr.unwrap());
            println!("visit {new_id:?}");
            let Some(Node::Unknown {
                ref mut children, ..
            }) = self.ref_graph.get_mut(&self.current_id)
            else {
                panic!("prior node does not exist");
            };
            children.push(new_id);

            match self.ref_graph.entry(new_id) {
                Entry::Occupied(mut o) => {
                    println!("find another reference to {new_id:?}");
                    match o.get_mut() {
                        Node::Reachable => (),
                        Node::Unknown {
                            ref mut n_unaccounted,
                            ..
                        } => {
                            *n_unaccounted -= 1;
                        }
                    }
                }
                Entry::Vacant(v) => {
                    // This allocation has never been visited by the reference graph builder.
                    // Attempt to acquire its lock.
                    match unsafe { new_id.0.as_ref().try_lock() } {
                        Ok(guard) => {
                            // This allocation is not currently being inspected by anything else and
                            // is therefore of unknown reachability.

                            let _ = v.insert(Node::Unknown {
                                children: Vec::new(),
                                n_unaccounted: guard.get() - 1,
                                destroy_fn: destroy_opaque::<T>,
                                ptr: OpaquePtr::new(gc.ptr.unwrap()),
                            });
                            self.guards.insert(new_id, guard);

                            // Save the previously visited ID, then carry on to the next one
                            swap(&mut new_id, &mut self.current_id);

                            // TODO: on failure of acceptance, overwrite new_entry and sweep from it
                            (**gc).accept(self).unwrap();

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

            Ok(())
        }

        fn visit_unsync<T>(&mut self, _: &crate::unsync::Gc<T>) -> Result<(), ()>
        where
            T: Collectable + ?Sized,
        {
            panic!("A `dumpster::sync::Gc` may not own a `dumpster::unsync::Gc` because `dumpster::unsync::Gc` is `Sync`");
        }
    }

    if let Entry::Vacant(v) = ref_graph.entry(starting_id) {
        println!("begin a search from {starting_id:?}, create entry");
        match unsafe { starting_id.0.as_ref().try_lock() } {
            Ok(guard) => {
                v.insert(Node::Unknown {
                    children: Vec::new(),
                    n_unaccounted: guard.get(),
                    destroy_fn: destroy_opaque::<T>,
                    ptr,
                });
                guards.insert(starting_id, guard);

                ptr.specify::<GcBox<T>>()
                    .as_ref()
                    .value
                    .accept(&mut BuildRefGraph {
                        ref_graph,
                        current_id: starting_id,
                        guards,
                    })
                    .unwrap();
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
    specified.value.destroy_gcs(&mut DestroyGcs);
    let layout = Layout::for_value(specified);
    drop_in_place(specified);
    dealloc((specified as *mut GcBox<T>).cast(), layout);
}
