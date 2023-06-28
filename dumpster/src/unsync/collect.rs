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
    cell::{Cell, RefCell},
    collections::{hash_map::Entry, HashMap, HashSet},
    num::NonZeroUsize,
    ops::Deref,
    ptr::{addr_of_mut, drop_in_place, NonNull},
};

use crate::{unsync::Gc, Collectable, Destroyer, OpaquePtr, Visitor};

use super::GcBox;

thread_local! {
    /// The global collection of allocation information for this thread.
    pub static DUMPSTER: Dumpster = Dumpster {
        to_collect: RefCell::new(HashMap::new()),
        n_ref_drops: Cell::new(0),
        n_refs_living: Cell::new(0),
    };
}

/// A dumpster is a collection of all the garbage that may or may not need to be cleaned up.
/// It also contains information relevant to when a sweep should be triggered.
pub struct Dumpster {
    /// A map from allocation IDs for allocations which may need to be collected to pointers to
    /// their allocations.
    to_collect: RefCell<HashMap<AllocationId, Cleanup>>,
    /// The number of times a reference has been dropped since the last collection was triggered.
    pub n_ref_drops: Cell<usize>,
    /// The number of references that currently exist in the entire heap and stack.
    pub n_refs_living: Cell<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A unique identifier for an allocated garbage-collected block.
///
/// It contains a pointer to the reference count of the allocation.
struct AllocationId(pub NonNull<Cell<usize>>);

impl AllocationId {
    unsafe fn count(self) -> usize {
        self.0.as_ref().get()
    }
}

impl <T> From<NonNull<GcBox<T>>> for AllocationId where T: Collectable + ?Sized {
    fn from(value: NonNull<GcBox<T>>) -> Self {
        AllocationId(value.cast())
    }
}

#[derive(Debug)]
/// The necessary information required to collect some garbage-collected data.
/// This data is stored in a map from allocation IDs to the necessary cleanup operation.
struct Cleanup {
    build_graph_fn: unsafe fn(OpaquePtr, &mut BuildRefGraph),
    sweep_fn: unsafe fn(OpaquePtr, &mut Sweep),
    destroy_gcs_fn: unsafe fn(OpaquePtr, &mut DestroyGcs),
    ptr: OpaquePtr,
}

impl Cleanup {
    fn new<T: Collectable + ?Sized>(box_ptr: NonNull<GcBox<T>>) -> Cleanup {
        Cleanup {
            build_graph_fn: apply_visitor::<T, BuildRefGraph>,
            sweep_fn: apply_visitor::<T, Sweep>,
            destroy_gcs_fn: destroy_gcs::<T>,
            ptr: OpaquePtr::new(box_ptr),
        }
    }
}

unsafe fn apply_visitor<T: Collectable + ?Sized, V: Visitor>(ptr: OpaquePtr, visitor: &mut V) {
    let specified: NonNull<GcBox<T>> = ptr.specify();
    specified.as_ref().value.accept(visitor);
}

unsafe fn destroy_gcs<T: Collectable + ?Sized>(ptr: OpaquePtr, destroyer: &mut DestroyGcs) {
    let mut specific_ptr = ptr.specify::<GcBox<T>>();
    specific_ptr.as_mut().ref_count.set(0);
    specific_ptr.as_mut().value.destroy_gcs(destroyer);

    destroyer.collection_queue.push((
        specific_ptr.as_ptr().cast(),
        Layout::for_value(specific_ptr.as_ref()),
    ));
    drop_in_place(addr_of_mut!(specific_ptr.as_mut().value));
}

impl Dumpster {
    /// Collect all unreachable allocations that this dumpster is responsible for.
    pub fn collect_all(&self) {
        self.n_ref_drops.set(0);

        unsafe {
            let mut ref_graph_build = BuildRefGraph {
                visited: HashSet::new(),
                ref_state: HashMap::new(),
            };

            println!("building ref graph");
            for (k, v) in self.to_collect.borrow().iter() {
                if !ref_graph_build.visited.contains(k) {
                    ref_graph_build.visited.insert(*k);
                    (v.build_graph_fn)(v.ptr, &mut ref_graph_build);
                }
            }
            println!("found references: {:?}", ref_graph_build.ref_state);
            for (id, count) in ref_graph_build
                .ref_state
                .keys()
                .map(|id| (id, id.count()))
            {
                println!("true count for {:?}: {count}", id.0);
            }

            let mut sweep = Sweep {
                visited: HashSet::new(),
            };
            for (id, reachability) in
                ref_graph_build
                    .ref_state
                    .iter()
                    .filter(|(id, reachability)| {
                        id.count() != reachability.cyclic_ref_count.into()
                    })
            {
                sweep.visited.insert(*id);
                println!("id {id:?} is proven a root");
                (reachability.sweep_fn)(reachability.ptr, &mut sweep);
            }

            // any allocations which we didn't find must also be roots
            for (id, cleanup) in self
                .to_collect
                .borrow()
                .iter()
                .filter(|(id, _)| !ref_graph_build.ref_state.contains_key(id))
            {
                println!("id {:?} not found - must be root", cleanup.ptr);
                sweep.visited.insert(*id);
                (cleanup.sweep_fn)(cleanup.ptr, &mut sweep);
            }

            println!("reachable: {:?}", sweep.visited);

            let mut destroy = DestroyGcs {
                visited: HashSet::new(),
                collection_queue: Vec::new(),
                reachable: sweep.visited,
            };
            // any allocation not found in the sweep must be freed
            for (id, cleanup) in self.to_collect.borrow_mut().drain() {
                if !destroy.reachable.contains(&id) && destroy.visited.insert(id) {
                    (cleanup.destroy_gcs_fn)(cleanup.ptr, &mut destroy);
                }
            }

            for (ptr, layout) in destroy.collection_queue {
                dealloc(ptr, layout);
            }
        }
    }

    /// Mark an allocation as "dirty," implying that it may need to be swept through later to find
    /// out if it has any references pointing to it.
    pub(super) unsafe fn mark_dirty<T: Collectable + ?Sized>(&self, box_ptr: NonNull<GcBox<T>>) {
        println!("mark {:?} as dirty", std::ptr::addr_of!(*box_ptr.as_ref()));
        self.to_collect
            .borrow_mut()
            .entry(AllocationId::from(box_ptr))
            .or_insert_with(|| Cleanup::new(box_ptr));
    }

    /// Mark an allocation as "cleaned," implying that the allocation is about to be destroyed and
    /// therefore should not be cleaned up later.
    pub(super) fn mark_cleaned<T: Collectable + ?Sized>(&self, box_ptr: NonNull<GcBox<T>>) {
        println!("mark {box_ptr:?} as cleaned");
        self.to_collect.borrow_mut().remove(&AllocationId::from(box_ptr));
    }
}

impl Drop for Dumpster {
    fn drop(&mut self) {
        // cleanup any leftover allocations
        self.collect_all();
    }
}

struct BuildRefGraph {
    visited: HashSet<AllocationId>,
    ref_state: HashMap<AllocationId, Reachability>,
}

#[derive(Debug)]
struct Reachability {
    cyclic_ref_count: NonZeroUsize,
    ptr: OpaquePtr,
    sweep_fn: unsafe fn(OpaquePtr, &mut Sweep),
}

impl Visitor for BuildRefGraph {
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
        let next_id = AllocationId::from(gc.ptr.unwrap());
        match self.ref_state.entry(next_id) {
            Entry::Occupied(ref mut o) => {
                o.get_mut().cyclic_ref_count = o.get().cyclic_ref_count.saturating_add(1);
            }
            Entry::Vacant(v) => {
                v.insert(Reachability {
                    cyclic_ref_count: NonZeroUsize::MIN,
                    ptr: OpaquePtr::new(NonNull::from(gc)),
                    sweep_fn: apply_visitor::<T, Sweep>,
                });
            }
        }
        if self.visited.insert(next_id) {
            gc.deref().accept(self);
        }
    }
}

struct Sweep {
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
        println!("visit unsync id {:?}", AllocationId::from(gc.ptr.unwrap()));
        if self.visited.insert(AllocationId::from(gc.ptr.unwrap())) {
            gc.deref().accept(self);
        }
    }
}

struct DestroyGcs {
    visited: HashSet<AllocationId>,
    collection_queue: Vec<(*mut u8, Layout)>,
    reachable: HashSet<AllocationId>,
}

impl Destroyer for DestroyGcs {
    fn visit_sync<T>(&mut self, _: &mut crate::sync::Gc<T>)
    where
        T: Collectable + Sync + ?Sized,
    {
        // because `Gc` is `!Sync`, we know we won't find a `Gc` this way and can return
        // immediately.
    }

    fn visit_unsync<T>(&mut self, gc: &mut Gc<T>)
    where
        T: Collectable + ?Sized,
    {
        unsafe {
            if let Some(mut p) = gc.ptr {
                let id = AllocationId::from(p);
                gc.ptr = None;
                if !self.reachable.contains(&id) && self.visited.insert(id) {
                    p.as_mut().ref_count.set(0);
                    p.as_mut().value.destroy_gcs(self);
                    self.collection_queue
                        .push((p.as_ptr().cast(), dbg!(Layout::for_value(p.as_ref()))));
                    drop_in_place(addr_of_mut!(p.as_mut().value));
                }
            }
        }
    }
}
