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
    collections::HashMap,
    mem::swap,
    num::NonZeroUsize,
    ptr::NonNull,
    sync::{
        atomic::{AtomicPtr, AtomicUsize, Ordering},
        Mutex, MutexGuard,
    },
};

use chashmap::CHashMap;

use once_cell::sync::Lazy;

use crate::{Collectable, OpaquePtr, Visitor};

use super::{Gc, GcBox};

/// The global collection of allocations to clean up.
// wishing dreams: chashmap gets a const new function so that we can remove the once cell
pub(super) static DUMPSTER: Dumpster = Dumpster {
    to_clean: Lazy::new(|| AtomicPtr::new(Box::into_raw(Box::new(CHashMap::new())))),
    n_gcs_dropped: AtomicUsize::new(0),
    n_gcs_existing: AtomicUsize::new(0),
};

pub(super) struct Dumpster {
    to_clean: Lazy<AtomicPtr<CHashMap<AllocationId, Cleanup>>>,
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

struct Cleanup {
    ptr: OpaquePtr,
}

struct Node {
    children: Vec<AllocationId>,
    true_ref_count: NonZeroUsize,
    found_ref_count: usize,
    ptr: OpaquePtr,
}

/// The visitor structure used for building the found-reference-graph of allocations.
struct BuildRefGraph {
    /// The reference graph.
    /// Each allocation is assigned a node.
    ref_graph: HashMap<AllocationId, Node>,
    /// The allocation ID currently being visited.
    ///
    /// At the start of the graph-building process, `current_id` is `None`.
    /// However, as we depth-first-search through the graph, we keep track of what allocation we
    /// most recently visited so that we can correctly mark the children of a node.
    current_id: Option<AllocationId>,
    /// The currently-held mutex guards as we construct graph.
    /// Immediately after we finish our search, we should clear this vector to let other threads
    /// get back to their work.
    ///
    /// Although these guards have `'static` lifetime as declared, this is a workaround because our
    /// allocations' lifetimes interact poorly under the hood with Rust's lifetime system.
    /// These guards must be dropped _before_ we start dropping allocations to prevent disaster.
    guards: Vec<MutexGuard<'static, usize>>,
}

impl Dumpster {
    /// Search through the set of existing allocations which have been marked inacessible, and see
    /// if they are inaccessible.
    /// If so, drop those allocations.
    pub fn collect_all(&self) {
        let mut brg = BuildRefGraph {
            ref_graph: HashMap::new(),
            current_id: None,
            guards: Vec::new(),
        };
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
        unsafe {
            self.to_clean
                .load(Ordering::Relaxed)
                .as_ref()
                .unwrap()
                .insert(AllocationId::from(allocation), Cleanup::new(allocation));
        }
    }

    /// Mark an allocation as "clean," implying that it has already been cleaned up and does not
    /// need to be cleaned again.
    pub fn mark_clean<T>(&self, allocation: NonNull<GcBox<T>>)
    where
        T: Collectable + Sync + ?Sized,
    {
        unsafe {
            self.to_clean
                .load(Ordering::Relaxed)
                .as_ref()
                .unwrap()
                .remove(&AllocationId::from(allocation));
        }
    }
}

impl Cleanup {
    fn new<T>(ptr: NonNull<GcBox<T>>) -> Cleanup
    where
        T: Collectable + Sync + ?Sized,
    {
        Cleanup {
            ptr: OpaquePtr::new(ptr),
        }
    }
}

impl Visitor for BuildRefGraph {
    fn visit_sync<T>(&mut self, gc: &Gc<T>)
    where
        T: Collectable + Sync + ?Sized,
    {
        let mut new_id = AllocationId::from(gc.ptr.unwrap());
        self.ref_graph
            .get_mut(&self.current_id.unwrap())
            .unwrap()
            .children
            .push(new_id);

        self.ref_graph.entry(new_id).or_insert_with(|| {
            let guard = unsafe { new_id.0.as_ref().lock().unwrap() };
            let true_ref_count = NonZeroUsize::new(*guard).unwrap();
            self.guards.push(guard);
            Node {
                children: Vec::new(),
                true_ref_count,
                found_ref_count: 1,
                ptr: OpaquePtr::new(gc.ptr.unwrap()),
            }
        });

        // Save the previously visited ID, then carry on to the next one
        swap(&mut new_id, self.current_id.as_mut().unwrap());

        // Restore current_id and carry on
        swap(&mut new_id, self.current_id.as_mut().unwrap());
    }

    fn visit_unsync<T>(&mut self, _: &crate::unsync::Gc<T>)
    where
        T: Collectable + ?Sized,
    {
        panic!("A `dumpster::sync::Gc` may not own a `dumpster::unsync::Gc` because `dumpster::unsync::Gc` is `Sync`");
    }
}
