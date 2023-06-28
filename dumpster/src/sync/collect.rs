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
    num::NonZeroUsize,
    ptr::NonNull,
    sync::{
        atomic::{AtomicUsize, Ordering},
        LazyLock, Mutex,
    },
};

use crate::{Collectable, OpaquePtr};

use super::GcBox;

pub(super) static DUMPSTER: LazyLock<Dumpster> = LazyLock::new(|| Dumpster {
    to_clean: Mutex::new(HashMap::new()),
    n_gcs_dropped: AtomicUsize::new(0),
    n_gcs_existing: AtomicUsize::new(0),
});

pub(super) struct Dumpster {
    to_clean: Mutex<HashMap<AllocationId, Cleanup>>,
    n_gcs_dropped: AtomicUsize,
    n_gcs_existing: AtomicUsize,
}

struct AllocationId(NonNull<Mutex<usize>>);

unsafe impl Send for AllocationId {}
unsafe impl Sync for AllocationId {}

struct Cleanup {
    ptr: OpaquePtr,
}

struct Node {
    children: Vec<AllocationId>,
    true_ref_count: NonZeroUsize,
    found_ref_count: usize,
    ptr: OpaquePtr,
}

struct BuildRefGraph {
    ref_graph: HashMap<AllocationId, Node>,
}

impl Dumpster {
    pub fn collect_all(&self) {
        let mut to_clean = self.to_clean.lock().unwrap();
    }

    pub fn notify_dropped_gc(&self) {
        self.n_gcs_dropped.fetch_add(1, Ordering::Relaxed);
        self.n_gcs_existing.fetch_sub(1, Ordering::Relaxed);

        todo!("logic for determining whether to sweep");
    }

    pub fn notify_created_gc(&self) {
        self.n_gcs_existing.fetch_add(1, Ordering::Relaxed);
    }

    pub fn mark_dirty<T>(&self, allocation: NonNull<GcBox<T>>)
    where
        T: Collectable + Sync + ?Sized,
    {
    }
}
