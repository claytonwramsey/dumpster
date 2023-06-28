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

use std::{ptr::NonNull, sync::{Mutex, LazyLock}, collections::HashMap, num::NonZeroUsize};

use crate::OpaquePtr;

pub(super) static DUMPSTER: LazyLock<Dumpster> = LazyLock::new(|| Dumpster {
    to_clean: Mutex::new(HashMap::new()),
});

pub(super) struct Dumpster {
    to_clean: Mutex<HashMap<AllocationId, Cleanup>>,
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
}