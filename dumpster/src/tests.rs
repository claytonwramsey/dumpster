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

//! Simple tests using manual implementations of [`Collectable`].

use super::*;
use std::{
    cell::RefCell,
    sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering},
};

#[test]
/// Test a simple data structure
fn simple() {
    static DROPPED: AtomicBool = AtomicBool::new(false);
    struct Foo(u8);

    impl Drop for Foo {
        fn drop(&mut self) {
            DROPPED.store(true, Ordering::Relaxed);
        }
    }

    unsafe impl Collectable for Foo {
        fn add_to_ref_graph(&self, _: &mut RefGraph) {}
        fn sweep(&self, _: bool, _: &mut RefGraph) {}
        unsafe fn destroy_gcs(&mut self, _: &mut RefGraph) {}
    }

    let gc1 = Gc::new(Foo(1));
    let gc2 = Gc::clone(&gc1);

    assert!(!DROPPED.load(Ordering::Relaxed));

    drop(gc1);

    assert!(!DROPPED.load(Ordering::Relaxed));

    drop(gc2);

    assert!(DROPPED.load(Ordering::Relaxed));
}

#[derive(Debug)]
struct MultiRef<'a> {
    refs: RefCell<Vec<Gc<MultiRef<'a>>>>,
    drop_count: &'a AtomicUsize,
}

unsafe impl Collectable for MultiRef<'_> {
    fn add_to_ref_graph(&self, ref_graph: &mut RefGraph) {
        self.refs.add_to_ref_graph(ref_graph);
    }

    fn sweep(&self, is_accessible: bool, ref_graph: &mut RefGraph) {
        self.refs.sweep(is_accessible, ref_graph);
    }

    unsafe fn destroy_gcs(&mut self, ref_graph: &mut RefGraph) {
        self.refs.destroy_gcs(ref_graph);
    }
}

impl Drop for MultiRef<'_> {
    fn drop(&mut self) {
        self.drop_count.fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn self_referential() {
    static DROPPED: AtomicU8 = AtomicU8::new(0);
    struct Foo(RefCell<Option<Gc<Foo>>>);

    unsafe impl Collectable for Foo {
        fn add_to_ref_graph(&self, ref_graph: &mut RefGraph) {
            self.0.add_to_ref_graph(ref_graph);
        }
        fn sweep(&self, is_accessible: bool, ref_graph: &mut RefGraph) {
            self.0.sweep(is_accessible, ref_graph);
        }
        unsafe fn destroy_gcs(&mut self, ref_graph: &mut RefGraph) {
            self.0.destroy_gcs(ref_graph);
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            println!("dropped!");
            DROPPED.fetch_add(1, Ordering::Relaxed);
        }
    }

    let gc = Gc::new(Foo(RefCell::new(None)));
    gc.0.replace(Some(Gc::clone(&gc)));

    assert_eq!(DROPPED.load(Ordering::Relaxed), 0);
    drop(gc);
    assert_eq!(DROPPED.load(Ordering::Relaxed), 1);
}

#[test]
fn cyclic() {
    static DROPPED: AtomicU8 = AtomicU8::new(0);
    struct Foo(RefCell<Option<Gc<Foo>>>);

    unsafe impl Collectable for Foo {
        fn add_to_ref_graph(&self, ref_graph: &mut RefGraph) {
            self.0.add_to_ref_graph(ref_graph);
        }
        fn sweep(&self, is_accessible: bool, ref_graph: &mut RefGraph) {
            self.0.sweep(is_accessible, ref_graph);
        }
        unsafe fn destroy_gcs(&mut self, ref_graph: &mut RefGraph) {
            self.0.destroy_gcs(ref_graph);
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            println!("dropped!");
            DROPPED.fetch_add(1, Ordering::Relaxed);
        }
    }

    let foo1 = Gc::new(Foo(RefCell::new(None)));
    let foo2 = Gc::new(Foo(RefCell::new(Some(Gc::clone(&foo1)))));
    foo1.0.replace(Some(Gc::clone(&foo2)));

    assert_eq!(DROPPED.load(Ordering::Relaxed), 0);
    drop(foo1);
    assert_eq!(DROPPED.load(Ordering::Relaxed), 0);
    drop(foo2);
    assert_eq!(DROPPED.load(Ordering::Relaxed), 2);
}

/// Construct a complete graph of garbage-collected
fn complete_graph(detectors: &[AtomicUsize]) -> Vec<Gc<MultiRef<'_>>> {
    let mut gcs = Vec::new();
    for d in detectors {
        let gc = Gc::new(MultiRef {
            refs: RefCell::new(Vec::new()),
            drop_count: d,
        });
        for x in &gcs {
            gc.refs.borrow_mut().push(Gc::clone(x));
            x.refs.borrow_mut().push(Gc::clone(&gc));
        }
        gcs.push(gc);
    }

    gcs
}

#[test]
fn complete4() {
    let detectors: [AtomicUsize; 4] = [
        AtomicUsize::new(0),
        AtomicUsize::new(0),
        AtomicUsize::new(0),
        AtomicUsize::new(0),
    ];

    let mut gcs = complete_graph(&detectors);

    for _ in 0..3 {
        gcs.pop();
    }

    for detector in &detectors {
        assert_eq!(detector.load(Ordering::Relaxed), 0);
    }

    drop(gcs);

    for detector in &detectors {
        assert_eq!(detector.load(Ordering::Relaxed), 1);
    }
}
