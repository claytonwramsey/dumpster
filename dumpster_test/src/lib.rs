/*
    dumpster, a cycle-tracking garbage collector for Rust.
    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![cfg(test)]

use std::{
    cell::RefCell,
    sync::atomic::{AtomicU8, AtomicUsize, Ordering},
};

use dumpster::unsync::{collect, Gc};
use dumpster_derive::Trace;

#[derive(Trace)]
struct Empty;

#[derive(Trace)]
#[allow(dead_code)]
struct UnitTuple();

#[derive(Trace)]
struct MultiRef {
    counter: &'static AtomicUsize,
    pointers: RefCell<Vec<Gc<MultiRef>>>,
}

#[derive(Trace)]
#[allow(unused)]
enum Refs {
    None,
    One(Gc<Refs>),
    Many { refs: Vec<Gc<Refs>> },
}

#[derive(Trace)]
#[allow(unused)]
enum A {
    None,
}

#[derive(Trace)]
#[allow(unused)]
enum B {
    One(Gc<B>),
}

impl Drop for MultiRef {
    fn drop(&mut self) {
        self.counter.fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn unit() {
    static DROP_COUNT: AtomicU8 = AtomicU8::new(0);
    #[derive(Trace)]
    struct DropCount;

    impl Drop for DropCount {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(1, Ordering::Relaxed);
        }
    }

    let gc1 = Gc::new(DropCount);
    let gc2 = Gc::clone(&gc1);

    drop(gc1);
    assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 0);
    drop(gc2);
    assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 1);
}

#[test]
fn self_referential() {
    static COUNT: AtomicUsize = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        counter: &COUNT,
        pointers: RefCell::new(Vec::new()),
    });
    gc1.pointers.borrow_mut().push(Gc::clone(&gc1));

    assert_eq!(COUNT.load(Ordering::Relaxed), 0);
    drop(gc1);
    collect();
    assert_eq!(COUNT.load(Ordering::Relaxed), 1);
}

#[test]
fn double_loop() {
    static COUNT: AtomicUsize = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        counter: &COUNT,
        pointers: RefCell::new(Vec::new()),
    });
    gc1.pointers
        .borrow_mut()
        .extend([Gc::clone(&gc1), Gc::clone(&gc1)]);

    assert_eq!(COUNT.load(Ordering::Relaxed), 0);
    drop(gc1);
    collect();
    assert_eq!(COUNT.load(Ordering::Relaxed), 1);
}

#[test]
fn parallel_loop() {
    static COUNT_1: AtomicUsize = AtomicUsize::new(0);
    static COUNT_2: AtomicUsize = AtomicUsize::new(0);
    static COUNT_3: AtomicUsize = AtomicUsize::new(0);
    static COUNT_4: AtomicUsize = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        counter: &COUNT_1,
        pointers: RefCell::new(Vec::new()),
    });
    let gc2 = Gc::new(MultiRef {
        counter: &COUNT_2,
        pointers: RefCell::new(vec![Gc::clone(&gc1)]),
    });
    let gc3 = Gc::new(MultiRef {
        counter: &COUNT_3,
        pointers: RefCell::new(vec![Gc::clone(&gc1)]),
    });
    let gc4 = Gc::new(MultiRef {
        counter: &COUNT_4,
        pointers: RefCell::new(vec![Gc::clone(&gc2), Gc::clone(&gc3)]),
    });
    gc1.pointers.borrow_mut().push(Gc::clone(&gc4));

    drop(gc1);
    drop(gc2);
    drop(gc3);
    assert_eq!(COUNT_1.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_2.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_3.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_4.load(Ordering::Relaxed), 0);
    drop(gc4);
    collect();
    assert_eq!(COUNT_1.load(Ordering::Relaxed), 1);
    assert_eq!(COUNT_2.load(Ordering::Relaxed), 1);
    assert_eq!(COUNT_3.load(Ordering::Relaxed), 1);
    assert_eq!(COUNT_4.load(Ordering::Relaxed), 1);
}

#[test]
#[allow(clippy::similar_names)]
fn unsync_as_ptr() {
    #[derive(Trace)]
    struct B(Gc<Empty>);

    let empty = Gc::new(Empty);
    let empty_a = Gc::clone(&empty);
    let empty_ptr = Gc::as_ptr(&empty);
    assert_eq!(empty_ptr, Gc::as_ptr(&empty_a));

    let b = B(Gc::clone(&empty));
    assert_eq!(empty_ptr, Gc::as_ptr(&b.0));
    let bb = Gc::new(B(Gc::clone(&empty)));
    assert_eq!(empty_ptr, Gc::as_ptr(&bb.0));

    let empty2 = Gc::new(Empty);
    let empty2_ptr = Gc::as_ptr(&empty2);
    assert_ne!(empty_ptr, empty2_ptr);
    let b2 = Gc::new(B(Gc::clone(&empty2)));
    assert_eq!(empty2_ptr, Gc::as_ptr(&b2.0));
    assert_ne!(empty_ptr, Gc::as_ptr(&b2.0));
    assert_ne!(Gc::as_ptr(&b.0), Gc::as_ptr(&b2.0));
    assert_ne!(Gc::as_ptr(&b.0), empty2_ptr);
}
