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

#![cfg(test)]

use std::{
    cell::RefCell,
    sync::atomic::{AtomicU8, AtomicUsize, Ordering},
};

use dumpster::Gc;
use dumpster_derive::Collectable;

#[derive(Collectable)]
struct Empty;

#[derive(Collectable)]
struct UnitTuple();

#[derive(Collectable)]
struct MultiRef<'a> {
    counter: &'a AtomicUsize,
    pointers: RefCell<Vec<Gc<MultiRef<'a>>>>,
}

impl<'a> Drop for MultiRef<'a> {
    fn drop(&mut self) {
        self.counter.fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn unit() {
    static DROP_COUNT: AtomicU8 = AtomicU8::new(0);
    #[derive(Collectable)]
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
    let count = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        counter: &count,
        pointers: RefCell::new(Vec::new()),
    });
    gc1.pointers.borrow_mut().push(Gc::clone(&gc1));

    assert_eq!(count.load(Ordering::Relaxed), 0);
    drop(gc1);
    assert_eq!(count.load(Ordering::Relaxed), 1);
}

#[test]
fn double_loop() {
    let count = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        counter: &count,
        pointers: RefCell::new(Vec::new()),
    });
    gc1.pointers
        .borrow_mut()
        .extend([Gc::clone(&gc1), Gc::clone(&gc1)]);

    assert_eq!(count.load(Ordering::Relaxed), 0);
    drop(gc1);
    assert_eq!(count.load(Ordering::Relaxed), 1);
}

#[test]
fn parallel_loop() {
    let count1 = AtomicUsize::new(0);
    let count2 = AtomicUsize::new(0);
    let count3 = AtomicUsize::new(0);
    let count4 = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        counter: &count1,
        pointers: RefCell::new(Vec::new()),
    });
    let gc2 = Gc::new(MultiRef {
        counter: &count2,
        pointers: RefCell::new(vec![Gc::clone(&gc1)]),
    });
    let gc3 = Gc::new(MultiRef {
        counter: &count3,
        pointers: RefCell::new(vec![Gc::clone(&gc1)]),
    });
    let gc4 = Gc::new(MultiRef {
        counter: &count4,
        pointers: RefCell::new(vec![Gc::clone(&gc2), Gc::clone(&gc3)]),
    });
    gc1.pointers.borrow_mut().push(Gc::clone(&gc4));

    drop(gc1);
    drop(gc2);
    drop(gc3);
    assert_eq!(count1.load(Ordering::Relaxed), 0);
    assert_eq!(count2.load(Ordering::Relaxed), 0);
    assert_eq!(count3.load(Ordering::Relaxed), 0);
    assert_eq!(count4.load(Ordering::Relaxed), 0);
    drop(gc4);
    assert_eq!(count1.load(Ordering::Relaxed), 1);
    assert_eq!(count2.load(Ordering::Relaxed), 1);
    assert_eq!(count3.load(Ordering::Relaxed), 1);
    assert_eq!(count4.load(Ordering::Relaxed), 1);
}
