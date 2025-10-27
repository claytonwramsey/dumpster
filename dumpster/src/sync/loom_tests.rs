/*
    dumpster, a cycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

use loom::{
    lazy_static,
    sync::atomic::{AtomicUsize, Ordering},
};

use loom_ext::{Mutex, OnceLock};

use crate::Visitor;

use super::*;

struct DropCount<'a>(&'a AtomicUsize);

impl Drop for DropCount<'_> {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::Release);
    }
}

unsafe impl Trace for DropCount<'_> {
    fn accept<V: crate::Visitor>(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

struct MultiRef {
    refs: Mutex<Vec<Gc<MultiRef>>>,
    #[expect(unused)]
    count: DropCount<'static>,
}

unsafe impl Trace for MultiRef {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.refs.accept(visitor)
    }
}

#[test]
fn loom_single_alloc() {
    lazy_static! {
        static ref DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
    }

    loom::model(|| {
        let gc1 = Gc::new(DropCount(&DROP_COUNT));

        collect();
        assert_eq!(DROP_COUNT.load(Ordering::Acquire), 0);
        drop(gc1);
        collect();
        assert_eq!(DROP_COUNT.load(Ordering::Acquire), 1);
    });
}

#[test]
fn loom_self_referential() {
    struct Foo(Mutex<Option<Gc<Foo>>>);

    lazy_static! {
        static ref DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
    }

    unsafe impl Trace for Foo {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            // println!("begin increment of the drop count!");
            DROP_COUNT.fetch_add(1, Ordering::Release);
        }
    }

    loom::model(|| {
        let gc1 = Gc::new(Foo(Mutex::new(None)));
        *gc1.0.lock() = Some(Gc::clone(&gc1));

        assert_eq!(DROP_COUNT.load(Ordering::Acquire), 0);
        drop(gc1);
        collect();
        assert_eq!(DROP_COUNT.load(Ordering::Acquire), 1);
    });
}

#[test]
fn loom_two_cycle() {
    lazy_static! {
        static ref DROP_0: AtomicUsize = AtomicUsize::new(0);
        static ref DROP_1: AtomicUsize = AtomicUsize::new(0);
    }

    loom::model(|| {
        let gc0 = Gc::new(MultiRef {
            refs: Mutex::new(Vec::new()),
            count: DropCount(&DROP_0),
        });
        let gc1 = Gc::new(MultiRef {
            refs: Mutex::new(vec![Gc::clone(&gc0)]),
            count: DropCount(&DROP_1),
        });
        gc0.refs.lock().push(Gc::clone(&gc1));

        collect();
        assert_eq!(DROP_0.load(Ordering::Acquire), 0);
        assert_eq!(DROP_0.load(Ordering::Acquire), 0);
        drop(gc0);
        collect();
        assert_eq!(DROP_0.load(Ordering::Acquire), 0);
        assert_eq!(DROP_0.load(Ordering::Acquire), 0);
        drop(gc1);
        collect();
        assert_eq!(DROP_0.load(Ordering::Acquire), 1);
        assert_eq!(DROP_0.load(Ordering::Acquire), 1);
    });
}

#[test]
/// Test that creating a `Gc` during a `Drop` implementation will still not leak the `Gc`.
fn loom_sync_leak_by_creation_in_drop() {
    lazy_static! {
        static ref BAR_DROP_COUNT: [AtomicUsize; 2] = [AtomicUsize::new(0), AtomicUsize::new(0)];
    }

    struct Foo(OnceLock<Gc<Self>>, usize);
    struct Bar(OnceLock<Gc<Self>>, usize);

    unsafe impl Trace for Foo {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    unsafe impl Trace for Bar {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            println!("calling drop for foo");
            let gcbar = Gc::new(Bar(OnceLock::new(), self.1));
            gcbar.0.set(gcbar.clone());
            drop(gcbar);

            // MUST be included for the test to succeed (in case Foo is collected on separate
            // thread)
            crate::sync::collect::deliver_dumpster();
            println!("drop for foo done");
        }
    }

    impl Drop for Bar {
        fn drop(&mut self) {
            println!("drop Bar");
            BAR_DROP_COUNT[self.1].fetch_add(1, Ordering::Relaxed);
        }
    }

    loom::model(|| {
        println!("=========== NEW MODEL ITERATION ===============");

        let mut join_handles = vec![];

        for i in 0..2 {
            join_handles.push(loom::thread::spawn(move || {
                let foo = Gc::new(Foo(OnceLock::new(), i));
                foo.0.set(foo.clone());
                drop(foo);

                println!("===== collect from {i} number 1");
                collect(); // causes Bar to be created and then leaked
                println!("===== collect from {i} number 2");
                collect(); // cleans up Bar (eventually)

                assert_eq!(
                    BAR_DROP_COUNT[i].load(Ordering::Relaxed),
                    1,
                    "failed to collect on thread 0"
                );
                collect::DUMPSTER.with(|d| println!("{:?}", d.contents));
                assert!(collect::DUMPSTER.with(|d| d.contents.borrow().is_empty()));
            }));
        }

        for join_handle in join_handles {
            join_handle.join().unwrap();
        }
    });
}
