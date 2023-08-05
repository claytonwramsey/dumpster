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
    ptr::NonNull,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Mutex,
    },
};

use crate::Visitor;

use super::*;

struct DropCount<'a>(&'a AtomicUsize);

impl<'a> Drop for DropCount<'a> {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::Release);
    }
}

unsafe impl Collectable for DropCount<'_> {
    fn accept<V: crate::Visitor>(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

struct MultiRef {
    refs: Mutex<Vec<Gc<MultiRef>>>,
    #[allow(unused)]
    count: DropCount<'static>,
}

unsafe impl Collectable for MultiRef {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.refs.accept(visitor)
    }
}

#[test]
fn single_alloc() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
    let gc1 = Gc::new(DropCount(&DROP_COUNT));

    collect_await();
    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 0);
    drop(gc1);
    collect_await();
    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 1);
}

#[test]
fn ref_count() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
    let gc1 = Gc::new(DropCount(&DROP_COUNT));
    let gc2 = Gc::clone(&gc1);

    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 0);
    drop(gc1);
    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 0);
    drop(gc2);
    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 1);
}

#[test]
fn self_referential() {
    struct Foo(Mutex<Option<Gc<Foo>>>);
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    unsafe impl Collectable for Foo {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            println!("begin increment of the drop count!");
            DROP_COUNT.fetch_add(1, Ordering::Release);
        }
    }

    let gc1 = Gc::new(Foo(Mutex::new(None)));
    *(*gc1).0.lock().unwrap() = Some(Gc::clone(&gc1));

    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 0);
    drop(gc1);
    collect_await();
    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 1);
}

#[test]
fn two_cycle() {
    static DROP_0: AtomicUsize = AtomicUsize::new(0);
    static DROP_1: AtomicUsize = AtomicUsize::new(0);

    let gc0 = Gc::new(MultiRef {
        refs: Mutex::new(Vec::new()),
        count: DropCount(&DROP_0),
    });
    let gc1 = Gc::new(MultiRef {
        refs: Mutex::new(vec![Gc::clone(&gc0)]),
        count: DropCount(&DROP_1),
    });
    gc0.refs.lock().unwrap().push(Gc::clone(&gc1));

    collect_await();
    assert_eq!(DROP_0.load(Ordering::Acquire), 0);
    assert_eq!(DROP_0.load(Ordering::Acquire), 0);
    drop(gc0);
    collect_await();
    assert_eq!(DROP_0.load(Ordering::Acquire), 0);
    assert_eq!(DROP_0.load(Ordering::Acquire), 0);
    drop(gc1);
    collect_await();
    assert_eq!(DROP_0.load(Ordering::Acquire), 1);
    assert_eq!(DROP_0.load(Ordering::Acquire), 1);
}

#[test]
fn self_ref_two_cycle() {
    static DROP_0: AtomicUsize = AtomicUsize::new(0);
    static DROP_1: AtomicUsize = AtomicUsize::new(0);

    let gc0 = Gc::new(MultiRef {
        refs: Mutex::new(Vec::new()),
        count: DropCount(&DROP_0),
    });
    let gc1 = Gc::new(MultiRef {
        refs: Mutex::new(vec![Gc::clone(&gc0)]),
        count: DropCount(&DROP_1),
    });
    gc0.refs.lock().unwrap().extend([gc0.clone(), gc1.clone()]);
    gc1.refs.lock().unwrap().push(gc1.clone());

    collect_await();
    assert_eq!(DROP_0.load(Ordering::Acquire), 0);
    assert_eq!(DROP_0.load(Ordering::Acquire), 0);
    drop(gc0);
    collect_await();
    assert_eq!(DROP_0.load(Ordering::Acquire), 0);
    assert_eq!(DROP_0.load(Ordering::Acquire), 0);
    drop(gc1);
    collect_await();
    assert_eq!(DROP_0.load(Ordering::Acquire), 1);
    assert_eq!(DROP_0.load(Ordering::Acquire), 1);
}

#[test]
fn parallel_loop() {
    static COUNT_1: AtomicUsize = AtomicUsize::new(0);
    static COUNT_2: AtomicUsize = AtomicUsize::new(0);
    static COUNT_3: AtomicUsize = AtomicUsize::new(0);
    static COUNT_4: AtomicUsize = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        count: DropCount(&COUNT_1),
        refs: Mutex::new(Vec::new()),
    });
    let gc2 = Gc::new(MultiRef {
        count: DropCount(&COUNT_2),
        refs: Mutex::new(vec![Gc::clone(&gc1)]),
    });
    let gc3 = Gc::new(MultiRef {
        count: DropCount(&COUNT_3),
        refs: Mutex::new(vec![Gc::clone(&gc1)]),
    });
    let gc4 = Gc::new(MultiRef {
        count: DropCount(&COUNT_4),
        refs: Mutex::new(vec![Gc::clone(&gc2), Gc::clone(&gc3)]),
    });
    gc1.refs.lock().unwrap().push(Gc::clone(&gc4));

    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_3.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_4.load(Ordering::Acquire), 0);
    drop(gc1);
    collect_await();
    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_3.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_4.load(Ordering::Acquire), 0);
    drop(gc2);
    collect_await();
    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_3.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_4.load(Ordering::Acquire), 0);
    drop(gc3);
    collect_await();
    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_3.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_4.load(Ordering::Acquire), 0);
    drop(gc4);
    collect_await();
    assert_eq!(COUNT_1.load(Ordering::Acquire), 1);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 1);
    assert_eq!(COUNT_3.load(Ordering::Acquire), 1);
    assert_eq!(COUNT_4.load(Ordering::Acquire), 1);
}

#[test]
/// Test that we can drop a Gc which points to some allocation with a locked Mutex inside it
// note: I tried using `ntest::timeout` but for some reason that caused this test to trivially pass.
fn deadlock() {
    let gc1 = Gc::new(Mutex::new(()));
    let gc2 = gc1.clone();

    let guard = gc1.lock();
    drop(gc2);
    collect_await();
    drop(guard);
}

#[test]
fn open_drop() {
    static COUNT_1: AtomicUsize = AtomicUsize::new(0);
    let gc1 = Gc::new(MultiRef {
        refs: Mutex::new(Vec::new()),
        count: DropCount(&COUNT_1),
    });

    gc1.refs.lock().unwrap().push(gc1.clone());
    let guard = gc1.refs.lock();
    collect_await();
    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    drop(guard);
    drop(gc1);
    collect_await();

    assert_eq!(COUNT_1.load(Ordering::Acquire), 1);
}

#[test]
fn eventually_collect_await() {
    static COUNT_1: AtomicUsize = AtomicUsize::new(0);
    static COUNT_2: AtomicUsize = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        refs: Mutex::new(Vec::new()),
        count: DropCount(&COUNT_1),
    });
    let gc2 = Gc::new(MultiRef {
        refs: Mutex::new(vec![gc1.clone()]),
        count: DropCount(&COUNT_2),
    });
    gc1.refs.lock().unwrap().push(gc2.clone());

    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 0);

    drop(gc1);
    drop(gc2);

    for _ in 0..100 {
        let gc = Gc::new(());
        drop(gc);
    }

    // after enough time, gc1 and gc2 should have been collected
    assert_eq!(COUNT_1.load(Ordering::Acquire), 1);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 1);
}

#[test]
#[cfg(feature = "coerce-unsized")]
fn coerce_array() {
    let gc1: Gc<[u8; 3]> = Gc::new([0, 0, 0]);
    let gc2: Gc<[u8]> = gc1;
    assert_eq!(gc2.len(), 3);
    assert_eq!(
        std::mem::size_of::<Gc<[u8]>>(),
        2 * std::mem::size_of::<usize>()
    );
}

#[test]
fn malicious() {
    static EVIL: AtomicUsize = AtomicUsize::new(0);
    struct A {
        x: Gc<X>,
        y: Gc<Y>,
    }
    struct X {
        a: Mutex<Option<Gc<A>>>,
        y: NonNull<Y>,
    }
    struct Y {
        a: Mutex<Option<Gc<A>>>,
    }

    unsafe impl Collectable for A {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.x.accept(visitor)?;
            self.y.accept(visitor)
        }
    }

    unsafe impl Collectable for X {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.a.accept(visitor)?;

            if EVIL.fetch_add(1, Ordering::Relaxed) == 2 {
                println!("committing evil...");
                // simulates a malicious thread
                let y = unsafe { self.y.as_ref() };
                *y.a.lock().unwrap() = (*self.a.lock().unwrap()).take();
            }

            Ok(())
        }
    }

    unsafe impl Collectable for Y {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.a.accept(visitor)
        }
    }

    unsafe impl Sync for X {}

    let y = Gc::new(Y {
        a: Mutex::new(None),
    });
    let x = Gc::new(X {
        a: Mutex::new(None),
        y: NonNull::from(y.as_ref()),
    });
    let a = Gc::new(A { x, y });
    *a.x.a.lock().unwrap() = Some(a.clone());

    collect_await();
    drop(a.clone());
    EVIL.store(1, Ordering::Relaxed);
    collect_await();
}
