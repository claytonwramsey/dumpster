/*
    dumpster, acycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

use std::{
    collections::{hash_map::Entry, HashMap},
    mem::{swap, take, transmute, MaybeUninit},
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

unsafe impl Trace for DropCount<'_> {
    fn accept<V: crate::Visitor>(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

struct MultiRef {
    refs: Mutex<Vec<Gc<MultiRef>>>,
    #[allow(unused)]
    count: DropCount<'static>,
}

unsafe impl Trace for MultiRef {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.refs.accept(visitor)
    }
}

#[test]
fn single_alloc() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
    let gc1 = Gc::new(DropCount(&DROP_COUNT));

    collect();
    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 0);
    drop(gc1);
    collect();
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

    unsafe impl Trace for Foo {
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
    *gc1.0.lock().unwrap() = Some(Gc::clone(&gc1));

    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 0);
    drop(gc1);
    collect();
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
    collect();
    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_3.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_4.load(Ordering::Acquire), 0);
    drop(gc2);
    collect();
    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_3.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_4.load(Ordering::Acquire), 0);
    drop(gc3);
    collect();
    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_2.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_3.load(Ordering::Acquire), 0);
    assert_eq!(COUNT_4.load(Ordering::Acquire), 0);
    drop(gc4);
    collect();
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
    collect();
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
    collect();
    assert_eq!(COUNT_1.load(Ordering::Acquire), 0);
    drop(guard);
    drop(gc1);
    collect();

    assert_eq!(COUNT_1.load(Ordering::Acquire), 1);
}

#[test]
#[cfg_attr(miri, ignore = "miri is too slow")]
fn eventually_collect() {
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

    for _ in 0..200_000 {
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
        3 * std::mem::size_of::<usize>()
    );
}

#[test]
fn malicious() {
    static EVIL: AtomicUsize = AtomicUsize::new(0);
    static A_DROP_DETECT: AtomicUsize = AtomicUsize::new(0);
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

    unsafe impl Send for X {}

    unsafe impl Trace for A {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.x.accept(visitor)?;
            self.y.accept(visitor)
        }
    }

    unsafe impl Trace for X {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.a.accept(visitor)?;

            if EVIL.fetch_add(1, Ordering::Relaxed) == 1 {
                println!("committing evil...");
                // simulates a malicious thread
                let y = unsafe { self.y.as_ref() };
                *y.a.lock().unwrap() = (*self.a.lock().unwrap()).take();
            }

            Ok(())
        }
    }

    unsafe impl Trace for Y {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.a.accept(visitor)
        }
    }

    unsafe impl Sync for X {}

    impl Drop for A {
        fn drop(&mut self) {
            A_DROP_DETECT.fetch_add(1, Ordering::Relaxed);
        }
    }

    let y = Gc::new(Y {
        a: Mutex::new(None),
    });
    let x = Gc::new(X {
        a: Mutex::new(None),
        y: NonNull::from(y.as_ref()),
    });
    let a = Gc::new(A { x, y });
    *a.x.a.lock().unwrap() = Some(a.clone());

    collect();
    drop(a.clone());
    EVIL.store(1, Ordering::Relaxed);
    collect();
    assert_eq!(A_DROP_DETECT.load(Ordering::Relaxed), 0);
    drop(a);
    collect();
    assert_eq!(A_DROP_DETECT.load(Ordering::Relaxed), 1);
}

#[test]
#[cfg_attr(miri, ignore = "miri is too slow")]
#[allow(clippy::too_many_lines)]
fn fuzz() {
    const N: usize = 20_000;
    static DROP_DETECTORS: [AtomicUsize; N] = {
        let mut detectors: [MaybeUninit<AtomicUsize>; N] =
            unsafe { transmute(MaybeUninit::<[AtomicUsize; N]>::uninit()) };

        let mut i = 0;
        while i < N {
            detectors[i] = MaybeUninit::new(AtomicUsize::new(0));
            i += 1;
        }

        unsafe { transmute(detectors) }
    };

    #[derive(Debug)]
    struct Alloc {
        refs: Mutex<Vec<Gc<Alloc>>>,
        id: usize,
    }

    impl Drop for Alloc {
        fn drop(&mut self) {
            DROP_DETECTORS[self.id].fetch_add(1, Ordering::Relaxed);
        }
    }

    unsafe impl Trace for Alloc {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.refs.accept(visitor)
        }
    }

    fn dfs(alloc: &Gc<Alloc>, graph: &mut HashMap<usize, Vec<usize>>) {
        if let Entry::Vacant(v) = graph.entry(alloc.id) {
            if alloc.id == 2822 || alloc.id == 2814 {
                println!("{} - {alloc:?}", alloc.id);
            }
            v.insert(Vec::new());
            alloc.refs.lock().unwrap().iter().for_each(|a| {
                graph.get_mut(&alloc.id).unwrap().push(a.id);
                dfs(a, graph);
            });
        }
    }

    fastrand::seed(12345);
    let mut gcs = (0..50)
        .map(|i| {
            Gc::new(Alloc {
                refs: Mutex::new(Vec::new()),
                id: i,
            })
        })
        .collect::<Vec<_>>();

    let mut next_detector = 50;
    for _ in 0..N {
        if gcs.is_empty() {
            gcs.push(Gc::new(Alloc {
                refs: Mutex::new(Vec::new()),
                id: next_detector,
            }));
            next_detector += 1;
        }
        match fastrand::u8(0..4) {
            0 => {
                println!("add gc {next_detector}");
                gcs.push(Gc::new(Alloc {
                    refs: Mutex::new(Vec::new()),
                    id: next_detector,
                }));
                next_detector += 1;
            }
            1 => {
                if gcs.len() > 1 {
                    let from = fastrand::usize(0..gcs.len());
                    let to = fastrand::usize(0..gcs.len());
                    println!("add ref {} -> {}", gcs[from].id, gcs[to].id);
                    let new_gc = gcs[to].clone();
                    let mut guard = gcs[from].refs.lock().unwrap();
                    guard.push(new_gc);
                }
            }
            2 => {
                let idx = fastrand::usize(0..gcs.len());
                println!("remove gc {}", gcs[idx].id);
                gcs.swap_remove(idx);
            }
            3 => {
                let from = fastrand::usize(0..gcs.len());
                let mut guard = gcs[from].refs.lock().unwrap();
                if !guard.is_empty() {
                    let to = fastrand::usize(0..guard.len());
                    println!("drop ref {} -> {}", gcs[from].id, guard[to].id);
                    guard.swap_remove(to);
                }
            }
            _ => unreachable!(),
        }
    }

    let mut graph = HashMap::new();
    graph.insert(9999, Vec::new());
    for alloc in &gcs {
        graph.get_mut(&9999).unwrap().push(alloc.id);
        dfs(alloc, &mut graph);
    }
    println!("{graph:#?}");

    drop(gcs);
    collect();

    let mut n_missing = 0;
    for (id, count) in DROP_DETECTORS[..next_detector].iter().enumerate() {
        let num = count.load(Ordering::Relaxed);
        if num != 1 {
            println!("expected 1 for id {id} but got {num}");
            n_missing += 1;
        }
    }
    assert_eq!(n_missing, 0);
}

#[test]
fn root_canal() {
    struct A {
        b: Gc<B>,
    }

    struct B {
        a0: Mutex<Option<Gc<A>>>,
        a1: Mutex<Option<Gc<A>>>,
        a2: Mutex<Option<Gc<A>>>,
        a3: Mutex<Option<Gc<A>>>,
    }

    unsafe impl Trace for A {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.b.accept(visitor)
        }
    }

    unsafe impl Trace for B {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            let n_prior_visits = B_VISIT_COUNT.fetch_add(1, Ordering::Relaxed);
            self.a0.accept(visitor)?;
            self.a1.accept(visitor)?;

            // simulate a malicious thread swapping things around
            if n_prior_visits == 1 {
                println!("committing evil...");
                swap(
                    &mut *SMUGGLED_POINTERS[0].lock().unwrap(),
                    &mut *SMUGGLED_POINTERS[1]
                        .lock()
                        .unwrap()
                        .as_ref()
                        .unwrap()
                        .b
                        .a0
                        .lock()
                        .unwrap(),
                );
                swap(&mut *self.a0.lock().unwrap(), &mut *self.a2.lock().unwrap());
                swap(
                    &mut *SMUGGLED_POINTERS[0].lock().unwrap(),
                    &mut *SMUGGLED_POINTERS[1]
                        .lock()
                        .unwrap()
                        .as_ref()
                        .unwrap()
                        .b
                        .a1
                        .lock()
                        .unwrap(),
                );
                swap(&mut *self.a1.lock().unwrap(), &mut *self.a3.lock().unwrap());
            }

            self.a2.accept(visitor)?;
            self.a3.accept(visitor)?;

            // smuggle out some pointers
            if n_prior_visits == 0 {
                println!("smuggling...");
                *SMUGGLED_POINTERS[0].lock().unwrap() = take(&mut *self.a2.lock().unwrap());
                *SMUGGLED_POINTERS[1].lock().unwrap() = take(&mut *self.a3.lock().unwrap());
            }

            Ok(())
        }
    }

    impl Drop for B {
        fn drop(&mut self) {
            B_DROP_DETECT.fetch_add(1, Ordering::Relaxed);
        }
    }

    static SMUGGLED_POINTERS: [Mutex<Option<Gc<A>>>; 2] = [Mutex::new(None), Mutex::new(None)];
    static B_VISIT_COUNT: AtomicUsize = AtomicUsize::new(0);
    static B_DROP_DETECT: AtomicUsize = AtomicUsize::new(0);

    let a = Gc::new(A {
        b: Gc::new(B {
            a0: Mutex::new(None),
            a1: Mutex::new(None),
            a2: Mutex::new(None),
            a3: Mutex::new(None),
        }),
    });
    *a.b.a0.lock().unwrap() = Some(a.clone());
    *a.b.a1.lock().unwrap() = Some(a.clone());
    *a.b.a2.lock().unwrap() = Some(a.clone());
    *a.b.a3.lock().unwrap() = Some(a.clone());

    drop(a.clone());
    collect();
    println!("{}", CURRENT_TAG.load(Ordering::Relaxed));

    assert!(dbg!(SMUGGLED_POINTERS[0].lock().unwrap().as_ref()).is_some());
    assert!(SMUGGLED_POINTERS[1].lock().unwrap().as_ref().is_some());
    println!("{}", B_VISIT_COUNT.load(Ordering::Relaxed));

    assert_eq!(B_DROP_DETECT.load(Ordering::Relaxed), 0);
    drop(a);
    assert_eq!(B_DROP_DETECT.load(Ordering::Relaxed), 0);
    collect();
    println!("{}", CURRENT_TAG.load(Ordering::Relaxed));

    assert_eq!(B_DROP_DETECT.load(Ordering::Relaxed), 0);

    *SMUGGLED_POINTERS[0].lock().unwrap() = None;
    *SMUGGLED_POINTERS[1].lock().unwrap() = None;
    collect();

    assert_eq!(B_DROP_DETECT.load(Ordering::Relaxed), 1);
}

#[test]
#[should_panic = "Attempting to dereference Gc to already-deallocated object.This is caused by accessing a Gc during a Drop implementation, likely implying a bug in your code."]
fn escape_dead_pointer() {
    static ESCAPED: Mutex<Option<Gc<Escape>>> = Mutex::new(None);

    struct Escape {
        x: u8,
        ptr: Mutex<Option<Gc<Escape>>>,
    }

    impl Drop for Escape {
        fn drop(&mut self) {
            let mut escaped_guard = ESCAPED.lock().unwrap();
            if escaped_guard.is_none() {
                *escaped_guard = self.ptr.lock().unwrap().take();
            }
        }
    }

    unsafe impl Trace for Escape {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.ptr.accept(visitor)
        }
    }

    let esc = Gc::new(Escape {
        x: 0,
        ptr: Mutex::new(None),
    });

    *(*esc).ptr.lock().unwrap() = Some(esc.clone());
    drop(esc);
    collect();
    println!("{}", ESCAPED.lock().unwrap().as_ref().unwrap().x);
}
