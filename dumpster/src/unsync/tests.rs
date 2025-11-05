/*
    dumpster, a cycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! Simple tests using manual implementations of [`Trace`].

use crate::{unsync::coerce_gc, Visitor};

use super::*;
use std::{
    cell::{OnceCell, RefCell},
    collections::{hash_map::Entry, HashMap},
    mem::{take, transmute, MaybeUninit},
    sync::{
        atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering},
        Mutex,
    },
};

struct DropCount(&'static AtomicUsize);

impl Drop for DropCount {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::Relaxed);
    }
}

unsafe impl<V: Visitor> TraceWith<V> for DropCount {
    fn accept(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

#[test]
/// Test a simple data structure
fn simple() {
    static DROPPED: AtomicBool = AtomicBool::new(false);
    struct Foo;

    impl Drop for Foo {
        fn drop(&mut self) {
            DROPPED.store(true, Ordering::Relaxed);
        }
    }

    unsafe impl<V: Visitor> TraceWith<V> for Foo {
        fn accept(&self, _: &mut V) -> Result<(), ()> {
            Ok(())
        }
    }

    let gc1 = Gc::new(Foo);
    let gc2 = Gc::clone(&gc1);

    assert!(!DROPPED.load(Ordering::Relaxed));

    drop(gc1);

    assert!(!DROPPED.load(Ordering::Relaxed));

    drop(gc2);

    assert!(DROPPED.load(Ordering::Relaxed));
}

#[derive(Debug)]
struct MultiRef {
    refs: RefCell<Vec<Gc<MultiRef>>>,
    drop_count: &'static AtomicUsize,
}

unsafe impl<V: Visitor> TraceWith<V> for MultiRef {
    fn accept(&self, visitor: &mut V) -> Result<(), ()> {
        self.refs.accept(visitor)
    }
}

impl Drop for MultiRef {
    fn drop(&mut self) {
        self.drop_count.fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn self_referential() {
    static DROPPED: AtomicU8 = AtomicU8::new(0);
    struct Foo(RefCell<Option<Gc<Foo>>>);

    unsafe impl<V: Visitor> TraceWith<V> for Foo {
        #[inline]
        fn accept(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            DROPPED.fetch_add(1, Ordering::Relaxed);
        }
    }

    let gc = Gc::new(Foo(RefCell::new(None)));
    gc.0.replace(Some(Gc::clone(&gc)));

    assert_eq!(DROPPED.load(Ordering::Relaxed), 0);
    drop(gc);
    collect();
    assert_eq!(DROPPED.load(Ordering::Relaxed), 1);
}

#[test]
fn cyclic() {
    static DROPPED: AtomicU8 = AtomicU8::new(0);
    struct Foo(RefCell<Option<Gc<Foo>>>);

    unsafe impl<V: Visitor> TraceWith<V> for Foo {
        #[inline]
        fn accept(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
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
    collect();
    assert_eq!(DROPPED.load(Ordering::Relaxed), 2);
}

/// Construct a complete graph of garbage-collected
fn complete_graph(detectors: &'static [AtomicUsize]) -> Vec<Gc<MultiRef>> {
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
    static DETECTORS: [AtomicUsize; 4] = [
        AtomicUsize::new(0),
        AtomicUsize::new(0),
        AtomicUsize::new(0),
        AtomicUsize::new(0),
    ];

    let mut gcs = complete_graph(&DETECTORS);

    for _ in 0..3 {
        gcs.pop();
    }

    for detector in &DETECTORS {
        assert_eq!(detector.load(Ordering::Relaxed), 0);
    }

    drop(gcs);
    collect();

    for detector in &DETECTORS {
        assert_eq!(detector.load(Ordering::Relaxed), 1);
    }
}

#[test]
fn parallel_loop() {
    static COUNT_1: AtomicUsize = AtomicUsize::new(0);
    static COUNT_2: AtomicUsize = AtomicUsize::new(0);
    static COUNT_3: AtomicUsize = AtomicUsize::new(0);
    static COUNT_4: AtomicUsize = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        drop_count: &COUNT_1,
        refs: RefCell::new(Vec::new()),
    });
    let gc2 = Gc::new(MultiRef {
        drop_count: &COUNT_2,
        refs: RefCell::new(vec![Gc::clone(&gc1)]),
    });
    let gc3 = Gc::new(MultiRef {
        drop_count: &COUNT_3,
        refs: RefCell::new(vec![Gc::clone(&gc1)]),
    });
    let gc4 = Gc::new(MultiRef {
        drop_count: &COUNT_4,
        refs: RefCell::new(vec![Gc::clone(&gc2), Gc::clone(&gc3)]),
    });
    gc1.refs.borrow_mut().push(Gc::clone(&gc4));

    assert_eq!(COUNT_1.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_2.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_3.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_4.load(Ordering::Relaxed), 0);
    drop(gc1);
    assert_eq!(COUNT_1.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_2.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_3.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_4.load(Ordering::Relaxed), 0);
    drop(gc2);
    assert_eq!(COUNT_1.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_2.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_3.load(Ordering::Relaxed), 0);
    assert_eq!(COUNT_4.load(Ordering::Relaxed), 0);
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
/// Check that we can drop a Gc which points to some allocation with a borrowed `RefCell` in it.
fn double_borrow() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    let gc = Gc::new(MultiRef {
        refs: RefCell::new(Vec::new()),
        drop_count: &DROP_COUNT,
    });
    gc.refs.borrow_mut().push(gc.clone());
    let mut my_borrow = gc.refs.borrow_mut();
    my_borrow.pop();
    drop(my_borrow);

    assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 0);
    collect();
    drop(gc);
    collect();
    assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 1);
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
fn coerce_array_using_macro() {
    let gc1: Gc<[u8; 3]> = Gc::new([0, 0, 0]);
    let gc2: Gc<[u8]> = coerce_gc!(gc1);
    assert_eq!(gc2.len(), 3);
    assert_eq!(
        std::mem::size_of::<Gc<[u8]>>(),
        2 * std::mem::size_of::<usize>()
    );
}

#[test]
#[should_panic = "dereferencing Gc to already-collected object. This means a Gc escaped from a Drop implementation, likely implying a bug in your code."]
fn escape_dead_pointer() {
    thread_local! {static  ESCAPED: Mutex<Option<Gc<Escape>>> = const { Mutex::new(None) };}

    struct Escape {
        x: u8,
        ptr: Mutex<Option<Gc<Escape>>>,
    }

    impl Drop for Escape {
        fn drop(&mut self) {
            ESCAPED.with(|e| {
                let mut escaped_guard = e.lock().unwrap();
                if escaped_guard.is_none() {
                    *escaped_guard = (*self.ptr.lock().unwrap()).take();
                }
            });
        }
    }

    unsafe impl<V: Visitor> TraceWith<V> for Escape {
        fn accept(&self, visitor: &mut V) -> Result<(), ()> {
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
    let _x = ESCAPED.with(|e| e.lock().unwrap().as_ref().unwrap().x);
}

#[test]
fn from_box() {
    let gc: Gc<String> = Gc::from(Box::new(String::from("hello")));

    // The `From<Box<T>>` implementation executes a different code path to
    // construct the `Gc`.
    //
    // Here we ensure that the metadata is initialized to a valid state.
    assert_eq!(Gc::ref_count(&gc).get(), 1);

    assert_eq!(&*gc, "hello");
}

#[test]
fn from_slice() {
    let gc: Gc<[String]> = Gc::from(&[String::from("hello"), String::from("world")][..]);

    // The `From<&[T]>` implementation executes a different code path to
    // construct the `Gc`.
    //
    // Here we ensure that the metadata is initialized to a valid state.
    assert_eq!(Gc::ref_count(&gc).get(), 1);

    assert_eq!(&*gc, ["hello", "world"]);
}

#[test]
#[should_panic = "told you"]
fn from_slice_panic() {
    struct MayPanicOnClone {
        value: String,
        panic: bool,
    }

    impl Clone for MayPanicOnClone {
        fn clone(&self) -> Self {
            assert!(!self.panic, "told you");

            Self {
                value: self.value.clone(),
                panic: self.panic,
            }
        }
    }

    unsafe impl<V: Visitor> TraceWith<V> for MayPanicOnClone {
        fn accept(&self, _: &mut V) -> Result<(), ()> {
            Ok(())
        }
    }

    let slice: &[MayPanicOnClone] = &[
        MayPanicOnClone {
            value: String::from("a"),
            panic: false,
        },
        MayPanicOnClone {
            value: String::from("b"),
            panic: false,
        },
        MayPanicOnClone {
            value: String::from("c"),
            panic: true,
        },
    ];

    let _: Gc<[MayPanicOnClone]> = Gc::from(slice);
}

#[test]
fn from_vec() {
    let gc: Gc<[String]> = Gc::from(vec![String::from("hello"), String::from("world")]);

    // The `From<Vec<T>>` implementation executes a different code path to
    // construct the `Gc`.
    //
    // Here we ensure that the metadata is initialized to a valid state.
    assert_eq!(Gc::ref_count(&gc).get(), 1);

    assert_eq!(&*gc, ["hello", "world"]);
}

#[test]
fn make_mut() {
    let mut a = Gc::new(42);
    let mut b = a.clone();
    let mut c = b.clone();

    assert_eq!(*Gc::make_mut(&mut a), 42);
    assert_eq!(*Gc::make_mut(&mut b), 42);
    assert_eq!(*Gc::make_mut(&mut c), 42);

    *Gc::make_mut(&mut a) += 1;
    *Gc::make_mut(&mut b) += 2;
    *Gc::make_mut(&mut c) += 3;

    assert_eq!(*a, 43);
    assert_eq!(*b, 44);
    assert_eq!(*c, 45);

    // they should all be unique
    assert_eq!(Gc::ref_count(&a).get(), 1);
    assert_eq!(Gc::ref_count(&b).get(), 1);
    assert_eq!(Gc::ref_count(&c).get(), 1);
}

#[test]
fn make_mut_2() {
    let mut a = Gc::new(42);
    let b = a.clone();
    let c = b.clone();

    assert_eq!(*a, 42);
    assert_eq!(*b, 42);
    assert_eq!(*c, 42);

    *Gc::make_mut(&mut a) += 1;

    assert_eq!(*a, 43);
    assert_eq!(*b, 42);
    assert_eq!(*c, 42);

    // a should be unique
    // b and c should share their object
    assert_eq!(Gc::ref_count(&a).get(), 1);
    assert_eq!(Gc::ref_count(&b).get(), 2);
    assert_eq!(Gc::ref_count(&c).get(), 2);
}

#[test]
fn make_mut_of_object_in_dumpster() {
    #[derive(Clone)]
    struct Foo {
        // just some gc pointer so foo lands in the dumpster
        something: Gc<i32>,
    }

    unsafe impl<V: Visitor> TraceWith<V> for Foo {
        fn accept(&self, visitor: &mut V) -> Result<(), ()> {
            self.something.accept(visitor)
        }
    }

    let mut foo = Gc::new(Foo {
        something: Gc::new(5),
    });

    drop(foo.clone());

    // now foo is in the dumpster
    // and its ref count is one
    assert_eq!(Gc::ref_count(&foo).get(), 1);

    // we get a mut reference
    let foo_mut = Gc::make_mut(&mut foo);

    // now we collect garbage while we're also holding onto a mutable reference to foo
    // if foo is still in the dumpster then the collection will dereference it and cause UB
    collect();

    // we need to do something with `foo_mut` here so the mutable borrow is actually held
    // during collection
    assert_eq!(*foo_mut.something, 5);
}

#[test]
#[should_panic = "panic on visit"]
#[cfg_attr(miri, ignore = "intentionally leaks memory")]
fn panic_visit() {
    struct PanicVisit;

    /// We technically can make it part of the contract for `Trace` to reject panicking impls,
    /// but it is good form to accept these even though they are malformed.
    unsafe impl<V: Visitor> TraceWith<V> for PanicVisit {
        fn accept(&self, _: &mut V) -> Result<(), ()> {
            panic!("panic on visit");
        }
    }

    let gc = Gc::new(PanicVisit);
    let _ = gc.clone();
    drop(gc);
    collect();
}

#[test]
fn new_cyclic_nothing() {
    static COUNT: AtomicUsize = AtomicUsize::new(0);

    let gc = Gc::new_cyclic(|_| DropCount(&COUNT));
    drop(gc);
    // collect not necessary since this a drop by reference count
    assert_eq!(COUNT.load(Ordering::Relaxed), 1);
}

#[test]
fn new_cyclic_one() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
    #[expect(unused)]
    struct Cycle(Gc<Self>, DropCount);

    unsafe impl<V: Visitor> TraceWith<V> for Cycle {
        fn accept(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    let cyc = Gc::new_cyclic(|gc| Cycle(gc, DropCount(&DROP_COUNT)));
    assert_eq!(Gc::ref_count(&cyc).get(), 2);
    drop(cyc);
    collect();

    assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 1);
}

#[test]
#[should_panic = "ehehe"]
fn new_cyclic_panic() {
    let _: Gc<()> = Gc::new_cyclic(|_| panic!("ehehe"));
}

#[test]
fn dead_inside_alive() {
    struct Cycle(Option<Gc<Self>>);
    thread_local! {
        static ESCAPE: Cell<Option<Gc<Cycle>>> = const { Cell::new(None) };
    }

    unsafe impl<V: Visitor> TraceWith<V> for Cycle {
        fn accept(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    impl Drop for Cycle {
        fn drop(&mut self) {
            ESCAPE.set(take(&mut self.0));
        }
    }

    let c1 = Gc::new_cyclic(|gc| Cycle(Some(gc)));
    drop(c1);
    collect();

    // `ESCAPE` is now a dead pointer

    let alloc = Gc::new(ESCAPE.take().unwrap());
    let alloc2 = alloc.clone();
    drop(alloc);
    drop(alloc2);
    collect(); // if correct, this collection should not panic or encounter UB when collecting
               // `alloc`
}

#[test]
/// Test that creating a `Gc` during a `Drop` implementation will still not leak the `Gc`.
fn leak_by_creation_in_drop() {
    static DID_BAR_DROP: AtomicBool = AtomicBool::new(false);
    struct Foo(OnceCell<Gc<Self>>);
    struct Bar(OnceCell<Gc<Self>>);

    unsafe impl<V: Visitor> TraceWith<V> for Foo {
        fn accept(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    unsafe impl<V: Visitor> TraceWith<V> for Bar {
        fn accept(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            let gcbar = Gc::new(Bar(OnceCell::new()));
            let _ = gcbar.0.set(gcbar.clone());
            drop(gcbar);
        }
    }

    impl Drop for Bar {
        fn drop(&mut self) {
            DID_BAR_DROP.store(true, Ordering::Relaxed);
        }
    }

    let foo = Gc::new(Foo(OnceCell::new()));
    let _ = foo.0.set(foo.clone());
    drop(foo);
    collect(); // causes Bar to be created and then leaked
    collect(); // cleans up Bar
    assert!(DID_BAR_DROP.load(Ordering::Relaxed));
}

#[test]
#[cfg_attr(miri, ignore = "miri is too slow")]
#[expect(clippy::too_many_lines)]
fn unsync_fuzz() {
    const N: usize = 100_000;
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
            let n_drop = DROP_DETECTORS[self.id].fetch_add(1, Ordering::Relaxed);
            assert_eq!(n_drop, 0, "must not double drop an allocation");
        }
    }

    unsafe impl<V: Visitor> TraceWith<V> for Alloc {
        fn accept(&self, visitor: &mut V) -> Result<(), ()> {
            self.refs.accept(visitor)
        }
    }

    fn dfs(alloc: &Gc<Alloc>, graph: &mut HashMap<usize, Vec<usize>>) {
        if let Entry::Vacant(v) = graph.entry(alloc.id) {
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
                // println!("add gc {next_detector}");
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
                    // println!("add ref {} -> {}", gcs[from].id, gcs[to].id);
                    let new_gc = gcs[to].clone();
                    let mut guard = gcs[from].refs.lock().unwrap();
                    guard.push(new_gc);
                }
            }
            2 => {
                let idx = fastrand::usize(0..gcs.len());
                // println!("remove gc {}", gcs[idx].id);
                gcs.swap_remove(idx);
            }
            3 => {
                let from = fastrand::usize(0..gcs.len());
                let mut guard = gcs[from].refs.lock().unwrap();
                if !guard.is_empty() {
                    let to = fastrand::usize(0..guard.len());
                    // println!("drop ref {} -> {}", gcs[from].id, guard[to].id);
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
    // println!("{graph:#?}");

    drop(gcs);
    collect();

    let mut n_missing = 0;
    for count in &DROP_DETECTORS[..next_detector] {
        let num = count.load(Ordering::Relaxed);
        if num != 1 {
            // println!("expected 1 for id {id} but got {num}");
            n_missing += 1;
        }
    }
    assert_eq!(n_missing, 0);
}

#[test]
fn custom_trait_object() {
    trait MyTrait: Trace + Send + Sync {}
    impl<T: Trace + Send + Sync> MyTrait for T {}

    let gc = Gc::new(5i32);
    let gc: Gc<dyn MyTrait> = coerce_gc!(gc);
    _ = gc;
}

#[test]
fn coerce_option_gc_using_macro() {
    let gc: OptionGc<[i32]> = coerce_option_gc!(OptionGc::some(Gc::new([1, 2, 3])));
    assert_eq!(gc.as_deref().unwrap(), &[1, 2, 3]);

    let gc: OptionGc<dyn Trace> = coerce_option_gc!(OptionGc::some(Gc::new(1)));
    assert!(gc.is_some());

    let gc: OptionGc<[i32]> = coerce_option_gc!(OptionGc::<[i32; 3]>::NONE);
    assert!(gc.is_none());

    let gc: OptionGc<dyn Trace> = coerce_option_gc!(OptionGc::<i32>::NONE);
    assert!(gc.is_none());
}

#[test]
#[cfg(feature = "coerce-unsized")]
fn coerce_option_gc() {
    let gc: Gc<[u8; 3]> = Gc::new([1, 2, 3]);
    let slice: OptionGc<[u8]> = OptionGc::some(gc.clone());
    let trait_object: OptionGc<dyn Trace> = OptionGc::some(gc);
    _ = slice;
    _ = trait_object;
}
