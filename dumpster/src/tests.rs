use super::*;
use std::{
    cell::RefCell,
    sync::atomic::{AtomicBool, AtomicU8, Ordering},
};

#[test]
fn simple() {
    static DROPPED: AtomicBool = AtomicBool::new(false);
    struct Foo(u8);

    impl Drop for Foo {
        fn drop(&mut self) {
            DROPPED.store(true, Ordering::Relaxed);
        }
    }

    impl Collectable for Foo {
        fn add_to_ref_graph<const IS_ALLOCATION: bool>(
            &self,
            self_ref: AllocationId,
            ref_graph: &mut RefGraph,
        ) {
            if IS_ALLOCATION && ref_graph.mark_visited(self_ref) {
                return;
            }
            self.0.add_to_ref_graph::<false>(self_ref, ref_graph);
        }
    }

    let gc1 = Gc::new(Foo(1));
    let gc2 = Gc::clone(&gc1);

    assert!(!DROPPED.load(Ordering::Relaxed));

    drop(gc1);

    assert!(!DROPPED.load(Ordering::Relaxed));

    drop(gc2);

    assert!(DROPPED.load(Ordering::Relaxed));
}

#[test]
fn cyclic() {
    static DROPPED: AtomicU8 = AtomicU8::new(0);
    struct Foo(RefCell<Option<Gc<Foo>>>);

    impl Collectable for Foo {
        fn add_to_ref_graph<const IS_ALLOCATION: bool>(
            &self,
            self_ref: AllocationId,
            ref_graph: &mut RefGraph,
        ) {
            if IS_ALLOCATION && ref_graph.mark_visited(self_ref) {
                return;
            }
            self.0.add_to_ref_graph::<false>(self_ref, ref_graph);
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
