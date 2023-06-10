use super::*;
use std::sync::atomic::{AtomicBool, Ordering};

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
        fn add_to_parent_map(
            &self,
            _: AllocationId,
            _: &mut HashMap<AllocationId, Vec<AllocationId>>,
        ) {
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
