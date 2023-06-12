#![cfg(test)]

use std::sync::atomic::{AtomicU8, Ordering};

use dumpster::Gc;
use dumpster_derive::Collectable;

#[derive(Collectable)]
struct Empty;

#[derive(Collectable)]
struct UnitTuple();

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
