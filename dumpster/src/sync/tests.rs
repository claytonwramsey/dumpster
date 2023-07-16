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
    sync::atomic::{AtomicUsize, Ordering},
    thread::sleep,
    time::Duration,
};

use crate::{Destroyer, Visitor};

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

    unsafe fn destroy_gcs<D: crate::Destroyer>(&mut self, _: &mut D) {}
}

struct MultiRef<'a> {
    refs: Mutex<Vec<Gc<MultiRef<'a>>>>,
    #[allow(unused)]
    count: DropCount<'a>,
}

unsafe impl<'a> Collectable for MultiRef<'a> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.refs.accept(visitor)
    }

    unsafe fn destroy_gcs<D: Destroyer>(&mut self, destroyer: &mut D) {
        self.refs.destroy_gcs(destroyer);
    }
}

#[test]
#[ignore = "searching for the broken one"]
fn single_alloc() {
    let drop_count = AtomicUsize::new(0);
    let gc1 = Gc::new(DropCount(&drop_count));

    assert_eq!(drop_count.load(Ordering::Acquire), 0);
    drop(gc1);
    assert_eq!(drop_count.load(Ordering::Acquire), 1);
}

#[test]
#[ignore = "searching for the broken one"]
fn ref_count() {
    let drop_count = AtomicUsize::new(0);
    let gc1 = Gc::new(DropCount(&drop_count));
    let gc2 = Gc::clone(&gc1);

    assert_eq!(drop_count.load(Ordering::Acquire), 0);
    drop(gc1);
    assert_eq!(drop_count.load(Ordering::Acquire), 0);
    drop(gc2);
    assert_eq!(drop_count.load(Ordering::Acquire), 1);
}

#[test]
fn self_referential() {
    struct Foo(Mutex<Option<Gc<Foo>>>);
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    unsafe impl Collectable for Foo {
        fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
            self.0.accept(visitor)
        }

        unsafe fn destroy_gcs<D: Destroyer>(&mut self, destroyer: &mut D) {
            println!("calling destroy_gcs in self_referential");
            self.0.destroy_gcs(destroyer);
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
#[ignore = "searching for the broken one"]
fn two_cycle() {
    let drop0 = AtomicUsize::new(0);
    let drop1 = AtomicUsize::new(0);

    let gc0 = Gc::new(MultiRef {
        refs: Mutex::new(Vec::new()),
        count: DropCount(&drop0),
    });
    let gc1 = Gc::new(MultiRef {
        refs: Mutex::new(vec![Gc::clone(&gc0)]),
        count: DropCount(&drop1),
    });
    gc0.refs.lock().unwrap().push(Gc::clone(&gc1));

    collect();
    assert_eq!(drop0.load(Ordering::Acquire), 0);
    assert_eq!(drop0.load(Ordering::Acquire), 0);
    drop(gc0);
    collect();
    assert_eq!(drop0.load(Ordering::Acquire), 0);
    assert_eq!(drop0.load(Ordering::Acquire), 0);
    drop(gc1);
    collect();
    assert_eq!(drop0.load(Ordering::Acquire), 1);
    assert_eq!(drop0.load(Ordering::Acquire), 1);
}

#[test]
fn self_ref_two_cycle() {
    let drop0 = AtomicUsize::new(0);
    let drop1 = AtomicUsize::new(0);

    let gc0 = Gc::new(MultiRef {
        refs: Mutex::new(Vec::new()),
        count: DropCount(&drop0),
    });
    let gc1 = Gc::new(MultiRef {
        refs: Mutex::new(vec![Gc::clone(&gc0)]),
        count: DropCount(&drop1),
    });
    gc0.refs.lock().unwrap().extend([gc0.clone(), gc1.clone()]);
    gc1.refs.lock().unwrap().push(gc1.clone());

    collect();
    assert_eq!(drop0.load(Ordering::Acquire), 0);
    assert_eq!(drop0.load(Ordering::Acquire), 0);
    drop(gc0);
    collect();
    assert_eq!(drop0.load(Ordering::Acquire), 0);
    assert_eq!(drop0.load(Ordering::Acquire), 0);
    drop(gc1);
    collect();
    assert_eq!(drop0.load(Ordering::Acquire), 1);
    assert_eq!(drop0.load(Ordering::Acquire), 1);
}

#[test]
#[ignore = "searching for the broken one"]
fn parallel_loop() {
    let count1 = AtomicUsize::new(0);
    let count2 = AtomicUsize::new(0);
    let count3 = AtomicUsize::new(0);
    let count4 = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        count: DropCount(&count1),
        refs: Mutex::new(Vec::new()),
    });
    let gc2 = Gc::new(MultiRef {
        count: DropCount(&count2),
        refs: Mutex::new(vec![Gc::clone(&gc1)]),
    });
    let gc3 = Gc::new(MultiRef {
        count: DropCount(&count3),
        refs: Mutex::new(vec![Gc::clone(&gc1)]),
    });
    let gc4 = Gc::new(MultiRef {
        count: DropCount(&count4),
        refs: Mutex::new(vec![Gc::clone(&gc2), Gc::clone(&gc3)]),
    });
    gc1.refs.lock().unwrap().push(Gc::clone(&gc4));

    assert_eq!(count1.load(Ordering::Acquire), 0);
    assert_eq!(count2.load(Ordering::Acquire), 0);
    assert_eq!(count3.load(Ordering::Acquire), 0);
    assert_eq!(count4.load(Ordering::Acquire), 0);
    drop(gc1);
    collect();
    assert_eq!(count1.load(Ordering::Acquire), 0);
    assert_eq!(count2.load(Ordering::Acquire), 0);
    assert_eq!(count3.load(Ordering::Acquire), 0);
    assert_eq!(count4.load(Ordering::Acquire), 0);
    drop(gc2);
    collect();
    assert_eq!(count1.load(Ordering::Acquire), 0);
    assert_eq!(count2.load(Ordering::Acquire), 0);
    assert_eq!(count3.load(Ordering::Acquire), 0);
    assert_eq!(count4.load(Ordering::Acquire), 0);
    drop(gc3);
    collect();
    assert_eq!(count1.load(Ordering::Acquire), 0);
    assert_eq!(count2.load(Ordering::Acquire), 0);
    assert_eq!(count3.load(Ordering::Acquire), 0);
    assert_eq!(count4.load(Ordering::Acquire), 0);
    drop(gc4);
    collect();
    assert_eq!(count1.load(Ordering::Acquire), 1);
    assert_eq!(count2.load(Ordering::Acquire), 1);
    assert_eq!(count3.load(Ordering::Acquire), 1);
    assert_eq!(count4.load(Ordering::Acquire), 1);
}

#[test]
#[ignore = "searching for the broken one"]
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
#[ignore = "searching for the broken one"]
fn open_drop() {
    let count1 = AtomicUsize::new(0);
    let gc1 = Gc::new(MultiRef {
        refs: Mutex::new(Vec::new()),
        count: DropCount(&count1),
    });

    gc1.refs.lock().unwrap().push(gc1.clone());
    let guard = gc1.refs.lock();
    collect();
    assert_eq!(count1.load(Ordering::Acquire), 0);
    drop(guard);
    drop(gc1);
    collect();

    assert_eq!(count1.load(Ordering::Acquire), 1);
}

#[test]
#[ignore = "searching for the broken one"]
fn eventually_collect() {
    let count1 = AtomicUsize::new(0);
    let count2 = AtomicUsize::new(0);

    let gc1 = Gc::new(MultiRef {
        refs: Mutex::new(Vec::new()),
        count: DropCount(&count1),
    });
    let gc2 = Gc::new(MultiRef {
        refs: Mutex::new(vec![gc1.clone()]),
        count: DropCount(&count2),
    });
    gc1.refs.lock().unwrap().push(gc2.clone());

    assert_eq!(count1.load(Ordering::Acquire), 0);
    assert_eq!(count2.load(Ordering::Acquire), 0);

    drop(gc1);
    drop(gc2);

    for _ in 0..100 {
        let gc = Gc::new(());
        drop(gc);
    }

    // after enough time, gc1 and gc2 should have been collected
    assert_eq!(count1.load(Ordering::Acquire), 1);
    assert_eq!(count2.load(Ordering::Acquire), 1);
}
