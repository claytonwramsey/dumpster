use std::{cell::RefCell, sync::Mutex};

/// A garbage-collected structure which points to an arbitrary number of other garbage-collected
/// structures.
///
/// Cloning a `Multiref` yields a duplicated pointer, not a deep copy.
pub trait Multiref: Clone {
    /// Create a new multiref which points to some data.
    fn new(points_to: Vec<Self>) -> Self;
    /// Apply some function to the backing set of references owned by this structure.
    fn apply(&self, f: impl FnOnce(&mut Vec<Self>));
    /// Collect all the floating GCs out there.
    fn collect();
}

/// A trait for thread-safe synchronized multirefs.
pub trait SyncMultiref: Sync + Multiref {}

impl<T> SyncMultiref for T where T: Sync + Multiref {}

#[derive(dumpster_derive::Collectable)]
pub struct DumpsterSyncMultiref {
    refs: Mutex<Vec<dumpster::sync::Gc<DumpsterSyncMultiref>>>,
}

#[derive(dumpster_derive::Collectable)]
pub struct DumpsterUnsyncMultiref {
    refs: RefCell<Vec<dumpster::unsync::Gc<DumpsterUnsyncMultiref>>>,
}

pub struct GcMultiref {
    refs: gc::GcCell<Vec<gc::Gc<GcMultiref>>>,
}

impl gc::Finalize for GcMultiref {}

unsafe impl gc::Trace for GcMultiref {
    #[inline]
    unsafe fn trace(&self) {
        self.refs.trace();
    }

    #[inline]
    unsafe fn root(&self) {
        self.refs.root();
    }

    #[inline]
    unsafe fn unroot(&self) {
        self.refs.unroot();
    }

    #[inline]
    fn finalize_glue(&self) {
        self.refs.finalize_glue()
    }
}

impl Multiref for dumpster::sync::Gc<DumpsterSyncMultiref> {
    fn new(points_to: Vec<Self>) -> Self {
        dumpster::sync::Gc::new(DumpsterSyncMultiref {
            refs: Mutex::new(points_to),
        })
    }

    fn apply(&self, f: impl FnOnce(&mut Vec<Self>)) {
        f(self.refs.lock().unwrap().as_mut());
    }

    fn collect() {
        dumpster::sync::collect()
    }
}

impl Multiref for dumpster::unsync::Gc<DumpsterUnsyncMultiref> {
    fn new(points_to: Vec<Self>) -> Self {
        dumpster::unsync::Gc::new(DumpsterUnsyncMultiref {
            refs: RefCell::new(points_to),
        })
    }

    fn apply(&self, f: impl FnOnce(&mut Vec<Self>)) {
        f(self.refs.borrow_mut().as_mut());
    }

    fn collect() {
        dumpster::sync::collect()
    }
}

impl Multiref for gc::Gc<GcMultiref> {
    fn new(points_to: Vec<Self>) -> Self {
        gc::Gc::new(GcMultiref {
            refs: gc::GcCell::new(points_to),
        })
    }

    fn apply(&self, f: impl FnOnce(&mut Vec<Self>)) {
        f(self.refs.borrow_mut().as_mut())
    }

    fn collect() {
        gc::force_collect();
    }
}
