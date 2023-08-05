use std::{
    cell::RefCell,
    rc::Rc,
    sync::{Arc, Mutex},
};

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

/// A samle multi-reference which uses `Rc`, which is technically not a garbage collector, as a
/// baseline.
pub struct RcMultiref {
    refs: RefCell<Vec<Rc<Self>>>,
}

/// A samle multi-reference which uses `Arc`, which is technically not a garbage collector, as a
/// baseline.
pub struct ArcMultiref {
    refs: Mutex<Vec<Arc<Self>>>,
}

#[derive(dumpster_derive::Collectable)]
pub struct DumpsterSyncMultiref {
    refs: Mutex<Vec<dumpster::sync::Gc<Self>>>,
}

#[derive(dumpster_derive::Collectable)]
pub struct DumpsterUnsyncMultiref {
    refs: RefCell<Vec<dumpster::unsync::Gc<Self>>>,
}

pub struct GcMultiref {
    refs: gc::GcCell<Vec<gc::Gc<GcMultiref>>>,
}

pub struct BaconRajanMultiref {
    refs: RefCell<Vec<bacon_rajan_cc::Cc<Self>>>,
}

#[derive(shredder_derive::Scan)]
pub struct ShredderMultiref {
    refs: RefCell<Vec<shredder::Gc<Self>>>,
}

#[derive(shredder_derive::Scan)]
pub struct ShredderSyncMultiref {
    refs: Mutex<Vec<shredder::Gc<Self>>>,
}

impl bacon_rajan_cc::Trace for BaconRajanMultiref {
    fn trace(&self, tracer: &mut bacon_rajan_cc::Tracer) {
        self.refs.borrow().trace(tracer);
    }
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
        dumpster::unsync::collect()
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

impl Multiref for bacon_rajan_cc::Cc<BaconRajanMultiref> {
    fn new(points_to: Vec<Self>) -> Self {
        bacon_rajan_cc::Cc::new(BaconRajanMultiref {
            refs: RefCell::new(points_to),
        })
    }

    fn apply(&self, f: impl FnOnce(&mut Vec<Self>)) {
        f(self.refs.borrow_mut().as_mut());
    }

    fn collect() {
        bacon_rajan_cc::collect_cycles();
        assert_eq!(bacon_rajan_cc::number_of_roots_buffered(), 0);
    }
}

impl Multiref for shredder::Gc<ShredderMultiref> {
    fn new(points_to: Vec<Self>) -> Self {
        shredder::Gc::new(ShredderMultiref {
            refs: RefCell::new(points_to),
        })
    }

    fn apply(&self, f: impl FnOnce(&mut Vec<Self>)) {
        f(self.get().refs.borrow_mut().as_mut());
    }

    fn collect() {
        shredder::synchronize_destructors();
    }
}

impl Multiref for Rc<RcMultiref> {
    fn new(points_to: Vec<Self>) -> Self {
        Rc::new(RcMultiref {
            refs: RefCell::new(points_to),
        })
    }

    fn apply(&self, f: impl FnOnce(&mut Vec<Self>)) {
        f(self.refs.borrow_mut().as_mut());
    }

    fn collect() {}
}

impl Multiref for Arc<ArcMultiref> {
    fn new(points_to: Vec<Self>) -> Self {
        Arc::new(ArcMultiref {
            refs: Mutex::new(points_to),
        })
    }

    fn apply(&self, f: impl FnOnce(&mut Vec<Self>)) {
        f(self.refs.lock().unwrap().as_mut());
    }

    fn collect() {}
}
