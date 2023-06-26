//! Thread-local garbage collection.

use std::{
    alloc::{dealloc, Layout},
    cell::Cell,
    marker::PhantomData,
    ops::Deref,
    ptr::{drop_in_place, NonNull},
};

use crate::{Collectable, Destroyer, Visitor};

use self::collect::{AllocationId, Dumpster, DUMPSTER};

mod collect;
#[cfg(test)]
mod tests;

#[derive(Debug)]
/// A garbage-collected pointer.
///
/// # Examples
///
/// ```
/// use dumpster::Gc;
///
/// let x: Gc<u8> = Gc::new(3);
///
/// println!("{}", *x); // prints '3'
///                     // x is then freed automatically!
/// ```
pub struct Gc<T: Collectable + ?Sized> {
    /// A pointer to the heap allocation containing the data under concern.
    /// The pointee box should never be mutated.
    ptr: Option<NonNull<GcBox<T>>>,
    /// Phantom data to ensure correct lifetime analysis.
    _phantom: PhantomData<T>,
}

/// Collect all existing unreachable allocations.
///
/// This only collects the allocations local to the caller's thread.
pub fn collect() {
    DUMPSTER.with(Dumpster::collect_all);
}

#[repr(C)]
/// The underlying heap allocation for a [`Gc`].
struct GcBox<T: Collectable + ?Sized> {
    /// The number of extant references to this garbage-collected data.
    /// If the stored reference count is zero, then this value is a "zombie" - in the process of
    /// being dropped - and should not be dropped again.
    ref_count: Cell<usize>,
    /// The stored value inside this garbage-collected box.
    value: T,
}

impl<T: Collectable + ?Sized> Gc<T> {
    /// Construct a new garbage-collected allocation, with `value` as its value.
    pub fn new(value: T) -> Gc<T>
    where
        T: Sized,
    {
        DUMPSTER.with(|d| d.n_refs_living.set(d.n_refs_living.get() + 1));
        Gc {
            ptr: Some(NonNull::from(Box::leak(Box::new(GcBox {
                ref_count: Cell::new(1),
                value,
            })))),
            _phantom: PhantomData,
        }
    }
}

impl<T: Collectable + ?Sized> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            &self
                .ptr
                .expect("Dereferenced Gc during Drop")
                .as_ref()
                .value
        }
    }
}

impl<T: Collectable + ?Sized> Clone for Gc<T> {
    #[allow(clippy::clone_on_copy)]
    /// Create a duplicate reference to the same data pointed to by `self`.
    /// This does not duplicate the data.
    fn clone(&self) -> Self {
        unsafe {
            let box_ref = self.ptr.unwrap().as_ref();
            box_ref.ref_count.set(box_ref.ref_count.get() + 1);
        }
        DUMPSTER.with(|d| d.n_refs_living.set(d.n_refs_living.get() + 1));
        Self {
            ptr: self.ptr.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<T: Collectable + ?Sized> Drop for Gc<T> {
    /// Destroy this garbage-collected pointer.
    ///
    /// If this is the last reference which can reach the pointed-to data, the allocation that it
    /// points to will be destroyed.
    fn drop(&mut self) {
        if let Some(mut ptr) = self.ptr {
            DUMPSTER.with(|d| {
                // Decrement the number of living references and increment the total number of
                // dropped references
                d.n_ref_drops.set(d.n_ref_drops.get() + 1);
                d.n_refs_living.set(d.n_refs_living.get() - 1);
                unsafe {
                    let box_ref = ptr.as_ref();
                    match box_ref.ref_count.get() {
                        0 => (), // allocation is already being destroyed
                        1 => {
                            d.mark_cleaned(box_ref);
                            // this was the last reference, drop unconditionally
                            drop_in_place(ptr.as_mut());
                            // note: `box_ref` is no longer usable
                            dealloc(ptr.as_ptr().cast::<u8>(), Layout::for_value(ptr.as_ref()));
                        }
                        n => {
                            // decrement the ref count - but another reference to this data still
                            // lives
                            box_ref.ref_count.set(n - 1);
                            // remaining references could be a cycle - therefore, mark it as dirty
                            // so we can check later
                            d.mark_dirty(box_ref);

                            // check if it's been a long time since the last time we collected all
                            // the garbage.
                            // if so, go and collect it all again (amortized O(1))
                            if d.n_ref_drops.get() << 1 >= d.n_refs_living.get() {
                                d.collect_all();
                            }
                        }
                    }
                }
            });
        }
    }
}

unsafe impl<T: Collectable + ?Sized> Collectable for Gc<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) {
        visitor.visit_unsync(self);
    }

    unsafe fn destroy_gcs<D: Destroyer>(&mut self, visitor: &mut D) {
        visitor.visit_unsync(self);
    }
}

impl<T: Collectable + ?Sized> GcBox<T> {
    /// Get a unique ID for this allocation.
    fn id(&self) -> AllocationId {
        AllocationId(NonNull::from(&self.ref_count))
    }
}
