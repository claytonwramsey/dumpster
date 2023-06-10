use std::{
    alloc::{dealloc, Layout},
    cell::Cell,
    collections::HashMap,
    marker::PhantomData,
    ops::Deref,
    ptr::{self, NonNull},
};

#[cfg(test)]
mod tests;

/// The trait that any garbage-collectable data must implement.
///
/// This trait should usually be implemented by using `#[derive(Collectable)]`.
/// Only data structures using raw pointers or other magic should manually implement `Collectable`.
pub trait Collectable {
    /// Search through all allocations reachable from this value and return a map from its
    /// allocation ID to the allocations which could be found that point to it.
    fn add_to_parent_map(
        &self,
        self_id: AllocationId,
        map: &mut HashMap<AllocationId, Vec<AllocationId>>,
    );
}

/// A garbage-collected pointer.
pub struct Gc<T: Collectable + ?Sized> {
    /// A pointer to the heap allocation containing the data under concern.
    /// The pointee box should never be mutated.
    ptr: NonNull<GcBox<T>>,
    /// Phantom data to ensure correct lifetime analysis.
    _phantom: PhantomData<T>,
}

#[repr(C)]
/// The underlying heap allocation for a [`Gc`].
struct GcBox<T: Collectable + ?Sized> {
    /// The number of extant references to this garbage-collected data.
    ref_count: Cell<usize>,
    /// The stored value inside this garbage-collected box.
    value: T,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A unique identifier for an allocated garbage-collected block.
///
/// It contains a pointer to the reference count of the allocation.
pub struct AllocationId(NonNull<Cell<usize>>);

impl<T: Collectable + ?Sized> Gc<T> {
    /// Construct a new garbage-collected allocation, with `value` as its value.
    pub fn new(value: T) -> Gc<T>
    where
        T: Sized,
    {
        Gc {
            ptr: NonNull::from(Box::leak(Box::new(GcBox {
                ref_count: Cell::new(1),
                value,
            }))),
            _phantom: PhantomData,
        }
    }

    /// Get a unique ID for the data pointed to by this garbage-collected pointer.
    ///
    /// This is used especially for the implementation of [`Collectable::add_to_parent_map`].
    pub fn id(gc: &Gc<T>) -> AllocationId {
        unsafe { gc.ptr.as_ref().id() }
    }
}

impl<T: Collectable + ?Sized> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.ptr.as_ref().value }
    }
}

impl<T: Collectable + ?Sized> Clone for Gc<T> {
    #[allow(clippy::clone_on_copy)]
    /// Create a duplicate reference to the same data pointed to by `self`.
    /// This does not duplicate the data.
    fn clone(&self) -> Self {
        unsafe {
            let box_ref = self.ptr.as_ref();
            box_ref.ref_count.set(box_ref.ref_count.get() + 1);
        }
        Self {
            ptr: self.ptr.clone(),
            _phantom: self._phantom.clone(),
        }
    }
}

impl<T: Collectable + ?Sized> Drop for Gc<T> {
    /// Destroy this garbage-collected pointer.
    ///
    /// If this is the last reference which can reach the pointed-to data,
    fn drop(&mut self) {
        let box_ref = unsafe { self.ptr.as_ref() };
        let old_ref_count = box_ref.ref_count.get();
        println!("old ref count {old_ref_count}");
        box_ref.ref_count.set(old_ref_count - 1);
        if old_ref_count == 1 || box_ref.is_orphaned() {
            unsafe {
                ptr::drop_in_place(self.ptr.as_mut());
                dealloc(
                    self.ptr.as_ptr() as *mut u8,
                    Layout::for_value(self.ptr.as_ref()),
                )
            };
        }
    }
}

impl<T: Collectable + ?Sized> GcBox<T> {
    /// Get a unique ID for this allocation.
    fn id(&self) -> AllocationId {
        AllocationId(NonNull::from(&self.ref_count))
    }

    /// Determine whether this `GcBox` exists only because it is part of an orphaned cycle.
    fn is_orphaned(&self) -> bool {
        let mut parent_map = HashMap::new();
        parent_map.insert(self.id(), Vec::new());
        self.value.add_to_parent_map(self.id(), &mut parent_map);

        fn all_accounted_ancestors(
            id: AllocationId,
            parent_map: &mut HashMap<AllocationId, Vec<AllocationId>>,
        ) -> bool {
            match parent_map.remove(&id) {
                // we have already visited this node and verified its ancestors are accounted for
                None => true,
                Some(v) => {
                    if v.len() != unsafe { id.0.as_ref() }.get() {
                        // mismatched ref count and number of found parents
                        return false;
                    }
                    for next_parent in v {
                        if !all_accounted_ancestors(next_parent, parent_map) {
                            return false;
                        }
                    }
                    true
                }
            }
        }

        all_accounted_ancestors(self.id(), &mut parent_map)
    }
}
