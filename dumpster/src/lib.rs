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

//! A cycle-tracking garbage collector.
//!
//! Most garbage collecters are _tracing_ garbage collectors, meaning that they keep track of a set
//! of roots which are directly accessible from the stack, and then use those roots to find the set
//! of all accessible allocations.
//! However, because Rust does not allow us to hook into when a value is moved, it's quite difficult
//! to detect when a garbage-collected value stops being a root.
//!
//! `dumpster` takes a different approach.
//! It begins by using simple reference counting, then automatically detects cycles.
//! Allocations are freed when their reference count reaches zero or when they are only accessible
//! via their descendants.
//!
//! Garbage-collected pointers can be created and destroyed in _O(1)_ amortized time, but destroying
//! a garbage-collected pointer may take _O(r)_, where _r_ is the number of existing
//! garbage-collected references, on occasion.
//! However, the sweeps that require _O(r)_ performance are performed once every _O(1/r)_ times
//! a reference is dropped, yielding an amortized _O(1)_ runtime.
//!
//! # Module structure
//!
//! `dumpster` contains 3 core modules: the root (this module), as well as [`sync`] and [`unsync`].
//! `sync` contains an implementation of thread-safe garbage-collected pointers, while `unsync`
//! contains an implementation of thread-local garbage-collected pointers which cannot be shared
//! across threads.
//! Thread-safety requires some synchronization overhead, so for a single-threaded application,
//! it is recommended to use `unsync`.
//!
//! The project root contains common definitions across both `sync` and `unsync`.
//! Types which implement [`Collectable`] can immediately be used in `unsync`, but in order to use
//! `sync`'s garbage collector, the types must also implement [`Sync`].

#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]
#![allow(clippy::multiple_crate_versions, clippy::result_unit_err)]

use std::{
    fmt,
    mem::{size_of, MaybeUninit},
    ptr::{addr_of, addr_of_mut, copy_nonoverlapping, NonNull},
};

mod impls;

pub mod sync;
pub mod unsync;

/// The trait that any garbage-collectable data must implement.
///
/// This trait should usually be implemented by using `#[derive(Collectable)]`, using the macro from
/// the crate `dumpster_derive`.
/// Only data structures using raw pointers or other magic should manually implement `Collectable`.
///
/// # Safety
///
/// If the implementation of this trait is incorrect, this will result in undefined behavior,
/// typically double-frees or use-after-frees.
/// This includes [`Collectable::accept`], even though it is a safe function, since its correctness
/// is required for safety.
///
/// # Examples
///
/// Implementing `Collectable` for a scalar type which contains no garbage-collected references
/// is very easy.
/// Accepting a visitor and destroying all garbage-collected fields is simply a no-op.
///
/// ```
/// use dumpster::{Collectable, Destroyer, Visitor};
///
/// struct Foo(u8);
///
/// unsafe impl Collectable for Foo {
///     fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
///         Ok(())
///     }
///     unsafe fn destroy_gcs<D: Destroyer>(&mut self, destroyer: &mut D) {}
/// }
/// ```
///
/// However, if a data structure contains a garbage collected pointer, it must delegate to its
/// fields in `accept` and `destroy_gcs`.
///
/// ```
/// use dumpster::{unsync::Gc, Collectable, Destroyer, Visitor};
///
/// struct Bar(Gc<Bar>);
///
/// unsafe impl Collectable for Bar {
///     fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
///         self.0.accept(visitor)
///     }
///
///     unsafe fn destroy_gcs<D: Destroyer>(&mut self, destroyer: &mut D) {
///         self.0.destroy_gcs(destroyer);
///     }
/// }
/// ```
///
/// A data structure with two or more fields which could own a garbage-collected pointer should
/// delegate to both fields in a consistent order:
///
/// ```
/// use dumpster::{unsync::Gc, Collectable, Destroyer, Visitor};
///
/// struct Baz {
///     a: Gc<Baz>,
///     b: Gc<Baz>,
/// }
///
/// unsafe impl Collectable for Baz {
///     fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
///         self.a.accept(visitor)?;
///         self.b.accept(visitor)?;
///         Ok(())
///     }
///
///     unsafe fn destroy_gcs<D: Destroyer>(&mut self, destroyer: &mut D) {
///         self.a.destroy_gcs(destroyer);
///         self.b.destroy_gcs(destroyer);
///     }
/// }
/// ```
pub unsafe trait Collectable {
    /// Accept a visitor to this garbage-collected value.
    ///
    /// Implementors of this function need only delegate to all fields owned by this value which
    /// may contain a garbage-collected reference (either a [`sync::Gc`] or a [`unsync::Gc`]).
    ///
    /// For structures which have more than one field, they should return immediately after the
    /// first `Err` is returned from one of its fields.
    /// To do so efficiently, we recommend using the try operator (`?`) on each field and then
    /// returning `Ok(())` after delegating to each field.
    ///
    /// # Errors
    ///
    /// Errors are returned from this function whenever a field of this object returns an error
    /// after delegating acceptance to it, or if this value's data is inaccessible (such as
    /// attempting) to borrow from a [`RefCell`](std::cell::RefCell) which has already been
    /// mutably borrowed.
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()>;

    /// Destroy all garbage-collected fields of this structure, immediately prior to dropping it.
    ///
    /// Implementors of this function need only delegate to all of their fields which may contain
    /// a garbage-collected pointer, even if transitively.
    ///
    /// # Safety
    ///
    /// This function may not dereference any garbage-collected pointers during its execution.
    unsafe fn destroy_gcs<D: Destroyer>(&mut self, destroyer: &mut D);
}

/// A visitor for a garbage collected value.
///
/// This visitor allows us to hide details of the implementation of the garbage-collection procedure
/// from implementors of [`Collectable`].
///
/// When accepted by a `Collectable`, this visitor will be delegated down until it reaches a
/// garbage-collected pointer.
/// Then, the garabge-collected pointer will call one of `visit_sync` or `visit_unsync`, depending
/// on which type of pointer it is.
pub trait Visitor {
    /// Visit a synchronized garbage-collected pointer.
    fn visit_sync<T>(&mut self, gc: &sync::Gc<T>)
    where
        T: Collectable + Sync + ?Sized;

    /// Visit a thread-local garbage-collected pointer.
    fn visit_unsync<T>(&mut self, gc: &unsync::Gc<T>)
    where
        T: Collectable + ?Sized;
}

/// A destroyer for a garbage-collected pointer.
///
/// Unlike [`Visitor`], a `Destroyer` can mutate the garbage-collected pointers that it visits.
/// This enables it to mark garbage-collected pointers for deletion during a bulk cleanp of the
/// garbage collected value.
pub trait Destroyer {
    /// Visit a synchronized garbage-collected pointer.
    fn visit_sync<T>(&mut self, gc: &mut sync::Gc<T>)
    where
        T: Collectable + Sync + ?Sized;

    /// Visit a thread-local garbage-collected pointer.
    fn visit_unsync<T>(&mut self, gc: &mut unsync::Gc<T>)
    where
        T: Collectable + ?Sized;
}

#[repr(align(16))]
#[repr(C)]
#[derive(Clone, Copy)]
/// A pointer for an allocation, extracted out as raw data.
/// This contains both the pointer and all the pointer's metadata, but hidden behind an unknown
/// interpretation.
/// We trust that all pointers (even to `?Sized` or `dyn` types) are 2 words or fewer in size.
/// This is a hack! Like, a big hack!
struct OpaquePtr([usize; 2]);

impl OpaquePtr {
    /// Construct a new opaque pointer to some data from a reference
    ///
    /// # Panics
    ///
    /// This function will panic if the size of a reference is larger than the size of an
    /// `OpaquePtr`.
    /// To my knowledge, there are no pointer types with this property.
    fn new<T: ?Sized>(reference: NonNull<T>) -> OpaquePtr {
        let mut ptr = OpaquePtr([0; 2]);
        let ptr_size = size_of::<NonNull<T>>();
        // Extract out the pointer as raw memory
        assert!(
            ptr_size <= size_of::<OpaquePtr>(),
            "pointers to T are too big for storage"
        );
        unsafe {
            // SAFETY: We know that `cleanup` has at least as much space as `ptr_size`, and that
            // `box_ref` has size equal to `ptr_size`.
            copy_nonoverlapping(
                addr_of!(reference).cast::<u8>(),
                addr_of_mut!(ptr.0).cast::<u8>(),
                ptr_size,
            );
        }

        ptr
    }

    /// Specify this pointer into a pointer of a particular type.
    ///
    /// # Safety
    ///
    /// This function must only be specified to the type that the pointer was constructed with
    /// via [`OpaquePtr::new`].
    unsafe fn specify<T: ?Sized>(self) -> NonNull<T> {
        let mut box_ref: MaybeUninit<NonNull<T>> = MaybeUninit::zeroed();

        // For some reason, switching the ordering of casts causes this to create wacky undefined
        // behavior. Why? I don't know. I have better things to do than pontificate on this on a
        // Sunday afternoon.
        copy_nonoverlapping(
            addr_of!(self.0).cast::<u8>(),
            addr_of_mut!(box_ref).cast::<u8>(),
            size_of::<NonNull<T>>(),
        );

        box_ref.assume_init()
    }
}

impl fmt::Debug for OpaquePtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "OpaquePtr({:x?})", self.0)
    }
}

#[cfg(test)]
mod tests {
    use std::{
        alloc::{dealloc, Layout},
        mem::align_of,
    };

    use super::*;

    #[test]
    fn opaque_align() {
        assert_eq!(align_of::<OpaquePtr>(), 16);
    }

    #[test]
    fn opaque_alloc() {
        let orig_ptr = Box::leak(Box::new(7u8));
        let opaque_ptr = OpaquePtr::new(NonNull::from(orig_ptr));

        unsafe {
            let remade_ptr = opaque_ptr.specify::<u8>();
            dealloc(remade_ptr.as_ptr(), Layout::for_value(remade_ptr.as_ref()));
        }
    }
}
