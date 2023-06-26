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

#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]

use std::{
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
pub unsafe trait Collectable {
    fn accept<V: Visitor>(&self, visitor: &mut V);
    unsafe fn destroy_gcs<D: Destroyer>(&mut self, destroyer: &mut D);
}

pub trait Visitor {
    fn visit_sync<T>(&mut self, gc: &sync::Gc<T>)
    where
        T: Collectable + Sync + ?Sized;
    fn visit_unsync<T>(&mut self, gc: &unsync::Gc<T>)
    where
        T: Collectable + ?Sized;
}

pub trait Destroyer {
    fn visit_sync<T>(&mut self, gc: &mut sync::Gc<T>)
    where
        T: Collectable + Sync + ?Sized;
    fn visit_unsync<T>(&mut self, gc: &mut unsync::Gc<T>)
    where
        T: Collectable + ?Sized;
}

const MAX_PTR_SIZE: usize = 2 * size_of::<usize>() / size_of::<u8>();

#[repr(align(16))]
#[derive(Clone, Copy)]
/// A pointer for an allocation, extracted out as raw data.
/// This contains both the pointer and all the pointer's metadata, but hidden behind an unknown
/// interpretation.
/// We trust that all pointers (even to `?Sized` or `dyn` types) are 2 words or fewer in size.
/// This is a hack! Like, a big hack!
struct OpaquePtr([u8; MAX_PTR_SIZE]);

impl OpaquePtr {
    /// Construct a new opaque pointer to some data from a reference
    ///
    /// # Panics
    ///
    /// This function will panic if the size of a reference is larger than `MAX_PTR_SIZE`.
    fn new<T: ?Sized>(reference: &T) -> OpaquePtr {
        let mut ptr = OpaquePtr([0; MAX_PTR_SIZE]);
        let ptr_size = size_of::<&T>();

        println!(
            "store pointer size {ptr_size}, address {:?}",
            reference as *const T
        );
        // Extract out the pointer as raw memory
        assert!(
            ptr_size <= MAX_PTR_SIZE,
            "pointers to T are too big for storage"
        );
        unsafe {
            // SAFETY: We know that `cleanup` has at least as much space as `ptr_size`, and that
            // `box_ref` has size equal to `ptr_size`.
            println!(
                "copy from {:?} to {:?}",
                addr_of!(reference).cast::<u8>(),
                addr_of_mut!(ptr.0)
            );
            copy_nonoverlapping(
                addr_of!(reference).cast::<u8>(),
                addr_of_mut!(ptr.0).cast(),
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
        copy_nonoverlapping(
            addr_of!(self.0),
            addr_of_mut!(box_ref).cast(),
            size_of::<MaybeUninit<NonNull<T>>>(),
        );
        println!("specify pointer size {}, address {:?}", size_of::<NonNull<T>>(),
        box_ref.assume_init());
        box_ref.assume_init()
    }
}
