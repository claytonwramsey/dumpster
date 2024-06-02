/*
    dumpster, acycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! Custom pointer types used by this garbage collector.

use std::{
    fmt,
    mem::{size_of, MaybeUninit},
    ptr::{addr_of, addr_of_mut, copy_nonoverlapping, NonNull},
};

#[repr(C)]
#[derive(Clone, Copy)]
/// A pointer for an allocation, extracted out as raw data.
/// This contains both the pointer and all the pointer's metadata, but hidden behind an unknown
/// interpretation.
/// We trust that all pointers (even to `?Sized` or `dyn` types) are 2 words or fewer in size.
/// This is a hack! Like, a big hack!
pub(crate) struct Erased([usize; 2]);

impl Erased {
    /// Construct a new erased pointer to some data from a reference
    ///
    /// # Panics
    ///
    /// This function will panic if the size of a reference is larger than the size of an
    /// `ErasedPtr`.
    /// To my knowledge, there are no pointer types with this property.
    pub fn new<T: ?Sized>(reference: NonNull<T>) -> Erased {
        let mut ptr = Erased([0; 2]);
        let ptr_size = size_of::<NonNull<T>>();
        // Extract out the pointer as raw memory
        assert!(
            ptr_size <= size_of::<Erased>(),
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
    /// via [`ErasedPtr::new`].
    pub unsafe fn specify<T: ?Sized>(self) -> NonNull<T> {
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

impl fmt::Debug for Erased {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ErasedPtr({:x?})", self.0)
    }
}

#[cfg(not(feature = "coerce-unsized"))]
/// A nullable pointer to an `?Sized` type.
///
/// We need this because it's actually impossible to create a null `*mut T` if `T` is `?Sized`.
pub(crate) struct Nullable<T: ?Sized>(Option<NonNull<T>>);
#[cfg(feature = "coerce-unsized")]
/// A nullable pointer to an `?Sized` type.
///
/// We need this because it's actually impossible to create a null `*mut T` if `T` is `?Sized`.
pub(crate) struct Nullable<T: ?Sized>(*mut T);

impl<T: ?Sized> Nullable<T> {
    /// Create a new nullable pointer from a non-null pointer.
    pub fn new(ptr: NonNull<T>) -> Nullable<T> {
        #[cfg(not(feature = "coerce-unsized"))]
        {
            Nullable(Some(ptr))
        }
        #[cfg(feature = "coerce-unsized")]
        {
            Nullable(ptr.as_ptr())
        }
    }

    #[allow(clippy::unused_self)]
    /// Convert this pointer to a null pointer.
    pub fn as_null(self) -> Nullable<T> {
        #[cfg(not(feature = "coerce-unsized"))]
        {
            Nullable(None)
        }
        #[cfg(feature = "coerce-unsized")]
        {
            Nullable(self.0.with_addr(0))
        }
    }

    /// Determine whether this pointer is null.
    pub fn is_null(self) -> bool {
        self.as_option().is_none()
    }

    /// Convert this pointer to an `Option<NonNull<T>>`.
    pub fn as_option(self) -> Option<NonNull<T>> {
        #[cfg(not(feature = "coerce-unsized"))]
        {
            self.0
        }
        #[cfg(feature = "coerce-unsized")]
        {
            NonNull::new(self.0)
        }
    }

    /// Convert this pointer to a `NonNull<T>`, panicking if this pointer is null with message
    /// `msg`.
    pub fn expect(self, msg: &str) -> NonNull<T> {
        self.as_option().expect(msg)
    }

    /// Convert this pointer to a `NonNull<T>`, panicking if this pointer is null.
    pub fn unwrap(self) -> NonNull<T> {
        self.as_option().unwrap()
    }
}

impl<T: ?Sized> Clone for Nullable<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: ?Sized> Copy for Nullable<T> {}

#[cfg(feature = "coerce-unsized")]
impl<T, U> std::ops::CoerceUnsized<Nullable<U>> for Nullable<T>
where
    T: std::marker::Unsize<U> + ?Sized,
    U: ?Sized,
{
}

impl<T: ?Sized> fmt::Debug for Nullable<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Nullable({:x?})", self.0)
    }
}

#[cfg(test)]
mod tests {
    use std::alloc::{dealloc, Layout};

    use super::*;

    #[test]
    fn erased_alloc() {
        let orig_ptr = Box::leak(Box::new(7u8));
        let erased_ptr = Erased::new(NonNull::from(orig_ptr));

        unsafe {
            let remade_ptr = erased_ptr.specify::<u8>();
            dealloc(remade_ptr.as_ptr(), Layout::for_value(remade_ptr.as_ref()));
        }
    }
}
