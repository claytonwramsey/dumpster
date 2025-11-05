/*
    dumpster, a cycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! A shim for using either Loom or the standard library in garbage-collected environments.

#[cfg(loom)]
use loom::cell::UnsafeCell;

#[cfg(not(loom))]
use std::cell::UnsafeCell;

#[derive(Debug)]
/// An unsafe cell that is agnostic over using `std` or `loom` as its backing implementation.
/// It is intended to only be used with [`Copy`] data.
pub struct UCell<T>(UnsafeCell<T>);

impl<T> UCell<T> {
    /// Construct a `UCell` containing the value.
    #[cfg(loom)]
    pub fn new(x: T) -> Self {
        Self(UnsafeCell::new(x))
    }

    /// Construct a `UCell` containing the value.
    #[cfg(not(loom))]
    pub const fn new(x: T) -> Self {
        Self(UnsafeCell::new(x))
    }

    /// Get the value inside the `UCell`.
    ///
    /// # Safety
    ///
    /// This function can only be called when no other code is calling [`UCell::set`].
    pub unsafe fn get(&self) -> T
    where
        T: Copy,
    {
        #[cfg(loom)]
        {
            *self.0.get().deref()
        }
        #[cfg(not(loom))]
        {
            *self.0.get()
        }
    }

    /// Overwrite the value inside this cell.
    ///
    /// # Safety
    ///
    /// This function can only be called when no other code is calling [`UCell::set`] or
    /// [`UCell::get`].
    pub unsafe fn set(&self, x: T) {
        #[cfg(loom)]
        {
            *self.0.get_mut().deref() = x;
        }
        #[cfg(not(loom))]
        {
            *self.0.get() = x;
        }
    }
}

#[cfg(not(loom))]
#[cfg(feature = "coerce-unsized")]
impl<T, U> std::ops::CoerceUnsized<UCell<crate::ptr::Nullable<U>>>
    for UCell<crate::ptr::Nullable<T>>
where
    T: std::marker::Unsize<U> + ?Sized,
    U: ?Sized,
{
}
