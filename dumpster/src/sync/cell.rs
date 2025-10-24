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
pub struct UCell<T>(UnsafeCell<T>);

impl<T> UCell<T> {
    pub fn new(x: T) -> Self {
        Self(UnsafeCell::new(x))
    }

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

    pub unsafe fn set(&self, x: T) {
        #[cfg(loom)]
        {
            *self.0.get_mut().deref() = x;
        }
        #[cfg(not(loom))]
        {
            *self.0.get() = x
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
