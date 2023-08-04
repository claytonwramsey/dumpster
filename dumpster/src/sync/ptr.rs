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

//! Implementation of a tagged pointer for use by the collector.

use std::ptr::NonNull;

use crate::Collectable;

use super::GcBox;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// A tagged pointer with an extra bit.
pub struct Tagged<T: Collectable + Sync + ?Sized>(NonNull<GcBox<T>>);

impl<T: Collectable + Sync + ?Sized> Tagged<T> {
    /// Construct a new tagged pointer with the provided tag.
    pub fn new(ptr: NonNull<GcBox<T>>, tag: bool) -> Tagged<T> {
        Tagged(NonNull::new(ptr.as_ptr().map_addr(|a| a | usize::from(tag))).unwrap())
    }

    /// Create a tagged pointer pointing to the same allocation as `self` but with tag `tag`.
    pub fn with_tag(self, tag: bool) -> Tagged<T> {
        Tagged(NonNull::new(self.0.as_ptr().map_addr(|a| (a & !1) | usize::from(tag))).unwrap())
    }

    /// Is this pointer tagged?
    pub fn tagged(self) -> bool {
        self.0.as_ptr().addr() & 1 == 1
    }

    /// Get a new reference out of this pointer.
    ///
    /// # Safety
    ///
    /// This function is only safe if it is acceptable to create a reference, i.e. the pointee is
    /// not mutated for the lifetime of the box.
    pub unsafe fn as_ref<'a>(self) -> &'a GcBox<T> {
        unsafe { self.as_ptr().as_ref().unwrap() }
    }

    /// Get a new reference out of this pointer.
    ///
    /// # Safety
    ///
    /// This function is only safe if it is acceptable to create a reference, i.e. that `self` is
    /// unique.
    pub unsafe fn as_mut<'a>(self) -> &'a mut GcBox<T> {
        unsafe { self.as_ptr().as_mut().unwrap() }
    }

    /// Convert this pointer into a raw pointer, removing tag information.
    pub fn as_ptr(self) -> *mut GcBox<T> {
        self.0.as_ptr().map_addr(|a| a & !1)
    }

    pub fn as_nonnull(self) -> NonNull<GcBox<T>> {
        NonNull::new(self.as_ptr()).unwrap()
    }
}

#[cfg(feature = "coerce-unsized")]
impl<T, U> std::ops::CoerceUnsized<Tagged<U>> for Tagged<T>
where
    T: std::marker::Unsize<U> + Collectable + Sync + ?Sized,
    U: Collectable + Sync + ?Sized,
{
}

#[cfg(test)]
mod tests {
    use std::{cell::UnsafeCell, ptr::NonNull};

    use super::Tagged;

    fn copiable() {
        let x: Tagged<()> = Tagged::new(NonNull::dangling(), false);
        let _ = x.as_ptr();
        let _ = x.as_ptr();
    }

    fn with_unsafe_cell() {
        let x: UnsafeCell<Tagged<()>> = UnsafeCell::new(Tagged::new(NonNull::dangling(), false));
        let y = &x;
        let _ = unsafe { (*y.get()).as_ptr() };
    }
}
