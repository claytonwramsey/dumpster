/*
    dumpster, a cycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! Contains macro to create optional garbage collection pointers.

/// The pointer address representing "none".
///
/// The address `usize::MAX` is never valid for a `Gc`, since a `GcBox`
/// always occupies at least one byte of memory. If a `GcBox` were placed
/// at `usize::MAX`, its size would overflow the address space.
pub(crate) const NONE_ADDR: usize = usize::MAX;

/// Trait for types that support `OptionGc::NONE`.
#[diagnostic::on_unimplemented(
    message = "`OptionGc::NONE` is not available for `{Self}`",
    label = "not supported for `{Self}`",
    note = "`OptionGc::NONE` is only available if `T` is `Sized`, a slice or a `str`",
    note = "for more info see the `OptionGc::NONE` documentation"
)]
pub(crate) trait SizedOrSliceOrStr {
    /// The pointer representation of "none".
    const NONE_PTR_REPR: *const Self;
}

impl<T> SizedOrSliceOrStr for T {
    const NONE_PTR_REPR: *const Self = std::ptr::without_provenance(NONE_ADDR);
}

impl<T> SizedOrSliceOrStr for [T] {
    const NONE_PTR_REPR: *const Self = <[T; 0]>::NONE_PTR_REPR;
}

impl SizedOrSliceOrStr for str {
    const NONE_PTR_REPR: *const Self = <[u8]>::NONE_PTR_REPR as _;
}

/// Macro to create optional garbage collection pointers.
macro_rules! make_option_gc {
    (
        module: $module:ident,
        visit_fn: $visit_fn:ident,
        extra_bounds: { $($($bounds:tt)+)? },
        from_ptr: |$from_ptr_param:ident| $from_ptr:expr,
        get_ptr: |$get_ptr_gc:ident| $get_ptr:expr,
        set_ptr: |$set_ptr_gc:ident, $set_ptr_ptr:ident| $set_ptr:expr,
    ) => {
        const _: () = {
            // to validate and add ide highlighting to the macro call site
            #[expect(unused)]
            use $crate::$module as _;
        };

        /// An alternative to <code>[Option]\<[Gc]\<T\>\></code> that takes up less space.
        ///
        /// Specifically `OptionGc<T>` always has the same size as `Gc<T>`.
        pub struct OptionGc<T: Trace $(+ $($bounds)*)? + ?Sized + 'static>(ManuallyDrop<Gc<T>>);

        #[expect(private_bounds)]
        impl<T: $crate::option::SizedOrSliceOrStr + Trace $(+ $($bounds)*)? + ?Sized + 'static> OptionGc<T> {
            /// An `OptionGc<T>` representing no value.
            ///
            /// This is only available for `Sized` values, slices and `str`s.
            /// To create "none" for a trait object or a custom DST you can use `NONE` with `coerce_option_gc`.
            ///
            /// # Examples
            ///
            /// ```
            #[doc = concat!("use dumpster::{Trace, ", stringify!($module), "::{OptionGc, coerce_option_gc}};")]
            ///
            /// let value: OptionGc<u8> = OptionGc::NONE;
            /// let slice: OptionGc<[u8]> = OptionGc::NONE;
            /// let str: OptionGc<str> = OptionGc::NONE;
            ///
            #[doc = concat!("let trait_object: OptionGc<dyn Trace" $(, " ", stringify!( + $($bounds)*))?, "> = coerce_option_gc!(OptionGc::<u8>::NONE);")]
            ///
            /// assert!(value.is_none());
            /// assert!(slice.is_none());
            /// assert!(str.is_none());
            /// assert!(trait_object.is_none());
            /// ```
            #[expect(clippy::declare_interior_mutable_const)]
            pub const NONE: Self = {
                let $from_ptr_param = <T as $crate::option::SizedOrSliceOrStr>::NONE_PTR_REPR as _;
                Self(ManuallyDrop::new(unsafe { $from_ptr }))
            };
        }

        impl<T: Trace $(+ $($bounds)*)? + ?Sized + 'static> OptionGc<T> {
            /// Returns the inner `GcBox<T>` pointer.
            fn get_ptr(&self) -> Nullable<GcBox<T>> {
                let $get_ptr_gc = &self.0;
                $get_ptr
            }

            /// Sets the inner `GcBox<T>` pointer.
            fn set_ptr(&mut self, $set_ptr_ptr: Nullable<GcBox<T>>) {
                let $set_ptr_gc = &mut self.0;
                $set_ptr
            }

            /// Returns `true` if the option contains some value of `T`.
            #[inline]
            pub fn is_some(&self) -> bool {
                !self.is_none()
            }

            /// Returns `true` if the option contains no value.
            #[inline]
            pub fn is_none(&self) -> bool {
                self.get_ptr().addr() == $crate::option::NONE_ADDR
            }

            /// Create an `OptionGc<T>` from a `Gc<T>`.
            ///
            /// # Examples
            ///
            /// ```
            #[doc = concat!("use dumpster::", stringify!($module), "::{Gc, OptionGc};")]
            ///
            /// let gc = Gc::new(7);
            /// let option_gc = OptionGc::some(gc);
            ///
            /// assert_eq!(**option_gc.as_ref().unwrap(), 7);
            /// ```
            #[inline]
            #[must_use]
            pub fn some(gc: Gc<T>) -> Self {
                Self(ManuallyDrop::new(gc))
            }

            /// Converts from `&OptionGc<T>` to `Option<&Gc<T>>`.
            ///
            /// # Examples
            ///
            /// Calculates the length of an `OptionGc<str>` without moving
            /// the `Gc<str>`.
            ///
            /// ```
            #[doc = concat!("use dumpster::", stringify!($module), "::{Gc, OptionGc};")]
            ///
            /// let text: OptionGc<str> = OptionGc::some(Gc::from("Hello, world!"));
            /// // First, convert `&OptionGc<str>` to `Option<&Gc<str>>` with `as_ref`,
            /// // then consume *that* with `map`, leaving `text` on the stack.
            /// let text_length: Option<usize> = text.as_ref().map(|s| s.len());
            /// # assert_eq!(text_length, Some(13));
            /// println!("still can print text: {text:?}");
            /// ```
            #[inline]
            pub fn as_ref(&self) -> Option<&Gc<T>> {
                if self.is_none() {
                    return None;
                }

                Some(&self.0)
            }

            /// Converts from `&mut OptionGc<T>` to `Option<&mut Gc<T>>`.
            ///
            /// # Examples
            ///
            /// ```
            #[doc = concat!("use dumpster::", stringify!($module), "::{Gc, OptionGc};")]
            ///
            /// let mut x: OptionGc<i32> = OptionGc::some(Gc::new(2));
            ///
            /// match x.as_mut() {
            ///     Some(v) => *v = Gc::new(42),
            ///     None => {}
            /// }
            ///
            /// assert_eq!(**x.as_ref().unwrap(), 42);
            /// ```
            #[inline]
            pub fn as_mut(&mut self) -> Option<&mut Gc<T>> {
                if self.is_none() {
                    return None;
                }

                Some(&mut self.0)
            }

            /// Converts from `&OptionGc<T>` to `Option<&T>`.
            ///
            /// # Examples
            ///
            /// ```
            #[doc = concat!("use dumpster::", stringify!($module), "::{Gc, OptionGc};")]
            ///
            /// let text: OptionGc<str> = OptionGc::some(Gc::from("Hello, world!"));
            /// let str: Option<&str> = text.as_deref();
            /// assert_eq!(str, Some("Hello, world!"));
            /// ```
            #[inline]
            pub fn as_deref(&self) -> Option<&T> {
                if self.is_none() {
                    return None;
                }

                Some(&self.0)
            }

            /// Convert this `OptionGc<T>` into an `Option<Gc<T>>`.
            #[inline]
            pub fn into_option(self) -> Option<Gc<T>> {
                if self.is_none() {
                    return None;
                }

                let mut this = ManuallyDrop::new(self);
                Some(unsafe { ManuallyDrop::take(&mut this.0) })
            }

            /// Takes the `Gc<T>` out, leaving "none" in its place.
            ///
            /// # Examples
            ///
            /// ```
            #[doc = concat!("use dumpster::", stringify!($module), "::OptionGc;")]
            ///
            /// let mut x = OptionGc::from(Some(2));
            /// let y = x.take();
            /// assert!(x.is_none());
            /// assert_eq!(*y.unwrap(), 2);
            ///
            /// let mut x: OptionGc<u8> = OptionGc::NONE;
            /// let y = x.take();
            /// assert!(x.is_none());
            /// assert!(y.is_none());
            /// ```
            #[inline]
            pub fn take(&mut self) -> Option<Gc<T>> {
                if self.is_none() {
                    return None;
                }

                let gc = unsafe { ManuallyDrop::take(&mut self.0) };
                self.set_ptr(self.get_ptr().with_addr($crate::option::NONE_ADDR));
                Some(gc)
            }

            /// Inserts the default value if this option is "none",
            /// then returns a mutable reference to the contained `Gc<T>`.
            ///
            /// [`is_none`]: Self::is_none
            #[inline]
            pub fn get_or_insert_default(&mut self) -> &mut Gc<T>
            where
                T: Default,
            {
                self.get_or_insert_with(Default::default)
            }

            /// Inserts a `Gc<T>` computed from `f` if this option is "none",
            /// then returns a mutable reference to the contained `Gc<T>`.
            ///
            /// [`is_none`]: Self::is_none
            #[inline]
            pub fn get_or_insert_with(&mut self, f: impl FnOnce() -> Gc<T>) -> &mut Gc<T> {
                if self.is_none() {
                    self.0 = ManuallyDrop::new(f());
                }

                &mut self.0
            }

            /// Determine whether two `OptionGc`s are equivalent by reference.
            /// Returns `true` if both `this` and `other` point to the same value, in the same style as
            /// [`std::ptr::eq`].
            ///
            /// # Examples
            ///
            /// ```
            #[doc = concat!("use dumpster::", stringify!($module), "::{Gc, OptionGc};")]
            ///
            /// let gc1 = OptionGc::some(Gc::new(0));
            /// let gc2 = gc1.clone(); // points to same spot as `gc1`
            /// let gc3 = OptionGc::some(Gc::new(0)); // same value, but points to a different object than `gc1`
            ///
            /// assert!(gc1.ptr_eq(&gc2));
            /// assert!(!gc1.ptr_eq(&gc3));
            ///
            /// let gc4 = OptionGc::<i32>::NONE; // no value
            /// let gc5 = OptionGc::<i32>::NONE; // also no value
            /// assert!(gc4.ptr_eq(&gc5));
            /// ```
            #[inline]
            pub fn ptr_eq(&self, other: &Self) -> bool {
                self.get_ptr().addr() == other.get_ptr().addr()
            }

            /// Get the number of references to the value pointed to by this `OptionGc`.
            ///
            /// This does not include internal references generated by the garbage collector.
            ///
            /// Returns `0` if this option is none.
            ///
            /// # Examples
            ///
            /// ```
            #[doc = concat!("use dumpster::", stringify!($module), "::{Gc, OptionGc};")]
            ///
            /// let gc = OptionGc::some(Gc::new(()));
            /// assert_eq!(gc.ref_count(), 1);
            /// let gc2 = gc.clone();
            /// assert_eq!(gc.ref_count(), 2);
            /// drop(gc);
            /// drop(gc2);
            ///
            /// let gc = OptionGc::<i32>::NONE;
            /// assert_eq!(gc.ref_count(), 0);
            /// ```
            pub fn ref_count(&self) -> usize {
                match self.as_ref() {
                    Some(gc) => Gc::ref_count(gc).get(),
                    None => 0,
                }
            }

            /// Exists solely for the [`coerce_option_gc`] macro.
            #[inline]
            #[must_use]
            #[doc(hidden)]
            pub unsafe fn __private_into_gc(this: Self) -> Gc<T> {
                let mut this = ManuallyDrop::new(this);
                ManuallyDrop::take(&mut this.0)
            }

            /// Exists solely for the [`coerce_option_gc`] macro.
            #[inline]
            #[must_use]
            #[doc(hidden)]
            pub unsafe fn __private_from_gc(gc: Gc<T>) -> Self {
                Self(ManuallyDrop::new(gc))
            }
        }

        impl<T: Trace $(+ $($bounds)*)? + ?Sized + 'static> Drop for OptionGc<T> {
            fn drop(&mut self) {
                if self.is_none() {
                    return;
                }

                unsafe { ManuallyDrop::drop(&mut self.0) }
            }
        }

        impl<T: Trace $(+ $($bounds)*)? + ?Sized + 'static + Debug> Debug for OptionGc<T> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                Debug::fmt(&self.as_ref(), f)
            }
        }

        unsafe impl<V: Visitor, T: Trace $(+ $($bounds)*)? + ?Sized> TraceWith<V> for OptionGc<T> {
            fn accept(&self, visitor: &mut V) -> Result<(), ()> {
                if let Some(gc) = self.as_ref() {
                    visitor.$visit_fn(gc);
                }

                Ok(())
            }
        }

        impl<T: Trace $(+ $($bounds)*)? + ?Sized + 'static> Clone for OptionGc<T> {
            fn clone(&self) -> Self {
                match self.as_ref() {
                    Some(gc) => Self::some(gc.clone()),
                    // Create a bitwise copy of `self`.
                    //
                    // SAFETY: `self` is a reference, so it's valid to read.
                    // When `self` is `None`, the inner `Gc` will not be dropped
                    // so this cannot cause a double-drop.
                    None => unsafe { ptr::read(self) },
                }
            }
        }

        impl<T: $crate::option::SizedOrSliceOrStr + Trace $(+ $($bounds)*)? + ?Sized + 'static> Default for OptionGc<T> {
            /// Returns [`NONE`](Self::NONE).
            ///
            /// # Examples
            ///
            /// ```
            #[doc = concat!("use dumpster::", stringify!($module), "::OptionGc;")]
            ///
            /// let value: OptionGc<u8> = OptionGc::default();
            /// let slice: OptionGc<[u8]> = OptionGc::default();
            /// let str: OptionGc<str> = OptionGc::default();
            ///
            /// assert!(value.is_none());
            /// assert!(slice.is_none());
            /// assert!(str.is_none());
            /// ```
            fn default() -> Self {
                Self::NONE
            }
        }

        impl<T: $crate::option::SizedOrSliceOrStr + Trace $(+ $($bounds)*)? + ?Sized + 'static, U: Into<Gc<T>>> From<Option<U>> for OptionGc<T> {
            /// Converts any `Option<U>` to an `OptionGc<T>` where `U` is convertible to `Gc<T>`.
            ///
            /// # Examples
            ///
            /// ```
            /// use std::borrow::Cow;
            #[doc = concat!("use dumpster::", stringify!($module), "::{Gc, OptionGc};")]
            ///
            /// let from_gc: OptionGc<u8> = Some(Gc::new(1)).into();
            ///
            /// let from_slice: OptionGc<[u8]> = Some(&[1, 2, 3][..]).into();
            /// let from_str: OptionGc<str> = Some("Hello, world!").into();
            /// let from_box: OptionGc<u8> = Some(Box::new(1)).into();
            /// let from_cow: OptionGc<str> = Some(Cow::Borrowed("Hello, world!")).into();
            /// let from_string: OptionGc<str> = Some(String::from("Hello, world!")).into();
            /// let from_value: OptionGc<u8> = Some(1).into();
            /// let from_vec: OptionGc<[u8]> = Some(vec![1, 2, 3]).into();
            /// let from_array: OptionGc<[u8]> = Some([1, 2, 3]).into();
            ///
            /// let bytes_from_gc_str: OptionGc<[u8]> = Some(Gc::<str>::from("Hello, world!")).into();
            /// ```
            fn from(value: Option<U>) -> Self {
                match value {
                    Some(some) => Self(ManuallyDrop::new(some.into())),
                    None => Self::NONE,
                }
            }
        }

        impl<T: Trace $(+ $($bounds)*)? + ?Sized + 'static> From<OptionGc<T>> for Option<Gc<T>> {
            fn from(value: OptionGc<T>) -> Self {
                value.into_option()
            }
        }

        impl<T: Trace $(+ $($bounds)*)? + ?Sized + 'static + PartialEq> PartialEq for OptionGc<T> {
            fn eq(&self, other: &OptionGc<T>) -> bool {
                self.as_ref() == other.as_ref()
            }
        }

        impl<T: Trace $(+ $($bounds)*)? + ?Sized + 'static + Eq> Eq for OptionGc<T> {}
    };
}

pub(crate) use make_option_gc;
