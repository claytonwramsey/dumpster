/*
    dumpster, acycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! Implementations of [`Trace`] for common data types.

#![allow(deprecated)]

use std::{
    any::TypeId,
    borrow::Cow,
    cell::{Cell, OnceCell, RefCell},
    collections::{
        hash_map::{DefaultHasher, RandomState},
        BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque,
    },
    ffi::{OsStr, OsString},
    hash::{BuildHasher, BuildHasherDefault, SipHasher},
    marker::PhantomData,
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
        NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
    },
    ops::Deref,
    path::{Path, PathBuf},
    rc::Rc,
    sync::{
        atomic::{
            AtomicI16, AtomicI32, AtomicI64, AtomicI8, AtomicIsize, AtomicU16, AtomicU32,
            AtomicU64, AtomicU8, AtomicUsize,
        },
        Mutex, MutexGuard, RwLock, RwLockReadGuard, TryLockError,
    },
};

use crate::{Trace, Visitor};

/// Implement `Trace` trivially for some parametric `?Sized` type.
macro_rules! param_trivial_impl_unsized {
    ($x: ty) => {
        unsafe impl<T: ?Sized> Trace for $x {
            #[inline]
            fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> {
                Ok(())
            }
        }
    };
}

param_trivial_impl_unsized!(MutexGuard<'static, T>);
param_trivial_impl_unsized!(RwLockReadGuard<'static, T>);
param_trivial_impl_unsized!(&'static T);
param_trivial_impl_unsized!(PhantomData<T>);

unsafe impl<T: Trace + ?Sized> Trace for Box<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        (**self).accept(visitor)
    }
}

unsafe impl<T> Trace for BuildHasherDefault<T> {
    fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

unsafe impl<'a, T: ToOwned> Trace for Cow<'a, T>
where
    T::Owned: Trace,
{
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        if let Cow::Owned(ref v) = self {
            v.accept(visitor)?;
        }
        Ok(())
    }
}

unsafe impl<T: Trace + ?Sized> Trace for RefCell<T> {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.try_borrow().map_err(|_| ())?.accept(visitor)
    }
}

unsafe impl<T: Trace + ?Sized> Trace for Mutex<T> {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.try_lock()
            .map_err(|e| match e {
                TryLockError::Poisoned(_) => panic!(),
                TryLockError::WouldBlock => (),
            })?
            .deref()
            .accept(visitor)
    }
}

unsafe impl<T: Trace + ?Sized> Trace for RwLock<T> {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.try_read()
            .map_err(|e| match e {
                TryLockError::Poisoned(_) => panic!(),
                TryLockError::WouldBlock => (),
            })?
            .deref()
            .accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for Option<T> {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        match self {
            Some(x) => x.accept(visitor),
            None => Ok(()),
        }
    }
}

unsafe impl<T: Trace, E: Trace> Trace for Result<T, E> {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        match self {
            Ok(t) => t.accept(visitor),
            Err(e) => e.accept(visitor),
        }
    }
}

unsafe impl<T: Copy + Trace> Trace for Cell<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get().accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for OnceCell<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get().map_or(Ok(()), |x| x.accept(visitor))
    }
}

/// Implement [`Trace`] for a collection data structure which has some method `iter()` that
/// iterates over all elements of the data structure and `iter_mut()` which does the same over
/// mutable references.
macro_rules! Trace_collection_impl {
    ($x: ty) => {
        unsafe impl<T: Trace> Trace for $x {
            #[inline]
            fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
                for elem in self {
                    elem.accept(visitor)?;
                }
                Ok(())
            }
        }
    };
}

Trace_collection_impl!(Vec<T>);
Trace_collection_impl!(VecDeque<T>);
Trace_collection_impl!(LinkedList<T>);
Trace_collection_impl!([T]);
Trace_collection_impl!(HashSet<T>);
Trace_collection_impl!(BinaryHeap<T>);
Trace_collection_impl!(BTreeSet<T>);

unsafe impl<K: Trace, V: Trace, S: BuildHasher + Trace> Trace for HashMap<K, V, S> {
    fn accept<Z: Visitor>(&self, visitor: &mut Z) -> Result<(), ()> {
        for (k, v) in self {
            k.accept(visitor)?;
            v.accept(visitor)?;
        }
        self.hasher().accept(visitor)
    }
}

unsafe impl<K: Trace, V: Trace> Trace for BTreeMap<K, V> {
    fn accept<Z: Visitor>(&self, visitor: &mut Z) -> Result<(), ()> {
        for (k, v) in self {
            k.accept(visitor)?;
            v.accept(visitor)?;
        }
        Ok(())
    }
}

unsafe impl<T: Trace, const N: usize> Trace for [T; N] {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        for elem in self {
            elem.accept(visitor)?;
        }
        Ok(())
    }
}

/// Implement [`Trace`] for a trivially-collected type which contains no  [`Gc`]s in its
/// fields.
macro_rules! Trace_trivial_impl {
    ($x: ty) => {
        unsafe impl Trace for $x {
            #[inline]
            fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> {
                Ok(())
            }
        }
    };
}

Trace_trivial_impl!(());

Trace_trivial_impl!(u8);
Trace_trivial_impl!(u16);
Trace_trivial_impl!(u32);
Trace_trivial_impl!(u64);
Trace_trivial_impl!(u128);
Trace_trivial_impl!(usize);
Trace_trivial_impl!(i8);
Trace_trivial_impl!(i16);
Trace_trivial_impl!(i32);
Trace_trivial_impl!(i64);
Trace_trivial_impl!(i128);
Trace_trivial_impl!(isize);

Trace_trivial_impl!(bool);
Trace_trivial_impl!(char);

Trace_trivial_impl!(f32);
Trace_trivial_impl!(f64);

Trace_trivial_impl!(AtomicU8);
Trace_trivial_impl!(AtomicU16);
Trace_trivial_impl!(AtomicU32);
Trace_trivial_impl!(AtomicU64);
Trace_trivial_impl!(AtomicUsize);
Trace_trivial_impl!(AtomicI8);
Trace_trivial_impl!(AtomicI16);
Trace_trivial_impl!(AtomicI32);
Trace_trivial_impl!(AtomicI64);
Trace_trivial_impl!(AtomicIsize);

Trace_trivial_impl!(NonZeroU8);
Trace_trivial_impl!(NonZeroU16);
Trace_trivial_impl!(NonZeroU32);
Trace_trivial_impl!(NonZeroU64);
Trace_trivial_impl!(NonZeroU128);
Trace_trivial_impl!(NonZeroUsize);
Trace_trivial_impl!(NonZeroI8);
Trace_trivial_impl!(NonZeroI16);
Trace_trivial_impl!(NonZeroI32);
Trace_trivial_impl!(NonZeroI64);
Trace_trivial_impl!(NonZeroI128);
Trace_trivial_impl!(NonZeroIsize);

Trace_trivial_impl!(String);
Trace_trivial_impl!(str);
Trace_trivial_impl!(PathBuf);
Trace_trivial_impl!(Path);
Trace_trivial_impl!(OsString);
Trace_trivial_impl!(OsStr);

Trace_trivial_impl!(DefaultHasher);
Trace_trivial_impl!(RandomState);
Trace_trivial_impl!(Rc<str>);
Trace_trivial_impl!(SipHasher);

Trace_trivial_impl!(TypeId);

/// Implement [`Trace`] for a tuple.
macro_rules! Trace_tuple {
    () => {}; // This case is handled above by the trivial case
    ($($args:ident),*) => {
        unsafe impl<$($args: Trace),*> Trace for ($($args,)*) {
            fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
                #[allow(non_snake_case)]
                let &($(ref $args,)*) = self;
                $(($args).accept(visitor)?;)*
                Ok(())
            }
        }
    }
}

Trace_tuple!();
Trace_tuple!(A);
Trace_tuple!(A, B);
Trace_tuple!(A, B, C);
Trace_tuple!(A, B, C, D);
Trace_tuple!(A, B, C, D, E);
Trace_tuple!(A, B, C, D, E, F);
Trace_tuple!(A, B, C, D, E, F, G);
Trace_tuple!(A, B, C, D, E, F, G, H);
Trace_tuple!(A, B, C, D, E, F, G, H, I);
Trace_tuple!(A, B, C, D, E, F, G, H, I, J);

/// Implement `Trace` for one function type.
macro_rules! Trace_fn {
    ($ty:ty $(,$args:ident)*) => {
        unsafe impl<Ret $(,$args)*> Trace for $ty {
            fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> { Ok(()) }
        }
    }
}

/// Implement `Trace` for all functions with a given set of args.
macro_rules! Trace_fn_group {
    () => {
        Trace_fn!(extern "Rust" fn () -> Ret);
        Trace_fn!(extern "C" fn () -> Ret);
        Trace_fn!(unsafe extern "Rust" fn () -> Ret);
        Trace_fn!(unsafe extern "C" fn () -> Ret);
    };
    ($($args:ident),*) => {
        Trace_fn!(extern "Rust" fn ($($args),*) -> Ret, $($args),*);
        Trace_fn!(extern "C" fn ($($args),*) -> Ret, $($args),*);
        Trace_fn!(extern "C" fn ($($args),*, ...) -> Ret, $($args),*);
        Trace_fn!(unsafe extern "Rust" fn ($($args),*) -> Ret, $($args),*);
        Trace_fn!(unsafe extern "C" fn ($($args),*) -> Ret, $($args),*);
        Trace_fn!(unsafe extern "C" fn ($($args),*, ...) -> Ret, $($args),*);
    }
}

Trace_fn_group!();
Trace_fn_group!(A);
Trace_fn_group!(A, B);
Trace_fn_group!(A, B, C);
Trace_fn_group!(A, B, C, D);
Trace_fn_group!(A, B, C, D, E);
Trace_fn_group!(A, B, C, D, E, F);
Trace_fn_group!(A, B, C, D, E, F, G);
Trace_fn_group!(A, B, C, D, E, F, G, H);
Trace_fn_group!(A, B, C, D, E, F, G, H, I);
Trace_fn_group!(A, B, C, D, E, F, G, H, I, J);
