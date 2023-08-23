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

//! Implementations of [`Collectable`] for common data types.

#![allow(deprecated)]

use std::{
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

use crate::{Collectable, Visitor};

/// Implement `Collectable` trivially for some parametric `?Sized` type.
macro_rules! param_trivial_impl_unsized {
    ($x: ty) => {
        unsafe impl<T: ?Sized> Collectable for $x {
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

unsafe impl<T: Collectable + ?Sized> Collectable for Box<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        (**self).accept(visitor)
    }
}

unsafe impl<T> Collectable for BuildHasherDefault<T> {
    fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> {
        Ok(())
    }
}

unsafe impl<'a, T: ToOwned> Collectable for Cow<'a, T>
where
    T::Owned: Collectable,
{
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        if let Cow::Owned(ref v) = self {
            v.accept(visitor)?;
        }
        Ok(())
    }
}

unsafe impl<T: Collectable + ?Sized> Collectable for RefCell<T> {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.try_borrow().map_err(|_| ())?.accept(visitor)
    }
}

unsafe impl<T: Collectable + ?Sized> Collectable for Mutex<T> {
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

unsafe impl<T: Collectable + ?Sized> Collectable for RwLock<T> {
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

unsafe impl<T: Collectable> Collectable for Option<T> {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        match self {
            Some(x) => x.accept(visitor),
            None => Ok(()),
        }
    }
}

unsafe impl<T: Collectable, E: Collectable> Collectable for Result<T, E> {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        match self {
            Ok(t) => t.accept(visitor),
            Err(e) => e.accept(visitor),
        }
    }
}

unsafe impl<T: Copy + Collectable> Collectable for Cell<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get().accept(visitor)
    }
}

unsafe impl<T: Collectable> Collectable for OnceCell<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get().map_or(Ok(()), |x| x.accept(visitor))
    }
}

/// Implement [`Collectable`] for a collection data structure which has some method `iter()` that
/// iterates over all elements of the data structure and `iter_mut()` which does the same over
/// mutable references.
macro_rules! collectable_collection_impl {
    ($x: ty) => {
        unsafe impl<T: Collectable> Collectable for $x {
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

collectable_collection_impl!(Vec<T>);
collectable_collection_impl!(VecDeque<T>);
collectable_collection_impl!(LinkedList<T>);
collectable_collection_impl!([T]);
collectable_collection_impl!(HashSet<T>);
collectable_collection_impl!(BinaryHeap<T>);
collectable_collection_impl!(BTreeSet<T>);

unsafe impl<K: Collectable, V: Collectable, S: BuildHasher + Collectable> Collectable
    for HashMap<K, V, S>
{
    fn accept<Z: Visitor>(&self, visitor: &mut Z) -> Result<(), ()> {
        for (k, v) in self {
            k.accept(visitor)?;
            v.accept(visitor)?;
        }
        self.hasher().accept(visitor)
    }
}

unsafe impl<K: Collectable, V: Collectable> Collectable for BTreeMap<K, V> {
    fn accept<Z: Visitor>(&self, visitor: &mut Z) -> Result<(), ()> {
        for (k, v) in self {
            k.accept(visitor)?;
            v.accept(visitor)?;
        }
        Ok(())
    }
}

unsafe impl<T: Collectable, const N: usize> Collectable for [T; N] {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        for elem in self {
            elem.accept(visitor)?;
        }
        Ok(())
    }
}

/// Implement [`Collectable`] for a trivially-collected type which contains no  [`Gc`]s in its
/// fields.
macro_rules! collectable_trivial_impl {
    ($x: ty) => {
        unsafe impl Collectable for $x {
            #[inline]
            fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> {
                Ok(())
            }
        }
    };
}

collectable_trivial_impl!(());

collectable_trivial_impl!(u8);
collectable_trivial_impl!(u16);
collectable_trivial_impl!(u32);
collectable_trivial_impl!(u64);
collectable_trivial_impl!(u128);
collectable_trivial_impl!(usize);
collectable_trivial_impl!(i8);
collectable_trivial_impl!(i16);
collectable_trivial_impl!(i32);
collectable_trivial_impl!(i64);
collectable_trivial_impl!(i128);
collectable_trivial_impl!(isize);

collectable_trivial_impl!(bool);
collectable_trivial_impl!(char);

collectable_trivial_impl!(f32);
collectable_trivial_impl!(f64);

collectable_trivial_impl!(AtomicU8);
collectable_trivial_impl!(AtomicU16);
collectable_trivial_impl!(AtomicU32);
collectable_trivial_impl!(AtomicU64);
collectable_trivial_impl!(AtomicUsize);
collectable_trivial_impl!(AtomicI8);
collectable_trivial_impl!(AtomicI16);
collectable_trivial_impl!(AtomicI32);
collectable_trivial_impl!(AtomicI64);
collectable_trivial_impl!(AtomicIsize);

collectable_trivial_impl!(NonZeroU8);
collectable_trivial_impl!(NonZeroU16);
collectable_trivial_impl!(NonZeroU32);
collectable_trivial_impl!(NonZeroU64);
collectable_trivial_impl!(NonZeroU128);
collectable_trivial_impl!(NonZeroUsize);
collectable_trivial_impl!(NonZeroI8);
collectable_trivial_impl!(NonZeroI16);
collectable_trivial_impl!(NonZeroI32);
collectable_trivial_impl!(NonZeroI64);
collectable_trivial_impl!(NonZeroI128);
collectable_trivial_impl!(NonZeroIsize);

collectable_trivial_impl!(String);
collectable_trivial_impl!(str);
collectable_trivial_impl!(PathBuf);
collectable_trivial_impl!(Path);
collectable_trivial_impl!(OsString);
collectable_trivial_impl!(OsStr);

collectable_trivial_impl!(DefaultHasher);
collectable_trivial_impl!(RandomState);
collectable_trivial_impl!(Rc<str>);
collectable_trivial_impl!(SipHasher);

/// Implement [`Collectable`] for a tuple.
macro_rules! collectable_tuple {
    () => {}; // This case is handled above by the trivial case
    ($($args:ident),*) => {
        unsafe impl<$($args: Collectable),*> Collectable for ($($args,)*) {
            fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
                #[allow(non_snake_case)]
                let &($(ref $args,)*) = self;
                $(($args).accept(visitor)?;)*
                Ok(())
            }
        }
    }
}

collectable_tuple!();
collectable_tuple!(A);
collectable_tuple!(A, B);
collectable_tuple!(A, B, C);
collectable_tuple!(A, B, C, D);
collectable_tuple!(A, B, C, D, E);
collectable_tuple!(A, B, C, D, E, F);
collectable_tuple!(A, B, C, D, E, F, G);
collectable_tuple!(A, B, C, D, E, F, G, H);
collectable_tuple!(A, B, C, D, E, F, G, H, I);
collectable_tuple!(A, B, C, D, E, F, G, H, I, J);

/// Implement `Collectable` for one function type.
macro_rules! collectable_fn {
    ($ty:ty $(,$args:ident)*) => {
        unsafe impl<Ret $(,$args)*> Collectable for $ty {
            fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> { Ok(()) }
        }
    }
}

/// Implement `Collectable` for all functions with a given set of args.
macro_rules! collectable_fn_group {
    () => {
        collectable_fn!(extern "Rust" fn () -> Ret);
        collectable_fn!(extern "C" fn () -> Ret);
        collectable_fn!(unsafe extern "Rust" fn () -> Ret);
        collectable_fn!(unsafe extern "C" fn () -> Ret);
    };
    ($($args:ident),*) => {
        collectable_fn!(extern "Rust" fn ($($args),*) -> Ret, $($args),*);
        collectable_fn!(extern "C" fn ($($args),*) -> Ret, $($args),*);
        collectable_fn!(extern "C" fn ($($args),*, ...) -> Ret, $($args),*);
        collectable_fn!(unsafe extern "Rust" fn ($($args),*) -> Ret, $($args),*);
        collectable_fn!(unsafe extern "C" fn ($($args),*) -> Ret, $($args),*);
        collectable_fn!(unsafe extern "C" fn ($($args),*, ...) -> Ret, $($args),*);
    }
}

collectable_fn_group!();
collectable_fn_group!(A);
collectable_fn_group!(A, B);
collectable_fn_group!(A, B, C);
collectable_fn_group!(A, B, C, D);
collectable_fn_group!(A, B, C, D, E);
collectable_fn_group!(A, B, C, D, E, F);
collectable_fn_group!(A, B, C, D, E, F, G);
collectable_fn_group!(A, B, C, D, E, F, G, H);
collectable_fn_group!(A, B, C, D, E, F, G, H, I);
collectable_fn_group!(A, B, C, D, E, F, G, H, I, J);
