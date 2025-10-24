/*
    dumpster, a cycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! Implementations of [`Trace`] for common data types.

#![allow(deprecated)]

use std::{
    borrow::Cow,
    cell::{Cell, OnceCell, RefCell},
    collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque},
    convert::Infallible,
    hash::{BuildHasher, BuildHasherDefault},
    marker::PhantomData,
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
        NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
    },
    ops::Deref,
    sync::{
        atomic::{
            AtomicI16, AtomicI32, AtomicI64, AtomicI8, AtomicIsize, AtomicU16, AtomicU32,
            AtomicU64, AtomicU8, AtomicUsize,
        },
        Mutex, MutexGuard, OnceLock, RwLock, RwLockReadGuard, TryLockError,
    },
};

use crate::{Trace, Visitor};

unsafe impl Trace for Infallible {
    fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> {
        match *self {}
    }
}

#[cfg(feature = "either")]
unsafe impl<A: Trace, B: Trace> Trace for either::Either<A, B> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        match self {
            either::Either::Left(a) => a.accept(visitor),
            either::Either::Right(b) => b.accept(visitor),
        }
    }
}

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

/// Implement `Trace` trivially for some parametric `Sized` type.
macro_rules! param_trivial_impl_sized {
    ($x: ty) => {
        unsafe impl<T> Trace for $x {
            #[inline]
            fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> {
                Ok(())
            }
        }
    };
}

param_trivial_impl_sized!(std::future::Pending<T>);
param_trivial_impl_sized!(std::mem::Discriminant<T>);

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

unsafe impl<T: ToOwned> Trace for Cow<'_, T>
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

unsafe impl<T: Trace> Trace for OnceLock<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get().map_or(Ok(()), |x| x.accept(visitor))
    }
}

unsafe impl<T: Trace> Trace for std::cmp::Reverse<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.0.accept(visitor)
    }
}

unsafe impl<T: Trace + ?Sized> Trace for std::io::BufReader<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get_ref().accept(visitor)
    }
}

unsafe impl<T: Trace + std::io::Write + ?Sized> Trace for std::io::BufWriter<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get_ref().accept(visitor)
    }
}

unsafe impl<T: Trace, U: Trace> Trace for std::io::Chain<T, U> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        let (t, u) = self.get_ref();
        t.accept(visitor)?;
        u.accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::io::Cursor<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get_ref().accept(visitor)
    }
}

unsafe impl<T: Trace + std::io::Write + ?Sized> Trace for std::io::LineWriter<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get_ref().accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::io::Take<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.get_ref().accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::mem::ManuallyDrop<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        (**self).accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::num::Saturating<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.0.accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::num::Wrapping<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.0.accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::ops::Range<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.start.accept(visitor)?;
        self.end.accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::ops::RangeFrom<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.start.accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::ops::RangeInclusive<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.start().accept(visitor)?;
        self.end().accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::ops::RangeTo<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.end.accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::ops::RangeToInclusive<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.end.accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::ops::Bound<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        match self {
            std::ops::Bound::Included(x) | std::ops::Bound::Excluded(x) => x.accept(visitor),
            std::ops::Bound::Unbounded => Ok(()),
        }
    }
}

unsafe impl<B: Trace, C: Trace> Trace for std::ops::ControlFlow<B, C> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        match self {
            std::ops::ControlFlow::Continue(c) => c.accept(visitor),
            std::ops::ControlFlow::Break(b) => b.accept(visitor),
        }
    }
}

unsafe impl<T: Trace> Trace for std::panic::AssertUnwindSafe<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.0.accept(visitor)
    }
}

unsafe impl<T: Trace> Trace for std::task::Poll<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        match self {
            std::task::Poll::Ready(r) => r.accept(visitor),
            std::task::Poll::Pending => Ok(()),
        }
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
Trace_collection_impl!(BinaryHeap<T>);
Trace_collection_impl!(BTreeSet<T>);

unsafe impl<T: Trace> Trace for std::vec::IntoIter<T> {
    #[inline]
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        for elem in self.as_slice() {
            elem.accept(visitor)?;
        }
        Ok(())
    }
}

unsafe impl<K: Trace, V: Trace, S: BuildHasher + Trace> Trace for HashMap<K, V, S> {
    fn accept<Z: Visitor>(&self, visitor: &mut Z) -> Result<(), ()> {
        for (k, v) in self {
            k.accept(visitor)?;
            v.accept(visitor)?;
        }
        self.hasher().accept(visitor)
    }
}

unsafe impl<T: Trace, S: BuildHasher + Trace> Trace for HashSet<T, S> {
    fn accept<Z: Visitor>(&self, visitor: &mut Z) -> Result<(), ()> {
        for elem in self {
            elem.accept(visitor)?;
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

/// Implement [`Trace`] for a trivially-collected type which contains no `Gc`s in its
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

Trace_trivial_impl!(std::alloc::Layout);
Trace_trivial_impl!(std::alloc::LayoutError);
Trace_trivial_impl!(std::alloc::System);

Trace_trivial_impl!(std::any::TypeId);

Trace_trivial_impl!(std::ascii::EscapeDefault);

Trace_trivial_impl!(std::backtrace::Backtrace);
Trace_trivial_impl!(std::backtrace::BacktraceStatus);

Trace_trivial_impl!(std::cmp::Ordering);

Trace_trivial_impl!(std::char::CharTryFromError);
Trace_trivial_impl!(std::char::EscapeDebug);
Trace_trivial_impl!(std::char::EscapeDefault);
Trace_trivial_impl!(std::char::EscapeUnicode);
Trace_trivial_impl!(std::char::ToLowercase);
Trace_trivial_impl!(std::char::ToUppercase);

Trace_trivial_impl!(std::env::Args);
Trace_trivial_impl!(std::env::ArgsOs);
Trace_trivial_impl!(std::env::JoinPathsError);
Trace_trivial_impl!(std::env::Vars);
Trace_trivial_impl!(std::env::VarsOs);
Trace_trivial_impl!(std::env::VarError);

Trace_trivial_impl!(std::ffi::CStr);
Trace_trivial_impl!(std::ffi::CString);
Trace_trivial_impl!(std::ffi::FromBytesUntilNulError);
Trace_trivial_impl!(std::ffi::FromVecWithNulError);
Trace_trivial_impl!(std::ffi::IntoStringError);
Trace_trivial_impl!(std::ffi::NulError);
Trace_trivial_impl!(std::ffi::OsStr);
Trace_trivial_impl!(std::ffi::OsString);
Trace_trivial_impl!(std::ffi::FromBytesWithNulError);
Trace_trivial_impl!(std::ffi::c_void);

Trace_trivial_impl!(std::fmt::Error);
Trace_trivial_impl!(std::fmt::Alignment);

Trace_trivial_impl!(std::fs::DirBuilder);
Trace_trivial_impl!(std::fs::DirEntry);
Trace_trivial_impl!(std::fs::File);
Trace_trivial_impl!(std::fs::FileTimes);
Trace_trivial_impl!(std::fs::FileType);
Trace_trivial_impl!(std::fs::Metadata);
Trace_trivial_impl!(std::fs::OpenOptions);
Trace_trivial_impl!(std::fs::Permissions);
Trace_trivial_impl!(std::fs::ReadDir);
Trace_trivial_impl!(std::fs::TryLockError);

Trace_trivial_impl!(std::hash::DefaultHasher);
Trace_trivial_impl!(std::hash::RandomState);
Trace_trivial_impl!(std::hash::SipHasher);

Trace_trivial_impl!(std::io::Empty);
Trace_trivial_impl!(std::io::Error);
Trace_trivial_impl!(std::io::PipeReader);
Trace_trivial_impl!(std::io::PipeWriter);
Trace_trivial_impl!(std::io::Repeat);
Trace_trivial_impl!(std::io::Sink);
Trace_trivial_impl!(std::io::Stdin);
Trace_trivial_impl!(std::io::Stdout);
Trace_trivial_impl!(std::io::WriterPanicked);
Trace_trivial_impl!(std::io::ErrorKind);
Trace_trivial_impl!(std::io::SeekFrom);

Trace_trivial_impl!(std::marker::PhantomPinned);

Trace_trivial_impl!(std::net::AddrParseError);
Trace_trivial_impl!(std::net::Ipv4Addr);
Trace_trivial_impl!(std::net::Ipv6Addr);
Trace_trivial_impl!(std::net::SocketAddrV4);
Trace_trivial_impl!(std::net::SocketAddrV6);
Trace_trivial_impl!(std::net::TcpListener);
Trace_trivial_impl!(std::net::TcpStream);
Trace_trivial_impl!(std::net::UdpSocket);
Trace_trivial_impl!(std::net::IpAddr);
Trace_trivial_impl!(std::net::Shutdown);
Trace_trivial_impl!(std::net::SocketAddr);

Trace_trivial_impl!(std::num::ParseFloatError);
Trace_trivial_impl!(std::num::ParseIntError);
Trace_trivial_impl!(std::num::TryFromIntError);
Trace_trivial_impl!(std::num::FpCategory);
Trace_trivial_impl!(std::num::IntErrorKind);

Trace_trivial_impl!(std::ops::RangeFull);

Trace_trivial_impl!(std::path::Path);
Trace_trivial_impl!(std::path::PathBuf);
Trace_trivial_impl!(std::path::StripPrefixError);

Trace_trivial_impl!(std::process::Child);
Trace_trivial_impl!(std::process::ChildStderr);
Trace_trivial_impl!(std::process::ChildStdin);
Trace_trivial_impl!(std::process::ChildStdout);
Trace_trivial_impl!(std::process::Command);
Trace_trivial_impl!(std::process::ExitCode);
Trace_trivial_impl!(std::process::Output);
Trace_trivial_impl!(std::process::Stdio);

Trace_trivial_impl!(std::slice::GetDisjointMutError);

Trace_trivial_impl!(str);
Trace_trivial_impl!(std::rc::Rc<str>);
Trace_trivial_impl!(std::sync::Arc<str>);

Trace_trivial_impl!(std::string::FromUtf8Error);
Trace_trivial_impl!(std::string::FromUtf16Error);
Trace_trivial_impl!(std::string::String);

Trace_trivial_impl!(std::thread::AccessError);
Trace_trivial_impl!(std::thread::Builder);
Trace_trivial_impl!(std::thread::Thread);
Trace_trivial_impl!(std::thread::ThreadId);

Trace_trivial_impl!(std::time::Duration);
Trace_trivial_impl!(std::time::Instant);
Trace_trivial_impl!(std::time::SystemTime);
Trace_trivial_impl!(std::time::SystemTimeError);
Trace_trivial_impl!(std::time::TryFromFloatSecsError);

/// Implement [`Trace`] for a tuple.
macro_rules! Trace_tuple {
    () => {}; // This case is handled above by the trivial case
    ($($args:ident),*) => {
        unsafe impl<$($args: Trace),*> Trace for ($($args,)*) {
            fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
                #[expect(clippy::allow_attributes)]
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
