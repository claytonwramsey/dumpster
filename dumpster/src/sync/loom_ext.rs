/*
    dumpster, acycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

use std::{
    mem::MaybeUninit,
    ops::Deref,
    sync::{PoisonError, TryLockError},
};

use loom::{
    cell::UnsafeCell,
    sync::{
        Mutex as MutexImpl, MutexGuard, RwLock as RwLockImpl, RwLockReadGuard, RwLockWriteGuard,
    },
};

use crate::{Trace, Visitor};

pub struct Mutex<T: ?Sized>(MutexImpl<T>);

unsafe impl<T: Trace + ?Sized> Trace for Mutex<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.0
            .try_lock()
            .map_err(|e| match e {
                TryLockError::Poisoned(_) => panic!(),
                TryLockError::WouldBlock => (),
            })?
            .deref()
            .accept(visitor)
    }
}

impl<T> Mutex<T> {
    pub fn new(value: T) -> Self {
        Self(MutexImpl::new(value))
    }

    pub fn lock(&self) -> MutexGuard<'_, T> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub fn is_locked(&self) -> bool {
        !matches!(self.0.try_lock(), Err(TryLockError::WouldBlock))
    }
}

pub struct RwLock<T>(RwLockImpl<T>);

impl<T> RwLock<T> {
    pub fn new(value: T) -> Self {
        Self(RwLockImpl::new(value))
    }

    pub fn read(&self) -> RwLockReadGuard<'_, T> {
        self.0.read().unwrap_or_else(PoisonError::into_inner)
    }

    pub fn write(&self) -> RwLockWriteGuard<'_, T> {
        self.0.write().unwrap_or_else(PoisonError::into_inner)
    }
}

struct Once(Mutex<bool>);

impl Once {
    fn new() -> Self {
        Self(Mutex::new(false))
    }

    fn call_once(&self, f: impl FnOnce()) {
        if self.is_completed() {
            return;
        }

        let mut guard = self.0.lock();
        f();
        *guard = true;
    }

    fn is_completed(&self) -> bool {
        *self.0.lock()
    }
}

pub struct OnceLock<T> {
    once: Once,
    value: UnsafeCell<MaybeUninit<T>>,
}

unsafe impl<T: Sync + Send> Sync for OnceLock<T> {}
unsafe impl<T: Send> Send for OnceLock<T> {}

unsafe impl<T: Trace> Trace for OnceLock<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        self.with(|value| value.accept(visitor)).unwrap_or(Ok(()))
    }
}

impl<T> OnceLock<T> {
    pub fn new() -> Self {
        Self {
            once: Once::new(),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    unsafe fn with_unchecked<R>(&self, f: impl FnOnce(&T) -> R) -> R {
        self.value
            .with(|ptr| f(unsafe { (*ptr).assume_init_ref() }))
    }

    pub fn with<R>(&self, f: impl FnOnce(&T) -> R) -> Option<R> {
        if self.once.is_completed() {
            Some(unsafe { self.with_unchecked(f) })
        } else {
            None
        }
    }

    pub fn with_or_init<R>(&self, init: impl FnOnce() -> T, f: impl FnOnce(&T) -> R) -> R {
        self.once.call_once(|| {
            self.value.with_mut(|ptr| unsafe {
                (*ptr).write(init());
            });
        });

        unsafe { self.with_unchecked(f) }
    }

    pub fn set(&self, value: T) {
        self.with_or_init(|| value, |_| {});
    }
}

pub struct LazyLock<T>(OnceLock<T>, fn() -> T);

impl<T> LazyLock<T> {
    pub fn new(f: fn() -> T) -> Self {
        Self(OnceLock::new(), f)
    }
}

impl<T> Deref for LazyLock<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        todo!()
    }
}
