/*
    dumpster, a cycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! Tests for running under loom.

#![cfg_attr(not(test), allow(dead_code))]

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

/// Simple wrapper mutex type.
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
    /// Construct a new mutex.
    pub fn new(value: T) -> Self {
        Self(MutexImpl::new(value))
    }

    /// Lock the mutex.
    pub fn lock(&self) -> MutexGuard<'_, T> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    #[expect(dead_code)]
    /// Is the mutex locked?
    pub fn is_locked(&self) -> bool {
        !matches!(self.0.try_lock(), Err(TryLockError::WouldBlock))
    }
}

/// A read-write lock
pub struct RwLock<T>(RwLockImpl<T>);

impl<T> RwLock<T> {
    /// Construct a rwlock.
    pub fn new(value: T) -> Self {
        Self(RwLockImpl::new(value))
    }

    /// Get a read guard.
    pub fn read(&self) -> RwLockReadGuard<'_, T> {
        self.0.read().unwrap_or_else(PoisonError::into_inner)
    }

    /// Get a write guard.
    pub fn write(&self) -> RwLockWriteGuard<'_, T> {
        self.0.write().unwrap_or_else(PoisonError::into_inner)
    }
}

/// A once-object.
struct Once {
    /// Completed?
    is_completed: Mutex<bool>,
}

impl Once {
    /// Construct a once.
    fn new() -> Self {
        Self {
            is_completed: Mutex::new(false),
        }
    }

    /// Call a function once.
    fn call_once(&self, f: impl FnOnce()) {
        let mut is_completed = self.is_completed.lock();

        if *is_completed {
            return;
        }

        f();
        *is_completed = true;
    }

    /// Determine if we are completed.
    fn is_completed(&self) -> bool {
        *self.is_completed.lock()
    }
}

/// A once-lock.
pub struct OnceLock<T> {
    /// A thing that does it once.
    once: Once,
    /// The data.
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
    /// Construct a once-lock.
    pub fn new() -> Self {
        Self {
            once: Once::new(),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Call a function uncheckedly.
    unsafe fn with_unchecked<R>(&self, f: impl FnOnce(&T) -> R) -> R {
        self.value
            .with(|ptr| f(unsafe { (*ptr).assume_init_ref() }))
    }

    /// Apply a function.
    pub fn with<R>(&self, f: impl FnOnce(&T) -> R) -> Option<R> {
        if self.once.is_completed() {
            Some(unsafe { self.with_unchecked(f) })
        } else {
            None
        }
    }

    /// Apply or initialize.
    pub fn with_or_init<R>(&self, init: impl FnOnce() -> T, f: impl FnOnce(&T) -> R) -> R {
        self.once.call_once(|| {
            self.value.with_mut(|ptr| unsafe {
                (*ptr).write(init());
            });
        });

        unsafe { self.with_unchecked(f) }
    }

    /// Set the value.
    pub fn set(&self, value: T) {
        self.with_or_init(|| value, |_| {});
    }
}

#[test]
fn test_once() {
    use loom::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };

    loom::model(|| {
        let once = Arc::new(Once::new());
        let counter = Arc::new(AtomicUsize::new(0));

        let mut join_handles = vec![];

        for _ in 0..2 {
            let once = once.clone();
            let counter = counter.clone();

            join_handles.push(loom::thread::spawn(move || {
                once.call_once(|| {
                    counter.fetch_add(1, Ordering::Relaxed);
                });
            }));
        }

        for join_handle in join_handles {
            join_handle.join().unwrap();
        }

        assert_eq!(counter.load(Ordering::Relaxed), 1);
    });
}

#[test]
fn test_once_lock() {
    use loom::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };

    loom::model(|| {
        let once_lock = Arc::new(OnceLock::<String>::new());
        let counter = Arc::new(AtomicUsize::new(0));

        let mut join_handles = vec![];

        for _ in 0..2 {
            let once_lock = once_lock.clone();
            let counter = counter.clone();

            join_handles.push(loom::thread::spawn({
                move || {
                    once_lock.with_or_init(
                        || {
                            counter.fetch_add(1, Ordering::Relaxed);
                            String::from("test")
                        },
                        |value| {
                            assert_eq!(value, "test");
                        },
                    );
                }
            }));
        }

        for join_handle in join_handles {
            join_handle.join().unwrap();
        }

        assert_eq!(counter.load(Ordering::Relaxed), 1);
    });
}
