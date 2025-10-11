/*
    dumpster, acycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

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

    #[expect(dead_code)]
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

struct Once {
    is_completed: Mutex<bool>,
}

impl Once {
    fn new() -> Self {
        Self {
            is_completed: Mutex::new(false),
        }
    }

    fn call_once(&self, f: impl FnOnce()) {
        let mut is_completed = self.is_completed.lock();

        if *is_completed {
            return;
        }

        f();
        *is_completed = true;
    }

    fn is_completed(&self) -> bool {
        *self.is_completed.lock()
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
