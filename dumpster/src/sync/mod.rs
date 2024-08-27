/*
    dumpster, acycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! Thread-safe shared garbage collection.
//!
//! Most users of this module will be interested in using [`Gc`] directly out of the box - this will
//! just work.
//! Those with more particular needs (such as benchmarking) should turn toward
//! [`set_collect_condition`] in order to tune exactly when the garbage collector does cleanups.
//!
//! # Examples
//!
//! ```
//! use dumpster::sync::Gc;
//!
//! let my_gc = Gc::new(100);
//! let other_gc = my_gc.clone();
//!
//! drop(my_gc);
//! drop(other_gc);
//!
//! // contents of the Gc are automatically freed
//! ```

mod collect;
#[cfg(test)]
mod tests;

use std::{
    alloc::{dealloc, Layout},
    borrow::Borrow,
    cell::UnsafeCell,
    fmt::Debug,
    ops::Deref,
    ptr::{addr_of, addr_of_mut, drop_in_place, NonNull},
    sync::atomic::{fence, AtomicUsize, Ordering},
};

use crate::{contains_gcs, ptr::Nullable, Trace, Visitor};

use self::collect::{
    collect_all_await, currently_cleaning, mark_clean, mark_dirty, n_gcs_dropped, n_gcs_existing,
    notify_created_gc, notify_dropped_gc,
};

/// A thread-safe garbage-collected pointer.
///
/// This pointer can be duplicated and then shared across threads.
/// Garbage collection is performed concurrently.
///
/// # Examples
///
/// ```
/// use dumpster::sync::Gc;
/// use std::sync::atomic::{AtomicUsize, Ordering};
///
/// let shared = Gc::new(AtomicUsize::new(0));
///
/// std::thread::scope(|s| {
///     s.spawn(|| {
///         let other_gc = shared.clone();
///         other_gc.store(1, Ordering::Relaxed);
///     });
///
///     shared.store(2, Ordering::Relaxed);
/// });
///
/// println!("{}", shared.load(Ordering::Relaxed));
/// ```
///
/// # Interaction with `Drop`
///
/// While collecting cycles, it's possible for a `Gc` to exist that points to some deallocated
/// object.
/// To prevent undefined behavior, these `Gc`s are marked as dead during collection and rendered
/// inaccessible.
/// Dereferencing or cloning a `Gc` during the `Drop` implementation of a `Trace` type could
/// result in the program panicking to keep the program from accessing memory after freeing it.
/// If you're accessing a `Gc` during a `Drop` implementation, make sure to use the fallible
/// operations [`Gc::try_deref`] and [`Gc::try_clone`].
pub struct Gc<T: Trace + Send + Sync + ?Sized + 'static> {
    /// The pointer to the allocation.
    ptr: UnsafeCell<Nullable<GcBox<T>>>,
    /// The tag information of this pointer, used for mutation detection when marking.
    tag: AtomicUsize,
}

/// The tag of the current sweep operation.
/// All new allocations are minted with the current tag.
static CURRENT_TAG: AtomicUsize = AtomicUsize::new(0);

#[repr(C)]
/// The backing allocation for a [`Gc`].
struct GcBox<T>
where
    T: Trace + Send + Sync + ?Sized,
{
    /// The "strong" count, which is the number of extant `Gc`s to this allocation.
    /// If the strong count is zero, a value contained in the allocation may be dropped, but the
    /// allocation itself must still be valid.
    strong: AtomicUsize,
    /// The "weak" count, which is the number of references to this allocation stored in to-collect
    /// buffers by the collection algorithm.
    /// If the weak count is zero, the allocation may be destroyed.
    weak: AtomicUsize,
    /// The current generation number of the allocation.
    /// The generation number is assigned to the global generation every time a strong reference is
    /// created or destroyed or a `Gc` pointing to this allocation is dereferenced.
    generation: AtomicUsize,
    /// The actual data stored in the allocation.
    value: T,
}

unsafe impl<T> Send for Gc<T> where T: Trace + Send + Sync + ?Sized {}
unsafe impl<T> Sync for Gc<T> where T: Trace + Send + Sync + ?Sized {}

/// Begin a collection operation of the allocations on the heap.
///
/// Due to concurrency issues, this might not collect every single unreachable allocation that
/// currently exists, but often calling `collect()` will get allocations made by this thread.
///
/// # Examples
///
/// ```
/// use dumpster::sync::{collect, Gc};
///
/// let gc = Gc::new(vec![1, 2, 3]);
/// drop(gc);
///
/// collect(); // the vector originally in `gc` _might_ be dropped now, but could be dropped later
/// ```
pub fn collect() {
    collect_all_await();
}

#[derive(Debug)]
/// Information passed to a [`CollectCondition`] used to determine whether the garbage collector
/// should start collecting.
///
/// A `CollectInfo` is exclusively created by being passed as an argument to the collection
/// condition.
/// To set a custom collection condition, refer to [`set_collect_condition`].
///
/// # Examples
///
/// ```
/// use dumpster::sync::{set_collect_condition, CollectInfo};
///
/// fn my_collect_condition(info: &CollectInfo) -> bool {
///     (info.n_gcs_dropped_since_last_collect() + info.n_gcs_existing()) % 2 == 0
/// }
///
/// set_collect_condition(my_collect_condition);
/// ```
pub struct CollectInfo {
    /// Dummy value so this is a private structure.
    _private: (),
}

/// A function which determines whether the garbage collector should start collecting.
/// This type primarily exists so that it can be used with [`set_collect_condition`].
///
/// # Examples
///
/// ```rust
/// use dumpster::sync::{set_collect_condition, CollectInfo};
///
/// fn always_collect(_: &CollectInfo) -> bool {
///     true
/// }
///
/// set_collect_condition(always_collect);
/// ```
pub type CollectCondition = fn(&CollectInfo) -> bool;

#[must_use]
/// The default collection condition used by the garbage collector.
///
/// There are no guarantees about what this function returns, other than that it will return `true`
/// with sufficient frequency to ensure that all `Gc` operations are amortized _O(1)_ in runtime.
///
/// This function isn't really meant to be called by users, but rather it's supposed to be handed
/// off to [`set_collect_condition`] to return to the default operating mode of the library.
///
/// This collection condition applies globally, i.e. to every thread.
///
/// # Examples
///
/// ```rust
/// use dumpster::sync::{default_collect_condition, set_collect_condition, CollectInfo};
///
/// fn other_collect_condition(info: &CollectInfo) -> bool {
///     info.n_gcs_existing() >= 25 || default_collect_condition(info)
/// }
///
/// // Use my custom collection condition.
/// set_collect_condition(other_collect_condition);
///
/// // I'm sick of the custom collection condition.
/// // Return to the original.
/// set_collect_condition(default_collect_condition);
/// ```
pub fn default_collect_condition(info: &CollectInfo) -> bool {
    info.n_gcs_dropped_since_last_collect() > info.n_gcs_existing()
}

pub use collect::set_collect_condition;

impl<T> Gc<T>
where
    T: Trace + Send + Sync + ?Sized,
{
    /// Construct a new garbage-collected value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::sync::Gc;
    ///
    /// let _ = Gc::new(0);
    /// ```
    pub fn new(value: T) -> Gc<T>
    where
        T: Sized,
    {
        notify_created_gc();
        Gc {
            ptr: UnsafeCell::new(Nullable::new(NonNull::from(Box::leak(Box::new(GcBox {
                strong: AtomicUsize::new(1),
                weak: AtomicUsize::new(0),
                generation: AtomicUsize::new(CURRENT_TAG.load(Ordering::Acquire)),
                value,
            }))))),
            tag: AtomicUsize::new(0),
        }
    }

    /// Attempt to dereference this `Gc`.
    ///
    /// This function will return `None` if `self` is a "dead" `Gc`, which points to an
    /// already-deallocated object.
    /// This can only occur if a `Gc` is accessed during the `Drop` implementation of a
    /// [`Trace`] object.
    ///
    /// For a version which panics instead of returning `None`, consider using [`Deref`].
    ///
    /// # Examples
    ///
    /// For a still-living `Gc`, this always returns `Some`.
    ///
    /// ```
    /// use dumpster::sync::Gc;
    ///
    /// let gc1 = Gc::new(0);
    /// assert!(Gc::try_deref(&gc1).is_some());
    /// ```
    ///
    /// The only way to get a `Gc` which fails on `try_clone` is by accessing a `Gc` during its
    /// `Drop` implementation.
    ///
    /// ```
    /// use dumpster::{sync::Gc, Trace};
    /// use std::sync::Mutex;
    ///
    /// #[derive(Trace)]
    /// struct Cycle(Mutex<Option<Gc<Self>>>);
    ///
    /// impl Drop for Cycle {
    ///     fn drop(&mut self) {
    ///         let guard = self.0.lock().unwrap();
    ///         let maybe_ref = Gc::try_deref(guard.as_ref().unwrap());
    ///         assert!(maybe_ref.is_none());
    ///     }
    /// }
    ///
    /// let gc1 = Gc::new(Cycle(Mutex::new(None)));
    /// *gc1.0.lock().unwrap() = Some(gc1.clone());
    /// # drop(gc1);
    /// # dumpster::sync::collect();
    /// ```
    pub fn try_deref(gc: &Gc<T>) -> Option<&T> {
        #[allow(clippy::unnecessary_lazy_evaluations)]
        unsafe {
            (!(*gc.ptr.get()).is_null()).then(|| &**gc)
        }
    }

    /// Attempt to clone this `Gc`.
    ///
    /// This function will return `None` if `self` is a "dead" `Gc`, which points to an
    /// already-deallocated object.
    /// This can only occur if a `Gc` is accessed during the `Drop` implementation of a
    /// [`Trace`] object.
    ///
    /// For a version which panics instead of returning `None`, consider using [`Clone`].
    ///
    /// # Examples
    ///
    /// For a still-living `Gc`, this always returns `Some`.
    ///
    /// ```
    /// use dumpster::sync::Gc;
    ///
    /// let gc1 = Gc::new(0);
    /// let gc2 = Gc::try_clone(&gc1).unwrap();
    /// ```
    ///
    /// The only way to get a `Gc` which fails on `try_clone` is by accessing a `Gc` during its
    /// `Drop` implementation.
    ///
    /// ```
    /// use dumpster::{sync::Gc, Trace};
    /// use std::sync::Mutex;
    ///
    /// #[derive(Trace)]
    /// struct Cycle(Mutex<Option<Gc<Self>>>);
    ///
    /// impl Drop for Cycle {
    ///     fn drop(&mut self) {
    ///         let cloned = Gc::try_clone(self.0.lock().unwrap().as_ref().unwrap());
    ///         assert!(cloned.is_none());
    ///     }
    /// }
    ///
    /// let gc1 = Gc::new(Cycle(Mutex::new(None)));
    /// *gc1.0.lock().unwrap() = Some(gc1.clone());
    /// # drop(gc1);
    /// # dumpster::sync::collect();
    /// ```
    pub fn try_clone(gc: &Gc<T>) -> Option<Gc<T>> {
        unsafe { (!(*gc.ptr.get()).is_null()).then(|| gc.clone()) }
    }

    /// Provides a raw pointer to the data.
    ///
    /// Panics if `self` is a "dead" `Gc`,
    /// which points to an already-deallocated object.
    /// This can only occur if a `Gc` is accessed during the `Drop` implementation of a
    /// [`Trace`] object.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::sync::Gc;
    /// let x = Gc::new("hello".to_owned());
    /// let y = Gc::clone(&x);
    /// let x_ptr = Gc::as_ptr(&x);
    /// assert_eq!(x_ptr, Gc::as_ptr(&x));
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// ```
    pub fn as_ptr(gc: &Gc<T>) -> *const T {
        unsafe {
            let ptr = NonNull::as_ptr((*gc.ptr.get()).unwrap());
            addr_of_mut!((*ptr).value)
        }
    }

    /// Determine whether two `Gc`s are equivalent by reference.
    /// Returns `true` if both `this` and `other` point to the same value, in the same style as
    /// [`std::ptr::eq`].
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::sync::Gc;
    ///
    /// let gc1 = Gc::new(0);
    /// let gc2 = Gc::clone(&gc1); // points to same spot as `gc1`
    /// let gc3 = Gc::new(0); // same value, but points to a different object than `gc1`
    ///
    /// assert!(Gc::ptr_eq(&gc1, &gc2));
    /// assert!(!Gc::ptr_eq(&gc1, &gc3));
    /// ```
    pub fn ptr_eq(this: &Gc<T>, other: &Gc<T>) -> bool {
        unsafe { *this.ptr.get() }.as_option() == unsafe { *other.ptr.get() }.as_option()
    }
}

impl<T> Clone for Gc<T>
where
    T: Trace + Send + Sync + ?Sized,
{
    /// Clone a garbage-collected reference.
    /// This does not clone the underlying data.
    ///
    /// # Panics
    ///
    /// This function will panic if the `Gc` being cloned points to a deallocated object.
    /// This is only possible if said `Gc` is accessed during the `Drop` implementation of a
    /// `Trace` value.
    ///
    /// For a fallible version, refer to [`Gc::try_clone`].
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::sync::Gc;
    /// use std::sync::atomic::{AtomicU8, Ordering};
    ///
    /// let gc1 = Gc::new(AtomicU8::new(0));
    /// let gc2 = gc1.clone();
    ///
    /// gc1.store(1, Ordering::Relaxed);
    /// assert_eq!(gc2.load(Ordering::Relaxed), 1);
    /// ```
    ///
    /// The following example will fail, because cloning a `Gc` to a deallocated object is wrong.
    ///
    /// ```should_panic
    /// use dumpster::{sync::Gc, Trace};
    /// use std::sync::Mutex;
    ///
    /// #[derive(Trace)]
    /// struct Cycle(Mutex<Option<Gc<Self>>>);
    ///
    /// impl Drop for Cycle {
    ///     fn drop(&mut self) {
    ///         let _ = self.0.lock().unwrap().as_ref().unwrap().clone();
    ///     }
    /// }
    ///
    /// let gc1 = Gc::new(Cycle(Mutex::new(None)));
    /// *gc1.0.lock().unwrap() = Some(gc1.clone());
    /// # drop(gc1);
    /// # dumpster::sync::collect();
    /// ```
    fn clone(&self) -> Gc<T> {
        let box_ref = unsafe {
            (*self.ptr.get()).expect("attempt to clone Gc to already-deallocated object. \
            This means a Gc was accessed during a Drop implementation, likely implying a bug in your code.").as_ref()
        };
        // increment strong count before generation to ensure cleanup never underestimates ref count
        box_ref.strong.fetch_add(1, Ordering::Acquire);
        box_ref
            .generation
            .store(CURRENT_TAG.load(Ordering::Acquire), Ordering::Release);
        notify_created_gc();
        // mark_clean(box_ref); // causes performance drops
        Gc {
            ptr: UnsafeCell::new(unsafe { *self.ptr.get() }),
            tag: AtomicUsize::new(CURRENT_TAG.load(Ordering::Acquire)),
        }
    }
}

impl<T> Drop for Gc<T>
where
    T: Trace + Send + Sync + ?Sized,
{
    fn drop(&mut self) {
        if currently_cleaning() {
            return;
        }
        let Some(mut ptr) = unsafe { *self.ptr.get() }.as_option() else {
            return;
        };
        let box_ref = unsafe { ptr.as_ref() };
        box_ref.weak.fetch_add(1, Ordering::AcqRel); // ensures that this allocation wasn't freed
                                                     // while we weren't looking
        box_ref
            .generation
            .store(CURRENT_TAG.load(Ordering::Relaxed), Ordering::Release);
        match box_ref.strong.fetch_sub(1, Ordering::AcqRel) {
            0 => unreachable!("strong cannot reach zero while a Gc to it exists"),
            1 => {
                mark_clean(box_ref);
                if box_ref.weak.fetch_sub(1, Ordering::Release) == 1 {
                    // destroyed the last weak reference! we can safely deallocate this
                    let layout = Layout::for_value(box_ref);
                    fence(Ordering::Acquire);
                    unsafe {
                        drop_in_place(ptr.as_mut());
                        dealloc(ptr.as_ptr().cast(), layout);
                    }
                }
            }
            _ => {
                if contains_gcs(&box_ref.value).unwrap_or(true) {
                    mark_dirty(ptr);
                }
                box_ref.weak.fetch_sub(1, Ordering::Release);
            }
        }
        notify_dropped_gc();
    }
}

impl CollectInfo {
    #[must_use]
    /// Get the number of times that a [`Gc`] has been dropped since the last time a collection
    /// operation was performed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::sync::{set_collect_condition, CollectInfo};
    ///
    /// // Collection condition for whether many Gc's have been dropped.
    /// fn have_many_gcs_dropped(info: &CollectInfo) -> bool {
    ///     info.n_gcs_dropped_since_last_collect() > 100
    /// }
    ///
    /// set_collect_condition(have_many_gcs_dropped);
    /// ```
    pub fn n_gcs_dropped_since_last_collect(&self) -> usize {
        n_gcs_dropped()
    }

    #[must_use]
    /// Get the total number of [`Gc`]s which currently exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::sync::{set_collect_condition, CollectInfo};
    ///
    /// // Collection condition for whether many Gc's currently exist.
    /// fn do_many_gcs_exist(info: &CollectInfo) -> bool {
    ///     info.n_gcs_existing() > 100
    /// }
    ///
    /// set_collect_condition(do_many_gcs_exist);
    /// ```
    pub fn n_gcs_existing(&self) -> usize {
        n_gcs_existing()
    }
}

unsafe impl<T: Trace + Send + Sync + ?Sized> Trace for Gc<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        visitor.visit_sync(self);
        Ok(())
    }
}

impl<T: Trace + Send + Sync + ?Sized> Deref for Gc<T> {
    type Target = T;

    /// Dereference this pointer, creating a reference to the contained value `T`.
    ///
    /// # Panics
    ///
    /// This function may panic if it is called from within the implementation of `std::ops::Drop`
    /// of its owning value, since returning such a reference could cause a use-after-free.
    /// It is not guaranteed to panic.
    ///
    /// # Examples
    ///
    /// The following is a correct time to dereference a `Gc`.
    ///
    /// ```
    /// use dumpster::sync::Gc;
    ///
    /// let my_gc = Gc::new(0u8);
    /// let my_ref: &u8 = &my_gc;
    /// ```
    ///
    /// Dereferencing a `Gc` while dropping is not correct.
    ///
    /// ```should_panic
    /// // This is wrong!
    /// use dumpster::{sync::Gc, Trace};
    /// use std::sync::Mutex;
    ///
    /// #[derive(Trace)]
    /// struct Bad {
    ///     s: String,
    ///     cycle: Mutex<Option<Gc<Bad>>>,
    /// }
    ///
    /// impl Drop for Bad {
    ///     fn drop(&mut self) {
    ///         println!("{}", self.cycle.lock().unwrap().as_ref().unwrap().s)
    ///     }
    /// }
    ///
    /// let foo = Gc::new(Bad {
    ///     s: "foo".to_string(),
    ///     cycle: Mutex::new(None),
    /// });
    /// ```
    fn deref(&self) -> &Self::Target {
        let box_ref = unsafe {
            (*self.ptr.get()).expect(
            "Attempting to dereference Gc to already-deallocated object.\
            This is caused by accessing a Gc during a Drop implementation, likely implying a bug in your code."
        ).as_ref()
        };
        let current_tag = CURRENT_TAG.load(Ordering::Acquire);
        self.tag.store(current_tag, Ordering::Release);
        box_ref.generation.store(current_tag, Ordering::Release);
        &box_ref.value
    }
}

impl<T> PartialEq<Gc<T>> for Gc<T>
where
    T: Trace + Send + Sync + ?Sized + PartialEq,
{
    /// Test for equality on two `Gc`s.
    ///
    /// Two `Gc`s are equal if their inner values are equal, even if they are stored in different
    /// allocations.
    /// Because `PartialEq` does not imply reflexivity, and there is no current path for trait
    /// specialization, this function does not do a "fast-path" check for reference equality.
    /// Therefore, if two `Gc`s point to the same allocation, the implementation of `eq` will still
    /// require a direct call to `eq` on the values.
    ///
    /// # Panics
    ///
    /// This function may panic if it is called from within the implementation of `std::ops::Drop`
    /// of its owning value, since returning such a reference could cause a use-after-free.
    /// It is not guaranteed to panic.
    /// Additionally, if this `Gc` is moved out of an allocation during a `Drop` implementation, it
    /// could later cause a panic.
    /// For further details, refer to the main documentation for `Gc`.
    ///
    /// ```
    /// use dumpster::sync::Gc;
    ///
    /// let gc = Gc::new(6);
    /// assert!(gc == Gc::new(6));
    /// ```
    fn eq(&self, other: &Gc<T>) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T> Eq for Gc<T> where T: Trace + Send + Sync + ?Sized + PartialEq {}

impl<T: Trace + Send + Sync + ?Sized> AsRef<T> for Gc<T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: Trace + Send + Sync + ?Sized> Borrow<T> for Gc<T> {
    fn borrow(&self) -> &T {
        self
    }
}

impl<T: Trace + Send + Sync + ?Sized> std::fmt::Pointer for Gc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Pointer::fmt(&addr_of!(**self), f)
    }
}

#[cfg(feature = "coerce-unsized")]
impl<T, U> std::ops::CoerceUnsized<Gc<U>> for Gc<T>
where
    T: std::marker::Unsize<U> + Trace + Send + Sync + ?Sized,
    U: Trace + Send + Sync + ?Sized,
{
}

impl<T: Trace + Send + Sync + ?Sized> Debug for Gc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Gc({:?}, {})",
            self.ptr,
            self.tag.load(Ordering::Acquire)
        )
    }
}
