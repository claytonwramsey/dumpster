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

pub(crate) mod collect;
#[cfg(test)]
mod tests;

use std::{
    alloc::{dealloc, handle_alloc_error, Layout},
    borrow::{Borrow, Cow},
    cell::UnsafeCell,
    fmt::Debug,
    mem::{self, ManuallyDrop},
    num::NonZeroUsize,
    ops::Deref,
    ptr::{self, addr_of, addr_of_mut, drop_in_place, NonNull},
    slice,
    sync::atomic::{fence, AtomicUsize, Ordering},
};

use crate::{contains_gcs, panic_deref_of_collected_object, ptr::Nullable, Trace, Visitor};

use self::collect::{
    collect_all_await, mark_clean, mark_dirty, n_gcs_dropped, n_gcs_existing, notify_created_gc,
    notify_dropped_gc,
};

/// A soft limit on the amount of references that may be made to a `Gc`.
///
/// Going above this limit will abort your program (although not
/// necessarily) at _exactly_ `MAX_REFCOUNT + 1` references.
///
/// See comment in `Gc::clone`.
const MAX_STRONG_COUNT: usize = (isize::MAX) as usize;

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
// This is only public to make the `sync_coerce_gc` macro work.
#[doc(hidden)]
/// The backing allocation for a [`Gc`].
pub struct GcBox<T>
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
        unsafe { (!(*gc.ptr.get()).is_null()).then(|| &**gc) }
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

    /// Get the number of references to the value pointed to by this `Gc`.
    ///
    /// This does not include internal references generated by the garbage collector.
    ///
    /// # Panics
    ///
    /// This function may panic if the `Gc` whose reference count we are loading is "dead" (i.e.
    /// generated through a `Drop` implementation). For further reference, take a look at
    /// [`Gc::is_dead`].
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::sync::Gc;
    ///
    /// let gc = Gc::new(());
    /// assert_eq!(gc.ref_count().get(), 1);
    /// let gc2 = gc.clone();
    /// assert_eq!(gc.ref_count().get(), 2);
    /// drop(gc);
    /// drop(gc2);
    /// ```
    pub fn ref_count(&self) -> NonZeroUsize {
        let box_ptr = unsafe { *self.ptr.get() }.expect(
            "Attempt to dereference Gc to already-collected object. \
    This means a Gc escaped from a Drop implementation, likely implying a bug in your code.",
        );
        let box_ref = unsafe { box_ptr.as_ref() };
        NonZeroUsize::new(box_ref.strong.load(Ordering::Relaxed))
            .expect("strong count to a GcBox may never be zero while a Gc to it exists")
    }

    /// Determine whether this is a dead `Gc`.
    ///
    /// A `Gc` is dead if it is accessed while the value it points to has been destroyed; this only
    /// occurs if one attempts to interact with a `Gc` during a structure's [`Drop`] implementation.
    /// However, this is not always guaranteed - sometime the garbage collector will leave `Gc`s
    /// alive in differing orders, so users should not rely on the destruction order of `Gc`s to
    /// determine whether it is dead.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::{sync::Gc, Trace};
    /// use std::sync::OnceLock;
    ///
    /// #[derive(Trace)]
    /// struct Cycle(OnceLock<Gc<Self>>);
    ///
    /// impl Drop for Cycle {
    ///     fn drop(&mut self) {
    ///         assert!(self.0.get().unwrap().is_dead());
    ///     }
    /// }
    ///
    /// let gc1 = Gc::new(Cycle(OnceLock::new()));
    /// gc1.0.set(gc1.clone());
    /// # drop(gc1);
    /// # dumpster::sync::collect();
    /// ```
    #[inline]
    pub fn is_dead(&self) -> bool {
        unsafe { *self.ptr.get() }.is_null()
    }

    /// Consumes the `Gc<T>`, returning the inner `GcBox<T>` pointer and tag.
    #[inline]
    #[must_use]
    fn into_ptr(this: Self) -> (*const GcBox<T>, usize) {
        let this = ManuallyDrop::new(this);
        let ptr = &raw const this.ptr;
        let tag = &raw const this.tag;
        let ptr = unsafe { ptr.read() }.into_inner().as_ptr();
        let tag = unsafe { tag.read() }.into_inner();
        (ptr, tag)
    }

    /// Constructs a `Gc<T>` from the innner `GcBox<T>` pointer and tag.
    #[inline]
    #[must_use]
    unsafe fn from_ptr(ptr: *const GcBox<T>, tag: usize) -> Self {
        Self {
            ptr: UnsafeCell::new(Nullable::from_ptr(ptr.cast_mut())),
            tag: AtomicUsize::new(tag),
        }
    }

    /// Exists solely for the [`sync_coerce_gc`] macro.
    #[inline]
    #[must_use]
    #[doc(hidden)]
    pub fn __private_into_ptr(this: Self) -> (*const GcBox<T>, usize) {
        Self::into_ptr(this)
    }

    /// Exists solely for the [`sync_coerce_gc`] macro.
    #[inline]
    #[must_use]
    #[doc(hidden)]
    pub unsafe fn __private_from_ptr(ptr: *const GcBox<T>, tag: usize) -> Self {
        Self::from_ptr(ptr, tag)
    }
}

impl<T: Trace + Send + Sync + Clone> Gc<T> {
    /// Makes a mutable reference to the given `Gc`.
    ///
    /// If there are other `Gc` pointers to the same allocation, then `make_mut` will
    /// [`clone`] the inner value to a new allocation to ensure unique ownership. This is also
    /// referred to as clone-on-write.
    ///
    /// [`clone`]: Clone::clone
    ///
    /// # Panics
    ///
    /// This function may panic if the `Gc` whose reference count we are loading is "dead" (i.e.
    /// generated through a `Drop` implementation). For further reference, take a look at
    /// [`Gc::is_dead`].
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::unsync::Gc;
    ///
    /// let mut data = Gc::new(5);
    ///
    /// *Gc::make_mut(&mut data) += 1; // Won't clone anything
    /// let mut other_data = Gc::clone(&data); // Won't clone inner data
    /// *Gc::make_mut(&mut data) += 1; // Clones inner data
    /// *Gc::make_mut(&mut data) += 1; // Won't clone anything
    /// *Gc::make_mut(&mut other_data) *= 2; // Won't clone anything
    ///
    /// // Now `data` and `other_data` point to different allocations.
    /// assert_eq!(*data, 8);
    /// assert_eq!(*other_data, 12);
    /// ```
    #[inline]
    pub fn make_mut(this: &mut Self) -> &mut T {
        if this.is_dead() {
            panic_deref_of_collected_object();
        }

        // SAFETY: we checked above that the object is alive (not null)
        let box_ref = unsafe { this.ptr.get().read().unwrap_unchecked().as_ref() };

        let strong = box_ref.strong.load(Ordering::Acquire);
        let weak = box_ref.weak.load(Ordering::Acquire);

        if strong != 1 || weak != 0 {
            // We don't have unique access to the value so we need to clone it.
            *this = Gc::new(box_ref.value.clone());
        }

        // SAFETY: we have exclusive access to this `GcBox` because we ensured
        // that we hold the only reference to this allocation.
        // No other `Gc`s point to this allocation because the strong count is 1, and there are no
        // loose pointers internal to the collector because the weak count is 0.
        unsafe { &mut (*this.ptr.get_mut().as_ptr()).value }
    }
}

/// Allows coercing `T` of [`sync::Gc<T>`](Gc).
///
/// This means that you can convert a `Gc` containing a strictly-sized type (such as `[T; N]`) into
/// a `Gc` containing its unsized version (such as `[T]`), all without using nightly-only features.
///
/// # Examples
///
/// ```
/// use dumpster::{sync::Gc, sync_coerce_gc};
///
/// let gc1: Gc<[u8; 3]> = Gc::new([7, 8, 9]);
/// let gc2: Gc<[u8]> = sync_coerce_gc!(gc1);
/// assert_eq!(&gc2[..], &[7, 8, 9]);
/// ```
///
/// Note that although this macro allows for type conversion, it _cannot_ be used for converting
/// between incompatible types.
///
/// ```compile_fail
/// // This program is incorrect!
/// use dumpster::{sync::Gc, sync_coerce_gc};
///
/// let gc1: Gc<u8> = Gc::new(1);
/// let gc2: Gc<i8> = sync_coerce_gc!(gc1);
/// ```
#[macro_export]
macro_rules! sync_coerce_gc {
    ($gc:expr) => {{
        // Temporarily convert the `Gc` into a raw pointer to allow for coercion to occur.
        let (ptr, tag): (*const _, usize) = $crate::sync::Gc::__private_into_ptr($gc);
        unsafe { $crate::sync::Gc::__private_from_ptr(ptr, tag) }
    }};
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
        let old_strong = box_ref.strong.fetch_add(1, Ordering::Acquire);

        // We need to guard against massive refcounts in case someone is `mem::forget`ing
        // Gcs. If we don't do this the count can overflow and users will use-after free. This
        // branch will never be taken in any realistic program. We abort because such a program is
        // incredibly degenerate, and we don't care to support it.
        //
        // This check is not 100% water-proof: we error when the refcount grows beyond `isize::MAX`.
        // But we do that check *after* having done the increment, so there is a chance here that
        // the worst already happened and we actually do overflow the `usize` counter. However, that
        // requires the counter to grow from `isize::MAX` to `usize::MAX` between the increment
        // above and the `abort` below, which seems exceedingly unlikely.
        if old_strong > MAX_STRONG_COUNT {
            std::process::abort();
        }

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
        let is_bar = std::any::type_name::<T>()
            == "dumpster::sync::tests::sync_leak_by_creation_in_drop::Bar";
        if is_bar {
            println!("{}: call gc drop... ", std::any::type_name::<T>());
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
        if is_bar {
            println!(
                "starting strong count was {}",
                box_ref.strong.load(Ordering::Relaxed)
            );
        }
        match box_ref.strong.fetch_sub(1, Ordering::AcqRel) {
            0 => unreachable!("strong cannot reach zero while a Gc to it exists"),
            1 => {
                if is_bar {
                    println!("allocation has only one strong ref");
                }
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
                if is_bar {
                    println!("allocation has multiple strong refs");
                }
                if contains_gcs(&box_ref.value).unwrap_or(true) {
                    if is_bar {
                        println!("bar contains gcs");
                    }
                    // SAFETY: `ptr` is convertible to a reference
                    // We don't use `box_ref` here because that pointer
                    // only has `SharedReadOnly` permissions under the stacked borrows model
                    // when we need `Unique` for the `TrashCan`.
                    unsafe { mark_dirty(ptr) };
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

impl<T: Trace + Send + Sync + ?Sized> Gc<T> {
    /// Allocates an `GcBox<T>` with sufficient space for
    /// a value of the provided layout.
    ///
    /// The function `mem_to_gc_box` is called with the data pointer
    /// and must return back a pointer for the `GcBox<T>`.
    unsafe fn allocate_for_layout(
        value_layout: Layout,
        mem_to_gc_box: impl FnOnce(*mut u8) -> *mut GcBox<T>,
    ) -> *mut GcBox<T> {
        let layout = Layout::new::<GcBox<()>>()
            .extend(value_layout)
            .unwrap()
            .0
            .pad_to_align();

        Self::allocate_for_layout_of_box(layout, mem_to_gc_box)
    }

    /// Allocates an `GcBox<T>` with the given layout.
    ///
    /// The function `mem_to_gc_box` is called with the data pointer
    /// and must return back a pointer for the `GcBox<T>`.
    unsafe fn allocate_for_layout_of_box(
        layout: Layout,
        mem_to_gc_box: impl FnOnce(*mut u8) -> *mut GcBox<T>,
    ) -> *mut GcBox<T> {
        // SAFETY: layout has non-zero size because of the `ref_count` field
        let ptr = unsafe { std::alloc::alloc(layout) };

        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        let inner = mem_to_gc_box(ptr);

        unsafe {
            (&raw mut (*inner).strong).write(AtomicUsize::new(1));
            (&raw mut (*inner).weak).write(AtomicUsize::new(0));
            (&raw mut (*inner).generation).write(AtomicUsize::new(0));
        }

        inner
    }
}

impl<T: Trace + Send + Sync> Gc<[T]> {
    /// Allocates an `GcBox<[T]>` with the given length.
    fn allocate_for_slice(len: usize) -> *mut GcBox<[T]> {
        unsafe {
            Self::allocate_for_layout(Layout::array::<T>(len).unwrap(), |mem| {
                ptr::slice_from_raw_parts_mut(mem.cast::<T>(), len) as *mut GcBox<[T]>
            })
        }
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

impl<T: Trace + Send + Sync + Default> Default for Gc<T> {
    fn default() -> Self {
        Gc::new(T::default())
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

impl<T: Trace + Send + Sync> From<T> for Gc<T> {
    /// Converts a generic type `T` into an `Gc<T>`
    ///
    /// The conversion allocates on the heap and moves `t`
    /// from the stack into it.
    ///
    /// # Example
    /// ```rust
    /// # use dumpster::unsync::Gc;
    /// let x = 5;
    /// let rc = Gc::new(5);
    ///
    /// assert_eq!(Gc::from(x), rc);
    /// ```
    fn from(value: T) -> Self {
        Gc::new(value)
    }
}

impl<T: Trace + Send + Sync, const N: usize> From<[T; N]> for Gc<[T]> {
    /// Converts a [`[T; N]`](prim@array) into an `Gc<[T]>`.
    ///
    /// The conversion moves the array into a newly allocated `Gc`.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::unsync::Gc;
    /// let original: [i32; 3] = [1, 2, 3];
    /// let shared: Gc<[i32]> = Gc::from(original);
    /// assert_eq!(&[1, 2, 3], &shared[..]);
    /// ```
    #[inline]
    fn from(v: [T; N]) -> Gc<[T]> {
        sync_coerce_gc!(Gc::<[T; N]>::from(v))
    }
}

impl<T: Trace + Send + Sync + Clone> From<&[T]> for Gc<[T]> {
    /// Allocates a garbage-collected slice and fills it by cloning `slice`'s items.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::unsync::Gc;
    /// let original: &[i32] = &[1, 2, 3];
    /// let shared: Gc<[i32]> = Gc::from(original);
    /// assert_eq!(&[1, 2, 3], &shared[..]);
    /// ```
    #[inline]
    fn from(slice: &[T]) -> Gc<[T]> {
        // Panic guard while cloning T elements.
        // In the event of a panic, elements that have been written
        // into the new GcBox will be dropped, then the memory freed.
        struct Guard<T> {
            /// pointer to `GcBox` to deallocate on panic
            mem: *mut u8,
            /// layout of the `GcBox` to deallocate on panic
            layout: Layout,
            /// pointer to the `GcBox`'s value
            elems: *mut T,
            /// the number of elements cloned so far
            n_elems: usize,
        }

        impl<T> Drop for Guard<T> {
            fn drop(&mut self) {
                unsafe {
                    let slice = slice::from_raw_parts_mut(self.elems, self.n_elems);
                    ptr::drop_in_place(slice);

                    dealloc(self.mem, self.layout);
                }
            }
        }

        unsafe {
            let value_layout = Layout::array::<T>(slice.len()).unwrap();

            let layout = Layout::new::<GcBox<()>>()
                .extend(value_layout)
                .unwrap()
                .0
                .pad_to_align();

            let ptr = Self::allocate_for_layout_of_box(layout, |mem| {
                ptr::slice_from_raw_parts_mut(mem.cast::<T>(), slice.len()) as *mut GcBox<[T]>
            });

            // Pointer to first element
            let elems = (&raw mut (*ptr).value).cast::<T>();

            let mut guard = Guard {
                mem: ptr.cast::<u8>(),
                layout,
                elems,
                n_elems: 0,
            };

            for (i, item) in slice.iter().enumerate() {
                ptr::write(elems.add(i), item.clone());
                guard.n_elems += 1;
            }

            // All clear. Forget the guard so it doesn't free the new GcBox.
            mem::forget(guard);

            notify_created_gc();

            Self {
                ptr: UnsafeCell::new(Nullable::from_ptr(ptr)),
                tag: AtomicUsize::new(0),
            }
        }
    }
}

impl<T: Trace + Send + Sync + Clone> From<&mut [T]> for Gc<[T]> {
    /// Allocates a garbage-collected slice and fills it by cloning `v`'s items.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::unsync::Gc;
    /// let mut original = [1, 2, 3];
    /// let original: &mut [i32] = &mut original;
    /// let shared: Gc<[i32]> = Gc::from(original);
    /// assert_eq!(&[1, 2, 3], &shared[..]);
    /// ```
    #[inline]
    fn from(value: &mut [T]) -> Self {
        Gc::from(&*value)
    }
}

impl From<&str> for Gc<str> {
    /// Allocates a garbage-collected string slice and copies `v` into it.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::unsync::Gc;
    /// let shared: Gc<str> = Gc::from("statue");
    /// assert_eq!("statue", &shared[..]);
    /// ```
    #[inline]
    fn from(v: &str) -> Self {
        let bytes = Gc::<[u8]>::from(v.as_bytes());
        let (ptr, tag) = Gc::into_ptr(bytes);
        unsafe { Gc::from_ptr(ptr as *const GcBox<str>, tag) }
    }
}

impl From<&mut str> for Gc<str> {
    /// Allocates a garbage-collected string slice and copies `v` into it.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::unsync::Gc;
    /// let mut original = String::from("statue");
    /// let original: &mut str = &mut original;
    /// let shared: Gc<str> = Gc::from(original);
    /// assert_eq!("statue", &shared[..]);
    /// ```
    #[inline]
    fn from(v: &mut str) -> Self {
        Gc::from(&*v)
    }
}

impl From<Gc<str>> for Gc<[u8]> {
    /// Converts a garbage-collected string slice into a byte slice.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::unsync::Gc;
    /// let string: Gc<str> = Gc::from("eggplant");
    /// let bytes: Gc<[u8]> = Gc::from(string);
    /// assert_eq!("eggplant".as_bytes(), bytes.as_ref());
    /// ```
    #[inline]
    fn from(value: Gc<str>) -> Self {
        let (ptr, tag) = Gc::into_ptr(value);
        unsafe { Gc::from_ptr(ptr as *const GcBox<[u8]>, tag) }
    }
}

impl From<String> for Gc<str> {
    /// Allocates a garbage-collected string slice and copies `v` into it.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::unsync::Gc;
    /// let original: String = "statue".to_owned();
    /// let shared: Gc<str> = Gc::from(original);
    /// assert_eq!("statue", &shared[..]);
    /// ```
    #[inline]
    fn from(value: String) -> Self {
        Self::from(&value[..])
    }
}

impl<T: Trace + Send + Sync> From<Box<T>> for Gc<T> {
    /// Move a boxed object to a new, garbage collected, allocation.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::sync::Gc;
    /// let original: Box<i32> = Box::new(1);
    /// let shared: Gc<i32> = Gc::from(original);
    /// assert_eq!(1, *shared);
    /// ```
    #[inline]
    fn from(src: Box<T>) -> Self {
        unsafe {
            let layout = Layout::for_value(&*src);
            let gc_ptr = Gc::allocate_for_layout(layout, <*mut u8>::cast::<GcBox<T>>);

            // Copy value as bytes
            ptr::copy_nonoverlapping(
                (&raw const *src).cast::<u8>(),
                (&raw mut (*gc_ptr).value).cast::<u8>(),
                layout.size(),
            );

            // Free the allocation without dropping its contents
            let bptr = Box::into_raw(src);
            let src = Box::from_raw(bptr.cast::<mem::ManuallyDrop<T>>());
            drop(src);

            notify_created_gc();
            Self::from_ptr(gc_ptr, 0)
        }
    }
}

impl<T: Trace + Send + Sync> From<Vec<T>> for Gc<[T]> {
    /// Allocates a garbage-collected slice and moves `vec`'s items into it.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::unsync::Gc;
    /// let unique: Vec<i32> = vec![1, 2, 3];
    /// let shared: Gc<[i32]> = Gc::from(unique);
    /// assert_eq!(&[1, 2, 3], &shared[..]);
    /// ```
    #[inline]
    fn from(vec: Vec<T>) -> Self {
        let mut vec = ManuallyDrop::new(vec);
        let vec_cap = vec.capacity();
        let vec_len = vec.len();
        let vec_ptr = vec.as_mut_ptr();

        let gc_ptr = Self::allocate_for_slice(vec_len);

        unsafe {
            let dst_ptr = (&raw mut (*gc_ptr).value).cast::<T>();
            ptr::copy_nonoverlapping(vec_ptr, dst_ptr, vec_len);

            let _ = Vec::from_raw_parts(vec_ptr, 0, vec_cap);

            notify_created_gc();
            Self::from_ptr(gc_ptr, 0)
        }
    }
}

impl<'a, B: Trace + Send + Sync> From<Cow<'a, B>> for Gc<B>
where
    B: ToOwned + ?Sized,
    Gc<B>: From<&'a B> + From<B::Owned>,
{
    /// Creates a garbage-collected pointer from a clone-on-write pointer by
    /// copying its content.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use dumpster::unsync::Gc;
    /// # use std::borrow::Cow;
    /// let cow: Cow<'_, str> = Cow::Borrowed("eggplant");
    /// let shared: Gc<str> = Gc::from(cow);
    /// assert_eq!("eggplant", &shared[..]);
    /// ```
    #[inline]
    fn from(cow: Cow<'a, B>) -> Gc<B> {
        match cow {
            Cow::Borrowed(s) => Gc::from(s),
            Cow::Owned(s) => Gc::from(s),
        }
    }
}
