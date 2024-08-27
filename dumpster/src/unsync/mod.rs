/*
    dumpster, acycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! Thread-local garbage collection.
//!
//! Most users of this library will want to direct their attention to [`Gc`].
//! If you want to tune the garbage collector's cleanup frequency, take a look at
//! [`set_collect_condition`].
//!
//! # Examples
//!
//! ```
//! use dumpster::{unsync::Gc, Trace};
//! use std::cell::RefCell;
//!
//! #[derive(Trace)]
//! struct Foo {
//!     refs: RefCell<Vec<Gc<Self>>>,
//! }
//!
//! let foo = Gc::new(Foo {
//!     refs: RefCell::new(Vec::new()),
//! });
//!
//! // If you had used `Rc`, this would be a memory leak.
//! // `Gc` can collect it, though!
//! foo.refs.borrow_mut().push(foo.clone());
//! ```

use std::{
    alloc::{dealloc, Layout},
    borrow::Borrow,
    cell::Cell,
    num::NonZeroUsize,
    ops::Deref,
    ptr::{addr_of, addr_of_mut, drop_in_place, NonNull},
};

use crate::{contains_gcs, ptr::Nullable, Trace, Visitor};

use self::collect::{Dumpster, COLLECTING, DUMPSTER};

mod collect;
#[cfg(test)]
mod tests;

#[derive(Debug)]
/// A garbage-collected pointer.
///
/// This garbage-collected pointer may be used for data which is not safe to share across threads
/// (such as a [`std::cell::RefCell`]).
/// It can also be used for variably sized data.
///
/// # Examples
///
/// ```
/// use dumpster::unsync::Gc;
///
/// let x: Gc<u8> = Gc::new(3);
///
/// println!("{}", *x); // prints '3'
///                     // x is then freed automatically!
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
pub struct Gc<T: Trace + ?Sized + 'static> {
    /// A pointer to the heap allocation containing the data under concern.
    /// The pointee box should never be mutated.
    ///
    /// If `ptr` is `None`, then this is a dead `Gc`, meaning that the allocation it points to has
    /// been dropped.
    /// This can only happen observably if this `Gc` is accessed during the [`Drop`] implementation
    /// of a [`Trace`] type.
    ptr: Cell<Nullable<GcBox<T>>>,
}

/// Collect all existing unreachable allocations.
///
/// This operation is most useful for making sure that the `Drop` implementation for some data has
/// been called before moving on (such as for a file handle or mutex guard), because the garbage
/// collector is not eager under normal conditions.
/// This only collects the allocations local to the caller's thread.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
/// use dumpster::unsync::{collect, Gc};
/// use std::sync::Mutex;
///
/// static MY_MUTEX: Mutex<()> = Mutex::new(());
///
/// let guard_gc = Gc::new(MY_MUTEX.lock()?);
/// drop(guard_gc);
/// // We're not certain that the handle that was contained in `guard_gc` has been dropped, so we
/// // should force a collection to make sure.
/// collect();
///
/// // We know this won't cause a deadlock because we made sure to run a collection.
/// let _x = MY_MUTEX.lock()?;
/// # Ok(())
/// # }
/// ```
pub fn collect() {
    DUMPSTER.with(Dumpster::collect_all);
}

/// Information passed to a [`CollectCondition`] used to determine whether the garbage collector
/// should start collecting.
pub struct CollectInfo {
    /// Dummy value so this is a private structure.
    _private: (),
}

/// A function which determines whether the garbage collector should start collecting.
/// This function primarily exists so that it can be used with [`set_collect_condition`].
///
/// # Examples
///
/// ```rust
/// use dumpster::unsync::{set_collect_condition, CollectInfo};
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
/// This collection condition applies locally, i.e. only to this thread.
/// If you want it to apply globally, you'll have to update it every time you spawn a thread.
///
/// # Examples
///
/// ```rust
/// use dumpster::unsync::{default_collect_condition, set_collect_condition};
///
/// set_collect_condition(default_collect_condition);
/// ```
pub fn default_collect_condition(info: &CollectInfo) -> bool {
    info.n_gcs_dropped_since_last_collect() > info.n_gcs_existing()
}

#[allow(clippy::missing_panics_doc)]
/// Set the function which determines whether the garbage collector should be run.
///
/// `f` will be periodically called by the garbage collector to determine whether it should perform
/// a full cleanup of the heap.
/// When `f` returns true, a cleanup will begin.
///
/// # Examples
///
/// ```
/// use dumpster::unsync::{set_collect_condition, CollectInfo};
///
/// /// This function will make sure a GC cleanup never happens unless directly activated.
/// fn never_collect(_: &CollectInfo) -> bool {
///     false
/// }
///
/// set_collect_condition(never_collect);
/// ```
pub fn set_collect_condition(f: CollectCondition) {
    DUMPSTER.with(|d| d.collect_condition.set(f));
}

#[repr(C)]
/// The underlying heap allocation for a [`Gc`].
struct GcBox<T: Trace + ?Sized> {
    /// The number of extant references to this garbage-collected data.
    /// If the stored reference count is zero, then this value is a "zombie" - in the process of
    /// being dropped - and should not be dropped again.
    ref_count: Cell<NonZeroUsize>,
    /// The stored value inside this garbage-collected box.
    value: T,
}

impl<T: Trace + ?Sized> Gc<T> {
    /// Construct a new garbage-collected allocation, with `value` as its value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::unsync::Gc;
    ///
    /// let gc = Gc::new(0);
    /// ```
    pub fn new(value: T) -> Gc<T>
    where
        T: Sized,
    {
        DUMPSTER.with(Dumpster::notify_created_gc);
        Gc {
            ptr: Cell::new(Nullable::new(NonNull::from(Box::leak(Box::new(GcBox {
                ref_count: Cell::new(NonZeroUsize::MIN),
                value,
            }))))),
        }
    }

    #[allow(clippy::unnecessary_lazy_evaluations)]
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
    /// use dumpster::unsync::Gc;
    ///
    /// let gc1 = Gc::new(0);
    /// assert!(Gc::try_deref(&gc1).is_some());
    /// ```
    ///
    /// The only way to get a `Gc` which fails on `try_clone` is by accessing a `Gc` during its
    /// `Drop` implementation.
    ///
    /// ```
    /// use dumpster::{unsync::Gc, Trace};
    /// use std::cell::OnceCell;
    ///
    /// #[derive(Trace)]
    /// struct Cycle(OnceCell<Gc<Self>>);
    ///
    /// impl Drop for Cycle {
    ///     fn drop(&mut self) {
    ///         let maybe_ref = Gc::try_deref(self.0.get().unwrap());
    ///         assert!(maybe_ref.is_none());
    ///     }
    /// }
    ///
    /// let gc1 = Gc::new(Cycle(OnceCell::new()));
    /// gc1.0.set(gc1.clone());
    /// # drop(gc1);
    /// # dumpster::unsync::collect();
    /// ```
    pub fn try_deref(gc: &Gc<T>) -> Option<&T> {
        (!gc.ptr.get().is_null()).then(|| &**gc)
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
    /// use dumpster::unsync::Gc;
    ///
    /// let gc1 = Gc::new(0);
    /// let gc2 = Gc::try_clone(&gc1).unwrap();
    /// ```
    ///
    /// The only way to get a `Gc` which fails on `try_clone` is by accessing a `Gc` during its
    /// `Drop` implementation.
    ///
    /// ```
    /// use dumpster::{unsync::Gc, Trace};
    /// use std::cell::OnceCell;
    ///
    /// #[derive(Trace)]
    /// struct Cycle(OnceCell<Gc<Self>>);
    ///
    /// impl Drop for Cycle {
    ///     fn drop(&mut self) {
    ///         let cloned = Gc::try_clone(self.0.get().unwrap());
    ///         assert!(cloned.is_none());
    ///     }
    /// }
    ///
    /// let gc1 = Gc::new(Cycle(OnceCell::new()));
    /// gc1.0.set(gc1.clone());
    /// # drop(gc1);
    /// # dumpster::unsync::collect();
    /// ```
    pub fn try_clone(gc: &Gc<T>) -> Option<Gc<T>> {
        (!gc.ptr.get().is_null()).then(|| gc.clone())
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
    /// use dumpster::unsync::Gc;
    /// let x = Gc::new("hello".to_owned());
    /// let y = Gc::clone(&x);
    /// let x_ptr = Gc::as_ptr(&x);
    /// assert_eq!(x_ptr, Gc::as_ptr(&x));
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// ```
    pub fn as_ptr(gc: &Gc<T>) -> *const T {
        let ptr = NonNull::as_ptr(gc.ptr.get().unwrap());
        unsafe { addr_of_mut!((*ptr).value) }
    }

    /// Determine whether two `Gc`s are equivalent by reference.
    /// Returns `true` if both `this` and `other` point to the same value, in the same style as
    /// [`std::ptr::eq`].
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::unsync::Gc;
    ///
    /// let gc1 = Gc::new(0);
    /// let gc2 = Gc::clone(&gc1); // points to same spot as `gc1`
    /// let gc3 = Gc::new(0); // same value, but points to a different object than `gc1`
    ///
    /// assert!(Gc::ptr_eq(&gc1, &gc2));
    /// assert!(!Gc::ptr_eq(&gc1, &gc3));
    /// ```
    pub fn ptr_eq(this: &Gc<T>, other: &Gc<T>) -> bool {
        this.ptr.get().as_option() == other.ptr.get().as_option()
    }
}

impl<T: Trace + ?Sized> Deref for Gc<T> {
    type Target = T;

    /// Dereference this pointer, creating a reference to the contained value `T`.
    ///
    /// # Panics
    ///
    /// This function may panic if it is called from within the implementation of `std::ops::Drop`
    /// of its owning value, since returning such a reference could cause a use-after-free.
    /// It is not guaranteed to panic.
    ///
    /// For a version which returns `None` instead of panicking, consider [`Gc::try_deref`].
    ///
    /// # Examples
    ///
    /// The following is a correct time to dereference a `Gc`.
    ///
    /// ```
    /// use dumpster::unsync::Gc;
    ///
    /// let my_gc = Gc::new(0u8);
    /// let my_ref: &u8 = &my_gc;
    /// ```
    ///
    /// Dereferencing a `Gc` while dropping is not correct.
    ///
    /// ```should_panic
    /// // This is wrong!
    /// use dumpster::{unsync::Gc, Trace};
    /// use std::cell::RefCell;
    ///
    /// #[derive(Trace)]
    /// struct Bad {
    ///     s: String,
    ///     cycle: RefCell<Option<Gc<Bad>>>,
    /// }
    ///
    /// impl Drop for Bad {
    ///     fn drop(&mut self) {
    ///         println!("{}", self.cycle.borrow().as_ref().unwrap().s)
    ///     }
    /// }
    ///
    /// let foo = Gc::new(Bad {
    ///     s: "foo".to_string(),
    ///     cycle: RefCell::new(None),
    /// });
    /// ```
    fn deref(&self) -> &Self::Target {
        assert!(
            !COLLECTING.with(Cell::get),
            "dereferencing GC to already-collected object"
        );
        unsafe {
            &self.ptr.get().expect("dereferencing Gc to already-collected object. \
            This means a Gc escaped from a Drop implementation, likely implying a bug in your code.").as_ref().value
        }
    }
}

impl<T: Trace + ?Sized> Clone for Gc<T> {
    #[allow(clippy::clone_on_copy)]
    /// Create a duplicate reference to the same data pointed to by `self`.
    /// This does not duplicate the data.
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
    /// use dumpster::unsync::Gc;
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
    /// use dumpster::{unsync::Gc, Trace};
    /// use std::cell::OnceCell;
    ///
    /// #[derive(Trace)]
    /// struct Cycle(OnceCell<Gc<Self>>);
    ///
    /// impl Drop for Cycle {
    ///     fn drop(&mut self) {
    ///         let _ = self.0.get().unwrap().clone();
    ///     }
    /// }
    ///
    /// let gc1 = Gc::new(Cycle(OnceCell::new()));
    /// gc1.0.set(gc1.clone());
    /// # drop(gc1);
    /// # dumpster::unsync::collect();
    /// ```
    fn clone(&self) -> Self {
        unsafe {
            let box_ref = self.ptr.get().expect("Attempt to clone Gc to already-collected object. \
            This means a Gc escaped from a Drop implementation, likely implying a bug in your code.").as_ref();
            box_ref
                .ref_count
                .set(box_ref.ref_count.get().saturating_add(1));
        }
        DUMPSTER.with(|d| {
            d.notify_created_gc();
            // d.mark_cleaned(self.ptr);
        });
        Self {
            ptr: self.ptr.clone(),
        }
    }
}

impl<T: Trace + ?Sized> Drop for Gc<T> {
    /// Destroy this garbage-collected pointer.
    ///
    /// If this is the last reference which can reach the pointed-to data, the allocation that it
    /// points to will be destroyed.
    fn drop(&mut self) {
        if COLLECTING.with(Cell::get) {
            return;
        }
        let Some(mut ptr) = self.ptr.get().as_option() else {
            return;
        };
        DUMPSTER.with(|d| {
            let box_ref = unsafe { ptr.as_ref() };
            match box_ref.ref_count.get() {
                NonZeroUsize::MIN => {
                    d.mark_cleaned(ptr);
                    unsafe {
                        // this was the last reference, drop unconditionally
                        drop_in_place(addr_of_mut!(ptr.as_mut().value));
                        // note: `box_ref` is no longer usable
                        dealloc(ptr.as_ptr().cast::<u8>(), Layout::for_value(ptr.as_ref()));
                    }
                }
                n => {
                    // decrement the ref count - but another reference to this data still
                    // lives
                    box_ref
                        .ref_count
                        .set(NonZeroUsize::new(n.get() - 1).unwrap());

                    if contains_gcs(&box_ref.value).unwrap_or(true) {
                        // remaining references could be a cycle - therefore, mark it as dirty
                        // so we can check later
                        d.mark_dirty(ptr);
                    }
                }
            }
            // Notify that a GC has been dropped, potentially triggering a cleanup
            d.notify_dropped_gc();
        });
    }
}

impl<T> PartialEq<Gc<T>> for Gc<T>
where
    T: Trace + ?Sized + PartialEq,
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
    /// # Examples
    ///
    /// ```
    /// use dumpster::unsync::Gc;
    ///
    /// let gc = Gc::new(6);
    /// assert!(gc == Gc::new(6));
    /// ```
    fn eq(&self, other: &Gc<T>) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T> Eq for Gc<T> where T: Trace + ?Sized + PartialEq {}

impl CollectInfo {
    #[must_use]
    /// Get the number of times that a [`Gc`] has been dropped since the last time a collection
    /// operation was performed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::unsync::{set_collect_condition, CollectInfo};
    ///
    /// // Collection condition for whether many Gc's have been dropped.
    /// fn have_many_gcs_dropped(info: &CollectInfo) -> bool {
    ///     info.n_gcs_dropped_since_last_collect() > 100
    /// }
    ///
    /// set_collect_condition(have_many_gcs_dropped);
    /// ```
    pub fn n_gcs_dropped_since_last_collect(&self) -> usize {
        DUMPSTER.with(|d| d.n_ref_drops.get())
    }

    #[must_use]
    /// Get the total number of [`Gc`]s which currently exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::unsync::{set_collect_condition, CollectInfo};
    ///
    /// // Collection condition for whether many Gc's currently exist.
    /// fn do_many_gcs_exist(info: &CollectInfo) -> bool {
    ///     info.n_gcs_existing() > 100
    /// }
    ///
    /// set_collect_condition(do_many_gcs_exist);
    /// ```
    pub fn n_gcs_existing(&self) -> usize {
        DUMPSTER.with(|d| d.n_refs_living.get())
    }
}

unsafe impl<T: Trace + ?Sized> Trace for Gc<T> {
    fn accept<V: Visitor>(&self, visitor: &mut V) -> Result<(), ()> {
        visitor.visit_unsync(self);
        Ok(())
    }
}

impl<T: Trace + ?Sized> AsRef<T> for Gc<T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: Trace + ?Sized> Borrow<T> for Gc<T> {
    fn borrow(&self) -> &T {
        self
    }
}

impl<T: Trace + Default> Default for Gc<T> {
    fn default() -> Self {
        Gc::new(T::default())
    }
}

impl<T: Trace + ?Sized> std::fmt::Pointer for Gc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Pointer::fmt(&addr_of!(**self), f)
    }
}

#[cfg(feature = "coerce-unsized")]
impl<T, U> std::ops::CoerceUnsized<Gc<U>> for Gc<T>
where
    T: std::marker::Unsize<U> + Trace + ?Sized,
    U: Trace + ?Sized,
{
}
