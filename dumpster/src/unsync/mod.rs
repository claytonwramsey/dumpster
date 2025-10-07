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
    alloc::{dealloc, handle_alloc_error, Layout},
    any::TypeId,
    borrow::{Borrow, Cow},
    cell::Cell,
    mem::{self, ManuallyDrop, MaybeUninit},
    num::NonZeroUsize,
    ops::Deref,
    ptr::{self, addr_of, addr_of_mut, drop_in_place, NonNull},
    slice,
};

use crate::{contains_gcs, panic_deref_of_collected_object, ptr::Nullable, Trace, Visitor};

use self::collect::{Dumpster, DUMPSTER};

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
// This is only public to make the `unsync_coerce_gc` macro work.
#[doc(hidden)]
/// The underlying heap allocation for a [`Gc`].
pub struct GcBox<T: Trace + ?Sized> {
    /// The number of extant references to this garbage-collected data.
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

    /// Construct a self-referencing `Gc`.
    ///
    /// `new_cyclic` first allocates memory for `T`, then constructs a dead `Gc` pointing to the
    /// allocation. The dead `Gc` is then passed to `data_fn` to construct a value of `T`, which
    /// is stored in the allocation. Finally, `new_cyclic` will update the dead self-referential
    /// `Gc`s and rehydrate them to produce the final value.
    ///
    /// # Panics
    ///
    /// If `data_fn` panics, the panic is propagated to the caller.
    /// The allocation is cleaned up normally.
    ///
    /// Additionally, if, when attempting to rehydrate the `Gc` members of `F`, the visitor fails to
    /// reach a `Gc`, this function will panic and reserve the allocation to be cleaned up
    /// later.
    ///
    /// # Notes on safety
    ///
    /// Incorrect implementations of `data_fn` may have unusual or strange results.
    /// Although `dumpster` guarantees that it will be safe, and will do its best to ensure correct
    /// results, it is generally unwise to allow dead `Gc`s to exist for long.
    /// If you implement `data_fn` wrong, this may cause panics later on inside of the collection
    /// process.
    ///
    /// # Examples
    ///
    /// ```
    /// use dumpster::{unsync::Gc, Trace};
    ///
    /// #[derive(Trace)]
    /// struct Cycle {
    ///     this: Gc<Self>,
    /// }
    ///
    /// let gc = Gc::new_cyclic(|this| Cycle { this });
    /// assert!(Gc::ptr_eq(&gc, &gc.this));
    /// ```
    pub fn new_cyclic<F: FnOnce(Gc<T>) -> T>(data_fn: F) -> Self
    where
        T: Sized,
    {
        /// A struct containing an uninitialized value of `T`.
        /// May only be used inside `new_cyclic`.
        #[repr(transparent)]
        struct Uninitialized<T>(MaybeUninit<T>);

        unsafe impl<T> Trace for Uninitialized<T> {
            fn accept<V: Visitor>(&self, _: &mut V) -> Result<(), ()> {
                Ok(())
            }
        }

        /// A struct for converting dead `Gc`s into live ones.
        struct Rehydrate<U: Trace + 'static>(Nullable<GcBox<U>>);

        impl<U: Trace + 'static> Visitor for Rehydrate<U> {
            fn visit_sync<T>(&mut self, _: &crate::sync::Gc<T>)
            where
                T: Trace + Send + Sync + ?Sized,
            {
            }

            fn visit_unsync<T>(&mut self, gc: &Gc<T>)
            where
                T: Trace + ?Sized,
            {
                if TypeId::of::<T>() == TypeId::of::<U>() && gc.is_dead() {
                    unsafe {
                        // SAFETY: it is safe to transmute these pointers because we have checked
                        // that they are of the same type.
                        // Additionally, the `GcBox` has been fully initialized, so it is safe to
                        // create a reference here.
                        let cell_ptr = (&raw const gc.ptr).cast::<Cell<Nullable<GcBox<U>>>>();
                        (*cell_ptr).set(self.0);

                        let box_ref = &*self.0.as_ptr();
                        box_ref
                            .ref_count
                            .set(box_ref.ref_count.get().saturating_add(1));
                        DUMPSTER.with(Dumpster::notify_created_gc);
                    }
                }
            }
        }

        /// Data structure for cleaning up the allocation in case we panic along the way.
        struct CleanUp<T: Trace + 'static> {
            /// Is `true` if the [`GcBox::value`] is initialized.
            initialized: bool,
            /// Pointer to the `GcBox` with a maybe uninitialized value.
            ptr: NonNull<GcBox<T>>,
        }

        impl<T: Trace + 'static> Drop for CleanUp<T> {
            fn drop(&mut self) {
                if self.initialized {
                    // push this `Gc` into the destruction queue
                    DUMPSTER.with(|d| d.mark_dirty(self.ptr));
                } else {
                    // deallocate
                    unsafe {
                        dealloc(
                            self.ptr.as_ptr().cast::<u8>(),
                            Layout::for_value(self.ptr.as_ref()),
                        );
                    }
                }
            }
        }

        // make an uninitialized allocation
        DUMPSTER.with(Dumpster::notify_created_gc);
        let mut gcbox = NonNull::from(Box::leak(Box::new(GcBox {
            ref_count: Cell::new(NonZeroUsize::MIN),
            value: Uninitialized(MaybeUninit::<T>::uninit()),
        })));
        let mut cleanup = CleanUp {
            ptr: gcbox,
            initialized: false,
        };

        // nilgc is a dead Gc
        let nilgc = Gc {
            ptr: Cell::new(Nullable::new(gcbox.cast::<GcBox<T>>()).as_null()),
        };
        assert!(nilgc.is_dead());
        unsafe {
            // SAFETY: `gcbox` is a valid pointer to an uninitialized datum that we have allocated.
            gcbox.as_mut().value = Uninitialized(MaybeUninit::new(data_fn(nilgc)));
        }
        cleanup.initialized = true;

        let gcbox = gcbox.cast::<GcBox<T>>();
        let res = unsafe {
            // SAFETY: the above unsafe block correctly constructed the Uninitialized value, so it
            // is safe to cast `gcbox` and then construct a reference.
            gcbox
                .as_ref()
                .value
                .accept(&mut Rehydrate(Nullable::new(gcbox)))
        };

        assert!(
            res.is_ok(),
            "visitor must be able to access all Gc fields of structure when rehydrating dead Gcs"
        );
        let gc = Gc {
            ptr: Cell::new(Nullable::new(gcbox)),
        };

        let _ = ManuallyDrop::new(cleanup);
        gc
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
    /// use dumpster::unsync::Gc;
    ///
    /// let gc = Gc::new(());
    /// assert_eq!(gc.ref_count().get(), 1);
    /// let gc2 = gc.clone();
    /// assert_eq!(gc.ref_count().get(), 2);
    /// drop(gc);
    /// drop(gc2);
    /// ```
    pub fn ref_count(&self) -> NonZeroUsize {
        let box_ptr = self.ptr.get().expect(
            "Attempt to dereference Gc to already-collected object. \
    This means a Gc escaped from a Drop implementation, likely implying a bug in your code.",
        );
        let box_ref = unsafe { box_ptr.as_ref() };
        box_ref.ref_count.get()
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
    /// use dumpster::{unsync::Gc, Trace};
    /// use std::cell::OnceCell;
    ///
    /// #[derive(Trace)]
    /// struct Cycle(OnceCell<Gc<Self>>);
    ///
    /// impl Drop for Cycle {
    ///     fn drop(&mut self) {
    ///         assert!(self.0.get().unwrap().is_dead());
    ///     }
    /// }
    ///
    /// let gc1 = Gc::new(Cycle(OnceCell::new()));
    /// gc1.0.set(gc1.clone());
    /// # drop(gc1);
    /// # dumpster::unsync::collect();
    /// ```
    pub fn is_dead(&self) -> bool {
        self.ptr.get().is_null()
    }

    /// Consumes the `Gc<T>`, returning the inner `GcBox<T>` pointer.
    #[inline]
    #[must_use]
    fn into_ptr(this: Self) -> *const GcBox<T> {
        let this = ManuallyDrop::new(this);
        this.ptr.get().as_ptr()
    }

    /// Constructs a `Gc<T>` from the innner `GcBox<T>` pointer.
    #[inline]
    #[must_use]
    unsafe fn from_ptr(ptr: *const GcBox<T>) -> Self {
        Self {
            ptr: Cell::new(Nullable::from_ptr(ptr.cast_mut())),
        }
    }

    /// Exists solely for the [`coerce_gc`] macro.
    #[inline]
    #[must_use]
    #[doc(hidden)]
    pub fn __private_into_ptr(this: Self) -> *const GcBox<T> {
        Self::into_ptr(this)
    }

    /// Exists solely for the [`coerce_gc`] macro.
    #[inline]
    #[must_use]
    #[doc(hidden)]
    pub unsafe fn __private_from_ptr(ptr: *const GcBox<T>) -> Self {
        Self::from_ptr(ptr)
    }

    /// Kill this `Gc`, replacing it with a dead `Gc`.
    fn kill(&self) {
        self.ptr.set(self.ptr.get().as_null());
    }
}

impl<T: Trace + Clone> Gc<T> {
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
        let ptr = unsafe { this.ptr.get().unwrap_unchecked() };
        let box_ref = unsafe { ptr.as_ref() };

        if box_ref.ref_count.get() == NonZeroUsize::MIN {
            // The dumpster must not contain this allocation while we hold
            // a mutable reference to its value because on collection
            // it would dereference the value to trace it.
            DUMPSTER.with(|d| d.mark_cleaned(ptr));
        } else {
            // We don't have unique access to the value so we need to clone it.
            *this = Gc::new(box_ref.value.clone());
        }

        // SAFETY: we have exclusive access to this `GcBox` because we ensured
        // that the ref count is 1 and that there are no loose pointers in the
        // `to_collect` buffer of this thread's dumpster.
        unsafe { &mut (*this.ptr.get_mut().as_ptr()).value }
    }
}

impl<T: Trace + ?Sized> Gc<T> {
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
            (&raw mut (*inner).ref_count).write(Cell::new(NonZeroUsize::MIN));
        }

        inner
    }
}

impl<T: Trace> Gc<[T]> {
    /// Allocates an `GcBox<[T]>` with the given length.
    #[inline]
    fn allocate_for_slice(len: usize) -> *mut GcBox<[T]> {
        unsafe {
            Self::allocate_for_layout(Layout::array::<T>(len).unwrap(), |mem| {
                ptr::slice_from_raw_parts_mut(mem.cast::<T>(), len) as *mut GcBox<[T]>
            })
        }
    }
}

/// Allows coercing `T` of [`unsync::Gc<T>`](Gc).
///
/// This means that you can convert a `Gc` containing a strictly-sized type (such as `[T; N]`) into
/// a `Gc` containing its unsized version (such as `[T]`), all without using nightly-only features.
///
/// # Examples
///
/// ```
/// use dumpster::unsync::{coerce_gc, Gc};
///
/// let gc1: Gc<[u8; 3]> = Gc::new([7, 8, 9]);
/// let gc2: Gc<[u8]> = coerce_gc!(gc1);
/// assert_eq!(&gc2[..], &[7, 8, 9]);
/// ```
///
/// Note that although this macro allows for type conversion, it _cannot_ be used for converting
/// between incompatible types.
///
/// ```compile_fail
/// // This program is incorrect!
/// use dumpster::unsync::{Gc, coerce_gc};
///
/// let gc1: Gc<u8> = Gc::new(1);
/// let gc2: Gc<i8> = coerce_gc!(gc1);
/// ```
#[doc(hidden)]
#[macro_export]
macro_rules! __unsync_coerce_gc {
    ($gc:expr) => {{
        // Temporarily convert the `Gc` into a raw pointer to allow for coercion to occur.
        let ptr: *const _ = $crate::unsync::Gc::__private_into_ptr($gc);
        unsafe { $crate::unsync::Gc::__private_from_ptr(ptr) }
    }};
}

#[doc(inline)]
pub use crate::__unsync_coerce_gc as coerce_gc;

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
        unsafe {
            &self.ptr.get().expect("dereferencing Gc to already-collected object. \
            This means a Gc escaped from a Drop implementation, likely implying a bug in your code.").as_ref().value
        }
    }
}

impl<T: Trace + ?Sized> Clone for Gc<T> {
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

impl<T: Trace> From<T> for Gc<T> {
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

impl<T: Trace, const N: usize> From<[T; N]> for Gc<[T]> {
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
        coerce_gc!(Gc::<[T; N]>::from(v))
    }
}

impl<T: Trace + Clone> From<&[T]> for Gc<[T]> {
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

            DUMPSTER.with(Dumpster::notify_created_gc);

            Self {
                ptr: Cell::new(Nullable::from_ptr(ptr)),
            }
        }
    }
}

impl<T: Trace + Clone> From<&mut [T]> for Gc<[T]> {
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
        unsafe { Gc::from_ptr(Gc::into_ptr(bytes) as *const GcBox<str>) }
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
        unsafe { Gc::from_ptr(Gc::into_ptr(value) as *const GcBox<[u8]>) }
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

impl<T: Trace> From<Box<T>> for Gc<T> {
    /// Move a boxed object to a new, garbage collected, allocation.
    ///
    /// # Example
    ///
    /// ```
    /// # use dumpster::unsync::Gc;
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

            DUMPSTER.with(Dumpster::notify_created_gc);
            Self::from_ptr(gc_ptr)
        }
    }
}

impl<T: Trace> From<Vec<T>> for Gc<[T]> {
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

            DUMPSTER.with(Dumpster::notify_created_gc);
            Self::from_ptr(gc_ptr)
        }
    }
}

impl<'a, B: Trace> From<Cow<'a, B>> for Gc<B>
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
