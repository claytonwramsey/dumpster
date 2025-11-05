/*
    dumpster, a cycle-tracking garbage collector for Rust.    Copyright (C) 2023 Clayton Ramsey.

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

//! A cycle-tracking concurrent garbage collector with an easy-to-use API.
//!
//! Most garbage collectors are _tracing_ garbage collectors, meaning that they keep track of a set
//! of roots which are directly accessible from the stack, and then use those roots to find the set
//! of all accessible allocations.
//! However, because Rust does not allow us to hook into when a value is moved, it's quite difficult
//! to detect when a garbage-collected value stops being a root.
//!
//! `dumpster` takes a different approach.
//! It begins by using simple reference counting, then automatically detects cycles.
//! Allocations are freed when their reference count reaches zero or when they are only accessible
//! via their descendants.
//!
//! Garbage-collected pointers can be created and destroyed in _O(1)_ amortized time, but destroying
//! a garbage-collected pointer may take _O(r)_, where _r_ is the number of existing
//! garbage-collected references, on occasion.
//! However, the cleanups that require _O(r)_ performance are performed once every _O(1/r)_ times
//! a reference is dropped, yielding an amortized _O(1)_ runtime.
//!
//! # Why should you use this crate?
//!
//! In short, `dumpster` offers a great mix of usability, performance, and flexibility.
//!
//! - `dumpster`'s API is a drop-in replacement for `std`'s reference-counted shared allocations
//!   (`Rc` and `Arc`).
//! - It's very performant and has builtin implementations of both thread-local and concurrent
//!   garbage collection.
//! - There are no restrictions on the reference structure within a garbage-collected allocation
//!   (references may point in any way you like).
//! - It's trivial to make a custom type Trace using the provided derive macros.
//! - You can even store `?Sized` data in a garbage-collected pointer!
//!
//! # Module structure
//!
//! `dumpster` contains 3 core modules: the root (this module), as well as [`sync`] and [`unsync`].
//! `sync` contains an implementation of thread-safe garbage-collected pointers, while `unsync`
//! contains an implementation of thread-local garbage-collected pointers which cannot be shared
//! across threads.
//! Thread-safety requires some synchronization overhead, so for a single-threaded application,
//! it is recommended to use `unsync`.
//!
//! The project root contains common definitions across both `sync` and `unsync`.
//! Types which implement [`Trace`] can immediately be used in `unsync`, but in order to use
//! `sync`'s garbage collector, the types must also implement [`Sync`].
//!
//! # Examples
//!
//! If your code is meant to run as a single thread, or if your data doesn't need to be shared
//! across threads, you should use [`unsync::Gc`] to store your allocations.
//!
//! ```
//! use dumpster::unsync::Gc;
//! use std::cell::Cell;
//!
//! let my_gc = Gc::new(Cell::new(0451));
//!
//! let other_gc = my_gc.clone(); // shallow copy
//! other_gc.set(512);
//!
//! assert_eq!(my_gc.get(), 512);
//! ```
//!
//! For data which is shared across threads, you can use [`sync::Gc`] with the exact same API.
//!
//! ```
//! use dumpster::sync::Gc;
//! use std::sync::Mutex;
//!
//! let my_shared_gc = Gc::new(Mutex::new(25));
//! let other_shared_gc = my_shared_gc.clone();
//!
//! std::thread::scope(|s| {
//!     s.spawn(move || {
//!         *other_shared_gc.lock().unwrap() = 35;
//!     });
//! });
//!
//! println!("{}", *my_shared_gc.lock().unwrap());
//! ```
//!
//! It's trivial to use custom data structures with the provided derive macro.
//!
//! ```
//! use dumpster::{unsync::Gc, Trace};
//! use std::cell::RefCell;
//!
//! #[derive(Trace)]
//! struct Foo {
//!     refs: RefCell<Vec<Gc<Foo>>>,
//! }
//!
//! let foo = Gc::new(Foo {
//!     refs: RefCell::new(Vec::new()),
//! });
//!
//! foo.refs.borrow_mut().push(foo.clone());
//!
//! drop(foo);
//!
//! // even though foo had a self reference, it still got collected!
//! ```
//!
//! # Installation
//!
//! To use `dumpster`, add the following lines to your `Cargo.toml`.
//!
//! ```toml
//! [dependencies]
//! dumpster = "1.2.0"
//! ```
//!
//! # Optional features
//!
//! ## `derive`
//!
//! `derive` is enabled by default.
//! It enables the derive macro for `Trace`, which makes it easy for users to implement their
//! own Trace types.
//!
//! ```
//! use dumpster::{unsync::Gc, Trace};
//! use std::cell::RefCell;
//!
//! #[derive(Trace)] // no manual implementation required
//! struct Foo(RefCell<Option<Gc<Foo>>>);
//!
//! let my_foo = Gc::new(Foo(RefCell::new(None)));
//! *my_foo.0.borrow_mut() = Some(my_foo.clone());
//!
//! drop(my_foo); // my_foo will be automatically cleaned up
//! ```
//!
//! ## `either`
//!
//! `either` is disabled by default. It adds support for the [`either`](https://crates.io/crates/either) crate,
//! specifically by implementing [`Trace`] for [`either::Either`](https://docs.rs/either/1.13.0/either/enum.Either.html).
//!
//! ## `coerce-unsized`
//!
//! `coerce-unsized` is disabled by default.
//! This enables the implementation of [`std::ops::CoerceUnsized`] for each garbage collector,
//! making it possible to use `Gc` with `!Sized` types conveniently.
#![cfg_attr(
    feature = "coerce-unsized",
    doc = r#"
```
// this only works with "coerce-unsized" enabled while compiling on nightly Rust
use dumpster::unsync::Gc;

let gc1: Gc<[u8]> = Gc::new([1, 2, 3]);
```
"#
)]
//! To use `coerce-unsized`, edit your installation to `Cargo.toml` to include the feature.
//!
//! ```toml
//! [dependencies]
//! dumpster = { version = "1.1.0", features = ["coerce-unsized"]}
//! ```
//!
//! ## Loom support
//!
//! `dumpster` has experimental support for permutation testing under [`loom`](https://github.com/tokio-rs/loom).
//! It is expected to be unstable and buggy.
//! To compile `dumpster` using `loom`, add `--cfg loom` to `RUSTFLAGS` when compiling, for example:
//!
//! ```sh
//! RUSTFLAGS='--cfg loom' cargo test
//! ```
//!
//! # License
//!
//! `dumpster` is licensed under the Mozilla Public License, version 2.0.
//! For more details, refer to
//! [LICENSE.md](https://github.com/claytonwramsey/dumpster/blob/master/LICENSE.md).
//!
//! This project includes portions of code derived from the Rust standard library,
//! which is dual-licensed under the MIT and Apache 2.0 licenses.
//! Copyright (c) The Rust Project Developers.

#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]
#![warn(clippy::allow_attributes, reason = "prefer expect over allow")]
#![allow(clippy::multiple_crate_versions, clippy::result_unit_err)]
#![cfg_attr(feature = "coerce-unsized", feature(coerce_unsized))]
#![cfg_attr(feature = "coerce-unsized", feature(unsize))]

mod impls;

mod option;
mod ptr;
pub mod sync;
pub mod unsync;

/// Contains the sealed trait for [`Trace`].
mod trace {
    use crate::{sync::TraceSync, unsync::TraceUnsync, ContainsGcs, TraceWith};

    /// The sealed trait for [`Trace`](crate::Trace),
    /// hiding away the implementation details and making it
    /// impossible to manually implement `Trace`.
    #[expect(clippy::missing_safety_doc)]
    #[expect(private_bounds)]
    pub unsafe trait TraceWithV: TraceWith<ContainsGcs> + TraceSync + TraceUnsync {}

    unsafe impl<T> TraceWithV for T where T: ?Sized + TraceWith<ContainsGcs> + TraceSync + TraceUnsync {}
}

/// The trait that any garbage-collected data must implement.
///
/// This trait should usually be implemented by using `#[derive(Trace)]`, using the provided
/// macro.
/// Only data structures using raw pointers or other magic should manually implement `Trace`.
///
/// To manually implement `Trace` you need to implement [`TraceWith<V>`].
/// Any type that implements `TraceWith` for all <code>V: [Visitor]</code>
/// automatically implements `Trace`.
///
/// # Examples
///
/// Implementing `Trace` for a scalar type which contains no garbage-collected references
/// is very easy.
/// Accepting a visitor is simply a no-op.
///
/// ```
/// use dumpster::{TraceWith, Visitor};
///
/// struct Foo(u8);
///
/// unsafe impl<V: Visitor> TraceWith<V> for Foo {
///     fn accept(&self, visitor: &mut V) -> Result<(), ()> {
///         Ok(())
///     }
/// }
/// ```
///
/// However, if a data structure contains a garbage collected pointer, it must delegate to its
/// fields in `accept`.
///
/// ```
/// use dumpster::{unsync::Gc, TraceWith, Visitor};
///
/// struct Bar(Gc<Bar>);
///
/// unsafe impl<V: Visitor> TraceWith<V> for Bar {
///     fn accept(&self, visitor: &mut V) -> Result<(), ()> {
///         self.0.accept(visitor)
///     }
/// }
/// ```
///
/// A data structure with two or more fields which could own a garbage-collected pointer should
/// delegate to both fields in a consistent order:
///
/// ```
/// use dumpster::{unsync::Gc, TraceWith, Visitor};
///
/// struct Baz {
///     a: Gc<Baz>,
///     b: Gc<Baz>,
/// }
///
/// unsafe impl<V: Visitor> TraceWith<V> for Baz {
///     fn accept(&self, visitor: &mut V) -> Result<(), ()> {
///         self.a.accept(visitor)?;
///         self.b.accept(visitor)?;
///         Ok(())
///     }
/// }
/// ```
///
/// `Trace` is dyn-compatible, so you can use it as a subtrait
/// to allocate your own trait object.
///
/// ```
/// use dumpster::{
///     unsync::{coerce_gc, Gc},
///     Trace,
/// };
///
/// trait MyTrait: Trace {}
/// impl<T: Trace> MyTrait for T {}
///
/// let gc: Gc<i32> = Gc::new(5);
/// let gc: Gc<dyn MyTrait> = coerce_gc!(gc);
/// ```
pub trait Trace: trace::TraceWithV {}

impl<T> Trace for T where T: trace::TraceWithV + ?Sized {}

/// The underlying tracing implementation powering the [`Trace`] trait.
///
/// # Safety
///
/// If the implementation of this trait is incorrect, this will result in undefined behavior,
/// typically double-frees or use-after-frees.
/// This includes [`TraceWith::accept`], even though it is a safe function, since its correctness
/// is required for safety.
///
/// The garbage collector in `dumpster` requires strong assumptions about the values inside of a
/// `Gc`; by implementing `TraceWith`, you are responsible for these assumptions.
/// Specifically, in order to be `TraceWith`, a value must have a _tree-like_ ownership structure.
/// If some type `T` implements `TraceWith`, it means that no references to a value inside `T` will
/// remain valid while `T` is moved. For instance, this means that `Rc` can never be `Trace`, as
/// moving one `Rc` will not invalidate other `Rc`s pointing to the same allocation.
/// We allow exceptions for fields of `T` that are not visited by the implementation of
/// [`TraceWith::accept`], such as borrows (see the implementation of `TraceWith` for `&T`) and
/// naturally for [`unsync::Gc`] and [`sync::Gc`].
///
/// Any structure whose implementation of `TraceWith` comes from `#[derive(Trace)]` satisfies the
/// tree-like requirement.
pub unsafe trait TraceWith<V: Visitor> {
    /// Accept a visitor to this garbage-collected value.
    ///
    /// Implementors of this function need only delegate to all fields owned by this value which
    /// may contain a garbage-collected reference (either a [`sync::Gc`] or a [`unsync::Gc`]).
    /// This delegation must be done in a consistent order.
    ///
    /// For structures which have more than one field, they should return immediately after the
    /// first `Err` is returned from one of its fields.
    /// To do so efficiently, we recommend using the try operator (`?`) on each field and then
    /// returning `Ok(())` after delegating to each field.
    ///
    /// # Errors
    ///
    /// Errors are returned from this function whenever a field of this object returns an error
    /// after delegating acceptance to it, or if this value's data is inaccessible (such as
    /// attempting to borrow from a [`RefCell`](std::cell::RefCell) which has already been
    /// mutably borrowed).
    fn accept(&self, visitor: &mut V) -> Result<(), ()>;
}

/// A visitor for a garbage collected value.
///
/// This visitor allows us to hide details of the implementation of the garbage-collection procedure
/// from implementors of [`Trace`].
///
/// When accepted by a `Trace`, this visitor will be delegated down until it reaches a
/// garbage-collected pointer.
/// Then, the garbage-collected pointer will call one of `visit_sync` or `visit_unsync`, depending
/// on which type of pointer it is.
///
/// In general, it's not expected for consumers of this library to write their own visitors.
pub trait Visitor {
    /// Visit a synchronized garbage-collected pointer.
    ///
    /// This function is called for every [`sync::Gc`] owned by the value that accepted this
    /// visitor.
    fn visit_sync<T>(&mut self, gc: &sync::Gc<T>)
    where
        T: Trace + Send + Sync + ?Sized;

    /// Visit a thread-local garbage-collected pointer.
    ///
    /// This function is called for every [`unsync::Gc`] owned by the value that accepted this
    /// visitor.
    fn visit_unsync<T>(&mut self, gc: &unsync::Gc<T>)
    where
        T: Trace + ?Sized;
}

// Re-export #[derive(Trace)].
//
// The reason re-exporting is not enabled by default is that disabling it would
// be annoying for crates that provide handwritten impls or data formats. They
// would need to disable default features and then explicitly re-enable std.
#[cfg(feature = "derive")]
extern crate dumpster_derive;

#[cfg(feature = "derive")]
/// The derive macro for implementing `Trace`.
///
/// This enables users of `dumpster` to easily store custom types inside a `Gc`.
/// To do so, simply annotate your type with `#[derive(Trace)]`.
///
/// # Examples
///
/// ```
/// use dumpster::Trace;
///
/// #[derive(Trace)]
/// struct Foo {
///     bar: Option<Box<Foo>>,
/// }
/// ```
///
/// You can specify the crate path for the `dumpster` crate using the `dumpster` attribute:
///
/// ```
/// use dumpster as dumpster_renamed;
/// use dumpster_renamed::Trace;
///
/// #[derive(Trace)]
/// #[dumpster(crate = dumpster_renamed)]
/// struct Foo {
///     bar: Option<Box<Foo>>,
/// }
/// ```
pub use dumpster_derive::Trace;

/// Determine whether some value contains a garbage-collected pointer.
///
/// This function will return one of three values:
/// - `Ok(true)`: The data structure contains a garbage-collected pointer.
/// - `Ok(false)`: The data structure contains no garbage-collected pointers.
/// - `Err(())`: The data structure was accessed while we checked it for garbage-collected pointers.
fn contains_gcs<T: Trace + ?Sized>(x: &T) -> Result<bool, ()> {
    let mut visit = ContainsGcs(false);
    x.accept(&mut visit)?;
    Ok(visit.0)
}

/// A visitor structure used for determining whether some garbage-collected pointer contains a
/// `Gc` in its pointed-to value.
struct ContainsGcs(bool);

impl Visitor for ContainsGcs {
    fn visit_sync<T>(&mut self, _: &sync::Gc<T>)
    where
        T: Trace + Send + Sync + ?Sized,
    {
        self.0 = true;
    }

    fn visit_unsync<T>(&mut self, _: &unsync::Gc<T>)
    where
        T: Trace + ?Sized,
    {
        self.0 = true;
    }
}

/// Panics with a message that explains that the gc object has already been collected.
#[cold]
#[inline(never)]
fn panic_deref_of_collected_object() -> ! {
    panic!(
        "Attempt to dereference Gc to already-collected object. \
    This means a Gc escaped from a Drop implementation, likely implying a bug in your code.",
    );
}
