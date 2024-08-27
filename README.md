# `dumpster`: A cycle-tracking garbage collector for Rust

`dumpster` is an cycle-detecting garbage collector for Rust.
It detects unreachable allocations and automatically frees them.

## Why should you use this crate?

In short, `dumpster` offers a great mix of usability, performance, and flexibility.

-   `dumpster`'s API is a drop-in replacement for `std`'s reference-counted shared allocations
    (`Rc` and `Arc`).
-   It's very performant and has builtin implementations of both thread-local and concurrent
    garbage collection.
-   There are no restrictions on the reference structure within a garbage-collected allocation
    (references may point in any way you like).
-   It's trivial to make a custom type Trace using the provided derive macros.
-   You can even store `?Sized` data in a garbage-collected pointer!

## How it works

`dumpster` is unlike most tracing garbage collectors.
Other GCs keep track of a set of roots, which can then be used to perform a sweep and find out
which allocations are reachable and which are not.
Instead, `dumpster` extends reference-counted garbage collection (such as `std::rc::Rc`) with a
cycle-detection algorithm, enabling it to effectively clean up self-referential data structures.

For a deeper dive, check out this
[blog post](https://claytonwramsey.github.io/2023/08/14/dumpster.html).

## What this library contains

`dumpster` actually contains two garbage collector implementations: one thread-local, non-`Send`
garbage collector in the module `unsync`, and one thread-safe garbage collector in the module
`sync`.
These garbage collectors can be safely mixed and matched.

This library also comes with a derive macro for creating custom Trace types.

## Examples

```rust
use dumpster::{Trace, unsync::Gc};

#[derive(Trace)]
struct Foo {
    ptr: RefCell<Option<Gc<Foo>>>,
}

// Create a new garbage-collected Foo.
let foo = Gc::new(Foo {
    ptr: RefCell::new(None),
});

// Insert a circular reference inside of the foo.
*foo.ptr.borrow_mut() = Some(foo.clone());

// Render the foo inaccessible.
// This may trigger a collection, but it's not guaranteed.
// If we had used `Rc` instead of `Gc`, this would have caused a memory leak.
drop(foo);

// Trigger a collection.
// This isn't necessary, but it guarantees that `foo` will be collected immediately (instead of
// later).
dumpster::unsync::collect();
```

## Installation

To install, simply add `dumpster` as a dependency to your project.

```toml
[dependencies]
dumpster = "1.0.0"
```

## Optional features

`dumpster` has two optional features: `derive` and `coerce-unsized`.

`derive` is enabled by default.
It enables the derive macro for `Trace`, which makes it easy for users to implement their
own Trace types.

```rust
use dumpster::{unsync::Gc, Trace};
use std::cell::RefCell;

#[derive(Trace)] // no manual implementation required
struct Foo(RefCell<Option<Gc<Foo>>>);

let my_foo = Gc::new(Foo(RefCell::new(None)));
*my_foo.0.borrow_mut() = Some(my_foo.clone());

drop(my_foo); // my_foo will be automatically cleaned up
```

`coerce-unsized` is disabled by default.
This enables the implementation of `CoerceUnsized` for each garbage collector,
making it possible to use `Gc` with `!Sized` types conveniently.

```rust
use dumpster::unsync::Gc;

// this only works with "coerce-unsized" enabled while compiling on nightly Rust
let gc1: Gc<[u8]> = Gc::new([1, 2, 3]);
```

To use `coerce-unsized`, edit your installation to `Cargo.toml` to include the feature.

```toml
[dependencies]
dumpster = { version = "1.0.0", features = ["coerce-unsized"]}
```

## License

This code is licensed under the Mozilla Public License, version 2.0.
For more information, refer to [LICENSE.md](LICENSE.md).
