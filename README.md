# `dumpster`: A cycle-tracking garbage collector for Rust

`dumpster` is an experimental garbage-collector for Rust.
It detects unreachable allocations and automatically frees them.

## Why should you use this library?

You should use this library if:

- You want to be able to trivially use your pre-existing data structures without manually 
  implementing traits.
- You cannot remove cyclic references from your data structures.
- You're only moderately picky about performance.
- You don't mind a little instability.
- You need to work with `?Sized` data.

## How it works

`dumpster` is unlike most tracing garbage collectors.
Other GCs keep track of a set of roots, which can then be used to perform a sweep and find out
which allocations are reachable and which are not.
Instead, `dumpster` extends reference-counted garbage collection (such as `std::rc::Rc`) with a
cycle-detection algorithm, enabling it to effectively clean up self-referential data structures.

## What this library contains

`dumpster` actually contains two garbage collector implementations: one thread-local, non-`Send` 
garbarge collector in the module `unsync`, and one thread-safe garbage collector in the module
`sync`.
These garbage collectors can be safely mixed and matched.

Additionally, we provide a second crate, `dumpster_derive`, which implements derive macros for 
the `Collectable` trait mandated for all data that is used in a garbage-collected allocation.

## Examples

```rust
use dumpster::unsync::Gc;
use dumpster_derive::Collectable;

#[derive(Collectable)]
struct Foo {
    ptr: RefCell<Option<Gc<Foo>>>,
}

// Create a new garbage-collected Foo.
let foo = Foo {
   ptr: RefCell::new(None),
}

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

`dumpster` has not been published to [crates.io](https://crates.io) yet. 
Check back later for installation instructions.

## License

This code is licensed under the GNU GPLv3.
For more information, refer to [LICENSE.md](LICENSE.md).
