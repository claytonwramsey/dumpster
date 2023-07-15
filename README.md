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

## How it works

`dumpster` is unlike most tracing garbage collectors.
Other GCs keep track of a set of roots, which can then be used to perform a sweep and find out
which allocations are reachable and which are not.
Instead, `dumpster` extends reference-counted garbage collection (such as `std::rc::Rc`) with a
cycle-detection algorithm, enabling it to effectively clean up self-referential data structures.

## License

This code is licensed under the GNU GPLv3.
For more information, refer to [LICENSE.md](LICENSE.md).
