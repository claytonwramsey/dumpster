# `dumpster` Changelog

## 2.0.0

### Breaking changes

- Refactored `Trace` to use `TraceWith<V>`.

### New features

- Added `sync::Gc::new_cyclic`.

## 1.2.0

### New features

- Added experimental support for testing under `loom`.
- Added `unsync::Gc::new_cyclic`.
- Implemented `Default` for `Gc`.
- Added `Gc::make_mut`.
- Added `From` implementations for `Gc`.
- Supported differing `BuildHasher` types in `Trace` implementation for `HashSet`.
- Added `sync::coerce_gc` and `unsync::coerce_gc`.
- Added `Trace` implementation to more types in the Rust standard library.

### Bug fixes

- Fixed broken references in documentation.
- Added overflow testing for `Gc` reference counts.
- `Gc`s created in a garbage-collected value's `Drop` implementation are no longer leaked.

## 1.1.1

### Bug fixes

- Using `dumpster` no longer fails under Miri as we have changed our underlying pointer model.

## 1.1.0

### New features

- Added support for [`either`](https://crates.io/crates/either).

### Bug fixes

- Derive implementations no longer erroneously refer to `heapsize`.

### Other changes

- Slight performance and code style improvements.
- Improved internal documentation on safety.
- Remove `strict-provenance` requirement as it is now stabilized.

## 1.0.0

### Breaking changes

- Rename `Collectable` to `Trace`.

## 0.2.1

### New features

- Implement `Collectable` for `std::any::TypeId`.

## 0.2.0

### New features

- Added `Gc::as_ptr`.
- Added `Gc::ptr_eq`.
- Implemented `PartialEq` and `Eq` for garbage collected pointers.

### Other

- Changed license from GNU GPLv3 or later to MPL 2.0.
- Allocations which do not contain `Gc`s will simply be reference counted.

## 0.1.2

### New features

- Implement `Collectable` for `OnceCell`, `HashMap`, and `BTreeMap`.
- Add `try_clone` and `try_deref` to `unsync::Gc` and `sync::Gc`.
- Make dereferencing `Gc` only panic on truly-dead `Gc`s.

### Bugfixes

- Prevent dead `Gc`s from escaping their `Drop` implementation, potentially causing UAFs.
- Use fully-qualified name for `Result` in derive macro, preventing some bugs.

### Other

- Improve performance in `unsync` by using `parking_lot` for concurrency primitives.
- Improve documentation of panicking behavior in `Gc`.
- Fix spelling mistakes in documentation.

## 0.1.1

### Bugfixes

- Prevent possible UAFs caused by accessing `Gc`s during `Drop` impls by panicking.

### Other

- Fix spelling mistakes in documentation.

## 0.1.0

Initial release.
