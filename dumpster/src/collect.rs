use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
    mem::{size_of, MaybeUninit, size_of_val},
    num::NonZeroUsize,
    ptr::{addr_of_mut, copy_nonoverlapping, NonNull, addr_of, drop_in_place}, alloc::{Layout, dealloc},
};

use crate::{Collectable, GcBox, RefGraph};

thread_local! {
    /// The global collection of allocation information for this thread.
    pub static DUMPSTER: Dumpster = Dumpster {
        to_collect: RefCell::new(HashMap::new()),
        n_ref_drops: Cell::new(0),
        n_refs_living: Cell::new(0),
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// A unique identifier for an allocated garbage-collected block.
///
/// It contains a pointer to the reference count of the allocation.
pub struct AllocationId(pub NonNull<Cell<usize>>);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// The set of states that we can know about an allocation's reachability.
pub enum AllocationInfo {
    /// The allocation has been proven reachable and is not safe to free.
    Reachable,
    /// The allocation's reachability is unknown.
    /// Field 0 of this case is the number of located references to this allocation.
    Unknown(NonZeroUsize),
}

/// A dumpster is a collection of all the garbage that may or may not need to be cleaned up.
/// It also contains information relevant to when a sweep should be triggered.
pub struct Dumpster {
    /// A map from allocation IDs for allocations which may need to be collected to pointers to
    /// their allocations.
    to_collect: RefCell<HashMap<AllocationId, Cleanup>>,
    /// The number of times a reference has been dropped since the last collection was triggered.
    pub n_ref_drops: Cell<usize>,
    /// The number of references that currently exist in the entire heap and stack.
    pub n_refs_living: Cell<usize>,
}

const MAX_PTR_SIZE: usize = 2 * size_of::<usize>() / size_of::<u8>();

#[repr(align(16))]
#[derive(Clone, Copy)]
/// A pointer for an allocation, extracted out as raw data.
/// This contains both the pointer and all the pointer's metadata, but hidden behind an unknown
/// interpretation.
/// We trust that all pointers (even to `?Sized` or `dyn` types) are 2 words or fewer in size.
/// This is a hack! Like, a big hack!
struct OpaquePtr([u8; MAX_PTR_SIZE]);

impl OpaquePtr {
    /// Construct a new opaque pointer to some data from its box reference.
    /// 
    /// # Panics
    /// 
    /// This function will panic if the size of a reference is larger than `MAX_PTR_SIZE`.
    fn new<T: Collectable + ?Sized>(box_ref: &GcBox<T>) -> OpaquePtr {
        let mut ptr = OpaquePtr([0; MAX_PTR_SIZE]);
        let ptr_size = size_of::<&GcBox<T>>();

        println!("store pointer size {ptr_size}, address {:?}", box_ref as *const GcBox<T>);
        // Extract out the pointer as raw memory
        assert!(
            ptr_size <= MAX_PTR_SIZE,
            "pointers to T are too big for storage"
        );
        unsafe {
            // SAFETY: We know that `cleanup` has at least as much space as `ptr_size`, and that
            // `box_ref` has size equal to `ptr_size`.
            println!("copy from {:?} to {:?}", addr_of!(box_ref).cast::<u8>(),addr_of_mut!(ptr.0));
            copy_nonoverlapping(
                addr_of!(box_ref).cast::<u8>(),
                addr_of_mut!(ptr.0).cast(),
                ptr_size,
            );
        }

        ptr
    }

    /// Specify this pointer into a pointer of a particular type.
    /// 
    /// # Safety
    /// 
    /// This function must only be specified to the type that the pointer was constructed with
    /// via [`OpaquePtr::new`].
    unsafe fn specify<T: Collectable + ?Sized>(self) -> NonNull<GcBox<T>> {
        let mut box_ref: MaybeUninit<NonNull<GcBox<T>>> = MaybeUninit::zeroed();
        copy_nonoverlapping(addr_of!(self.0), addr_of_mut!(box_ref).cast(), size_of_val(&box_ref));
        println!("specify pointer size {}, address {:?}", size_of_val(&box_ref), box_ref.assume_init());
        box_ref.assume_init()
    }
}

/// The necessary information required to collect some garbage-collected data.
/// This data is stored in a map from allocation IDs to the necessary cleanup operation.
struct Cleanup {
    graph_build_fn: unsafe fn(OpaquePtr, &mut RefGraph),
    sweep_fn: unsafe fn(OpaquePtr, &mut RefGraph),
    destroy_gcs_fn: unsafe fn(OpaquePtr, &mut RefGraph),
    ptr: OpaquePtr,
}

impl Cleanup {
    fn new<T: Collectable + ?Sized>(box_ref: &GcBox<T>) -> Cleanup {Cleanup {
            graph_build_fn: build_graph::<T>,
            sweep_fn: sweep::<T>,
            destroy_gcs_fn: destroy_gcs::<T>,
            ptr: OpaquePtr::new(box_ref),
        }
    }
}

/// Add `alloc` and all its children to a reference graph.
///
/// # Safety
///
/// `ptr` must point to an `OpaquePtr` constructed of type `T` which still exists.
unsafe fn build_graph<T: Collectable + ?Sized>(ptr: OpaquePtr, ref_graph: &mut RefGraph) {
    // it's safe to convert to a reference because the referent box still exists
    let box_ref: &GcBox<T> = ptr.specify().as_ref();
    let next_id = box_ref.id();
    if !ref_graph.mark_visited(next_id) {
        box_ref.value.add_to_ref_graph(ref_graph);
    }
}

/// Perform a sweep from `alloc`, marking any element of `graph` which is reachable from `alloc` as
/// reachable.
///
/// # Safety
///
/// `alloc` must point to a `GcBox` of type `T`.
/// `alloc` must be known to be reachable from outside of a garbage-collected allocation.
unsafe fn sweep<T: Collectable + ?Sized>(ptr: OpaquePtr, graph: &mut RefGraph) {
    let box_ref: &GcBox<T> = ptr.specify().as_ref();
    graph.mark_visited(box_ref.id());
    box_ref.value.sweep(false, graph);
}

/// Destroy all garbage-collected pointers owned by `alloc` and those values reachable exclusively
/// by `alloc`.
///
/// # Safety
///
/// `alloc` must point to a `GcBox` of type `T`.
/// `alloc` must be known to not be reachable from outside of a garbage-collected allocation.
unsafe fn destroy_gcs<T: Collectable + ?Sized>(ptr: OpaquePtr, graph: &mut RefGraph) {
    let box_ref: &GcBox<T> = ptr.specify().as_ref();
    let id = box_ref.id();
    if matches!(
        graph.allocations.get(&id),
        Some(AllocationInfo::Unknown(_)),
    ) && !graph.visited.contains(&id) {
        box_ref.ref_count.set(0);
        graph.mark_visited(id);
        let mut_ref: &mut GcBox<T> = ptr.specify().as_mut();
        mut_ref.value.destroy_gcs(graph);
        drop_in_place(mut_ref);
        dealloc((mut_ref as *mut GcBox<T>).cast(), Layout::for_value(mut_ref));
    }
}

impl Dumpster {
    /// Collect all unreachable allocations that this dumpster is responsible for.
    pub fn collect_all(&self) {
        self.n_ref_drops.set(0);

        let mut ref_graph = RefGraph {
            allocations: HashMap::new(),
            visited: HashSet::new(),
        };

        unsafe {

            println!("begin graph build");
            for a in self.to_collect.borrow().values() {
                (a.graph_build_fn)(a.ptr, &mut ref_graph);
            }
            println!("final ref graph: {:?}", ref_graph.allocations);
    
            println!("begin sweep");
            ref_graph.visited.clear();
            for a in self.to_collect.borrow().values() {
                (a.sweep_fn)(a.ptr, &mut ref_graph);
            }
            println!("sweep result: {:?}", ref_graph.allocations);

            ref_graph.visited.clear();
            for (_, a) in self.to_collect.borrow_mut().drain() {
                (a.destroy_gcs_fn)(a.ptr, &mut ref_graph);
            }
        }   

    }

    /// Mark an allocation as "dirty," implying that it may need to be swept through later to find
    /// out if it has any references pointing to it.
    pub(crate) fn mark_dirty<T: Collectable + ?Sized>(&self, box_ref: &GcBox<T>) {
        self.to_collect
            .borrow_mut()
            .entry(box_ref.id())
            .or_insert_with(|| Cleanup::new(box_ref));
    }

    /// Mark an allocation as "cleaned," implying that the allocation is about to be destroyed and
    /// therefore should not be cleaned up later.
    pub(crate) fn mark_cleaned<T: Collectable + ?Sized>(&self, box_ref: &GcBox<T>) {
        self.to_collect.borrow_mut().remove(&box_ref.id());
    }
}

impl Drop for Dumpster {
    fn drop(&mut self) {
        // cleanup any leftover allocations
        self.collect_all();
    }
}