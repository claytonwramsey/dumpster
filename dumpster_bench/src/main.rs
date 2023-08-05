//! Benchmarks for the `dumpster` garbage collection library.

use std::{
    rc::Rc,
    sync::Arc,
    thread::spawn,
    time::{Duration, Instant},
};

use dumpster_bench::{
    ArcMultiref, BaconRajanMultiref, DumpsterSyncMultiref, DumpsterUnsyncMultiref, GcMultiref,
    Multiref, RcMultiref, ShredderMultiref, SyncMultiref,
};

struct BenchmarkData {
    n_threads: usize,
    n_ops: usize,
    duration: Duration,
}

fn main() {
    const N_ITERS: usize = 1_000_000;
    single_threaded::<dumpster::unsync::Gc<DumpsterUnsyncMultiref>>(
        "dumpster::unsync::Gc",
        N_ITERS,
    );
    single_threaded::<dumpster::sync::Gc<DumpsterSyncMultiref>>("dumpster::sync::Gc", N_ITERS);
    single_threaded::<Rc<RcMultiref>>("std::rc::Rc", N_ITERS);
    single_threaded::<Arc<ArcMultiref>>("std::sync::Arc", N_ITERS);
    single_threaded::<gc::Gc<GcMultiref>>("gc::Gc", N_ITERS);
    single_threaded::<bacon_rajan_cc::Cc<BaconRajanMultiref>>("bacon_rajan_cc::Cc", N_ITERS);
    single_threaded::<shredder::Gc<ShredderMultiref>>("shredder::Gc", N_ITERS);
    single_threaded::<shredder::Gc<ShredderMultiref>>("shredder::Gc (wrapping a mutex)", N_ITERS);
}

/// Run a benchmark of a multi-threaded garbage collector.
fn single_threaded<M: Multiref>(name: &str, n_iters: usize) -> BenchmarkData {
    fastrand::seed(12345);
    let mut gcs = Vec::new();

    // println!("{name}: running...");
    let tic = Instant::now();
    for _n in 0..n_iters {
        // println!("iter {_n}");
        if gcs.is_empty() {
            gcs.push(M::new(Vec::new()));
        } else {
            match fastrand::u8(0..5) {
                0 | 2 => {
                    // println!("create allocation");
                    // create new allocation
                    gcs.push(M::new(Vec::new()));
                }
                1 => {
                    // println!("add reference");
                    // add a reference
                    if gcs.len() > 1 {
                        let from = fastrand::usize(0..gcs.len());
                        let to = fastrand::usize(0..gcs.len());
                        let new_gc = gcs[to].clone();
                        gcs[from].apply(|v| v.push(new_gc));
                    }
                }
                3 => {
                    // println!("remove gc");
                    // destroy a reference owned by the vector
                    gcs.swap_remove(fastrand::usize(0..gcs.len()));
                }
                4 => {
                    // println!("remove reference");
                    // destroy a reference owned by some gc
                    let from = fastrand::usize(0..gcs.len());
                    gcs[from].apply(|v| {
                        if !v.is_empty() {
                            let to = fastrand::usize(0..v.len());
                            v.swap_remove(to);
                        }
                    })
                }
                _ => unreachable!(),
            }
        }
    }
    drop(gcs);
    M::collect();
    let toc = Instant::now();
    println!("finished {name} in {:?}", (toc - tic));
    BenchmarkData {
        n_threads: 1,
        n_ops: n_iters,
        duration: toc.duration_since(tic),
    }
}

fn multi_threaded<M: SyncMultiref>(name: &str, n_iters: usize, n_threads: usize) -> BenchmarkData {
    todo!()
}
