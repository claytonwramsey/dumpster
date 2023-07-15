//! Benchmarks for the `dumpster` garbage collection library.

use std::{thread::spawn, time::Instant};

use dumpster_bench::{DumpsterSyncMultiref, DumpsterUnsyncMultiref, GcMultiref, Multiref};

fn main() {
    single_threaded::<dumpster::unsync::Gc<DumpsterUnsyncMultiref>>("dumpster::unsync");
    single_threaded::<dumpster::sync::Gc<DumpsterSyncMultiref>>("dumpster::sync");
    single_threaded::<gc::Gc<GcMultiref>>("gc");
}

/// Run a benchmark of a multi-threaded garbage collector.
fn single_threaded<M: Multiref>(name: &str) {
    fastrand::seed(12345);
    let mut gcs = Vec::new();

    // println!("{name}: running...");
    let tic = Instant::now();
    for _n in 0..1_000_000 {
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
                        let to = (from + fastrand::usize(1..gcs.len())) % gcs.len();
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
}

#[allow(dead_code)]
fn concurrent_scaling() {
    for nthreads in 1..16 {
        let handles = (0..nthreads)
            .map(|_| {
                spawn(|| {
                    todo!();
                })
            })
            .collect::<Vec<_>>();

        handles.into_iter().for_each(|x| {
            x.join().unwrap();
        });
    }
}
