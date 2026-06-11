//! Criterion benchmarks for the fixed-width `modinverse` paths.
//!
//! This is the fitness function for optimizing the algorithm: the Lean proof
//! decides whether a change is *correct*, these benches decide whether it is
//! *faster*. The workload is deterministic (fixed-seed xorshift), so numbers are
//! comparable across runs and machines-of-one.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use modinverse::modinverse;

const PAIRS_PER_WIDTH: usize = 1024;

fn xorshift64(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

/// Deterministic (a, m) pairs; `m` is forced odd so it is never zero and is
/// coprime to `a` roughly half the time — both the found and not-found paths
/// get exercised.
fn pairs(n: usize) -> Vec<(u64, u64)> {
    let mut state = 0x9E37_79B9_7F4A_7C15;
    (0..n)
        .map(|_| {
            let a = xorshift64(&mut state);
            let m = xorshift64(&mut state) | 1;
            (a, m)
        })
        .collect()
}

macro_rules! bench_width {
    ($group:expr, $name:literal, $ty:ty) => {
        let inputs: Vec<($ty, $ty)> = pairs(PAIRS_PER_WIDTH)
            .into_iter()
            .map(|(a, m)| (a as $ty, (m as $ty) | 1))
            .collect();
        $group.bench_function($name, |b| {
            b.iter(|| {
                let mut found = 0_u32;
                for &(a, m) in &inputs {
                    if modinverse(black_box(a), black_box(m)).is_some() {
                        found += 1;
                    }
                }
                found
            })
        });
    };
}

fn bench_modinverse(c: &mut Criterion) {
    let mut group = c.benchmark_group("modinverse");
    bench_width!(group, "u8", u8);
    bench_width!(group, "u16", u16);
    bench_width!(group, "u32", u32);
    bench_width!(group, "u64", u64);
    bench_width!(group, "u128", u128);
    bench_width!(group, "i8", i8);
    bench_width!(group, "i16", i16);
    bench_width!(group, "i32", i32);
    bench_width!(group, "i64", i64);
    bench_width!(group, "i128", i128);
    bench_width!(group, "usize", usize);
    bench_width!(group, "isize", isize);
    group.finish();
}

criterion_group!(benches, bench_modinverse);
criterion_main!(benches);
