// benchmarks/baselines/bench_rust.rs
// Reference Rust (-C opt-level=3 -C target-cpu=native) baseline for the lean-native
// Cross-Architecture Benchmark Suite (Wave 4b Differential C-ABI Parity).
//
// Implements all 8 benchmarks (6 core + 2 holdout) with exact deterministic 64-bit FNV-1a / scalar checksums
// and strict C-ABI (`extern "C"` raw pointers + lengths):
//   1. collatz_steps     (N = 5,000,000)   -> 740438133
//   2. tuple_accum_sum   (N = 50,000,000)  -> 2430072077297332099
//   3. sarray_scale_bias (N = 10,000,000)  -> 832419940395999471
//   4. dot_product_u64   (N = 10,000,000)  -> 9844157271583257408
//   5. saxpy_kernel      (N = 16,777,216)  -> 2559223112370776895
//   6. matmul_tiled_u64  (M = N = K = 512) -> 11211282456894907173
//   7. holdout_bitwise   (N = 10,000,000)  -> 17653976101919722312
//   8. holdout_loop_bounds (N = 10,000,000)-> 2318209942448586758

use std::env;
use std::hint::black_box;
use std::slice;
use std::time::Instant;

const FNV_OFFSET: u64 = 14695981039346656037;
const FNV_PRIME: u64 = 1099511628211;

#[inline(always)]
fn fnv1a_u64(h: u64, val: u64) -> u64 {
    (h ^ val).wrapping_mul(FNV_PRIME)
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_bench_collatz_steps(n: u64) -> u64 {
    let mut total_steps: u64 = 0;
    let mut i: u64 = 1;
    while i <= n {
        let mut x = i;
        let mut steps: u64 = 0;
        while x > 1 {
            if (x & 1) == 0 {
                x >>= 1;
            } else {
                x = x.wrapping_mul(3).wrapping_add(1);
            }
            steps = steps.wrapping_add(1);
        }
        total_steps = total_steps.wrapping_add(steps);
        i += 1;
    }
    total_steps
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_bench_tuple_accum_sum(n: u64) -> u64 {
    let mut a: u64 = 1;
    let mut b: u64 = 2;
    let mut i: u64 = 0;
    while i < n {
        let next_a = a.wrapping_add(i ^ b);
        let next_b = b.wrapping_add(i.wrapping_mul(3).wrapping_add(1));
        a = next_a;
        b = next_b;
        i += 1;
    }
    a ^ b
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn rust_bench_sarray_scale_bias(n: usize, arr_ptr: *mut u64) -> u64 {
    let arr = slice::from_raw_parts_mut(arr_ptr, n);
    for _pass in 0..2 {
        for v in arr.iter_mut() {
            *v = v.wrapping_mul(3).wrapping_add(7);
        }
    }
    let mut h = FNV_OFFSET;
    let mut i = 0;
    while i < n {
        h = fnv1a_u64(h, arr[i]);
        i += 64;
    }
    fnv1a_u64(h, arr[n - 1])
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn rust_bench_dot_product_u64(n: usize, a_ptr: *const u64, b_ptr: *const u64) -> u64 {
    let a = slice::from_raw_parts(a_ptr, n);
    let b = slice::from_raw_parts(b_ptr, n);
    let mut sum: u64 = 0;
    for (&va, &vb) in a.iter().zip(b.iter()) {
        sum = sum.wrapping_add(va.wrapping_mul(vb));
    }
    sum
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn rust_bench_saxpy_kernel(n: usize, alpha: u64, x_ptr: *const u64, y_ptr: *mut u64) -> u64 {
    let x = slice::from_raw_parts(x_ptr, n);
    let y = slice::from_raw_parts_mut(y_ptr, n);
    for (&vx, vy) in x.iter().zip(y.iter_mut()) {
        *vy = alpha.wrapping_mul(vx).wrapping_add(*vy);
    }
    let mut h = FNV_OFFSET;
    let mut i = 0;
    while i < n {
        h = fnv1a_u64(h, y[i]);
        i += 256;
    }
    fnv1a_u64(h, y[n - 1])
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn rust_bench_matmul_tiled_u64(
    m: usize,
    a_ptr: *const u64,
    b_ptr: *const u64,
    c_ptr: *mut u64,
) -> u64 {
    let total = m * m;
    let a = slice::from_raw_parts(a_ptr, total);
    let b = slice::from_raw_parts(b_ptr, total);
    let c = slice::from_raw_parts_mut(c_ptr, total);
    c.fill(0);
    const TILE: usize = 32;
    let mut i0 = 0;
    while i0 < m {
        let mut k0 = 0;
        while k0 < m {
            let mut j0 = 0;
            while j0 < m {
                for i in i0..(i0 + TILE).min(m) {
                    for k in k0..(k0 + TILE).min(m) {
                        let a_ik = a[i * m + k];
                        let c_row = &mut c[i * m + j0..(i * m + (j0 + TILE).min(m))];
                        let b_row = &b[k * m + j0..(k * m + (j0 + TILE).min(m))];
                        for (cv, &bv) in c_row.iter_mut().zip(b_row.iter()) {
                            *cv = cv.wrapping_add(a_ik.wrapping_mul(bv));
                        }
                    }
                }
                j0 += TILE;
            }
            k0 += TILE;
        }
        i0 += TILE;
    }
    let mut h = FNV_OFFSET;
    for &cv in c.iter() {
        h = fnv1a_u64(h, cv);
    }
    h
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_bench_evm_gas_schedule_u64(n: u64) -> u64 {
    let mut total_gas: u64 = 0;
    let mut i: u64 = 0;
    while i < n {
        let old_w = (i.wrapping_mul(2654435761).wrapping_add(11)) & 0x7FFF;
        let req_w = (i.wrapping_mul(2246822519).wrapping_add(29)) & 0xFFFF;
        let data_w = (i.wrapping_mul(3266489917).wrapping_add(7)) & 0xFF;
        let new_w = if req_w > old_w { req_w } else { old_w };
        let new_cost = 3u64.wrapping_mul(new_w).wrapping_add((new_w.wrapping_mul(new_w)) / 512);
        let old_cost = 3u64.wrapping_mul(old_w).wrapping_add((old_w.wrapping_mul(old_w)) / 512);
        let op_gas = (new_cost.wrapping_sub(old_cost))
            .wrapping_add(30)
            .wrapping_add(6u64.wrapping_mul(data_w));
        total_gas = total_gas.wrapping_add(op_gas);
        i += 1;
    }
    total_gas
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_bench_holdout_bitwise(n: u64) -> u64 {
    let mut acc: u64 = 0x123456789ABCDEF0;
    let mut i: u64 = 0;
    while i < n {
        let x = i.wrapping_add(acc);
        let v = (x << 3).wrapping_add(x).wrapping_add(x >> 2);
        acc ^= v.wrapping_add(i.wrapping_mul(17));
        i += 1;
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_bench_holdout_loop_bounds(n: u64) -> u64 {
    let mut sum1: u64 = 0;
    let mut sum2: u64 = 1;
    let mut i: u64 = 0;
    while i < n {
        sum1 = sum1.wrapping_add((i.wrapping_mul(5).wrapping_add(3)) ^ (sum2 & 0xFF));
        sum2 = (sum2.wrapping_mul(13).wrapping_add(i)) ^ (sum1 >> 3);
        i += 1;
    }
    sum1 ^ sum2
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let filter = if args.len() > 1 { args[1].as_str() } else { "all" };

    if filter == "all" || filter == "collatz_steps" {
        let t0 = Instant::now();
        let c = rust_bench_collatz_steps(black_box(5_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH collatz_steps checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "tuple_accum_sum" {
        let t0 = Instant::now();
        let c = rust_bench_tuple_accum_sum(black_box(50_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH tuple_accum_sum checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "sarray_scale_bias" {
        let n: usize = 10_000_000;
        let mut arr: Vec<u64> = (0..n)
            .map(|i| (i as u64).wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407))
            .collect();
        let t0 = Instant::now();
        let c = unsafe { rust_bench_sarray_scale_bias(black_box(n), black_box(arr.as_mut_ptr())) };
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH sarray_scale_bias checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "dot_product_u64" {
        let n: usize = 10_000_000;
        let a: Vec<u64> = (0..n)
            .map(|i| ((i as u64).wrapping_mul(11400714819323198485).wrapping_add(1)) & 0xFFFFFFFF)
            .collect();
        let b: Vec<u64> = (0..n)
            .map(|i| ((i as u64).wrapping_mul(14029467366897019727).wrapping_add(3)) & 0xFFFFFFFF)
            .collect();
        let t0 = Instant::now();
        let c = unsafe { rust_bench_dot_product_u64(black_box(n), black_box(a.as_ptr()), black_box(b.as_ptr())) };
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH dot_product_u64 checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "saxpy_kernel" {
        let n: usize = 16_777_216;
        let alpha: u64 = 314_159;
        let x: Vec<u64> = (0..n)
            .map(|i| (i as u64).wrapping_mul(2654435761).wrapping_add(7))
            .collect();
        let mut y: Vec<u64> = (0..n)
            .map(|i| (i as u64).wrapping_mul(2246822519).wrapping_add(13))
            .collect();
        let t0 = Instant::now();
        let c = unsafe {
            rust_bench_saxpy_kernel(
                black_box(n),
                black_box(alpha),
                black_box(x.as_ptr()),
                black_box(y.as_mut_ptr()),
            )
        };
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH saxpy_kernel checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "matmul_tiled_u64" {
        let m: usize = 512;
        let a: Vec<u64> = (0..m * m)
            .map(|i| ((i as u64).wrapping_mul(6364136223846793005).wrapping_add(1)) & 0xFFFF)
            .collect();
        let b: Vec<u64> = (0..m * m)
            .map(|i| ((i as u64).wrapping_mul(2862933555777941757).wrapping_add(3)) & 0xFFFF)
            .collect();
        let mut c: Vec<u64> = vec![0; m * m];
        let t0 = Instant::now();
        let chk = unsafe {
            rust_bench_matmul_tiled_u64(
                black_box(m),
                black_box(a.as_ptr()),
                black_box(b.as_ptr()),
                black_box(c.as_mut_ptr()),
            )
        };
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH matmul_tiled_u64 checksum={} time_ms={:.4}", chk, dt);
    }

    if filter == "all" || filter == "evm_gas_schedule_u64" {
        let t0 = Instant::now();
        let c = rust_bench_evm_gas_schedule_u64(black_box(10_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH evm_gas_schedule_u64 checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "holdout_bitwise" {
        let t0 = Instant::now();
        let c = rust_bench_holdout_bitwise(black_box(10_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH holdout_bitwise checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "holdout_loop_bounds" {
        let t0 = Instant::now();
        let c = rust_bench_holdout_loop_bounds(black_box(10_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH holdout_loop_bounds checksum={} time_ms={:.4}", c, dt);
    }
}
