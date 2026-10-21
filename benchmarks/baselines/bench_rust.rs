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
pub extern "C" fn rust_bench_keccak256_sponge_u64(n: u64) -> u64 {
    const RC: [u64; 8] = [
        0x0000000000000001, 0x0000000000008082,
        0x800000000000808a, 0x8000000080008000,
        0x000000000000808b, 0x0000000080000001,
        0x8000000080008081, 0x8000000000008009,
    ];
    let mut total: u64 = 0;
    let mut i: u64 = 0;
    while i < n {
        let mut s0 = i.wrapping_mul(6364136223846793005).wrapping_add(1);
        let mut s1 = i.wrapping_mul(2862933555777941757).wrapping_add(3);
        let mut s2 = i.wrapping_mul(11400714819323198485).wrapping_add(5);
        let mut s3 = i.wrapping_mul(14029467366897019727).wrapping_add(7);
        let mut s4 = i.wrapping_mul(3266489917).wrapping_add(11);
        for &rc in &RC {
            let d0 = s4 ^ s1.rotate_left(1);
            let d1 = s0 ^ s2.rotate_left(1);
            let d2 = s1 ^ s3.rotate_left(1);
            let d3 = s2 ^ s4.rotate_left(1);
            let d4 = s3 ^ s0.rotate_left(1);
            let b0 = s0 ^ d0;
            let b1 = (s1 ^ d1).rotate_left(44);
            let b2 = (s2 ^ d2).rotate_left(43);
            let b3 = (s3 ^ d3).rotate_left(21);
            let b4 = (s4 ^ d4).rotate_left(14);
            s0 = b0 ^ ((!b1) & b2) ^ rc;
            s1 = b1 ^ ((!b2) & b3);
            s2 = b2 ^ ((!b3) & b4);
            s3 = b3 ^ ((!b4) & b0);
            s4 = b4 ^ ((!b0) & b1);
        }
        let sum = s0.wrapping_add(s1).wrapping_add(s2).wrapping_add(s3).wrapping_add(s4);
        total ^= sum;
        i += 1;
    }
    total
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_bench_uint256_wad_muldiv_u64(n: u64) -> u64 {
    let mut total: u64 = 0;
    let mut i: u64 = 0;
    while i < n {
        let x0 = i.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let x1 = i.wrapping_mul(2862933555777941757).wrapping_add(3);
        let y0 = (i ^ 0x5555555555555555).wrapping_mul(11400714819323198485).wrapping_add(7);
        let y1 = i.wrapping_mul(3266489917).wrapping_add(11);
        let (s0, carry) = x0.overflowing_add(y0);
        let s1 = x1.wrapping_add(y1).wrapping_add(carry as u64);
        let p0 = (x0 as u128).wrapping_mul(y0 as u128);
        let p1 = (s0 as u128).wrapping_mul(1_000_000_000_000_000_000u128);
        let lo0 = p0 as u64;
        let hi0 = (p0 >> 64) as u64;
        let lo1 = p1 as u64;
        let hi1 = (p1 >> 64) as u64;
        let step_val = s0 ^ s1 ^ hi0 ^ hi1 ^ (lo0 >> 32) ^ (lo1 >> 32);
        total = total.wrapping_add(step_val);
        i += 1;
    }
    total
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_bench_goldilocks_ntt_modmul_u64(n: u64) -> u64 {
    const EPS: u64 = 0xFFFFFFFF;
    const M: u64 = 0xFFFFFFFF00000001;
    let mut total: u64 = 0;
    let mut i: u64 = 0;
    while i < n {
        let a = i.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let b = (i ^ 0xAAAAAAAAAAAAAAAA).wrapping_mul(11400714819323198485).wrapping_add(7);
        let p = (a as u128).wrapping_mul(b as u128);
        let lo = p as u64;
        let hi = (p >> 64) as u64;
        let x2 = hi & EPS;
        let x3 = hi >> 32;
        let (mut t0, borrow) = lo.overflowing_sub(x3);
        if borrow {
            t0 = t0.wrapping_sub(EPS);
        }
        let add2 = (x2 << 32).wrapping_sub(x2);
        let (mut t1, carry) = t0.overflowing_add(add2);
        if carry {
            t1 = t1.wrapping_add(EPS);
        }
        let r = if t1 >= M { t1.wrapping_sub(M) } else { t1 };
        total = total.wrapping_add(r ^ a.wrapping_add(b));
        i += 1;
    }
    total
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_bench_babybear_poseidon2_sbox_u64(n: u64) -> u64 {
    const P: u64 = 2013265921;
    let mut total: u64 = 0;
    let mut i: u64 = 0;
    while i < n {
        let x0 = (i.wrapping_mul(2654435761).wrapping_add(17)) & 0x3FFFFFFF;
        let x1 = (i.wrapping_mul(2246822519).wrapping_add(29)) & 0x3FFFFFFF;
        let x2 = (i.wrapping_mul(3266489917).wrapping_add(43)) & 0x3FFFFFFF;
        let x3 = (i.wrapping_mul(668265263).wrapping_add(59)) & 0x3FFFFFFF;
        let x0_2 = (x0 * x0) % P;
        let x0_3 = (x0_2 * x0) % P;
        let x0_4 = (x0_2 * x0_2) % P;
        let y0 = (x0_4 * x0_3) % P;
        let x1_2 = (x1 * x1) % P;
        let x1_3 = (x1_2 * x1) % P;
        let x1_4 = (x1_2 * x1_2) % P;
        let y1 = (x1_4 * x1_3) % P;
        let x2_2 = (x2 * x2) % P;
        let x2_3 = (x2_2 * x2) % P;
        let x2_4 = (x2_2 * x2_2) % P;
        let y2 = (x2_4 * x2_3) % P;
        let x3_2 = (x3 * x3) % P;
        let x3_3 = (x3_2 * x3) % P;
        let x3_4 = (x3_2 * x3_2) % P;
        let y3 = (x3_4 * x3_3) % P;
        let t = y0 + y1 + y2 + y3;
        let step_val = ((y0 + t) ^ ((y1 + t) << 16)).wrapping_add((y2 + t) ^ ((y3 + t) << 32));
        total = total.wrapping_add(step_val);
        i += 1;
    }
    total
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_bench_mersenne31_circle_butterfly_u64(n: u64) -> u64 {
    const P: u64 = 2147483647;
    const MASK: u64 = 0x3FFFFFFF;
    let mut total: u64 = 0;
    let mut i: u64 = 0;
    while i < n {
        let a = (i.wrapping_mul(2654435761).wrapping_add(17)) & MASK;
        let b = (i.wrapping_mul(2246822519).wrapping_add(29)) & MASK;
        let c = (i.wrapping_mul(3266489917).wrapping_add(43)) & MASK;
        let d = (i.wrapping_mul(668265263).wrapping_add(59)) & MASK;
        let w = (i.wrapping_mul(1664525).wrapping_add(1013904223)) & MASK;
        let tw_r = (c * w) % P;
        let tw_i = (d * ((w ^ 0x15555555) & MASK)) % P;
        let y0 = (a + tw_r) % P;
        let y1 = (a + P - tw_r) % P;
        let y2 = (b + tw_i) % P;
        let y3 = (b + P - tw_i) % P;
        let s = ((y0 * y2) % P) ^ ((y1 * y3) % P);
        let step_val = s.wrapping_add((y0 ^ (y1 << 16)).wrapping_add(y2 ^ (y3 << 32)));
        total = total.wrapping_add(step_val);
        i += 1;
    }
    total
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

    if filter == "all" || filter == "keccak256_sponge_u64" {
        let t0 = Instant::now();
        let c = rust_bench_keccak256_sponge_u64(black_box(2_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH keccak256_sponge_u64 checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "uint256_wad_muldiv_u64" {
        let t0 = Instant::now();
        let c = rust_bench_uint256_wad_muldiv_u64(black_box(5_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH uint256_wad_muldiv_u64 checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "goldilocks_ntt_modmul_u64" {
        let t0 = Instant::now();
        let c = rust_bench_goldilocks_ntt_modmul_u64(black_box(5_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH goldilocks_ntt_modmul_u64 checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "babybear_poseidon2_sbox_u64" {
        let t0 = Instant::now();
        let c = rust_bench_babybear_poseidon2_sbox_u64(black_box(5_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH babybear_poseidon2_sbox_u64 checksum={} time_ms={:.4}", c, dt);
    }

    if filter == "all" || filter == "mersenne31_circle_butterfly_u64" {
        let t0 = Instant::now();
        let c = rust_bench_mersenne31_circle_butterfly_u64(black_box(5_000_000));
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        println!("BENCH mersenne31_circle_butterfly_u64 checksum={} time_ms={:.4}", c, dt);
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
