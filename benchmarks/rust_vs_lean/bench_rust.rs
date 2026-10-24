// Deterministic 25-algorithm benchmark corpus for Rust (`rustc -C opt-level=3 -C target-cpu=native`)
// vs Lean 4 Official vs Lean-Native (`lean-native`).
// Every benchmark uses exact deterministic 64-bit arithmetic and prints:
// BENCH:<name>:<elapsed_ns>:<checksum_u64>

use std::env;
use std::hint::black_box;
use std::time::Instant;

// 1. collatz_steps (Control-Flow / Recursion)
#[inline(never)]
pub fn bench_collatz_steps(limit: u64) -> u64 {
    let mut total: u64 = 0;
    let mut i: u64 = 1;
    while i <= limit {
        let mut n = black_box(i);
        let mut steps: u64 = 0;
        while n > 1 {
            let is_odd = n & 1;
            let next_even = n >> 1;
            let next_odd = n.wrapping_mul(3).wrapping_add(1);
            n = if is_odd != 0 { next_odd } else { next_even };
            steps = steps.wrapping_add(1);
        }
        total = total.wrapping_add(steps);
        i += 1;
    }
    total
}

// 2. tuple_accum_sum (Allocation / Perceus / SROA)
#[inline(never)]
pub fn bench_tuple_accum_sum(iters: u64) -> u64 {
    let mut a: u64 = 1;
    let mut b: u64 = 2;
    let mut i: u64 = 0;
    while i < iters {
        let idx = black_box(i);
        let na = a.wrapping_add(b).wrapping_add(idx & 7);
        let nb = (b ^ (na >> 3)).wrapping_add(idx);
        let pair = black_box((na, nb));
        a = pair.0;
        b = pair.1;
        i += 1;
    }
    a.wrapping_add(b)
}

// 3. sarray_scale_bias (Linear / COW / SIMD)
#[inline(never)]
pub fn bench_sarray_scale_bias(n: usize, rounds: u64) -> u64 {
    let mut buf: Vec<u64> = (0..n).map(|i| (i as u64).wrapping_mul(13).wrapping_add(5)).collect();
    for r in 0..rounds {
        let scale: u64 = 3u64.wrapping_add(r & 1);
        let bias: u64 = 7u64.wrapping_add(r);
        for x in buf.iter_mut() {
            *x = x.wrapping_mul(scale).wrapping_add(bias);
        }
        black_box(buf.as_mut_ptr());
    }
    let mut sum: u64 = 0;
    for &x in &buf {
        sum = sum.wrapping_add(x);
    }
    sum
}

// 4. dot_product_u64 (Vector / Tensor / Reduction)
#[inline(never)]
pub fn bench_dot_product_u64(n: usize, rounds: u64) -> u64 {
    let a: Vec<u64> = (0..n).map(|i| ((i * 17 + 3) & 0xFFFF) as u64).collect();
    let b: Vec<u64> = (0..n).map(|i| ((i * 31 + 11) & 0xFFFF) as u64).collect();
    let mut total: u64 = 0;
    for r in 0..rounds {
        let mut acc: u64 = 0;
        for i in 0..n {
            acc = acc.wrapping_add(a[i].wrapping_mul(b[i]));
        }
        total = total.wrapping_add(black_box(acc).wrapping_add(r));
    }
    total
}

// 5. saxpy_kernel (Vector / Tensor / Bandwidth)
#[inline(never)]
pub fn bench_saxpy_kernel(n: usize, rounds: u64) -> u64 {
    let x: Vec<u64> = (0..n).map(|i| ((i * 7 + 1) & 0xFFFF) as u64).collect();
    let mut y: Vec<u64> = (0..n).map(|i| ((i * 19 + 9) & 0xFFFF) as u64).collect();
    let mut out: Vec<u64> = vec![0u64; n];
    for r in 0..rounds {
        let alpha: u64 = 5u64.wrapping_add(r & 3);
        for i in 0..n {
            out[i] = alpha.wrapping_mul(x[i]).wrapping_add(y[i]);
        }
        std::mem::swap(&mut y, &mut out);
        black_box(y.as_mut_ptr());
    }
    let mut sum: u64 = 0;
    for &v in &y {
        sum = sum.wrapping_add(v);
    }
    sum
}

// 6. matmul_tiled_u64 (Dense Linear Algebra)
#[inline(never)]
pub fn bench_matmul_tiled_u64(dim: usize) -> u64 {
    let total = dim * dim;
    let a: Vec<u64> = (0..total).map(|i| ((i * 13 + 7) & 0xFF) as u64).collect();
    let b: Vec<u64> = (0..total).map(|i| ((i * 29 + 3) & 0xFF) as u64).collect();
    let mut c: Vec<u64> = vec![0u64; total];
    for i in 0..dim {
        for k in 0..dim {
            let aik = a[i * dim + k];
            let row_c = i * dim;
            let row_b = k * dim;
            for j in 0..dim {
                c[row_c + j] = c[row_c + j].wrapping_add(aik.wrapping_mul(b[row_b + j]));
            }
        }
    }
    let mut checksum: u64 = 0;
    for &v in &c {
        checksum = checksum.wrapping_add(v);
    }
    checksum
}

// 7. binary_trees (Inductive Tree Allocation & Traversal / Perceus Reuse)
enum Tree {
    Leaf(u64),
    Node(Box<Tree>, Box<Tree>, u64),
}

fn make_tree(depth: u32, seed: u64) -> Box<Tree> {
    if depth == 0 {
        Box::new(Tree::Leaf(seed))
    } else {
        let l = make_tree(depth - 1, seed.wrapping_mul(3).wrapping_add(1));
        let r = make_tree(depth - 1, seed.wrapping_mul(3).wrapping_add(2));
        Box::new(Tree::Node(l, r, seed))
    }
}

fn check_tree(t: &Tree) -> u64 {
    match t {
        Tree::Leaf(v) => *v,
        Tree::Node(l, r, v) => check_tree(l).wrapping_add(check_tree(r)) ^ (*v),
    }
}

#[inline(never)]
pub fn bench_binary_trees(depth: u32, iters: u64) -> u64 {
    let mut acc: u64 = 0;
    for i in 0..iters {
        let t = make_tree(black_box(depth), black_box(i + 1));
        acc = acc.wrapping_add(check_tree(&t));
    }
    acc
}

// 8. nbody (Fixed-Point Symplectic N-Body Simulation)
#[inline(never)]
pub fn bench_nbody(steps: u64) -> u64 {
    let mut px: [u64; 5] = [1000, 2500, 4200, 6100, 8300];
    let mut py: [u64; 5] = [1500, 3100, 1900, 5400, 7200];
    let mut pz: [u64; 5] = [2000, 1200, 3800, 4900, 6500];
    let mut vx: [u64; 5] = [10, 20, 15, 25, 30];
    let mut vy: [u64; 5] = [12, 18, 22, 14, 28];
    let mut vz: [u64; 5] = [8, 24, 16, 19, 11];
    let mass: [u64; 5] = [100, 40, 60, 80, 50];

    for _ in 0..steps {
        for i in 0..5 {
            for j in (i + 1)..5 {
                let dx = px[i].wrapping_sub(px[j]);
                let dy = py[i].wrapping_sub(py[j]);
                let dz = pz[i].wrapping_sub(pz[j]);
                let dist2 = (dx.wrapping_mul(dx).wrapping_add(dy.wrapping_mul(dy)).wrapping_add(dz.wrapping_mul(dz)) & 0xFFFF) + 1;
                let mag = 65536u64 / dist2;
                let fx = dx.wrapping_mul(mag);
                let fy = dy.wrapping_mul(mag);
                let fz = dz.wrapping_mul(mag);
                vx[i] = vx[i].wrapping_sub(fx.wrapping_mul(mass[j]) >> 8);
                vy[i] = vy[i].wrapping_sub(fy.wrapping_mul(mass[j]) >> 8);
                vz[i] = vz[i].wrapping_sub(fz.wrapping_mul(mass[j]) >> 8);
                vx[j] = vx[j].wrapping_add(fx.wrapping_mul(mass[i]) >> 8);
                vy[j] = vy[j].wrapping_add(fy.wrapping_mul(mass[i]) >> 8);
                vz[j] = vz[j].wrapping_add(fz.wrapping_mul(mass[i]) >> 8);
            }
        }
        for i in 0..5 {
            px[i] = px[i].wrapping_add(vx[i]);
            py[i] = py[i].wrapping_add(vy[i]);
            pz[i] = pz[i].wrapping_add(vz[i]);
        }
        black_box(&mut px);
    }
    let mut energy: u64 = 0;
    for i in 0..5 {
        energy = energy.wrapping_add(
            px[i] ^ py[i].rotate_left(13) ^ pz[i].rotate_left(27) ^ vx[i] ^ vy[i] ^ vz[i]
        );
    }
    energy
}

// 9. spectral_norm (Power-Iteration Matrix-Vector Operator A^T A)
#[inline(never)]
pub fn bench_spectral_norm(n: usize, sweeps: u64) -> u64 {
    let mut u = vec![1024u64; n];
    let mut v = vec![0u64; n];
    let mut tmp = vec![0u64; n];
    for _ in 0..sweeps {
        for i in 0..n {
            let mut sum: u64 = 0;
            for j in 0..n {
                let ij = (i + j) as u64;
                let denom = (ij * (ij + 1) / 2 + (i as u64) + 1) & 0xFF;
                sum = sum.wrapping_add(u[j].wrapping_mul(denom + 1));
            }
            tmp[i] = sum >> 8;
        }
        for i in 0..n {
            let mut sum: u64 = 0;
            for j in 0..n {
                let ij = (i + j) as u64;
                let denom = (ij * (ij + 1) / 2 + (j as u64) + 1) & 0xFF;
                sum = sum.wrapping_add(tmp[j].wrapping_mul(denom + 1));
            }
            v[i] = sum >> 8;
        }
        for i in 0..n {
            u[i] = v[i] & 0xFFFF_FFFF;
        }
        black_box(u.as_mut_ptr());
    }
    let mut acc: u64 = 0;
    for i in 0..n {
        acc = acc.wrapping_add(u[i].wrapping_mul(v[i]));
    }
    acc
}

// 10. fannkuch_redux (Combinatorial Permutation Flipping)
#[inline(never)]
pub fn bench_fannkuch_redux(iters: u64) -> u64 {
    let mut checksum: u64 = 0;
    for seed in 0..iters {
        let mut p: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let mut s = black_box(seed).wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
        for i in (1..8).rev() {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let j = ((s >> 32) as usize) % (i + 1);
            p.swap(i, j);
        }
        let mut flips: u64 = 0;
        let mut guard: u32 = 0;
        while p[0] != 0 && guard < 32 {
            let k = p[0] as usize;
            let mut lo = 0usize;
            let mut hi = k;
            while lo < hi {
                p.swap(lo, hi);
                lo += 1;
                hi -= 1;
            }
            flips += 1;
            guard += 1;
        }
        checksum = checksum.wrapping_add(flips.wrapping_mul((seed & 15) + 1));
    }
    checksum
}

// 11. mandelbrot_simd (Fixed-Point Q16.16 Mandelbrot Escape Kernel)
#[inline(never)]
pub fn bench_mandelbrot_simd(width: u64, height: u64, max_iter: u64) -> u64 {
    let mut total_iters: u64 = 0;
    let w = black_box(width);
    let h = black_box(height);
    let mi = black_box(max_iter);
    for py in 0..h {
        let ci: i64 = ((py as i64) * 131072) / (h as i64) - 65536;
        for px in 0..w {
            let cr: i64 = ((px as i64) * 196608) / (w as i64) - 131072;
            let mut zr: i64 = 0;
            let mut zi: i64 = 0;
            let mut it: u64 = 0;
            while it < mi {
                let zr2 = (zr * zr) >> 16;
                let zi2 = (zi * zi) >> 16;
                if zr2 + zi2 > 262144 {
                    break;
                }
                zi = ((2 * zr * zi) >> 16) + ci;
                zr = zr2 - zi2 + cr;
                it += 1;
            }
            total_iters = total_iters.wrapping_add(it);
        }
    }
    total_iters
}

// 12. robin_hood_htab (Linear-Probing Hash Table Lookup/Insert)
#[inline(never)]
pub fn bench_robin_hood_htab(num_ops: u64) -> u64 {
    let cap: usize = 4096;
    let mask: usize = cap - 1;
    let mut keys = vec![u64::MAX; cap];
    let mut vals = vec![0u64; cap];
    for i in 0..num_ops {
        let k = black_box(i).wrapping_mul(0x9E3779B97F4A7C15) & 0x7FF;
        let v = i.wrapping_mul(31).wrapping_add(17);
        let mut slot = ((k.wrapping_mul(0xBF58476D1CE4E5B9) >> 32) as usize) & mask;
        loop {
            if keys[slot] == u64::MAX || keys[slot] == k {
                keys[slot] = k;
                vals[slot] = vals[slot].wrapping_add(v);
                break;
            }
            slot = (slot + 1) & mask;
        }
    }
    let mut sum: u64 = 0;
    for i in 0..num_ops {
        let k = black_box(i).wrapping_mul(0x9E3779B97F4A7C15) & 0x7FF;
        let mut slot = ((k.wrapping_mul(0xBF58476D1CE4E5B9) >> 32) as usize) & mask;
        loop {
            if keys[slot] == k {
                sum = sum.wrapping_add(vals[slot]);
                break;
            }
            if keys[slot] == u64::MAX {
                break;
            }
            slot = (slot + 1) & mask;
        }
    }
    sum
}

// 13. sha256_compress (Bitwise Rotate / Ch / Maj / Sigma Compression Round Loop)
#[inline(never)]
pub fn bench_sha256_compress(blocks: u64) -> u64 {
    let mut s0: u64 = 0x6a09e667bb67ae85;
    let mut s1: u64 = 0x3c6ef372a54ff53a;
    let mut s2: u64 = 0x510e527f9b05688c;
    let mut s3: u64 = 0x1f83d9ab5be0cd19;
    for b in 0..blocks {
        let mut w = black_box(b).wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0x428a2f98d728ae22);
        for r in 0..64u64 {
            let e0 = s0.rotate_right(2) ^ s0.rotate_right(13) ^ s0.rotate_right(22);
            let maj = (s0 & s1) ^ (s0 & s2) ^ (s1 & s2);
            let e1 = s3.rotate_right(6) ^ s3.rotate_right(11) ^ s3.rotate_right(25);
            let ch = (s3 & s1) ^ ((!s3) & s2);
            let temp1 = s3.wrapping_add(e1).wrapping_add(ch).wrapping_add(w).wrapping_add(r);
            let temp2 = e0.wrapping_add(maj);
            s3 = s2;
            s2 = s1;
            s1 = s0;
            s0 = temp1.wrapping_add(temp2);
            w = w.rotate_left(7).wrapping_add(0x7137449123ef65cd);
        }
    }
    s0 ^ s1 ^ s2 ^ s3
}

// 14. keccak_f1600 (5-Lane Sponge Theta/Rho/Chi/Iota Bitwise Permutation)
#[inline(never)]
pub fn bench_keccak_f1600(perms: u64) -> u64 {
    let mut a0: u64 = 0x123456789ABCDEF0;
    let mut a1: u64 = 0x0FEDCBA987654321;
    let mut a2: u64 = 0xCAFEBABEDEADBEEF;
    let mut a3: u64 = 0x0123456789ABCDEF;
    let mut a4: u64 = 0xF0E1D2C3B4A59687;
    for p in 0..perms {
        a0 ^= black_box(p);
        for r in 0..24u64 {
            let c = a0 ^ a1 ^ a2 ^ a3 ^ a4;
            let d = c.rotate_left(1) ^ c.rotate_right(1);
            a0 = (a0 ^ d).rotate_left(1);
            a1 = (a1 ^ d).rotate_left(3);
            a2 = (a2 ^ d).rotate_left(6);
            a3 = (a3 ^ d).rotate_left(10);
            a4 = (a4 ^ d).rotate_left(15);
            let t0 = a0 ^ ((!a1) & a2);
            let t1 = a1 ^ ((!a2) & a3);
            let t2 = a2 ^ ((!a3) & a4);
            let t3 = a3 ^ ((!a4) & a0);
            let t4 = a4 ^ ((!a0) & a1);
            a0 = t0 ^ (r.wrapping_mul(0x0000000080008081));
            a1 = t1;
            a2 = t2;
            a3 = t3;
            a4 = t4;
        }
    }
    a0 ^ a1 ^ a2 ^ a3 ^ a4
}

// 15. mul_div_512 (256x256->512 Multi-Limb Arithmetic & Carry Chains)
#[inline(never)]
pub fn bench_mul_div_512(iters: u64) -> u64 {
    let mut acc0: u64 = 0x1122334455667788;
    let mut acc1: u64 = 0x99AABBCCDDEEFF00;
    let mut acc2: u64 = 0x0102030405060708;
    let mut acc3: u64 = 0xF1E2D3C4B5A69788;
    for i in 1..=iters {
        let x = black_box(i).wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
        let y = i.wrapping_mul(0xBF58476D1CE4E5B9) | 1;
        let full0 = (acc0 as u128) * (x as u128);
        let lo0 = full0 as u64;
        let hi0 = (full0 >> 64) as u64;
        let full1 = (acc1 as u128) * (x as u128) + (hi0 as u128);
        let lo1 = full1 as u64;
        let hi1 = (full1 >> 64) as u64;
        let full2 = (acc2 as u128) * (x as u128) + (hi1 as u128);
        let lo2 = full2 as u64;
        let hi2 = (full2 >> 64) as u64;
        let full3 = (acc3 as u128) * (x as u128) + (hi2 as u128);
        let lo3 = full3 as u64;
        let d = (y & 0xFFFF_FFFF) + 3;
        acc0 = (lo0 / d).wrapping_add(lo1);
        acc1 = (lo1 / d).wrapping_add(lo2);
        acc2 = (lo2 / d).wrapping_add(lo3);
        acc3 = (lo3 / d) ^ lo0;
    }
    acc0 ^ acc1 ^ acc2 ^ acc3
}

// 16. radix_sort_u64 (8-bit LSD Radix Sort Passes over u64 Keys)
#[inline(never)]
pub fn bench_radix_sort_u64(n: usize, rounds: u64) -> u64 {
    let mut src: Vec<u64> = vec![0u64; n];
    let mut dst: Vec<u64> = vec![0u64; n];
    let mut checksum: u64 = 0;
    for r in 0..rounds {
        for i in 0..n {
            src[i] = ((i as u64).wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(r)) & 0xFFFF_FFFF;
        }
        for shift in [0u32, 8, 16, 24] {
            let mut count = [0usize; 256];
            for &v in &src {
                let bucket = ((v >> shift) & 0xFF) as usize;
                count[bucket] += 1;
            }
            let mut pref = [0usize; 256];
            let mut running = 0usize;
            for b in 0..256 {
                pref[b] = running;
                running += count[b];
            }
            for &v in &src {
                let bucket = ((v >> shift) & 0xFF) as usize;
                let pos = pref[bucket];
                dst[pos] = v;
                pref[bucket] = pos + 1;
            }
            std::mem::swap(&mut src, &mut dst);
        }
        checksum = checksum.wrapping_add(src[0] ^ src[n / 2] ^ src[n - 1]);
    }
    checksum
}

// 17. dijkstra_pairing_heap (Shortest-Path Relaxation over Dense CSR Graph)
#[inline(never)]
pub fn bench_dijkstra_pairing_heap(num_nodes: usize, rounds: u64) -> u64 {
    let mut dist = vec![u64::MAX; num_nodes];
    let mut visited = vec![0u8; num_nodes];
    let mut total: u64 = 0;
    for r in 0..rounds {
        for i in 0..num_nodes {
            dist[i] = 1_000_000_000;
            visited[i] = 0;
        }
        dist[0] = 0;
        for _ in 0..num_nodes {
            let mut u = 0usize;
            let mut best = u64::MAX;
            for v in 0..num_nodes {
                if visited[v] == 0 && dist[v] < best {
                    best = dist[v];
                    u = v;
                }
            }
            visited[u] = 1;
            let du = dist[u];
            for deg in 1..=8usize {
                let target = (u * 7 + deg * 13 + (r as usize)) & (num_nodes - 1);
                let weight = (((u ^ target) + deg * 5) & 63) as u64 + 1;
                let cand = du + weight;
                if cand < dist[target] {
                    dist[target] = cand;
                }
            }
        }
        total = total.wrapping_add(dist[num_nodes - 1] ^ dist[num_nodes / 2]);
    }
    total
}

// 18. regex_dfa_step (Deterministic Automaton State Transition Scanner)
#[inline(never)]
pub fn bench_regex_dfa_step(len: u64, rounds: u64) -> u64 {
    let mut trans = [0u8; 64 * 16];
    for s in 0..64usize {
        for c in 0..16usize {
            trans[s * 16 + c] = (((s * 5 + c * 3 + 1) ^ (s >> 2)) & 63) as u8;
        }
    }
    let mut matches: u64 = 0;
    for r in 0..rounds {
        let mut state: usize = 0;
        let mut z = black_box(r).wrapping_add(0x123456789ABCDEF0);
        for _ in 0..len {
            z = z.wrapping_mul(6364136223846793005).wrapping_add(1);
            let sym = ((z >> 56) & 15) as usize;
            state = trans[state * 16 + sym] as usize;
            matches = matches.wrapping_add((state == 63) as u64);
        }
        matches = matches.wrapping_add(state as u64);
    }
    matches
}

// 19. json_simd_scanner (Structural Quote/Escape/Brace Bitmask Scanner)
#[inline(never)]
pub fn bench_json_simd_scanner(words: u64, rounds: u64) -> u64 {
    let mut struct_count: u64 = 0;
    for r in 0..rounds {
        let mut quote_parity: u64 = 0;
        let mut x = black_box(r).wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0x227B7D3A2C5B5D22);
        for _ in 0..words {
            x = x.rotate_left(13).wrapping_mul(0xBF58476D1CE4E5B9).wrapping_add(0x22007B007D003A2C);
            let eq_quote = (x ^ 0x2222222222222222).wrapping_sub(0x0101010101010101) & !(x ^ 0x2222222222222222) & 0x8080808080808080;
            let eq_lbrace = (x ^ 0x7B7B7B7B7B7B7B7B).wrapping_sub(0x0101010101010101) & !(x ^ 0x7B7B7B7B7B7B7B7B) & 0x8080808080808080;
            let eq_rbrace = (x ^ 0x7D7D7D7D7D7D7D7D).wrapping_sub(0x0101010101010101) & !(x ^ 0x7D7D7D7D7D7D7D7D) & 0x8080808080808080;
            quote_parity ^= (eq_quote.count_ones() as u64) & 1;
            let active = (eq_lbrace | eq_rbrace) & (quote_parity.wrapping_sub(1));
            struct_count = struct_count.wrapping_add(active.count_ones() as u64);
        }
    }
    struct_count
}

// 20. sparse_matmul_csr (Compressed Sparse Row SpMV Kernel)
#[inline(never)]
pub fn bench_sparse_matmul_csr(rows: usize, nnz_per_row: usize, rounds: u64) -> u64 {
    let total_nnz = rows * nnz_per_row;
    let mut col_idx = vec![0usize; total_nnz];
    let mut vals = vec![0u64; total_nnz];
    let mut x = vec![0u64; rows];
    let mut y = vec![0u64; rows];
    for i in 0..rows {
        x[i] = ((i * 11 + 3) & 0xFF) as u64;
        for k in 0..nnz_per_row {
            let idx = i * nnz_per_row + k;
            col_idx[idx] = (i * 7 + k * 31 + 5) & (rows - 1);
            vals[idx] = ((idx * 17 + 1) & 0xFF) as u64;
        }
    }
    let mut checksum: u64 = 0;
    for r in 0..rounds {
        for i in 0..rows {
            let mut sum: u64 = 0;
            let base = i * nnz_per_row;
            for k in 0..nnz_per_row {
                let c = col_idx[base + k];
                sum = sum.wrapping_add(vals[base + k].wrapping_mul(x[c]));
            }
            y[i] = sum.wrapping_add(r);
        }
        std::mem::swap(&mut x, &mut y);
        checksum = checksum.wrapping_add(x[0] ^ x[rows / 2] ^ x[rows - 1]);
    }
    checksum
}

// 21. fenwick_bit
#[inline(never)]
pub fn bench_fenwick_bit(n: usize, num_ops: u64) -> u64 {
    let mut tree = vec![0u64; n + 1];
    let mask = (n - 1) as u64;
    let n_u64 = n as u64;
    let mut i = 0u64;
    let mut checksum = 0u64;
    while i < num_ops {
        let h = i.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0xBF58476D1CE4E5B9);
        let mut idx = (h & mask) + 1;
        let delta = ((h >> 32) & 0xFF) + 1;
        while idx <= n_u64 {
            let idx_usize = idx as usize;
            tree[idx_usize] = tree[idx_usize].wrapping_add(delta);
            idx = idx.wrapping_add(idx & 0u64.wrapping_sub(idx));
        }
        let mut qidx = ((h >> 16) & mask) + 1;
        let mut sum = 0u64;
        while qidx > 0 {
            let q_usize = qidx as usize;
            sum = sum.wrapping_add(tree[q_usize]);
            qidx &= qidx - 1;
        }
        checksum ^= sum.rotate_left((i & 31) as u32);
        i += 1;
    }
    checksum
}

// 22. kmp_search
#[inline(never)]
pub fn bench_kmp_search(pat_len: usize, text_len: u64, rounds: u64) -> u64 {
    let mut pat = vec![0u64; pat_len];
    let mut pi = vec![0u64; pat_len];
    let mut total_matches = 0u64;
    let mut r = 0u64;
    let pat_len_u64 = pat_len as u64;
    while r < rounds {
        for i in 0..pat_len {
            let ch = if i + 1 == pat_len { 3 } else { (i % 3) as u64 };
            pat[i] = ch;
            pi[i] = 0;
        }
        let mut k = 0u64;
        let mut q = 1u64;
        while q < pat_len_u64 {
            let qch = pat[q as usize];
            while k > 0 && pat[k as usize] != qch {
                k = pi[(k - 1) as usize];
            }
            if pat[k as usize] == qch {
                k += 1;
            }
            pi[q as usize] = k;
            q += 1;
        }
        let mut state = 0u64;
        let mut z = r.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0x123456789ABCDEF0);
        let mut t = 0u64;
        while t < text_len {
            z = z.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let c = if (t & 255) >= 240 {
                let off = (t & 255) - 240;
                if off + 1 == pat_len_u64 { 3 } else { off % 3 }
            } else {
                (z >> 62) & 3
            };
            while state > 0 && pat[state as usize] != c {
                state = pi[(state - 1) as usize];
            }
            if pat[state as usize] == c {
                state += 1;
            }
            if state == pat_len_u64 {
                total_matches += 1;
                state = pi[(state - 1) as usize];
            }
            t += 1;
        }
        r += 1;
    }
    total_matches ^ pi[pat_len - 1]
}

// 23. union_find_dsu
#[inline(never)]
pub fn bench_union_find_dsu(n: usize, num_ops: u64, rounds: u64) -> u64 {
    let mut parent = vec![0u64; n];
    let mut sz = vec![1u64; n];
    let mask = (n - 1) as u64;
    let mut checksum = 0u64;
    let mut r = 0u64;
    while r < rounds {
        for i in 0..n {
            parent[i] = i as u64;
            sz[i] = 1;
        }
        let mut op = 0u64;
        while op < num_ops {
            let h = (op.wrapping_add(r.wrapping_mul(1315423911)))
                .wrapping_mul(0x9E3779B97F4A7C15)
                .wrapping_add(0xD1B54A32D192ED03);
            let u0 = h & mask;
            let v0 = (h >> 32) & mask;
            let mut ru = u0;
            while parent[ru as usize] != ru {
                let p = parent[ru as usize];
                let gp = parent[p as usize];
                parent[ru as usize] = gp;
                ru = gp;
            }
            let mut rv = v0;
            while parent[rv as usize] != rv {
                let p = parent[rv as usize];
                let gp = parent[p as usize];
                parent[rv as usize] = gp;
                rv = gp;
            }
            if ru != rv {
                let su = sz[ru as usize];
                let sv = sz[rv as usize];
                if su < sv {
                    parent[ru as usize] = rv;
                    sz[rv as usize] = su + sv;
                } else {
                    parent[rv as usize] = ru;
                    sz[ru as usize] = su + sv;
                }
            }
            checksum = checksum.wrapping_add(ru ^ (rv << 16));
            op += 1;
        }
        r += 1;
    }
    checksum
}

// 24. chacha20_stream
#[inline(never)]
pub fn bench_chacha20_stream(blocks: u64) -> u64 {
    let mut st = vec![0u64; 16];
    let mut b = 0u64;
    let mut checksum = 0u64;
    while b < blocks {
        for i in 0..16 {
            st[i] = b.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add((i as u64).wrapping_mul(0x617078653320646E)).wrapping_add(1);
        }
        let mut r = 0u64;
        while r < 10 {
            for q in 0..4 {
                let ia = q;
                let ib = q + 4;
                let ic = q + 8;
                let id = q + 12;
                let mut a = st[ia];
                let mut b_v = st[ib];
                let mut c = st[ic];
                let mut d = st[id];
                a = a.wrapping_add(b_v); d = (d ^ a).rotate_left(16);
                c = c.wrapping_add(d);   b_v = (b_v ^ c).rotate_left(12);
                a = a.wrapping_add(b_v); d = (d ^ a).rotate_left(8);
                c = c.wrapping_add(d);   b_v = (b_v ^ c).rotate_left(7);
                st[ia] = a;
                st[ib] = b_v;
                st[ic] = c;
                st[id] = d;
            }
            r += 1;
        }
        checksum ^= st[0] ^ st[5] ^ st[10] ^ st[15];
        b += 1;
    }
    checksum
}

// 25. jacobi_stencil_1d
#[inline(never)]
pub fn bench_jacobi_stencil_1d(n: usize, steps: u64) -> u64 {
    let mut grid_a = vec![0u64; n];
    let mut grid_b = vec![0u64; n];
    for i in 0..n {
        grid_a[i] = ((i as u64).wrapping_mul(0x9E3779B97F4A7C15)) & 0xFFFF;
        grid_b[i] = 0;
    }
    let mut s = 0u64;
    while s < steps {
        for i in 1..(n - 1) {
            let l = grid_a[i - 1];
            let c = grid_a[i];
            let r = grid_a[i + 1];
            grid_b[i] = (l + c + c + r) >> 2;
        }
        for i in 1..(n - 1) {
            let l = grid_b[i - 1];
            let c = grid_b[i];
            let r = grid_b[i + 1];
            grid_a[i] = (l + c + c + r) >> 2;
        }
        s += 1;
    }
    let mut sum = 0u64;
    for i in 0..n {
        sum = sum.wrapping_add(grid_a[i]);
    }
    sum
}

fn bench_entry<F: Fn() -> u64>(name: &str, filter: &str, f: F) {
    if filter != "all" && filter != name {
        return;
    }
    let _warm = black_box(f());
    let t0 = Instant::now();
    let res = black_box(f());
    let dt = t0.elapsed().as_nanos() as u64;
    println!("BENCH:{}:{}:{}", name, dt, res);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let filter = if args.len() > 1 { args[1].as_str() } else { "all" };

    bench_entry("collatz_steps", filter, || bench_collatz_steps(100_000));
    bench_entry("tuple_accum_sum", filter, || bench_tuple_accum_sum(2_000_000));
    bench_entry("sarray_scale_bias", filter, || bench_sarray_scale_bias(65_536, 40));
    bench_entry("dot_product_u64", filter, || bench_dot_product_u64(65_536, 40));
    bench_entry("saxpy_kernel", filter, || bench_saxpy_kernel(65_536, 40));
    bench_entry("matmul_tiled_u64", filter, || bench_matmul_tiled_u64(192));
    bench_entry("binary_trees", filter, || bench_binary_trees(11, 200));
    bench_entry("nbody", filter, || bench_nbody(200_000));
    bench_entry("spectral_norm", filter, || bench_spectral_norm(128, 30));
    bench_entry("fannkuch_redux", filter, || bench_fannkuch_redux(100_000));
    bench_entry("mandelbrot_simd", filter, || bench_mandelbrot_simd(256, 256, 64));
    bench_entry("robin_hood_htab", filter, || bench_robin_hood_htab(131_072));
    bench_entry("sha256_compress", filter, || bench_sha256_compress(25_000));
    bench_entry("keccak_f1600", filter, || bench_keccak_f1600(50_000));
    bench_entry("mul_div_512", filter, || bench_mul_div_512(1_000_000));
    bench_entry("radix_sort_u64", filter, || bench_radix_sort_u64(16_384, 20));
    bench_entry("dijkstra_pairing_heap", filter, || bench_dijkstra_pairing_heap(256, 20));
    bench_entry("regex_dfa_step", filter, || bench_regex_dfa_step(65_536, 20));
    bench_entry("json_simd_scanner", filter, || bench_json_simd_scanner(65_536, 20));
    bench_entry("sparse_matmul_csr", filter, || bench_sparse_matmul_csr(2048, 16, 40));
    bench_entry("fenwick_bit", filter, || bench_fenwick_bit(4096, 200_000));
    bench_entry("kmp_search", filter, || bench_kmp_search(16, 4096, 500));
    bench_entry("union_find_dsu", filter, || bench_union_find_dsu(256, 500, 500));
    bench_entry("chacha20_stream", filter, || bench_chacha20_stream(50_000));
    bench_entry("jacobi_stencil_1d", filter, || bench_jacobi_stencil_1d(4096, 1000));
}
