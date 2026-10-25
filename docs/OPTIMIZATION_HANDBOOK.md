# `lean-native` Kernel, SIMD & Systems Optimization Handbook

This handbook documents the verified whole-slice C-ABI contracts, hardware SIMD idioms (`x86_64` AVX2/PCLMULQDQ and `aarch64` NEON PMULL/vtbl), cache-blocked transform schedules, and tiered benchmark harnesses provided by `lean-native` (`--c-abi`), `turbo-lean` (`audit-spec` / `build --seed-shards`), and `lean-sys` (`verifyParChunk` / `verifyArenaDisjoint`).

---

## 1. Whole-Slice C-ABI Contracts (`--c-abi`)

1. **Whole-Slice over Per-Element FFI (`leannative_verify_cabi_slice_io`)**:
   - Never cross the FFI boundary on individual field elements or small tuples. Expose contiguous slice entrypoints (`const uint8_t* in_ptr, uint8_t* out_ptr, size_t n_elems`) gated by `leannative_verify_cabi_slice_io` and `leannative_verify_no_runtime_slice_out` (zero runtime heap allocations inside hot loops).
2. **In-Kernel Specification & Non-Vacuity Gate**:
   - Every custom kernel or bitwise/table isomorphism must have a tight specification in `Spec.lean` or the project's proof module (`0 sorryAx`, `0 vacuous` specs under `turbo-lean --json audit-spec`) and a deterministic mutation test suite verifying that each mutant is rejected.
3. **Incremental Module DAG Compilation (`turbo-lean build --seed-shards`)**:
   - Use `turbo-lean build --seed-shards --project-dir .` so Lean module DAG compilation uses per-module content-addressed storage (CAS) and transactional `.olean` publishing into `.lake/build/lib/lean` in milliseconds when inputs are unchanged.

---

## 2. Binary Field (`GF(2^128)` & `GF(2^8)`) SIMD Patterns

### 2.1. Register-Resident 4-Multiply Schoolbook vs. Scalar-XOR Karatsuba
- Keep all `GF(2^128)` carryless products resident in 128-bit SIMD registers (`_mm_clmulepi64_si128` on `x86_64` / `vmull_p64` on `aarch64` NEON): `4` 64×64 carryless multiplies + `2`-CLMUL `0x87` ($x^{128} + x^7 + x^2 + x + 1$) reduction.
- **Anti-Pattern**: Never extract 64-bit limbs to general-purpose registers (GPRs) for 3-multiply Karatsuba XORs; SIMD-to-GPR roundtrips stall execution ports and break 128-bit load/store coalescing.

### 2.2. 3-Limb `(lo, mid, hi)` Unreduced Sum-of-Products Accumulation (`leannative_verify_lazy_reduction_slice`)
- When summing multiple `GF(2^128)` products inside an inner loop (`lean_native_f128_fold_and_msg_round_slice`, dot products, or matrix-vector folds):
  - Accumulate the raw 64×64 carryless products (`p00`, `p01 ^ p10`, `p11`) into **three separate 128-bit SIMD registers** (`acc_lo`, `acc_mid`, `acc_hi` — `4` `pclmulqdq`/`vmull_p64` + `4` `pxor` per term, with **zero** in-loop byte shifts or reductions).
  - Perform a single cross-limb byte shift (`_mm_slli_si128` / `_mm_srli_si128` or `vextq_p8`) and a single 2-CLMUL `0x87` reduction after the loop finishes.

### 2.3. `x86_64` (Skylake / Kaby Lake / Zen) Port-5 Contention & Unpack-Free Stride-32 Blend
- On `x86_64` (`AVX2 + PCLMULQDQ`), both `pclmulqdq` and shuffle/unpack instructions (`vpunpcklqdq`, `vpshufb`, `vpermq`) contend for **Port 5**.
- **Unpack-Free Stride-32 Blend**: When packing or interleaving 32-bit/64-bit lanes across carryless products, mask with `0x0000_00FF_0000_00FF` and combine via `_mm_blend_epi32::<0b1010>(p0, _mm_slli_epi64::<32>(p1))` (which dispatches across Ports 0/1/5 and shifts out cross-terms without extra AND masks) instead of `vpunpcklqdq` + `vpshufb`.
- **Pre-Permute XOR Reduction**: When accumulating linear combinations across lookup tables, XOR-combine the unpermuted table rows *before* executing lane permutations to halve Port-5 uops.

### 2.4. `aarch64` NEON Unreduced `vmull_p8` + Degree-14 Horner (`0x8d80`) Accumulation
- In multi-step `GF(2^8)` inner products on ARM64 NEON:
  - Accumulate unreduced 15-bit `vmull_p8` polynomial products using a 4-instruction degree-$\le 14$ Horner step in 16-bit lanes:
    ```c
    int16x8_t s = vshlq_n_s16(acc, 1);
    uint16x8_t mask = vcltq_s16(s, vdupq_n_s16(0));
    acc = veorq_u16(veorq_u16(vreinterpretq_u16_s16(s), vandq_u16(mask, vdupq_n_u16(0x8d80))), p_k);
    ```
  - Run `gf8_reduce_vec16` **once** at the end of the loop instead of after every multiplication.

### 2.5. `x86_64` AVX2 Composite-Field Tower $\text{GF}(2^8) \cong \mathbb{F}_{16}^2$ `vpshufb` Multiplier
- On `x86_64` CPUs without `GFNI`, scalar or bit-sliced `GF(2^8)` loops bottleneck on shift/XOR dependency chains.
- Map $\text{GF}(2^8) \cong \mathbb{F}_{16} \oplus \mathbb{F}_{16} Y$ ($Y^2 \oplus Y = \nu$) via the verified linear bit-matrix isomorphism (`gf8_composite_isomorphism_sound`), evaluate 16-lane parallel $\mathbb{F}_{16}$ multiplications using 3-multiply Karatsuba over 16-byte `vpshufb` log/exp tables in YMM registers, and fold with an 8-bit Horner step (`(acc << 1) ^ ((s >> 7) & 0x1b)`).

---

## 3. Lookup Tables, Cache Alignment & Basis Pre-Scaling

1. **$\mathbb{F}_2$-Linear Pre-Scaled Basis Table Fusion (`scaled_pair`)**:
   - When folding packed boolean or small-field witnesses via a linear table `fold_table(bytes)` followed by challenge interpolation $a_0 \oplus \rho_0 (a_0 \oplus a_1) = (1 \oplus \rho_0)a_0 \oplus \rho_0 a_1$, pre-scale the basis table once by $(1 \oplus \rho_0)$ and $\rho_0$ before the pass ($O(|\text{table}|)$ multiplications). The $O(2^m)$ inner loop then reduces to pure table-lookup XORs with **zero** in-loop field multiplications.
2. **Sparse-Mask Index Compaction & Loop Inversion**:
   - Never index a 256-entry ($4\text{ KiB}$) or multi-slice ($64\text{ KiB} > 32\text{ KiB}$ L1D) lookup table with sparse bit-masked indices such as `byte & 0x55` or `byte & 0xaa` (which touch only $2^4 = 16$ valid entries scattered across 16 cache lines). Compact 4-bit active nibbles into 16-entry ($256\text{ B}$) tables (`pext_even4` / `pext_odd4`), and tile outer loops into L1D-resident subtable halves × 4-lane SIMD register blocks.
3. **64-Byte Cache-Line Row Alignment**:
   - Align lookup table rows to 64-byte cache-line multiples (`64 B` or `128 B`). Avoid `96 B` (6 × 16B) row strides, where every odd-indexed row crosses a 64-byte cache-line boundary and incurs a split-line load penalty.

---

## 4. Additive NTT Fusion, Depth-First Cache Blocking & Cache-Set Aliasing

1. **2/3/4-Layer Radix-4/8 Butterfly Fusion (`leannative_verify_radix4_ntt_fusion`)**:
   - Fuse consecutive LCH Additive NTT layers (`lean_native_ntt_butterfly_fused_2layer_slice`, `lean_native_ntt_butterfly_fused_3layer_row_slice`, `lean_native_ntt_butterfly_fused_4layer_row_slice` on CPU and `lean_native_kernel_ntt_radix4_interleaved_f128` on Apple Metal 3.0) to cut memory traffic by $2\times\text{–}4\times$.
   - **Register Budget by Target**:
     - On 16-register `x86_64` AVX2, decompose 4-layer (16-point) butterflies into two 8-register Radix-4 stages in L1 cache (`[u128; 16]`) to prevent XMM stack spills.
     - On 32-register `aarch64` NEON, keep all 16 butterfly state registers live and hoist all `vextq_p8::<8>` twiddle byte-reversals (`tw_rev`) and the reduction polynomial outside the inner lane loop.
2. **Depth-First LLC/L2 Sub-NTT Blocking (`TARGET_SUBGROUP_LOG_BYTES = 21`)**:
   - Execute only the top $n_{\text{top}}$ layers ($n_{\text{top}} - \text{start} \equiv 0 \pmod 4$) across DRAM until sub-problems fit inside LLC/L2 ($2\text{ MiB}$), then recurse **depth-first** per sub-block using fused `4 + 4 + 3` passes so all remaining layers execute entirely in cache.
3. **Power-of-2 Cache-Set Aliasing Guard**:
   - Never stream $\ge 16$ simultaneous pointers separated by large power-of-2 byte strides ($64\text{ KiB}..512\text{ MiB}$) inside the same inner loop: they alias onto the exact same 8-way L1D and 16-way L2 cache sets and cause severe conflict-miss thrashing. Iterate outer sub-blocks sequentially around the parallel row loop.

---

## 5. Parallel Chunking, Disjoint Arenas & Multi-Type Slab Pooling (`lean-sys`)

1. **Verified Parallel Chunking & Disjoint Scratch Arenas (`leansys_verify_par_chunk`, `leansys_verify_arena_disjoint`)**:
   - Gate Rayon/OpenMP chunk boundaries and in-place buffer reuse through `LeanSys.Spec.verifyParChunk` and `LeanSys.Spec.verifyArenaDisjoint`.
2. **Multi-Type Thread-Safe Slab Recycling (`F128_POOL`, `U8_POOL`, `HASH_POOL`)**:
   - Any buffer allocation $\ge 16\text{ MiB}$ in an iterative prover or kernel pipeline (`F128` field vectors, packed `u8` witness matrices, or `[u8; 32]` Merkle digest layers) triggers OS `mmap`/`munmap` and minor page faults ($\sim 40\text{–}120\text{ ms}$ per call on Linux). Recycle all three buffer classes via prewarmed `Mutex<Vec<Vec<T>>>` pools (including `Drop` return on owned Merkle tree layers).

---

## 6. Two-Tier Benchmark & Build Discipline

1. **Fast Inner-Loop Microbenchmark (`< 5s` Cycle)**:
   - Isolate hot kernels behind a standalone single-binary microbenchmark or small-log2 test target (`log2=14..16` + deterministic checksum pre-filter $< 200\text{ ms}$) that compiles and runs in $< 5\text{ s}$ during kernel iteration.
   - Avoid rebuilding unrelated binaries or running full multi-binary benchmark suites until the microbenchmark confirms a clear win.
2. **Pinned Full Promotion Harness (`CV <= 3.0%`, `ΔE2E >= 1.0%`)**:
   - Promote a candidate to the main branch only after running the pinned end-to-end benchmark (`taskset -c`, fixed `RAYON_NUM_THREADS`/`OMP_NUM_THREADS`, warm-up + $\ge 3$ timed runs) and verifying $\Delta\text{E2E} \ge \max(1.0\%, 2 \times \text{CV})$ with `warm_state: "warm"`.
