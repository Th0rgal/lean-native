#ifndef LEAN_NATIVE_RUNTIME_H
#define LEAN_NATIVE_RUNTIME_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ============================================================================
 * Lean 4 ABI-Compatible Object & Scalar Array Layout
 * ============================================================================
 * Matches Lean 4's `lean_object` and `lean_sarray_object` memory layout:
 *   int32_t  m_rc;       // >0: single-threaded RC, <0: multi-threaded, 0: persistent
 *   uint16_t m_cs_sz;    // compact size / scalar element byte size
 *   uint8_t  m_other;    // num_objs for ctor, or unused for sarray
 *   uint8_t  m_tag;      // 248 (LeanScalarArray) for sarray, 0..243 for ctor
 */

#define LEAN_NATIVE_TAG_SARRAY 248u
#define LEAN_NATIVE_MIN_GPU_THRESHOLD 65536ULL

typedef struct lean_native_object {
    int32_t  m_rc;
    uint16_t m_cs_sz;
    uint8_t  m_other;
    uint8_t  m_tag;
} lean_native_object;

typedef struct lean_native_sarray_u64 {
    int32_t  m_rc;
    uint16_t m_cs_sz;
    uint8_t  m_other;
    uint8_t  m_tag;
    size_t   m_size;
    size_t   m_capacity;
    uint64_t m_data[];
} lean_native_sarray_u64;

/**
 * Zero-copy ByteSlice view over a contiguous `uint8_t` buffer (`ByteArray` / SSZ / RLP payload).
 */
typedef struct lean_native_byte_slice {
    const uint8_t* ptr;
    size_t         len;
} lean_native_byte_slice;

static inline lean_native_byte_slice lean_native_make_byte_slice(const uint8_t* base, size_t total_len, size_t offset, size_t slice_len) {
    lean_native_byte_slice s = { NULL, 0 };
    if (base && offset <= total_len && slice_len <= total_len - offset) {
        s.ptr = base + offset;
        s.len = slice_len;
    }
    return s;
}

/* ============================================================================
 * Reference Counting, Exclusivity, & COW Buffer Management
 * ============================================================================ */

static inline bool lean_native_is_scalar(const void* ptr) {
    return ((uintptr_t)ptr & 1u) != 0u;
}

static inline void* lean_native_box_usize(size_t n) {
    return (void*)((uintptr_t)(n << 1u) | 1u);
}

static inline size_t lean_native_unbox_usize(const void* ptr) {
    return (size_t)((uintptr_t)ptr >> 1u);
}

static inline bool lean_native_is_exclusive(const void* obj) {
    if (!obj || lean_native_is_scalar(obj)) {
        return false;
    }
    const lean_native_object* hdr = (const lean_native_object*)obj;
    return hdr->m_rc == 1;
}

void lean_native_inc(void* obj, size_t count);
void lean_native_dec(void* obj, size_t count);

lean_native_sarray_u64* lean_native_alloc_sarray_u64(size_t size, size_t capacity);
void lean_native_free_sarray_u64(lean_native_sarray_u64* arr);

/**
 * Ensures `arr` is exclusively owned (`m_rc == 1`).
 * - If `arr->m_rc == 1`, returns `arr` in-place (zero allocation, zero copy).
 * - If `arr->m_rc > 1` or persistent (`m_rc == 0`), decrements `arr`'s RC (when >1)
 *   and returns a freshly allocated clone with `m_rc = 1`.
 */
lean_native_sarray_u64* lean_native_ensure_exclusive(lean_native_sarray_u64* arr);

void* lean_native_box_u64(uint64_t val);
uint64_t lean_native_unbox_u64(const void* boxed);

/* C / Rust FFI zero-copy view helpers */
static inline uint64_t* lean_native_sarray_data_ptr(lean_native_sarray_u64* arr) {
    return arr ? arr->m_data : NULL;
}

static inline size_t lean_native_sarray_len(const lean_native_sarray_u64* arr) {
    return arr ? arr->m_size : 0;
}

/* ============================================================================
 * Hybrid CPU/GPU Dispatch & PTX Driver Runtime API
 * ============================================================================ */

/**
 * Returns 1 if an NVIDIA CUDA GPU is initialized and ready for PTX execution, 0 otherwise.
 */
int lean_native_gpu_available(void);

/**
 * Pre-flight CUDA / Grace-Blackwell unified memory headroom guard (`cuMemGetInfo`).
 * Returns 1 if at least `required_bytes + LEAN_NATIVE_CUDA_MIN_FREE_BYTES` (default 2 GiB)
 * of free device/unified memory is available, or 0 to trigger graceful CPU SIMD fallback.
 */
int lean_native_gpu_has_headroom(size_t required_bytes);

/**
 * Returns a human-readable description of the active GPU device (or "CPU-Only Fallback").
 */
const char* lean_native_gpu_device_name(void);

/**
 * Queries dynamic PTX JIT compilation & execution counters (`cuModuleLoadDataEx` / `cuLaunchKernel`).
 */
void lean_native_ptx_jit_stats(uint64_t* out_kernels_loaded, uint64_t* out_launches);

/**
 * Registers a custom PTX 8.0 source string with the CUDA Driver (`cuModuleLoadDataEx`).
 * Returns 0 on success, non-zero on error.
 */
int lean_native_register_ptx_module(const char* ptx_source);

/**
 * Launches a PTX kernel by symbol name (`kernel_name`) with parameter pointers `kernel_params`
 * over `num_elements` 1D work items (256 threads/block).
 * Returns 0 on success, non-zero if unavailable or on error.
 */
int lean_native_launch_ptx_kernel(
    const char* kernel_name,
    void** kernel_params,
    size_t num_elements
);

/**
 * Launches a 2D PTX kernel by symbol name (`kernel_name`) with explicit 2D grid and block dimensions
 * via `cuModuleGetFunction` + `cuLaunchKernel`.
 */
int lean_native_launch_ptx_kernel_2d(
    const char* kernel_name,
    void** kernel_params,
    unsigned int grid_x,
    unsigned int grid_y,
    unsigned int block_x,
    unsigned int block_y
);

/**
 * Hybrid CPU/GPU SAXPY (`out[i] = alpha * x[i] + y[i]`).
 * Uses PTX kernel on GPU when `n >= LEAN_NATIVE_MIN_GPU_THRESHOLD` and GPU is available,
 * otherwise executes vectorized CPU loop.
 */
int lean_native_hybrid_saxpy_u64(
    uint64_t* out,
    const uint64_t* x,
    const uint64_t* y,
    uint64_t alpha,
    size_t n
);

/**
 * Hybrid CPU/GPU Map-Scale-Add (`out[i] = in0[i] * scale + bias`).
 */
int lean_native_hybrid_map_scale_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    uint64_t scale,
    uint64_t bias,
    size_t n
);

/**
 * Hybrid CPU/GPU Zip-Add (`out[i] = in0[i] + in1[i]`).
 */
int lean_native_hybrid_zip_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
);

/**
 * Hybrid CPU/GPU 1D 3-Point Stencil (`out[i] = wl*in0[i-1] + wc*in0[i] + wr*in0[i+1]`).
 */
int lean_native_hybrid_stencil1d_u64(
    uint64_t* out,
    const uint64_t* in0,
    uint64_t wl,
    uint64_t wc,
    uint64_t wr,
    size_t n
);

/**
 * Hybrid CPU/GPU Dot Product Reduction (`*out_sum = sum_i (in0[i] * in1[i])`).
 * Executes `lean_native_kernel_dot_reduce_u64` via `cuModuleLoadDataEx` + `cuLaunchKernel`
 * with shared-memory tree reduction and `atom.global.add.u64`.
 */
int lean_native_hybrid_dot_product_u64(
    uint64_t* out_sum,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
);

/**
 * Hybrid CPU/GPU Dense Matrix Multiplication (`C[M x N] = A[M x K] * B[K x N]`).
 */
int lean_native_hybrid_matmul_u64(
    uint64_t* c,
    const uint64_t* a,
    const uint64_t* b,
    size_t m,
    size_t n,
    size_t k
);

/* Internal CPU fallback hooks also callable by CUDA runtime on small inputs or fallback */
void lean_native_cpu_saxpy_u64(
    uint64_t* out,
    const uint64_t* x,
    const uint64_t* y,
    uint64_t alpha,
    size_t n
);

void lean_native_cpu_map_scale_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    uint64_t scale,
    uint64_t bias,
    size_t n
);

void lean_native_cpu_zip_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
);

void lean_native_cpu_stencil1d_u64(
    uint64_t* out,
    const uint64_t* in0,
    uint64_t wl,
    uint64_t wc,
    uint64_t wr,
    size_t n
);

void lean_native_cpu_dot_product_u64(
    uint64_t* out_sum,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
);

void lean_native_cpu_matmul_u64(
    uint64_t* c,
    const uint64_t* a,
    const uint64_t* b,
    size_t m,
    size_t n,
    size_t k
);

/* ============================================================================
 * Apple Metal Unified-Memory Runtime API (Apple Silicon M1/M2/M3/M4 & Fallback)
 * ============================================================================ */

/**
 * Returns 1 if an Apple Metal GPU device (`MTLCreateSystemDefaultDevice`) is available, 0 otherwise.
 */
int lean_native_metal_available(void);

/**
 * Returns a human-readable description of the Apple Metal GPU device (or "Apple Metal Unavailable (CPU Fallback)").
 */
const char* lean_native_metal_device_name(void);

/**
 * Validates an Apple Metal Shading Language (MSL 3.0) source string (`msl_src`).
 * Returns 1 when valid, 0 otherwise.
 */
int lean_native_metal_validate_msl(const char* msl_src);

/**
 * Launches a 64-bit SAXPY kernel on Apple Metal using zero-copy unified memory (`MTLResourceStorageModeShared`),
 * falling back to `lean_native_cpu_saxpy_u64` on non-Apple platforms.
 */
int lean_native_metal_launch_saxpy_u64(
    uint64_t* out,
    const uint64_t* x,
    const uint64_t* y,
    uint64_t alpha,
    size_t n
);

/**
 * Launches a 16x16 threadgroup-tiled 64-bit matrix multiplication kernel on Apple Metal using zero-copy
 * unified memory (`MTLResourceStorageModeShared`), falling back to `lean_native_cpu_matmul_u64` on non-Apple platforms.
 */
int lean_native_metal_launch_matmul_u64(
    uint64_t* c,
    const uint64_t* a,
    const uint64_t* b,
    size_t m,
    size_t n,
    size_t k
);

/* ============================================================================
 * 256-Bit EVM Word (`u256`) & Persistent Storage Map (`SLOAD` / `SSTORE`)
 * ============================================================================ */

typedef struct {
    uint64_t limbs[4];
} lean_native_u256;

typedef struct lean_native_evm_storage_entry {
    lean_native_u256 key;
    lean_native_u256 val;
    uint8_t          occupied;
} lean_native_evm_storage_entry;

typedef struct lean_native_evm_storage_map {
    lean_native_object             m_header;
    size_t                         m_count;
    size_t                         m_capacity;
    lean_native_evm_storage_entry* m_entries;
} lean_native_evm_storage_map;

/**
 * Allocates and initializes an empty 256-bit EVM key-value storage map (`uint256 -> uint256`).
 */
void* lean_native_evm_storage_create(void);

/**
 * Frees a 256-bit EVM storage map allocated by `lean_native_evm_storage_create`.
 */
void lean_native_evm_storage_free(void* map_ptr);

/**
 * Reads a 256-bit value (`4 x uint64_t` limbs in little-endian order) from `slot_limbs`.
 * Uninitialized slots write `{0, 0, 0, 0}` to `out_val_limbs` per EVM SLOAD semantics.
 */
void lean_native_evm_sload(void* map_ptr, const uint64_t* slot_limbs, uint64_t* out_val_limbs);

/**
 * Writes a 256-bit value (`4 x uint64_t` limbs in little-endian order) to `slot_limbs` in `map_ptr`.
 */
void lean_native_evm_sstore(void* map_ptr, const uint64_t* slot_limbs, const uint64_t* val_limbs);

/* ============================================================================
 * Matryoshka M3 TRM Native Inference Kernels (CPU INT8 AVX2/NEON & Hybrid)
 * ============================================================================ */

/**
 * Scalar reference Matryoshka TRM block step (`SliceRMSNorm_d` + `ClippedReLU^2` + `MUDD` residual).
 * Computes one recursive step on quantized `INT8` hidden state `z_q8[d_model]` with weights
 * `w1_q8[d_model * d_hidden]` and `w2_q8[d_hidden * d_model]` (`ClippedReLU^2` capped at `16` so
 * `VPMADDUBSW` 16-bit signed accumulators never saturate).
 */
void lean_native_trm_matryoshka_ref_int8(
    int32_t* out_cost_q16,
    const int8_t* x0_q8,
    const int8_t* w1_q8,
    const int8_t* w2_q8,
    const int8_t* w_cost_q8,
    size_t d_model,
    size_t d_hidden,
    size_t steps
);

/**
 * Vectorized CPU SIMD (`AVX2` / `NEON` / scalar-exact) Matryoshka TRM inference kernel.
 * Bit-for-bit identical to `lean_native_trm_matryoshka_ref_int8` across slices `d_model in {16, 32, 64}`.
 */
void lean_native_trm_matryoshka_cpu_int8(
    int32_t* out_cost_q16,
    const int8_t* x0_q8,
    const int8_t* w1_q8,
    const int8_t* w2_q8,
    const int8_t* w_cost_q8,
    size_t d_model,
    size_t d_hidden,
    size_t steps
);

/**
 * Runs a deterministic bit-for-bit parity self-test between `lean_native_trm_matryoshka_ref_int8`
 * and `lean_native_trm_matryoshka_cpu_int8` across Matryoshka slices `S_0 (16x32)`, `S_1 (32x64)`,
 * `S_3 (64x128)`, and `S_4 (128x256, Trillium TPU v6e)`. Returns 1 if all slices match bit-for-bit, 0 otherwise.
 */
int lean_native_trm_matryoshka_parity_selftest(void);

/**
 * Unboxed Lean 4 `@[extern]` wrapper around `lean_native_trm_matryoshka_parity_selftest`:
 * takes a dummy `uint64_t` and returns `1ULL` if all Matryoshka slices (`16x32`, `32x64`, `64x128`)
 * match bit-for-bit between reference and vectorized kernels, or `0ULL` on mismatch.
 */
uint64_t lean_native_trm_matryoshka_parity_u64(uint64_t seed);

/**
 * Hybrid CPU/GPU Matryoshka TRM inference dispatcher (`NVFP4`/`FP16` on Blackwell `GB10` when
 * available, falling back deterministically to `lean_native_trm_matryoshka_cpu_int8`).
 */
int lean_native_hybrid_trm_matryoshka_int8(
    int32_t* out_cost_q16,
    const int8_t* x0_q8,
    const int8_t* w1_q8,
    const int8_t* w2_q8,
    const int8_t* w_cost_q8,
    size_t d_model,
    size_t d_hidden,
    size_t steps
);

/* ============================================================================
 * Universal Multi-Target Speculate-Forest ABI v2 (`CPU SIMD` / `Spark GPU` / `TPU XLA`)
 * ============================================================================ */

#define LEAN_NATIVE_FOREST_ABI_VERSION 2u
#define LEAN_NATIVE_TIER_S0_CPU_L1     0u
#define LEAN_NATIVE_TIER_S1_CPU_L2     1u
#define LEAN_NATIVE_TIER_S2_NEON_FP16  2u
#define LEAN_NATIVE_TIER_S3_SPARK_CUDA 3u
#define LEAN_NATIVE_TIER_S4_TPU_V6E    4u

/**
 * Evaluates the 16-opcode 256-bit (`U256`) RPN bytecode (`rpn_opcodes[16]`) deterministically
 * over `n_samples` SplitMix64 states seeded by `(base_seed, goal_idx)`.
 * If a counterexample is found, writes the minimum `sample_idx` to `*out_min_sample_idx`
 * and returns 1 (or 0 if all samples satisfy the property).
 */
int lean_native_rpn_u256_fastcheck_goal(
    uint64_t base_seed,
    uint64_t goal_idx,
    size_t n_samples,
    const int32_t* rpn_opcodes,
    uint64_t arg0,
    uint64_t arg1,
    uint64_t* out_min_sample_idx
);

/**
 * O(1) deterministic indexed-witness recertification (`verifyIndexedWitness` C-ABI v2).
 * Reconstructs the exact 256-bit state at `(base_seed, goal_idx, sample_idx)` via
 * `splitmix64(base_seed ^ (goal_idx * PHI) + sample_idx * PHI)` without transferring
 * 64-byte raw `U256` payloads over PCIe/HTTP, and returns 1 iff `sample_idx` is a
 * genuine counterexample to `rpn_opcodes[16]`.
 */
int lean_native_verify_indexed_witness_recert(
    uint64_t base_seed,
    uint64_t goal_idx,
    uint64_t sample_idx,
    const int32_t* rpn_opcodes,
    uint64_t arg0,
    uint64_t arg1
);

/**
 * Cross-slice Matryoshka cascade (`S_0 16x32` -> `S_1 32x64` -> `S_3 64x128` -> `S_4 128x256`)
 * with additive sum-of-squares (`combineSliceSumSq`) & pre-activation dot decomposition
 * (`combineSlicePrefixDot`) and tier-deviation margin abstention (`eps_tier_permille`).
 */
void lean_native_trm_matryoshka_cascade_int8(
    int32_t* out_cost_q16,
    int32_t* out_survival_permille,
    uint8_t* out_router_action,
    uint8_t* out_effective_tier,
    const int8_t* x0_q8,
    const int8_t* w1_q8,
    const int8_t* w2_q8,
    const int8_t* w_cost_q8,
    int32_t prune_floor_permille,
    int32_t escalate_band_permille,
    int32_t eps_tier_permille
);

/**
 * Hardware-agnostic forest speculation C-ABI v2 (`CPU SIMD` / `Spark GB10 CUDA` / `Cloud TPU v6e`).
 * Evaluates `n_goals` in parallel across the 16-opcode `U256` RPN counterexample sweep and
 * the Matryoshka `S_0 -> S_1 -> S_3 -> S_4` survival/router cascade, returning deterministic
 * index-based witnesses (`out_min_sample_idx[g]`) and locally recertified router actions.
 */
int lean_native_speculate_forest(
    size_t n_goals,
    size_t n_samples,
    uint64_t base_seed,
    const int32_t* rpn_opcodes,
    const uint64_t* rpn_arg0,
    const uint64_t* rpn_arg1,
    const int8_t* x0_q8,
    const int8_t* w1_q8,
    const int8_t* w2_q8,
    const int8_t* w_cost_q8,
    int32_t prune_floor_permille,
    int32_t escalate_band_permille,
    int32_t eps_tier_permille,
    uint8_t* out_cex_found,
    uint64_t* out_min_sample_idx,
    int32_t* out_survival_permille,
    uint8_t* out_router_action,
    uint8_t* out_effective_tier
);

#ifdef __cplusplus
}
#endif

#endif /* LEAN_NATIVE_RUNTIME_H */
