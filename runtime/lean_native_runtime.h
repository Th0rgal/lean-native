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

#ifdef __cplusplus
}
#endif

#endif /* LEAN_NATIVE_RUNTIME_H */
