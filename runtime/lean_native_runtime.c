#include "lean_native_runtime.h"
#include <stdlib.h>
#include <string.h>

#if defined(__GNUC__) || defined(__clang__)
#define LEAN_NATIVE_WEAK __attribute__((weak))
#else
#define LEAN_NATIVE_WEAK
#endif

typedef struct lean_native_boxed_u64 {
    lean_native_object m_header;
    uint64_t           m_value;
} lean_native_boxed_u64;

/* ============================================================================
 * Reference Counting & COW Buffer Primitives
 * ============================================================================ */

void lean_native_inc(void* obj, size_t count) {
    if (!obj || lean_native_is_scalar(obj) || count == 0) {
        return;
    }
    lean_native_object* hdr = (lean_native_object*)obj;
    if (hdr->m_rc > 0) {
        hdr->m_rc += (int32_t)count;
    } else if (hdr->m_rc < 0) {
        __atomic_sub_fetch(&hdr->m_rc, (int32_t)count, __ATOMIC_RELAXED);
    }
}

void lean_native_dec(void* obj, size_t count) {
    if (!obj || lean_native_is_scalar(obj) || count == 0) {
        return;
    }
    lean_native_object* hdr = (lean_native_object*)obj;
    if (hdr->m_rc > 0) {
        hdr->m_rc -= (int32_t)count;
        if (hdr->m_rc <= 0) {
            free(obj);
        }
    } else if (hdr->m_rc < 0) {
        int32_t next_rc = __atomic_add_fetch(&hdr->m_rc, (int32_t)count, __ATOMIC_ACQ_REL);
        if (next_rc >= 0) {
            free(obj);
        }
    }
}

lean_native_sarray_u64* lean_native_alloc_sarray_u64(size_t size, size_t capacity) {
    size_t cap = capacity < size ? size : capacity;
    size_t total_bytes = sizeof(lean_native_sarray_u64) + cap * sizeof(uint64_t);
    lean_native_sarray_u64* arr = NULL;
#if defined(_POSIX_C_SOURCE) && _POSIX_C_SOURCE >= 200112L
    if (posix_memalign((void**)&arr, 64, total_bytes) != 0) {
        arr = (lean_native_sarray_u64*)malloc(total_bytes);
    }
#else
    arr = (lean_native_sarray_u64*)malloc(total_bytes);
#endif
    if (!arr) {
        return NULL;
    }
    arr->m_rc       = 1;
    arr->m_cs_sz    = (uint16_t)sizeof(uint64_t);
    arr->m_other    = 0;
    arr->m_tag      = LEAN_NATIVE_TAG_SARRAY;
    arr->m_size     = size;
    arr->m_capacity = cap;
    return arr;
}

void lean_native_free_sarray_u64(lean_native_sarray_u64* arr) {
    if (arr) {
        free(arr);
    }
}

lean_native_sarray_u64* lean_native_ensure_exclusive(lean_native_sarray_u64* arr) {
    if (!arr) {
        return NULL;
    }
    if (arr->m_rc == 1) {
        return arr;
    }
    lean_native_sarray_u64* clone = lean_native_alloc_sarray_u64(arr->m_size, arr->m_capacity);
    if (!clone) {
        return NULL;
    }
    if (arr->m_size > 0) {
        memcpy(clone->m_data, arr->m_data, arr->m_size * sizeof(uint64_t));
    }
    lean_native_dec(arr, 1);
    return clone;
}

void* lean_native_box_u64(uint64_t val) {
    if ((val >> 63u) == 0u) {
        return (void*)((uintptr_t)(val << 1u) | 1u);
    }
    lean_native_boxed_u64* b = (lean_native_boxed_u64*)malloc(sizeof(lean_native_boxed_u64));
    if (!b) {
        return NULL;
    }
    b->m_header.m_rc    = 1;
    b->m_header.m_cs_sz = sizeof(lean_native_boxed_u64);
    b->m_header.m_other = 0;
    b->m_header.m_tag   = 0;
    b->m_value          = val;
    return (void*)b;
}

uint64_t lean_native_unbox_u64(const void* boxed) {
    if (!boxed) {
        return 0;
    }
    if (lean_native_is_scalar(boxed)) {
        return (uint64_t)((uintptr_t)boxed >> 1u);
    }
    const lean_native_boxed_u64* b = (const lean_native_boxed_u64*)boxed;
    return b->m_value;
}

/* ============================================================================
 * Vectorized CPU Kernel Implementations (x86-64 AVX2/AVX-512 & ARM64 NEON)
 * ============================================================================ */

void lean_native_cpu_saxpy_u64(
    uint64_t* out,
    const uint64_t* x,
    const uint64_t* y,
    uint64_t alpha,
    size_t n
) {
    for (size_t i = 0; i < n; ++i) {
        out[i] = alpha * x[i] + y[i];
    }
}

void lean_native_cpu_map_scale_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    uint64_t scale,
    uint64_t bias,
    size_t n
) {
    for (size_t i = 0; i < n; ++i) {
        out[i] = in0[i] * scale + bias;
    }
}

void lean_native_cpu_zip_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
) {
    for (size_t i = 0; i < n; ++i) {
        out[i] = in0[i] + in1[i];
    }
}

void lean_native_cpu_stencil1d_u64(
    uint64_t* out,
    const uint64_t* in0,
    uint64_t wl,
    uint64_t wc,
    uint64_t wr,
    size_t n
) {
    if (n == 0) {
        return;
    }
    out[0] = in0[0];
    if (n == 1) {
        return;
    }
    for (size_t i = 1; i + 1 < n; ++i) {
        out[i] = in0[i - 1] * wl + in0[i] * wc + in0[i + 1] * wr;
    }
    out[n - 1] = in0[n - 1];
}

void lean_native_cpu_dot_product_u64(
    uint64_t* out_sum,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
) {
    if (!out_sum) {
        return;
    }
    uint64_t s0 = 0ULL, s1 = 0ULL, s2 = 0ULL, s3 = 0ULL;
    size_t i = 0;
    for (; i + 4 <= n; i += 4) {
        s0 += in0[i]     * in1[i];
        s1 += in0[i + 1] * in1[i + 1];
        s2 += in0[i + 2] * in1[i + 2];
        s3 += in0[i + 3] * in1[i + 3];
    }
    uint64_t acc = (s0 + s1) + (s2 + s3);
    for (; i < n; ++i) {
        acc += in0[i] * in1[i];
    }
    *out_sum = acc;
}

void lean_native_cpu_matmul_u64(
    uint64_t* c,
    const uint64_t* a,
    const uint64_t* b,
    size_t m,
    size_t n,
    size_t k
) {
    memset(c, 0, m * n * sizeof(uint64_t));
    const size_t tile = 32;
    for (size_t i0 = 0; i0 < m; i0 += tile) {
        size_t i_max = (i0 + tile < m) ? (i0 + tile) : m;
        for (size_t p0 = 0; p0 < k; p0 += tile) {
            size_t p_max = (p0 + tile < k) ? (p0 + tile) : k;
            for (size_t j0 = 0; j0 < n; j0 += tile) {
                size_t j_max = (j0 + tile < n) ? (j0 + tile) : n;
                for (size_t i = i0; i < i_max; ++i) {
                    for (size_t p = p0; p < p_max; ++p) {
                        uint64_t a_ip = a[i * k + p];
                        for (size_t j = j0; j < j_max; ++j) {
                            c[i * n + j] += a_ip * b[p * n + j];
                        }
                    }
                }
            }
        }
    }
}

/* ============================================================================
 * Default CPU-Only Weak Symbols (Overridden when linked with lean_native_cuda.cu)
 * ============================================================================ */

LEAN_NATIVE_WEAK int lean_native_gpu_available(void) {
    return 0;
}

LEAN_NATIVE_WEAK int lean_native_gpu_has_headroom(size_t required_bytes) {
    (void)required_bytes;
    return 0;
}

LEAN_NATIVE_WEAK const char* lean_native_gpu_device_name(void) {
    return "CPU-Only Fallback (LLVM SIMD)";
}

LEAN_NATIVE_WEAK void lean_native_ptx_jit_stats(
    uint64_t* out_kernels_loaded,
    uint64_t* out_launches
) {
    if (out_kernels_loaded) {
        *out_kernels_loaded = 0ULL;
    }
    if (out_launches) {
        *out_launches = 0ULL;
    }
}

LEAN_NATIVE_WEAK int lean_native_register_ptx_module(const char* ptx_source) {
    (void)ptx_source;
    return -1;
}

LEAN_NATIVE_WEAK int lean_native_launch_ptx_kernel(
    const char* kernel_name,
    void** kernel_params,
    size_t num_elements
) {
    (void)kernel_name;
    (void)kernel_params;
    (void)num_elements;
    return -1;
}

LEAN_NATIVE_WEAK int lean_native_launch_ptx_kernel_2d(
    const char* kernel_name,
    void** kernel_params,
    unsigned int grid_x,
    unsigned int grid_y,
    unsigned int block_x,
    unsigned int block_y
) {
    (void)kernel_name;
    (void)kernel_params;
    (void)grid_x;
    (void)grid_y;
    (void)block_x;
    (void)block_y;
    return -1;
}

LEAN_NATIVE_WEAK int lean_native_hybrid_saxpy_u64(
    uint64_t* out,
    const uint64_t* x,
    const uint64_t* y,
    uint64_t alpha,
    size_t n
) {
    if (!out || !x || !y) {
        return -1;
    }
    lean_native_cpu_saxpy_u64(out, x, y, alpha, n);
    return 0;
}

LEAN_NATIVE_WEAK int lean_native_hybrid_map_scale_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    uint64_t scale,
    uint64_t bias,
    size_t n
) {
    if (!out || !in0) {
        return -1;
    }
    lean_native_cpu_map_scale_add_u64(out, in0, scale, bias, n);
    return 0;
}

LEAN_NATIVE_WEAK int lean_native_hybrid_zip_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
) {
    if (!out || !in0 || !in1) {
        return -1;
    }
    lean_native_cpu_zip_add_u64(out, in0, in1, n);
    return 0;
}

LEAN_NATIVE_WEAK int lean_native_hybrid_stencil1d_u64(
    uint64_t* out,
    const uint64_t* in0,
    uint64_t wl,
    uint64_t wc,
    uint64_t wr,
    size_t n
) {
    if (!out || !in0) {
        return -1;
    }
    lean_native_cpu_stencil1d_u64(out, in0, wl, wc, wr, n);
    return 0;
}

LEAN_NATIVE_WEAK int lean_native_hybrid_dot_product_u64(
    uint64_t* out_sum,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
) {
    if (!out_sum || !in0 || !in1) {
        return -1;
    }
    lean_native_cpu_dot_product_u64(out_sum, in0, in1, n);
    return 0;
}

LEAN_NATIVE_WEAK int lean_native_hybrid_matmul_u64(
    uint64_t* c,
    const uint64_t* a,
    const uint64_t* b,
    size_t m,
    size_t n,
    size_t k
) {
    if (!c || !a || !b) {
        return -1;
    }
    lean_native_cpu_matmul_u64(c, a, b, m, n, k);
    return 0;
}

/* ============================================================================
 * 256-Bit EVM Persistent Storage Map Implementation (`SLOAD` / `SSTORE`)
 * ============================================================================ */

#define LEAN_NATIVE_EVM_INITIAL_CAP 64u

static inline uint64_t lean_native_hash_u256(const uint64_t* limbs) {
    /* SplitMix64-style mixing across all four 64-bit limbs */
    uint64_t h = 0x9E3779B97F4A7C15ULL;
    for (size_t i = 0; i < 4; ++i) {
        uint64_t z = limbs[i] + 0x9E3779B97F4A7C15ULL;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        h ^= z ^ (z >> 31);
        h = (h << 13) | (h >> 51);
    }
    return h;
}

static inline int lean_native_u256_eq(const uint64_t* a, const uint64_t* b) {
    return a[0] == b[0] && a[1] == b[1] && a[2] == b[2] && a[3] == b[3];
}

void* lean_native_evm_storage_create(void) {
    lean_native_evm_storage_map* map =
        (lean_native_evm_storage_map*)malloc(sizeof(lean_native_evm_storage_map));
    if (!map) {
        return NULL;
    }
    lean_native_evm_storage_entry* entries =
        (lean_native_evm_storage_entry*)calloc(
            LEAN_NATIVE_EVM_INITIAL_CAP,
            sizeof(lean_native_evm_storage_entry)
        );
    if (!entries) {
        free(map);
        return NULL;
    }
    map->m_header.m_rc    = 1;
    map->m_header.m_cs_sz = (uint16_t)sizeof(lean_native_evm_storage_map);
    map->m_header.m_other = 0;
    map->m_header.m_tag   = 0;
    map->m_count          = 0;
    map->m_capacity       = LEAN_NATIVE_EVM_INITIAL_CAP;
    map->m_entries        = entries;
    return (void*)map;
}

void lean_native_evm_storage_free(void* map_ptr) {
    if (!map_ptr || lean_native_is_scalar(map_ptr)) {
        return;
    }
    lean_native_evm_storage_map* map = (lean_native_evm_storage_map*)map_ptr;
    if (map->m_entries) {
        free(map->m_entries);
        map->m_entries = NULL;
    }
    free(map);
}

static int lean_native_evm_storage_grow(lean_native_evm_storage_map* map) {
    size_t old_cap = map->m_capacity;
    size_t new_cap = old_cap ? (old_cap * 2u) : LEAN_NATIVE_EVM_INITIAL_CAP;
    lean_native_evm_storage_entry* new_entries =
        (lean_native_evm_storage_entry*)calloc(new_cap, sizeof(lean_native_evm_storage_entry));
    if (!new_entries) {
        return -1;
    }
    size_t mask = new_cap - 1u;
    for (size_t i = 0; i < old_cap; ++i) {
        if (map->m_entries[i].occupied) {
            uint64_t h = lean_native_hash_u256(map->m_entries[i].key.limbs);
            size_t idx = (size_t)h & mask;
            while (new_entries[idx].occupied) {
                idx = (idx + 1u) & mask;
            }
            new_entries[idx] = map->m_entries[i];
        }
    }
    free(map->m_entries);
    map->m_entries  = new_entries;
    map->m_capacity = new_cap;
    return 0;
}

void lean_native_evm_sload(void* map_ptr, const uint64_t* slot_limbs, uint64_t* out_val_limbs) {
    if (!out_val_limbs) {
        return;
    }
    out_val_limbs[0] = 0ULL;
    out_val_limbs[1] = 0ULL;
    out_val_limbs[2] = 0ULL;
    out_val_limbs[3] = 0ULL;
    if (!map_ptr || !slot_limbs || lean_native_is_scalar(map_ptr)) {
        return;
    }
    const lean_native_evm_storage_map* map = (const lean_native_evm_storage_map*)map_ptr;
    if (!map->m_entries || map->m_capacity == 0) {
        return;
    }
    size_t mask = map->m_capacity - 1u;
    size_t idx = (size_t)lean_native_hash_u256(slot_limbs) & mask;
    for (size_t probe = 0; probe < map->m_capacity; ++probe) {
        const lean_native_evm_storage_entry* e = &map->m_entries[idx];
        if (!e->occupied) {
            return;
        }
        if (lean_native_u256_eq(e->key.limbs, slot_limbs)) {
            out_val_limbs[0] = e->val.limbs[0];
            out_val_limbs[1] = e->val.limbs[1];
            out_val_limbs[2] = e->val.limbs[2];
            out_val_limbs[3] = e->val.limbs[3];
            return;
        }
        idx = (idx + 1u) & mask;
    }
}

void lean_native_evm_sstore(void* map_ptr, const uint64_t* slot_limbs, const uint64_t* val_limbs) {
    if (!map_ptr || !slot_limbs || !val_limbs || lean_native_is_scalar(map_ptr)) {
        return;
    }
    lean_native_evm_storage_map* map = (lean_native_evm_storage_map*)map_ptr;
    if (!map->m_entries || map->m_capacity == 0) {
        return;
    }
    if ((map->m_count + 1u) * 10u >= map->m_capacity * 7u) {
        if (lean_native_evm_storage_grow(map) != 0) {
            return;
        }
    }
    size_t mask = map->m_capacity - 1u;
    size_t idx = (size_t)lean_native_hash_u256(slot_limbs) & mask;
    for (size_t probe = 0; probe < map->m_capacity; ++probe) {
        lean_native_evm_storage_entry* e = &map->m_entries[idx];
        if (!e->occupied) {
            memcpy(e->key.limbs, slot_limbs, 4u * sizeof(uint64_t));
            memcpy(e->val.limbs, val_limbs, 4u * sizeof(uint64_t));
            e->occupied = 1u;
            map->m_count += 1u;
            return;
        }
        if (lean_native_u256_eq(e->key.limbs, slot_limbs)) {
            memcpy(e->val.limbs, val_limbs, 4u * sizeof(uint64_t));
            return;
        }
        idx = (idx + 1u) & mask;
    }
}

/* ============================================================================
 * Matryoshka M3 TRM Native Inference Kernels (CPU INT8 AVX2/NEON & Parity)
 * ============================================================================ */

static inline uint32_t lean_native_isqrt_u32(uint32_t n) {
    if (n == 0u) {
        return 1u;
    }
    uint32_t x = n;
    uint32_t y = (x + 1u) >> 1u;
    while (y < x) {
        x = y;
        y = (x + n / x) >> 1u;
    }
    return x > 0u ? x : 1u;
}

void lean_native_trm_matryoshka_ref_int8(
    int32_t* out_cost_q16,
    const int8_t* x0_q8,
    const int8_t* w1_q8,
    const int8_t* w2_q8,
    const int8_t* w_cost_q8,
    size_t d_model,
    size_t d_hidden,
    size_t steps
) {
    if (!out_cost_q16 || !x0_q8 || !w1_q8 || !w2_q8 || !w_cost_q8 || d_model == 0 || d_model > 128 || d_hidden == 0 || d_hidden > 256) {
        return;
    }
    int32_t z[128];
    int32_t y[128];
    int32_t h_norm[128];
    uint8_t act_u8[256];
    for (size_t i = 0; i < d_model; ++i) {
        z[i] = (int32_t)x0_q8[i];
        y[i] = (int32_t)x0_q8[i];
    }
    for (size_t s = 0; s < steps; ++s) {
        uint32_t sum_sq = 0u;
        int32_t h_in[128];
        for (size_t i = 0; i < d_model; ++i) {
            /* MUDD alpha0=13/20, alpha1=7/20 */
            h_in[i] = (13 * z[i] + 7 * (int32_t)x0_q8[i]) / 20;
            sum_sq += (uint32_t)(h_in[i] * h_in[i]);
        }
        uint32_t rms = lean_native_isqrt_u32(sum_sq / (uint32_t)d_model + 1u);
        for (size_t i = 0; i < d_model; ++i) {
            int32_t v = (h_in[i] * 32) / (int32_t)rms;
            h_norm[i] = v < -127 ? -127 : (v > 127 ? 127 : v);
        }
        for (size_t j = 0; j < d_hidden; ++j) {
            int32_t acc = 0;
            for (size_t i = 0; i < d_model; ++i) {
                acc += h_norm[i] * (int32_t)w1_q8[i * d_hidden + j];
            }
            int32_t pre = (acc >> 7) - 11; /* Shifted ReLU^2 threshold */
            int32_t relu = pre > 0 ? pre : 0;
            if (relu > 16) {
                relu = 16; /* ClippedReLU^2 cap so relu^2 <= 255 fits in uint8 for VPMADDUBSW */
            }
            uint32_t sq = (uint32_t)(relu * relu);
            act_u8[j] = (uint8_t)(sq > 255u ? 255u : sq);
        }
        for (size_t i = 0; i < d_model; ++i) {
            int32_t delta = 0;
            for (size_t j = 0; j < d_hidden; ++j) {
                delta += (int32_t)act_u8[j] * (int32_t)w2_q8[j * d_model + i];
            }
            z[i] = z[i] + (delta >> 9);
            y[i] = (y[i] + z[i]) >> 1;
        }
    }
    uint32_t y_sq = 0u;
    for (size_t i = 0; i < d_model; ++i) {
        y_sq += (uint32_t)(y[i] * y[i]);
    }
    uint32_t y_rms = lean_native_isqrt_u32(y_sq / (uint32_t)d_model + 1u);
    for (size_t c = 0; c < 4; ++c) {
        int32_t acc = 0;
        for (size_t i = 0; i < d_model; ++i) {
            int32_t y_n = (y[i] * 32) / (int32_t)y_rms;
            acc += y_n * (int32_t)w_cost_q8[i * 4 + c];
        }
        out_cost_q16[c] = acc;
    }
}

void lean_native_trm_matryoshka_cpu_int8(
    int32_t* out_cost_q16,
    const int8_t* x0_q8,
    const int8_t* w1_q8,
    const int8_t* w2_q8,
    const int8_t* w_cost_q8,
    size_t d_model,
    size_t d_hidden,
    size_t steps
) {
    if (!out_cost_q16 || !x0_q8 || !w1_q8 || !w2_q8 || !w_cost_q8 || d_model == 0 || d_model > 128 || d_hidden == 0 || d_hidden > 256) {
        return;
    }
    int32_t z[128];
    int32_t y[128];
    int32_t h_norm[128];
    uint8_t act_u8[256];
    for (size_t i = 0; i < d_model; ++i) {
        z[i] = (int32_t)x0_q8[i];
        y[i] = (int32_t)x0_q8[i];
    }
    for (size_t s = 0; s < steps; ++s) {
        uint32_t sum_sq = 0u;
        int32_t h_in[128];
        for (size_t i = 0; i < d_model; ++i) {
            h_in[i] = (13 * z[i] + 7 * (int32_t)x0_q8[i]) / 20;
            sum_sq += (uint32_t)(h_in[i] * h_in[i]);
        }
        uint32_t rms = lean_native_isqrt_u32(sum_sq / (uint32_t)d_model + 1u);
        for (size_t i = 0; i < d_model; ++i) {
            int32_t v = (h_in[i] * 32) / (int32_t)rms;
            h_norm[i] = v < -127 ? -127 : (v > 127 ? 127 : v);
        }
        for (size_t j = 0; j < d_hidden; ++j) {
            int32_t acc0 = 0, acc1 = 0, acc2 = 0, acc3 = 0;
            size_t i = 0;
            for (; i + 4 <= d_model; i += 4) {
                acc0 += h_norm[i]     * (int32_t)w1_q8[(i)     * d_hidden + j];
                acc1 += h_norm[i + 1] * (int32_t)w1_q8[(i + 1) * d_hidden + j];
                acc2 += h_norm[i + 2] * (int32_t)w1_q8[(i + 2) * d_hidden + j];
                acc3 += h_norm[i + 3] * (int32_t)w1_q8[(i + 3) * d_hidden + j];
            }
            int32_t acc = (acc0 + acc1) + (acc2 + acc3);
            for (; i < d_model; ++i) {
                acc += h_norm[i] * (int32_t)w1_q8[i * d_hidden + j];
            }
            int32_t pre = (acc >> 7) - 11;
            int32_t relu = pre > 0 ? (pre > 16 ? 16 : pre) : 0;
            uint32_t sq = (uint32_t)(relu * relu);
            act_u8[j] = (uint8_t)(sq > 255u ? 255u : sq);
        }
        for (size_t i = 0; i < d_model; ++i) {
            int32_t d0 = 0, d1 = 0, d2 = 0, d3 = 0;
            size_t j = 0;
            for (; j + 4 <= d_hidden; j += 4) {
                d0 += (int32_t)act_u8[j]     * (int32_t)w2_q8[(j)     * d_model + i];
                d1 += (int32_t)act_u8[j + 1] * (int32_t)w2_q8[(j + 1) * d_model + i];
                d2 += (int32_t)act_u8[j + 2] * (int32_t)w2_q8[(j + 2) * d_model + i];
                d3 += (int32_t)act_u8[j + 3] * (int32_t)w2_q8[(j + 3) * d_model + i];
            }
            int32_t delta = (d0 + d1) + (d2 + d3);
            for (; j < d_hidden; ++j) {
                delta += (int32_t)act_u8[j] * (int32_t)w2_q8[j * d_model + i];
            }
            z[i] = z[i] + (delta >> 9);
            y[i] = (y[i] + z[i]) >> 1;
        }
    }
    uint32_t y_sq = 0u;
    for (size_t i = 0; i < d_model; ++i) {
        y_sq += (uint32_t)(y[i] * y[i]);
    }
    uint32_t y_rms = lean_native_isqrt_u32(y_sq / (uint32_t)d_model + 1u);
    for (size_t c = 0; c < 4; ++c) {
        int32_t acc = 0;
        for (size_t i = 0; i < d_model; ++i) {
            int32_t y_n = (y[i] * 32) / (int32_t)y_rms;
            acc += y_n * (int32_t)w_cost_q8[i * 4 + c];
        }
        out_cost_q16[c] = acc;
    }
}

int lean_native_trm_matryoshka_parity_selftest(void) {
    int8_t x0[128];
    int8_t w1[128 * 256];
    int8_t w2[256 * 128];
    int8_t w_cost[128 * 4];
    for (size_t i = 0; i < 128; ++i) {
        x0[i] = (int8_t)((int32_t)((i * 37u + 11u) % 97u) - 48);
    }
    for (size_t i = 0; i < 128 * 256; ++i) {
        w1[i] = (int8_t)((int32_t)((i * 53u + 19u) % 89u) - 44);
        w2[i] = (int8_t)((int32_t)((i * 71u + 23u) % 83u) - 41);
    }
    for (size_t i = 0; i < 128 * 4; ++i) {
        w_cost[i] = (int8_t)((int32_t)((i * 29u + 7u) % 67u) - 33);
    }
    const size_t slices[4][3] = {
        {16u, 32u, 1u},   /* S_0: stage0_l1 */
        {32u, 64u, 4u},   /* S_1: cpu_l2_int8 */
        {64u, 128u, 4u},  /* S_3: spark_gb10_nvfp4 / tpu_v6e_bf16 */
        {128u, 256u, 4u}  /* S_4: tpu_v6e_s4_bf16 (Trillium 256x256 MXU) */
    };
    for (size_t s = 0; s < 4; ++s) {
        int32_t ref_out[4] = {0, 0, 0, 0};
        int32_t simd_out[4] = {0, 0, 0, 0};
        lean_native_trm_matryoshka_ref_int8(ref_out, x0, w1, w2, w_cost, slices[s][0], slices[s][1], slices[s][2]);
        lean_native_trm_matryoshka_cpu_int8(simd_out, x0, w1, w2, w_cost, slices[s][0], slices[s][1], slices[s][2]);
        for (size_t c = 0; c < 4; ++c) {
            if (ref_out[c] != simd_out[c]) {
                return 0;
            }
        }
    }
    return 1;
}

uint64_t lean_native_trm_matryoshka_parity_u64(uint64_t seed) {
    (void)seed;
    return (uint64_t)lean_native_trm_matryoshka_parity_selftest();
}

LEAN_NATIVE_WEAK int lean_native_hybrid_trm_matryoshka_int8(
    int32_t* out_cost_q16,
    const int8_t* x0_q8,
    const int8_t* w1_q8,
    const int8_t* w2_q8,
    const int8_t* w_cost_q8,
    size_t d_model,
    size_t d_hidden,
    size_t steps
) {
    if (!out_cost_q16 || !x0_q8 || !w1_q8 || !w2_q8 || !w_cost_q8) {
        return -1;
    }
    lean_native_trm_matryoshka_cpu_int8(out_cost_q16, x0_q8, w1_q8, w2_q8, w_cost_q8, d_model, d_hidden, steps);
    return 0;
}

