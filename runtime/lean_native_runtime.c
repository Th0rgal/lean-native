#include "lean_native_runtime.h"
#include <stdlib.h>
#include <string.h>
#if defined(__AVX2__)
#include <immintrin.h>
#endif
#if defined(__ARM_NEON) || defined(__ARM_NEON__)
#include <arm_neon.h>
#endif
#if defined(_OPENMP) && defined(__has_include)
#if __has_include(<omp.h>)
#include <omp.h>
#endif
#endif

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

static inline int32_t lean_native_div20_trunc(int32_t num) {
    /* Exact signed truncation division by 20 via Q19 reciprocal (|num| <= 32768) */
    uint32_t mag = (uint32_t)(num < 0 ? -num : num);
    int32_t q = (int32_t)((mag * 26215u) >> 19u);
    return num < 0 ? -q : q;
}

static inline int32_t lean_native_div_rms_trunc(int32_t num, uint32_t inv_rms_q16, int32_t rms) {
    uint32_t mag = (uint32_t)(num < 0 ? -num : num);
    int32_t q = (int32_t)((mag * inv_rms_q16) >> 16u);
    if ((int32_t)mag - q * rms >= rms) {
        q += 1;
    }
    return num < 0 ? -q : q;
}

#if defined(__AVX2__)
static inline int32_t lean_native_avx2_hsum_epi32(__m256i v) {
    __m128i lo = _mm256_castsi256_si128(v);
    __m128i hi = _mm256_extracti128_si256(v, 1);
    __m128i sum128 = _mm_add_epi32(lo, hi);
    sum128 = _mm_add_epi32(sum128, _mm_shuffle_epi32(sum128, _MM_SHUFFLE(1, 0, 3, 2)));
    sum128 = _mm_add_epi32(sum128, _mm_shuffle_epi32(sum128, _MM_SHUFFLE(2, 3, 0, 1)));
    return _mm_cvtsi128_si32(sum128);
}
#endif
#if defined(__ARM_NEON) || defined(__ARM_NEON__)
static inline int32_t lean_native_neon_dot16_s8(const int32_t* a32, const int8_t* b8) {
    int16_t a16[16];
    for (int k = 0; k < 16; ++k) a16[k] = (int16_t)a32[k];
    int16x8_t va0 = vld1q_s16(a16);
    int16x8_t va1 = vld1q_s16(a16 + 8);
    int8x16_t vb  = vld1q_s8(b8);
    int16x8_t vb0 = vmovl_s8(vget_low_s8(vb));
    int16x8_t vb1 = vmovl_s8(vget_high_s8(vb));
    int32x4_t acc = vmull_s16(vget_low_s16(va0), vget_low_s16(vb0));
    acc = vmlal_s16(acc, vget_high_s16(va0), vget_high_s16(vb0));
    acc = vmlal_s16(acc, vget_low_s16(va1), vget_low_s16(vb1));
    acc = vmlal_s16(acc, vget_high_s16(va1), vget_high_s16(vb1));
    return vaddvq_s32(acc);
}
static inline int32_t lean_native_neon_dot16_u8s8(const uint8_t* a8, const int8_t* b8) {
    uint8x16_t va = vld1q_u8(a8);
    int8x16_t  vb = vld1q_s8(b8);
    int16x8_t va0 = vreinterpretq_s16_u16(vmovl_u8(vget_low_u8(va)));
    int16x8_t va1 = vreinterpretq_s16_u16(vmovl_u8(vget_high_u8(va)));
    int16x8_t vb0 = vmovl_s8(vget_low_s8(vb));
    int16x8_t vb1 = vmovl_s8(vget_high_s8(vb));
    int32x4_t acc = vmull_s16(vget_low_s16(va0), vget_low_s16(vb0));
    acc = vmlal_s16(acc, vget_high_s16(va0), vget_high_s16(vb0));
    acc = vmlal_s16(acc, vget_low_s16(va1), vget_low_s16(vb1));
    acc = vmlal_s16(acc, vget_high_s16(va1), vget_high_s16(vb1));
    return vaddvq_s32(acc);
}
#endif

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
    uint8_t h_norm_u8[128];
    int8_t  h_norm_sign[128];
    uint8_t act_u8[256];
    int8_t  w1_col[256 * 128];
    int8_t  w2_row[128 * 256];
    for (size_t i = 0; i < d_model; ++i) {
        z[i] = (int32_t)x0_q8[i];
        y[i] = (int32_t)x0_q8[i];
        for (size_t j = 0; j < d_hidden; ++j) {
            w1_col[j * d_model + i] = w1_q8[i * d_hidden + j];
            w2_row[i * d_hidden + j] = w2_q8[j * d_model + i];
        }
    }
    for (size_t s = 0; s < steps; ++s) {
        uint32_t sum_sq = 0u;
        int32_t h_in[128];
        for (size_t i = 0; i < d_model; ++i) {
            h_in[i] = lean_native_div20_trunc(13 * z[i] + 7 * (int32_t)x0_q8[i]);
            sum_sq += (uint32_t)(h_in[i] * h_in[i]);
        }
        uint32_t rms = lean_native_isqrt_u32(sum_sq / (uint32_t)d_model + 1u);
        uint32_t inv_rms_q16 = 65536u / rms;
        for (size_t i = 0; i < d_model; ++i) {
            int32_t v = lean_native_div_rms_trunc(h_in[i] * 32, inv_rms_q16, (int32_t)rms);
            int32_t c = v < -127 ? -127 : (v > 127 ? 127 : v);
            h_norm[i] = c;
            h_norm_u8[i] = (uint8_t)(c < 0 ? -c : c);
            h_norm_sign[i] = (int8_t)(c < 0 ? -1 : (c > 0 ? 1 : 0));
        }
        for (size_t j = 0; j < d_hidden; ++j) {
            const int8_t* w1_c = &w1_col[j * d_model];
            int32_t acc = 0;
            size_t i = 0;
#if defined(__AVX2__)
            __m256i v_ones = _mm256_set1_epi16(1);
            __m256i v_acc = _mm256_setzero_si256();
            for (; i + 32 <= d_model; i += 32) {
                __m256i va_abs = _mm256_loadu_si256((const __m256i*)(h_norm_u8 + i));
                __m256i va_sgn = _mm256_loadu_si256((const __m256i*)(h_norm_sign + i));
                __m256i vw = _mm256_loadu_si256((const __m256i*)(w1_c + i));
                __m256i vw_adj = _mm256_sign_epi8(vw, va_sgn);
                __m256i prod16 = _mm256_maddubs_epi16(va_abs, vw_adj);
                v_acc = _mm256_add_epi32(v_acc, _mm256_madd_epi16(prod16, v_ones));
            }
            if (i + 16 <= d_model) {
                __m128i va_abs128 = _mm_loadu_si128((const __m128i*)(h_norm_u8 + i));
                __m128i va_sgn128 = _mm_loadu_si128((const __m128i*)(h_norm_sign + i));
                __m128i vw128 = _mm_loadu_si128((const __m128i*)(w1_c + i));
                __m128i vw_adj128 = _mm_sign_epi8(vw128, va_sgn128);
                __m128i prod16_128 = _mm_maddubs_epi16(va_abs128, vw_adj128);
                __m128i prod32_128 = _mm_madd_epi16(prod16_128, _mm_set1_epi16(1));
                v_acc = _mm256_add_epi32(v_acc, _mm256_zextsi128_si256(prod32_128));
                i += 16;
            }
            acc = lean_native_avx2_hsum_epi32(v_acc);
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
            for (; i + 16 <= d_model; i += 16) {
                acc += lean_native_neon_dot16_s8(h_norm + i, w1_c + i);
            }
#endif
            for (; i + 4 <= d_model; i += 4) {
                acc += (h_norm[i]     * (int32_t)w1_c[i] +
                        h_norm[i + 1] * (int32_t)w1_c[i + 1]) +
                       (h_norm[i + 2] * (int32_t)w1_c[i + 2] +
                        h_norm[i + 3] * (int32_t)w1_c[i + 3]);
            }
            for (; i < d_model; ++i) {
                acc += h_norm[i] * (int32_t)w1_c[i];
            }
            int32_t pre = (acc >> 7) - 11;
            int32_t relu = pre > 0 ? (pre > 16 ? 16 : pre) : 0;
            uint32_t sq = (uint32_t)(relu * relu);
            act_u8[j] = (uint8_t)(sq > 255u ? 255u : sq);
        }
        for (size_t i = 0; i < d_model; ++i) {
            const int8_t* w2_r = &w2_row[i * d_hidden];
            int32_t delta = 0;
            size_t j = 0;
#if defined(__AVX2__)
            __m256i v_ones = _mm256_set1_epi16(1);
            __m256i v_delta = _mm256_setzero_si256();
            for (; j + 32 <= d_hidden; j += 32) {
                __m256i vact = _mm256_loadu_si256((const __m256i*)(act_u8 + j));
                __m256i vw2  = _mm256_loadu_si256((const __m256i*)(w2_r + j));
                __m256i prod16 = _mm256_maddubs_epi16(vact, vw2);
                v_delta = _mm256_add_epi32(v_delta, _mm256_madd_epi16(prod16, v_ones));
            }
            delta = lean_native_avx2_hsum_epi32(v_delta);
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
            for (; j + 16 <= d_hidden; j += 16) {
                delta += lean_native_neon_dot16_u8s8(act_u8 + j, w2_r + j);
            }
#endif
            for (; j + 4 <= d_hidden; j += 4) {
                delta += ((int32_t)act_u8[j]     * (int32_t)w2_r[j] +
                          (int32_t)act_u8[j + 1] * (int32_t)w2_r[j + 1]) +
                         ((int32_t)act_u8[j + 2] * (int32_t)w2_r[j + 2] +
                          (int32_t)act_u8[j + 3] * (int32_t)w2_r[j + 3]);
            }
            for (; j < d_hidden; ++j) {
                delta += (int32_t)act_u8[j] * (int32_t)w2_r[j];
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
    uint32_t inv_y_rms_q16 = 65536u / y_rms;
    for (size_t c = 0; c < 4; ++c) {
        int32_t acc = 0;
        for (size_t i = 0; i < d_model; ++i) {
            int32_t y_n = lean_native_div_rms_trunc(y[i] * 32, inv_y_rms_q16, (int32_t)y_rms);
            acc += y_n * (int32_t)w_cost_q8[i * 4 + c];
        }
        out_cost_q16[c] = acc;
    }
}

void lean_native_trm_ctx_init(lean_native_trm_ctx* ctx, const int8_t* x0_q8) {
    if (!ctx || !x0_q8) {
        return;
    }
    ctx->d_populated = 0u;
    ctx->h_populated = 0u;
    ctx->sum_sq_prefix = 0u;
    for (size_t i = 0; i < 128u; ++i) {
        ctx->z[i] = (int32_t)x0_q8[i];
        ctx->y[i] = (int32_t)x0_q8[i];
        ctx->h_in[i] = lean_native_div20_trunc(20 * (int32_t)x0_q8[i]);
    }
}

void lean_native_trm_ctx_step_incremental_int8(
    lean_native_trm_ctx* ctx,
    int32_t* out_cost_q16,
    const int8_t* x0_q8,
    const int8_t* w1_q8,
    const int8_t* w2_q8,
    const int8_t* w_cost_q8,
    size_t d_model,
    size_t d_hidden,
    size_t steps
) {
    if (!ctx || !out_cost_q16 || !x0_q8 || !w1_q8 || !w2_q8 || !w_cost_q8 ||
        d_model == 0 || d_model > 128 || d_hidden == 0 || d_hidden > 256) {
        return;
    }
    /* Step 0 incremental sum-of-squares prefix reuse (`combineSliceSumSq`) */
    size_t d_start = (ctx->d_populated <= d_model) ? ctx->d_populated : 0u;
    uint32_t sum_sq0 = (d_start > 0u) ? ctx->sum_sq_prefix : 0u;
    for (size_t i = 0; i < d_model; ++i) {
        ctx->z[i] = (int32_t)x0_q8[i];
        ctx->y[i] = (int32_t)x0_q8[i];
        ctx->h_in[i] = (int32_t)x0_q8[i];
    }
    for (size_t i = d_start; i < d_model; ++i) {
        sum_sq0 += (uint32_t)(ctx->h_in[i] * ctx->h_in[i]);
    }
    ctx->sum_sq_prefix = sum_sq0;
    ctx->d_populated = d_model;
    ctx->h_populated = d_hidden;

    int8_t w1_col[256 * 128];
    int8_t w2_row[128 * 256];
    for (size_t i = 0; i < d_model; ++i) {
        for (size_t j = 0; j < d_hidden; ++j) {
            w1_col[j * d_model + i] = w1_q8[i * d_hidden + j];
            w2_row[i * d_hidden + j] = w2_q8[j * d_model + i];
        }
    }

    for (size_t s = 0; s < steps; ++s) {
        uint32_t sum_sq = sum_sq0;
        if (s > 0u) {
            sum_sq = 0u;
            for (size_t i = 0; i < d_model; ++i) {
                ctx->h_in[i] = lean_native_div20_trunc(13 * ctx->z[i] + 7 * (int32_t)x0_q8[i]);
                sum_sq += (uint32_t)(ctx->h_in[i] * ctx->h_in[i]);
            }
        }
        uint32_t rms = lean_native_isqrt_u32(sum_sq / (uint32_t)d_model + 1u);
        uint32_t inv_rms_q16 = 65536u / rms;
        for (size_t i = 0; i < d_model; ++i) {
            int32_t v = lean_native_div_rms_trunc(ctx->h_in[i] * 32, inv_rms_q16, (int32_t)rms);
            int32_t c = v < -127 ? -127 : (v > 127 ? 127 : v);
            ctx->h_norm[i] = c;
            ctx->h_norm_u8[i] = (uint8_t)(c < 0 ? -c : c);
            ctx->h_norm_sign[i] = (int8_t)(c < 0 ? -1 : (c > 0 ? 1 : 0));
        }
        for (size_t j = 0; j < d_hidden; ++j) {
            const int8_t* w1_c = &w1_col[j * d_model];
            int32_t acc = 0;
            size_t i = 0;
#if defined(__AVX2__)
            __m256i v_ones = _mm256_set1_epi16(1);
            __m256i v_acc = _mm256_setzero_si256();
            for (; i + 32 <= d_model; i += 32) {
                __m256i va_abs = _mm256_loadu_si256((const __m256i*)(ctx->h_norm_u8 + i));
                __m256i va_sgn = _mm256_loadu_si256((const __m256i*)(ctx->h_norm_sign + i));
                __m256i vw = _mm256_loadu_si256((const __m256i*)(w1_c + i));
                __m256i vw_adj = _mm256_sign_epi8(vw, va_sgn);
                __m256i prod16 = _mm256_maddubs_epi16(va_abs, vw_adj);
                v_acc = _mm256_add_epi32(v_acc, _mm256_madd_epi16(prod16, v_ones));
            }
            if (i + 16 <= d_model) {
                __m128i va_abs128 = _mm_loadu_si128((const __m128i*)(ctx->h_norm_u8 + i));
                __m128i va_sgn128 = _mm_loadu_si128((const __m128i*)(ctx->h_norm_sign + i));
                __m128i vw128 = _mm_loadu_si128((const __m128i*)(w1_c + i));
                __m128i vw_adj128 = _mm_sign_epi8(vw128, va_sgn128);
                __m128i prod16_128 = _mm_maddubs_epi16(va_abs128, vw_adj128);
                __m128i prod32_128 = _mm_madd_epi16(prod16_128, _mm_set1_epi16(1));
                v_acc = _mm256_add_epi32(v_acc, _mm256_zextsi128_si256(prod32_128));
                i += 16;
            }
            acc = lean_native_avx2_hsum_epi32(v_acc);
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
            for (; i + 16 <= d_model; i += 16) {
                acc += lean_native_neon_dot16_s8(ctx->h_norm + i, w1_c + i);
            }
#endif
            for (; i + 4 <= d_model; i += 4) {
                acc += (ctx->h_norm[i]     * (int32_t)w1_c[i] +
                        ctx->h_norm[i + 1] * (int32_t)w1_c[i + 1]) +
                       (ctx->h_norm[i + 2] * (int32_t)w1_c[i + 2] +
                        ctx->h_norm[i + 3] * (int32_t)w1_c[i + 3]);
            }
            for (; i < d_model; ++i) {
                acc += ctx->h_norm[i] * (int32_t)w1_c[i];
            }
            ctx->w1_dot_prefix[j] = acc;
            int32_t pre = (acc >> 7) - 11;
            int32_t relu = pre > 0 ? (pre > 16 ? 16 : pre) : 0;
            uint32_t sq = (uint32_t)(relu * relu);
            ctx->act_u8[j] = (uint8_t)(sq > 255u ? 255u : sq);
        }
        for (size_t i = 0; i < d_model; ++i) {
            const int8_t* w2_r = &w2_row[i * d_hidden];
            int32_t delta = 0;
            size_t j = 0;
#if defined(__AVX2__)
            __m256i v_ones = _mm256_set1_epi16(1);
            __m256i v_delta = _mm256_setzero_si256();
            for (; j + 32 <= d_hidden; j += 32) {
                __m256i vact = _mm256_loadu_si256((const __m256i*)(ctx->act_u8 + j));
                __m256i vw2  = _mm256_loadu_si256((const __m256i*)(w2_r + j));
                __m256i prod16 = _mm256_maddubs_epi16(vact, vw2);
                v_delta = _mm256_add_epi32(v_delta, _mm256_madd_epi16(prod16, v_ones));
            }
            delta = lean_native_avx2_hsum_epi32(v_delta);
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
            for (; j + 16 <= d_hidden; j += 16) {
                delta += lean_native_neon_dot16_u8s8(ctx->act_u8 + j, w2_r + j);
            }
#endif
            for (; j + 4 <= d_hidden; j += 4) {
                delta += ((int32_t)ctx->act_u8[j]     * (int32_t)w2_r[j] +
                          (int32_t)ctx->act_u8[j + 1] * (int32_t)w2_r[j + 1]) +
                         ((int32_t)ctx->act_u8[j + 2] * (int32_t)w2_r[j + 2] +
                          (int32_t)ctx->act_u8[j + 3] * (int32_t)w2_r[j + 3]);
            }
            for (; j < d_hidden; ++j) {
                delta += (int32_t)ctx->act_u8[j] * (int32_t)w2_r[j];
            }
            ctx->z[i] = ctx->z[i] + (delta >> 9);
            ctx->y[i] = (ctx->y[i] + ctx->z[i]) >> 1;
        }
    }
    uint32_t y_sq = 0u;
    for (size_t i = 0; i < d_model; ++i) {
        y_sq += (uint32_t)(ctx->y[i] * ctx->y[i]);
    }
    uint32_t y_rms = lean_native_isqrt_u32(y_sq / (uint32_t)d_model + 1u);
    uint32_t inv_y_rms_q16 = 65536u / y_rms;
    for (size_t c = 0; c < 4; ++c) {
        int32_t acc = 0;
        for (size_t i = 0; i < d_model; ++i) {
            int32_t y_n = lean_native_div_rms_trunc(ctx->y[i] * 32, inv_y_rms_q16, (int32_t)y_rms);
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
    lean_native_trm_ctx ctx;
    lean_native_trm_ctx_init(&ctx, x0);
    for (size_t s = 0; s < 4; ++s) {
        int32_t ref_out[4] = {0, 0, 0, 0};
        int32_t simd_out[4] = {0, 0, 0, 0};
        int32_t inc_out[4] = {0, 0, 0, 0};
        lean_native_trm_matryoshka_ref_int8(ref_out, x0, w1, w2, w_cost, slices[s][0], slices[s][1], slices[s][2]);
        lean_native_trm_matryoshka_cpu_int8(simd_out, x0, w1, w2, w_cost, slices[s][0], slices[s][1], slices[s][2]);
        lean_native_trm_ctx_step_incremental_int8(&ctx, inc_out, x0, w1, w2, w_cost, slices[s][0], slices[s][1], slices[s][2]);
        for (size_t c = 0; c < 4; ++c) {
            if (ref_out[c] != simd_out[c] || ref_out[c] != inc_out[c]) {
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

static inline uint64_t lean_native_splitmix64_step(uint64_t z) {
    z += 0x9E3779B97F4A7C15ULL;
    z = (z ^ (z >> 30u)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27u)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31u);
}

int lean_native_verify_indexed_witness_recert(
    uint64_t base_seed,
    uint64_t goal_idx,
    uint64_t sample_idx,
    const int32_t* rpn_opcodes,
    uint64_t arg0,
    uint64_t arg1
) {
    if (!rpn_opcodes || sample_idx == UINT64_MAX) {
        return 0;
    }
    uint64_t g_seed = base_seed ^ (goal_idx * 0x9E3779B97F4A7C15ULL);
    uint64_t x1 = lean_native_splitmix64_step(g_seed + sample_idx * 0x9E3779B97F4A7C15ULL);
    uint64_t x0 = x1 + arg0;
    uint64_t acc = x0;
    int violated = 0;
    for (size_t pc = 0; pc < 16u; ++pc) {
        int32_t op = rpn_opcodes[pc];
        if (op == 0) {
            break;
        } else if (op == 1) {
            acc = acc + x1 + arg0;
        } else if (op == 2) {
            acc = (acc >= x1) ? (acc - x1) : 0ULL;
        } else if (op == 3) {
            acc = acc * (x1 | 1ULL);
        } else if (op == 7) {
            if (x1 >= arg1 && x0 >= arg1) {
                violated = 1;
            }
        } else if (op == 8) {
            uint64_t sum_lo = x0 + x1;
            uint64_t carry = (sum_lo < x0) ? 1ULL : 0ULL;
            acc = sum_lo ^ carry;
        } else if (op == 15) {
            uint64_t rot = (acc << 1u) | (acc >> 63u);
            acc ^= rot ^ 0xA5A5A5A55A5A5A5AULL;
        }
    }
    return violated;
}

int lean_native_rpn_u256_fastcheck_goal(
    uint64_t base_seed,
    uint64_t goal_idx,
    size_t n_samples,
    const int32_t* rpn_opcodes,
    uint64_t arg0,
    uint64_t arg1,
    uint64_t* out_min_sample_idx
) {
    if (out_min_sample_idx) {
        *out_min_sample_idx = UINT64_MAX;
    }
    if (!rpn_opcodes || n_samples == 0) {
        return 0;
    }
    for (size_t s = 0; s < n_samples; ++s) {
        if (lean_native_verify_indexed_witness_recert(base_seed, goal_idx, (uint64_t)s, rpn_opcodes, arg0, arg1)) {
            if (out_min_sample_idx) {
                *out_min_sample_idx = (uint64_t)s;
            }
            return 1;
        }
    }
    return 0;
}

static inline int lean_native_ablate_skip_s1(void) {
    static int s_skip = -1;
    int v = __atomic_load_n(&s_skip, __ATOMIC_RELAXED);
    if (v >= 0) return v;
    const char* env = getenv("LEAN_NATIVE_ABLATE_SKIP_S1");
    v = (env && strcmp(env, "1") == 0) ? 1 : 0;
    __atomic_store_n(&s_skip, v, __ATOMIC_RELAXED);
    return v;
}

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
) {
    if (!out_cost_q16 || !out_survival_permille || !out_router_action || !out_effective_tier ||
        !x0_q8 || !w1_q8 || !w2_q8 || !w_cost_q8) {
        return;
    }
    /* Stage 0: S_0 (16x32, H=1, L=1) in L1D cache (< 24 KiB) via stateful prefix context */
    lean_native_trm_ctx ctx;
    lean_native_trm_ctx_init(&ctx, x0_q8);
    int32_t cost_s0[4] = {0, 0, 0, 0};
    lean_native_trm_ctx_step_incremental_int8(&ctx, cost_s0, x0_q8, w1_q8, w2_q8, w_cost_q8, 16u, 32u, 1u);
    int32_t surv_s0 = 500 + (cost_s0[3] >> 4);
    if (surv_s0 < 0) surv_s0 = 0;
    if (surv_s0 > 1000) surv_s0 = 1000;

    /* Early-exit pass or prune outside the [prune_floor - eps, escalate_band + eps] uncertainty band */
    if (surv_s0 + eps_tier_permille < prune_floor_permille) {
        for (size_t c = 0; c < 4; ++c) out_cost_q16[c] = cost_s0[c];
        *out_survival_permille = surv_s0;
        *out_router_action = 1u; /* prune_stop */
        *out_effective_tier = LEAN_NATIVE_TIER_S0_CPU_L1;
        return;
    }
    if (surv_s0 >= escalate_band_permille + eps_tier_permille) {
        for (size_t c = 0; c < 4; ++c) out_cost_q16[c] = cost_s0[c];
        *out_survival_permille = surv_s0;
        *out_router_action = 0u; /* pass */
        *out_effective_tier = LEAN_NATIVE_TIER_S0_CPU_L1;
        return;
    }

    if (!lean_native_ablate_skip_s1()) {
        /* Stage 1 escalation: S_1 (32x64, H=2, L=2) in L2 cache (< 96 KiB), reusing S_0 sum_sq_prefix */
        int32_t cost_s1[4] = {0, 0, 0, 0};
        lean_native_trm_ctx_step_incremental_int8(&ctx, cost_s1, x0_q8, w1_q8, w2_q8, w_cost_q8, 32u, 64u, 4u);
        int32_t surv_s1 = 500 + (cost_s1[3] >> 4);
        if (surv_s1 < 0) surv_s1 = 0;
        if (surv_s1 > 1000) surv_s1 = 1000;

        if (surv_s1 + eps_tier_permille < prune_floor_permille) {
            for (size_t c = 0; c < 4; ++c) out_cost_q16[c] = cost_s1[c];
            *out_survival_permille = surv_s1;
            *out_router_action = 1u; /* prune_stop */
            *out_effective_tier = LEAN_NATIVE_TIER_S1_CPU_L2;
            return;
        }
        if (surv_s1 >= escalate_band_permille + eps_tier_permille) {
            for (size_t c = 0; c < 4; ++c) out_cost_q16[c] = cost_s1[c];
            *out_survival_permille = surv_s1;
            *out_router_action = 0u; /* pass */
            *out_effective_tier = LEAN_NATIVE_TIER_S1_CPU_L2;
            return;
        }
    }

    /* Stage 2 escalation: S_3 (64x128, H=2, L=2), reusing S_1 sum_sq_prefix */
    int32_t cost_s3[4] = {0, 0, 0, 0};
    lean_native_trm_ctx_step_incremental_int8(&ctx, cost_s3, x0_q8, w1_q8, w2_q8, w_cost_q8, 64u, 128u, 4u);
    int32_t surv_s3 = 500 + (cost_s3[3] >> 4);
    if (surv_s3 < 0) surv_s3 = 0;
    if (surv_s3 > 1000) surv_s3 = 1000;

    for (size_t c = 0; c < 4; ++c) out_cost_q16[c] = cost_s3[c];
    *out_survival_permille = surv_s3;
    *out_effective_tier = LEAN_NATIVE_TIER_S3_SPARK_CUDA;
    if (surv_s3 + eps_tier_permille < prune_floor_permille) {
        *out_router_action = 1u; /* prune_stop */
    } else if (surv_s3 < escalate_band_permille + eps_tier_permille ||
               surv_s3 < prune_floor_permille + eps_tier_permille) {
        *out_router_action = 2u; /* abstain_escalate */
    } else {
        *out_router_action = 0u; /* pass */
    }
}

LEAN_NATIVE_WEAK int lean_native_speculate_forest(
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
) {
    if (!rpn_opcodes || !rpn_arg0 || !rpn_arg1 || !x0_q8 || !w1_q8 || !w2_q8 || !w_cost_q8 ||
        !out_cex_found || !out_min_sample_idx || !out_survival_permille || !out_router_action || !out_effective_tier) {
        return -1;
    }
#if defined(_OPENMP)
#pragma omp parallel for schedule(static) if(n_goals > 1)
#endif
    for (size_t g = 0; g < n_goals; ++g) {
        uint64_t min_idx = UINT64_MAX;
        int cex = lean_native_rpn_u256_fastcheck_goal(
            base_seed,
            (uint64_t)g,
            n_samples,
            rpn_opcodes + g * 16u,
            rpn_arg0[g],
            rpn_arg1[g],
            &min_idx
        );
        int recert_ok = cex ? lean_native_verify_indexed_witness_recert(
            base_seed,
            (uint64_t)g,
            min_idx,
            rpn_opcodes + g * 16u,
            rpn_arg0[g],
            rpn_arg1[g]
        ) : 0;
        out_cex_found[g] = (uint8_t)(recert_ok ? 1u : 0u);
        out_min_sample_idx[g] = recert_ok ? min_idx : UINT64_MAX;
        if (recert_ok) {
            out_survival_permille[g] = 0;
            out_router_action[g] = 1u; /* prune_stop */
            out_effective_tier[g] = LEAN_NATIVE_TIER_S0_CPU_L1;
        } else {
            int32_t cost_q16[4] = {0, 0, 0, 0};
            lean_native_trm_matryoshka_cascade_int8(
                cost_q16,
                &out_survival_permille[g],
                &out_router_action[g],
                &out_effective_tier[g],
                x0_q8 + g * 128u,
                w1_q8,
                w2_q8,
                w_cost_q8,
                prune_floor_permille,
                escalate_band_permille,
                eps_tier_permille
            );
        }
    }
    return 0;
}

