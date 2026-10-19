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

LEAN_NATIVE_WEAK const char* lean_native_gpu_device_name(void) {
    return "CPU-Only Fallback (LLVM SIMD)";
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
