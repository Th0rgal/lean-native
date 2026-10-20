#include "lean_native_runtime.h"
#include "generated_kernels.ptx.h"
#include <cuda.h>
#include <cuda_runtime.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ============================================================================
 * Global CUDA Driver / Grace-Blackwell Unified Memory Context State
 * ============================================================================ */

#define MATMUL_TILE_DIM 16
#define ZERO_COPY_MIN_ELEMS 65536ULL
#define ZERO_COPY_MAX_ELEMS 1048576ULL

typedef struct LeanNativeCudaState {
    int          initialized;
    int          available;
    int          can_map_host_memory;
    int          device_id;
    char         device_name[320];
    CUdevice     cu_device;
    CUcontext    cu_context;
    CUmodule     default_module;
    CUmodule     custom_module;
    cudaStream_t stream;
    /* Dynamic PTX JIT compilation & launch telemetry */
    uint64_t     ptx_kernels_loaded;
    uint64_t     ptx_kernel_launches;
    /* Reusable device/unified workspace buffers to avoid per-call allocation overhead */
    uint64_t*    d_buf0;
    uint64_t*    d_buf1;
    uint64_t*    d_buf2;
    size_t       buf_capacity_elems;
    /* Grace-Blackwell Zero-Copy Mapped Host Workspace (cudaHostAllocMapped) */
    uint64_t*    h_mapped0;
    uint64_t*    h_mapped1;
    uint64_t*    h_mapped2;
    uint64_t*    d_mapped0;
    uint64_t*    d_mapped1;
    uint64_t*    d_mapped2;
    size_t       mapped_capacity_elems;
} LeanNativeCudaState;

static LeanNativeCudaState g_cuda_state = {0};

static char* lean_native_read_ptx_file(const char* path) {
    if (!path || path[0] == '\0') {
        return NULL;
    }
    FILE* f = fopen(path, "rb");
    if (!f) {
        return NULL;
    }
    if (fseek(f, 0, SEEK_END) != 0) {
        fclose(f);
        return NULL;
    }
    long sz = ftell(f);
    if (sz <= 0 || fseek(f, 0, SEEK_SET) != 0) {
        fclose(f);
        return NULL;
    }
    char* buf = (char*)malloc((size_t)sz + 1);
    if (!buf) {
        fclose(f);
        return NULL;
    }
    size_t nread = fread(buf, 1, (size_t)sz, f);
    fclose(f);
    if (nread != (size_t)sz) {
        free(buf);
        return NULL;
    }
    buf[sz] = '\0';
    return buf;
}

static uint64_t lean_native_count_module_kernels(CUmodule mod) {
    static const char* kBuiltinSymbols[] = {
        "lean_native_kernel_map_scale_add",
        "lean_native_kernel_zip_add",
        "lean_native_kernel_zip_mul",
        "lean_native_kernel_saxpy",
        "lean_native_kernel_stencil1d",
        "lean_native_kernel_dot_reduce_u64",
        "lean_native_kernel_matmul_tiled_u64",
        "lean_native_kernel_saxpy_f64",
        "lean_native_kernel_map_scale_add_f64",
        "lean_native_kernel_fma_f32",
        "lean_native_decl_sarray_scale_bias",
        "lean_native_decl_saxpy_kernel",
        "lean_native_decl_matmul_tiled_u64",
        "lean_native_decl_dot_product_u64"
    };
    uint64_t count = 0;
    size_t num_syms = sizeof(kBuiltinSymbols) / sizeof(kBuiltinSymbols[0]);
    for (size_t i = 0; i < num_syms; ++i) {
        CUfunction fn = NULL;
        if (cuModuleGetFunction(&fn, mod, kBuiltinSymbols[i]) == CUDA_SUCCESS && fn != NULL) {
            count += 1;
        }
    }
    return count > 0 ? count : 1ULL;
}

static int lean_native_ensure_cuda_initialized(void) {
    if (g_cuda_state.initialized) {
        return g_cuda_state.available;
    }
    g_cuda_state.initialized = 1;
    g_cuda_state.available   = 0;
    snprintf(g_cuda_state.device_name, sizeof(g_cuda_state.device_name), "CPU-Only Fallback");

    if (cuInit(0) != CUDA_SUCCESS) {
        return 0;
    }
    int dev_count = 0;
    if (cudaGetDeviceCount(&dev_count) != cudaSuccess || dev_count <= 0) {
        return 0;
    }
    if (cudaSetDevice(0) != cudaSuccess) {
        return 0;
    }
    cudaDeviceProp prop;
    if (cudaGetDeviceProperties(&prop, 0) == cudaSuccess) {
        g_cuda_state.can_map_host_memory = prop.canMapHostMemory ? 1 : 0;
        snprintf(
            g_cuda_state.device_name,
            sizeof(g_cuda_state.device_name),
            "%.240s (sm_%d%d)",
            prop.name,
            prop.major,
            prop.minor
        );
    }
    if (cuDeviceGet(&g_cuda_state.cu_device, 0) != CUDA_SUCCESS) {
        return 0;
    }
    if (cuDevicePrimaryCtxRetain(&g_cuda_state.cu_context, g_cuda_state.cu_device) != CUDA_SUCCESS) {
        return 0;
    }
    if (cuCtxSetCurrent(g_cuda_state.cu_context) != CUDA_SUCCESS) {
        return 0;
    }
    if (cudaStreamCreateWithFlags(&g_cuda_state.stream, cudaStreamNonBlocking) != cudaSuccess) {
        g_cuda_state.stream = 0;
    }

    const char* env_ptx_path = getenv("LEAN_NATIVE_PTX_PATH");
    char* file_ptx = lean_native_read_ptx_file(env_ptx_path);
    const char* ptx_to_load = file_ptx ? file_ptx : EMBEDDED_PTX_MODULE;

    CUresult res = cuModuleLoadDataEx(
        &g_cuda_state.default_module,
        (const void*)ptx_to_load,
        0,
        NULL,
        NULL
    );
    if (file_ptx) {
        free(file_ptx);
    }
    if (res != CUDA_SUCCESS) {
        fprintf(stderr, "[lean_native_cuda] cuModuleLoadDataEx failed with CUresult=%d\n", (int)res);
        return 0;
    }

    g_cuda_state.ptx_kernels_loaded += lean_native_count_module_kernels(g_cuda_state.default_module);
    g_cuda_state.available = 1;
    return 1;
}

static int lean_native_ensure_workspace(size_t n_elems) {
    size_t req_elems = n_elems > 0 ? n_elems : 1;
    if (req_elems <= g_cuda_state.buf_capacity_elems &&
        g_cuda_state.d_buf0 && g_cuda_state.d_buf1 && g_cuda_state.d_buf2) {
        return 0;
    }
    if (g_cuda_state.d_buf0) { cudaFree(g_cuda_state.d_buf0); g_cuda_state.d_buf0 = NULL; }
    if (g_cuda_state.d_buf1) { cudaFree(g_cuda_state.d_buf1); g_cuda_state.d_buf1 = NULL; }
    if (g_cuda_state.d_buf2) { cudaFree(g_cuda_state.d_buf2); g_cuda_state.d_buf2 = NULL; }

    size_t bytes = req_elems * sizeof(uint64_t);
    if (cudaMalloc((void**)&g_cuda_state.d_buf0, bytes) != cudaSuccess ||
        cudaMalloc((void**)&g_cuda_state.d_buf1, bytes) != cudaSuccess ||
        cudaMalloc((void**)&g_cuda_state.d_buf2, bytes) != cudaSuccess) {
        if (g_cuda_state.d_buf0) { cudaFree(g_cuda_state.d_buf0); g_cuda_state.d_buf0 = NULL; }
        if (g_cuda_state.d_buf1) { cudaFree(g_cuda_state.d_buf1); g_cuda_state.d_buf1 = NULL; }
        if (g_cuda_state.d_buf2) { cudaFree(g_cuda_state.d_buf2); g_cuda_state.d_buf2 = NULL; }
        g_cuda_state.buf_capacity_elems = 0;
        return -1;
    }
    g_cuda_state.buf_capacity_elems = req_elems;
    return 0;
}

static int lean_native_ensure_zero_copy_workspace(size_t n_elems) {
    if (!g_cuda_state.can_map_host_memory ||
        n_elems < ZERO_COPY_MIN_ELEMS ||
        n_elems > ZERO_COPY_MAX_ELEMS) {
        return -1;
    }
    if (n_elems <= g_cuda_state.mapped_capacity_elems &&
        g_cuda_state.h_mapped0 && g_cuda_state.h_mapped1 && g_cuda_state.h_mapped2) {
        return 0;
    }
    if (g_cuda_state.h_mapped0) { cudaFreeHost(g_cuda_state.h_mapped0); g_cuda_state.h_mapped0 = NULL; }
    if (g_cuda_state.h_mapped1) { cudaFreeHost(g_cuda_state.h_mapped1); g_cuda_state.h_mapped1 = NULL; }
    if (g_cuda_state.h_mapped2) { cudaFreeHost(g_cuda_state.h_mapped2); g_cuda_state.h_mapped2 = NULL; }

    size_t bytes = n_elems * sizeof(uint64_t);
    unsigned int flags = cudaHostAllocMapped;
    if (cudaHostAlloc((void**)&g_cuda_state.h_mapped0, bytes, flags) != cudaSuccess ||
        cudaHostAlloc((void**)&g_cuda_state.h_mapped1, bytes, flags) != cudaSuccess ||
        cudaHostAlloc((void**)&g_cuda_state.h_mapped2, bytes, flags) != cudaSuccess ||
        cudaHostGetDevicePointer((void**)&g_cuda_state.d_mapped0, g_cuda_state.h_mapped0, 0) != cudaSuccess ||
        cudaHostGetDevicePointer((void**)&g_cuda_state.d_mapped1, g_cuda_state.h_mapped1, 0) != cudaSuccess ||
        cudaHostGetDevicePointer((void**)&g_cuda_state.d_mapped2, g_cuda_state.h_mapped2, 0) != cudaSuccess) {
        if (g_cuda_state.h_mapped0) { cudaFreeHost(g_cuda_state.h_mapped0); g_cuda_state.h_mapped0 = NULL; }
        if (g_cuda_state.h_mapped1) { cudaFreeHost(g_cuda_state.h_mapped1); g_cuda_state.h_mapped1 = NULL; }
        if (g_cuda_state.h_mapped2) { cudaFreeHost(g_cuda_state.h_mapped2); g_cuda_state.h_mapped2 = NULL; }
        g_cuda_state.mapped_capacity_elems = 0;
        return -1;
    }
    g_cuda_state.mapped_capacity_elems = n_elems;
    return 0;
}

/* ============================================================================
 * Public C ABI Implementation
 * ============================================================================ */

extern "C" int lean_native_gpu_available(void) {
    return lean_native_ensure_cuda_initialized();
}

extern "C" const char* lean_native_gpu_device_name(void) {
    lean_native_ensure_cuda_initialized();
    return g_cuda_state.device_name;
}

extern "C" void lean_native_ptx_jit_stats(
    uint64_t* out_kernels_loaded,
    uint64_t* out_launches
) {
    lean_native_ensure_cuda_initialized();
    if (out_kernels_loaded) {
        *out_kernels_loaded = g_cuda_state.ptx_kernels_loaded;
    }
    if (out_launches) {
        *out_launches = g_cuda_state.ptx_kernel_launches;
    }
}

extern "C" int lean_native_register_ptx_module(const char* ptx_source) {
    if (!ptx_source || !lean_native_ensure_cuda_initialized()) {
        return -1;
    }
    if (g_cuda_state.custom_module) {
        cuModuleUnload(g_cuda_state.custom_module);
        g_cuda_state.custom_module = NULL;
    }
    CUresult res = cuModuleLoadDataEx(
        &g_cuda_state.custom_module,
        (const void*)ptx_source,
        0,
        NULL,
        NULL
    );
    if (res != CUDA_SUCCESS) {
        return -1;
    }
    g_cuda_state.ptx_kernels_loaded += lean_native_count_module_kernels(g_cuda_state.custom_module);
    return 0;
}

extern "C" int lean_native_launch_ptx_kernel_2d(
    const char* kernel_name,
    void** kernel_params,
    unsigned int grid_x,
    unsigned int grid_y,
    unsigned int block_x,
    unsigned int block_y
) {
    if (!kernel_name || !kernel_params || grid_x == 0 || grid_y == 0 || block_x == 0 || block_y == 0) {
        return -1;
    }
    if (!lean_native_ensure_cuda_initialized()) {
        return -1;
    }
    CUfunction fn = NULL;
    CUresult res = CUDA_ERROR_NOT_FOUND;
    if (g_cuda_state.custom_module) {
        res = cuModuleGetFunction(&fn, g_cuda_state.custom_module, kernel_name);
    }
    if (res != CUDA_SUCCESS && g_cuda_state.default_module) {
        res = cuModuleGetFunction(&fn, g_cuda_state.default_module, kernel_name);
    }
    if (res != CUDA_SUCCESS || !fn) {
        return -1;
    }

    res = cuLaunchKernel(
        fn,
        grid_x, grid_y, 1,
        block_x, block_y, 1,
        0,
        g_cuda_state.stream,
        kernel_params,
        NULL
    );
    if (res != CUDA_SUCCESS) {
        return -1;
    }
    if (cudaStreamSynchronize(g_cuda_state.stream) != cudaSuccess) {
        return -1;
    }
    g_cuda_state.ptx_kernel_launches += 1;
    return 0;
}

extern "C" int lean_native_launch_ptx_kernel(
    const char* kernel_name,
    void** kernel_params,
    size_t num_elements
) {
    if (!kernel_name || !kernel_params || num_elements == 0) {
        return -1;
    }
    unsigned int block_dim = 256;
    unsigned int grid_dim  = (unsigned int)((num_elements + block_dim - 1) / block_dim);
    return lean_native_launch_ptx_kernel_2d(
        kernel_name,
        kernel_params,
        grid_dim, 1,
        block_dim, 1
    );
}

extern "C" int lean_native_hybrid_saxpy_u64(
    uint64_t* out,
    const uint64_t* x,
    const uint64_t* y,
    uint64_t alpha,
    size_t n
) {
    if (!out || !x || !y) {
        return -1;
    }
    if (n == 0) {
        return 0;
    }
    if (lean_native_ensure_cuda_initialized()) {
        size_t bytes = n * sizeof(uint64_t);
        if (lean_native_ensure_zero_copy_workspace(n) == 0) {
            memcpy(g_cuda_state.h_mapped1, x, bytes);
            memcpy(g_cuda_state.h_mapped2, y, bytes);
            uint64_t n_u64 = (uint64_t)n;
            void* params[5] = {
                &g_cuda_state.d_mapped0,
                &g_cuda_state.d_mapped1,
                &g_cuda_state.d_mapped2,
                &alpha,
                &n_u64
            };
            if (lean_native_launch_ptx_kernel("lean_native_kernel_saxpy", params, n) == 0) {
                memcpy(out, g_cuda_state.h_mapped0, bytes);
                return 0;
            }
        }
        if (lean_native_ensure_workspace(n) == 0) {
            cudaMemcpyAsync(g_cuda_state.d_buf1, x, bytes, cudaMemcpyHostToDevice, g_cuda_state.stream);
            cudaMemcpyAsync(g_cuda_state.d_buf2, y, bytes, cudaMemcpyHostToDevice, g_cuda_state.stream);
            uint64_t n_u64 = (uint64_t)n;
            void* params[5] = {
                &g_cuda_state.d_buf0,
                &g_cuda_state.d_buf1,
                &g_cuda_state.d_buf2,
                &alpha,
                &n_u64
            };
            if (lean_native_launch_ptx_kernel("lean_native_kernel_saxpy", params, n) == 0) {
                cudaMemcpyAsync(out, g_cuda_state.d_buf0, bytes, cudaMemcpyDeviceToHost, g_cuda_state.stream);
                if (cudaStreamSynchronize(g_cuda_state.stream) == cudaSuccess) {
                    return 0;
                }
            }
        }
    }
    lean_native_cpu_saxpy_u64(out, x, y, alpha, n);
    return 0;
}

extern "C" int lean_native_hybrid_map_scale_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    uint64_t scale,
    uint64_t bias,
    size_t n
) {
    if (!out || !in0) {
        return -1;
    }
    if (n == 0) {
        return 0;
    }
    if (lean_native_ensure_cuda_initialized()) {
        if (lean_native_ensure_workspace(n) == 0) {
            size_t bytes = n * sizeof(uint64_t);
            cudaMemcpyAsync(g_cuda_state.d_buf1, in0, bytes, cudaMemcpyHostToDevice, g_cuda_state.stream);
            uint64_t n_u64 = (uint64_t)n;
            void* params[5] = {
                &g_cuda_state.d_buf0,
                &g_cuda_state.d_buf1,
                &scale,
                &bias,
                &n_u64
            };
            if (lean_native_launch_ptx_kernel("lean_native_kernel_map_scale_add", params, n) == 0) {
                cudaMemcpyAsync(out, g_cuda_state.d_buf0, bytes, cudaMemcpyDeviceToHost, g_cuda_state.stream);
                if (cudaStreamSynchronize(g_cuda_state.stream) == cudaSuccess) {
                    return 0;
                }
            }
        }
    }
    lean_native_cpu_map_scale_add_u64(out, in0, scale, bias, n);
    return 0;
}

extern "C" int lean_native_hybrid_zip_add_u64(
    uint64_t* out,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
) {
    if (!out || !in0 || !in1) {
        return -1;
    }
    if (n == 0) {
        return 0;
    }
    if (lean_native_ensure_cuda_initialized()) {
        if (lean_native_ensure_workspace(n) == 0) {
            size_t bytes = n * sizeof(uint64_t);
            cudaMemcpyAsync(g_cuda_state.d_buf1, in0, bytes, cudaMemcpyHostToDevice, g_cuda_state.stream);
            cudaMemcpyAsync(g_cuda_state.d_buf2, in1, bytes, cudaMemcpyHostToDevice, g_cuda_state.stream);
            uint64_t n_u64 = (uint64_t)n;
            void* params[4] = {
                &g_cuda_state.d_buf0,
                &g_cuda_state.d_buf1,
                &g_cuda_state.d_buf2,
                &n_u64
            };
            if (lean_native_launch_ptx_kernel("lean_native_kernel_zip_add", params, n) == 0) {
                cudaMemcpyAsync(out, g_cuda_state.d_buf0, bytes, cudaMemcpyDeviceToHost, g_cuda_state.stream);
                if (cudaStreamSynchronize(g_cuda_state.stream) == cudaSuccess) {
                    return 0;
                }
            }
        }
    }
    lean_native_cpu_zip_add_u64(out, in0, in1, n);
    return 0;
}

extern "C" int lean_native_hybrid_stencil1d_u64(
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
    if (n == 0) {
        return 0;
    }
    if (lean_native_ensure_cuda_initialized()) {
        if (lean_native_ensure_workspace(n) == 0) {
            size_t bytes = n * sizeof(uint64_t);
            cudaMemcpyAsync(g_cuda_state.d_buf1, in0, bytes, cudaMemcpyHostToDevice, g_cuda_state.stream);
            uint64_t n_u64 = (uint64_t)n;
            void* params[6] = {
                &g_cuda_state.d_buf0,
                &g_cuda_state.d_buf1,
                &wl,
                &wc,
                &wr,
                &n_u64
            };
            if (lean_native_launch_ptx_kernel("lean_native_kernel_stencil1d", params, n) == 0) {
                cudaMemcpyAsync(out, g_cuda_state.d_buf0, bytes, cudaMemcpyDeviceToHost, g_cuda_state.stream);
                if (cudaStreamSynchronize(g_cuda_state.stream) == cudaSuccess) {
                    return 0;
                }
            }
        }
    }
    lean_native_cpu_stencil1d_u64(out, in0, wl, wc, wr, n);
    return 0;
}

extern "C" int lean_native_hybrid_dot_product_u64(
    uint64_t* out_sum,
    const uint64_t* in0,
    const uint64_t* in1,
    size_t n
) {
    if (!out_sum || !in0 || !in1) {
        return -1;
    }
    if (n == 0) {
        *out_sum = 0ULL;
        return 0;
    }
    if (lean_native_ensure_cuda_initialized()) {
        if (lean_native_ensure_workspace(n) == 0) {
            size_t bytes = n * sizeof(uint64_t);
            cudaMemsetAsync(g_cuda_state.d_buf0, 0, sizeof(uint64_t), g_cuda_state.stream);
            cudaMemcpyAsync(g_cuda_state.d_buf1, in0, bytes, cudaMemcpyHostToDevice, g_cuda_state.stream);
            cudaMemcpyAsync(g_cuda_state.d_buf2, in1, bytes, cudaMemcpyHostToDevice, g_cuda_state.stream);
            uint64_t n_u64 = (uint64_t)n;
            void* params[4] = {
                &g_cuda_state.d_buf0,
                &g_cuda_state.d_buf1,
                &g_cuda_state.d_buf2,
                &n_u64
            };
            unsigned int block_dim = 256;
            unsigned int grid_dim  = (unsigned int)((n + block_dim - 1) / block_dim);
            if (grid_dim > 1024u) {
                grid_dim = 1024u;
            }
            if (lean_native_launch_ptx_kernel_2d(
                    "lean_native_kernel_dot_reduce_u64",
                    params,
                    grid_dim, 1,
                    block_dim, 1) == 0) {
                uint64_t host_acc = 0ULL;
                cudaMemcpyAsync(&host_acc, g_cuda_state.d_buf0, sizeof(uint64_t), cudaMemcpyDeviceToHost, g_cuda_state.stream);
                if (cudaStreamSynchronize(g_cuda_state.stream) == cudaSuccess) {
                    *out_sum = host_acc;
                    return 0;
                }
            }
        }
    }
    lean_native_cpu_dot_product_u64(out_sum, in0, in1, n);
    return 0;
}

extern "C" int lean_native_hybrid_matmul_u64(
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
    if (m == 0 || n == 0 || k == 0) {
        return 0;
    }
    size_t max_elems = m * n;
    if (m * k > max_elems) max_elems = m * k;
    if (k * n > max_elems) max_elems = k * n;

    if (m == n && n == k && lean_native_ensure_cuda_initialized()) {
        if (lean_native_ensure_workspace(max_elems) == 0) {
            cudaMemcpyAsync(g_cuda_state.d_buf1, a, m * k * sizeof(uint64_t), cudaMemcpyHostToDevice, g_cuda_state.stream);
            cudaMemcpyAsync(g_cuda_state.d_buf2, b, k * n * sizeof(uint64_t), cudaMemcpyHostToDevice, g_cuda_state.stream);
            uint64_t dim_u64 = (uint64_t)m;
            void* params[4] = {
                &g_cuda_state.d_buf0,
                &g_cuda_state.d_buf1,
                &g_cuda_state.d_buf2,
                &dim_u64
            };
            unsigned int grid_x = (unsigned int)((n + MATMUL_TILE_DIM - 1) / MATMUL_TILE_DIM);
            unsigned int grid_y = (unsigned int)((m + MATMUL_TILE_DIM - 1) / MATMUL_TILE_DIM);
            if (lean_native_launch_ptx_kernel_2d(
                    "lean_native_kernel_matmul_tiled_u64",
                    params,
                    grid_x, grid_y,
                    MATMUL_TILE_DIM, MATMUL_TILE_DIM) == 0) {
                cudaMemcpyAsync(c, g_cuda_state.d_buf0, m * n * sizeof(uint64_t), cudaMemcpyDeviceToHost, g_cuda_state.stream);
                if (cudaStreamSynchronize(g_cuda_state.stream) == cudaSuccess) {
                    return 0;
                }
            }
        }
    }
    lean_native_cpu_matmul_u64(c, a, b, m, n, k);
    return 0;
}
