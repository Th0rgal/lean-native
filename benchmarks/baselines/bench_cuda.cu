/*
 * bench_cuda.cu
 * Reference CUDA / PTX GPU baseline & `lean-native` GPU backend harness.
 *
 * Targets NVIDIA Grace-Blackwell GB10 (sm_121 / sm_90+) and general CUDA architectures.
 * Produces the EXACT same 64-bit deterministic FNV-1a / scalar checksums as
 * `bench_cpp.cpp`, `bench_suite.lean`, and `bench_lean_native.c`.
 */

#include <cuda_runtime.h>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#define CUDA_CHECK(call)                                                       \
    do {                                                                       \
        cudaError_t err = call;                                                \
        if (err != cudaSuccess) {                                              \
            std::fprintf(stderr, "CUDA error at %s:%d: %s\n", __FILE__,        \
                         __LINE__, cudaGetErrorString(err));                   \
            std::exit(1);                                                      \
        }                                                                      \
    } while (0)

static inline uint64_t fnv1a_u64(uint64_t h, uint64_t val) {
    return (h ^ val) * 1099511628211ULL;
}

static constexpr uint64_t FNV_OFFSET = 14695981039346656037ULL;

static double now_ms() {
    auto now = std::chrono::steady_clock::now().time_since_epoch();
    return std::chrono::duration<double, std::milli>(now).count();
}

// 1. collatz_steps CUDA kernel (parallel reduction over N trajectories)
__global__ void collatz_kernel(uint64_t N, unsigned long long* global_sum) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
    uint64_t local_steps = 0;

    for (uint64_t i = idx + 1; i <= N; i += stride) {
        uint64_t x = i;
        uint64_t s = 0;
        while (x > 1ULL) {
            if ((x & 1ULL) == 0ULL) {
                x >>= 1;
            } else {
                x = 3ULL * x + 1ULL;
            }
            s++;
        }
        local_steps += s;
    }

    for (int offset = 16; offset > 0; offset /= 2) {
        local_steps += __shfl_down_sync(0xffffffff, local_steps, offset);
    }
    if ((threadIdx.x & 31) == 0) {
        atomicAdd(global_sum, (unsigned long long)local_steps);
    }
}

uint64_t run_cuda_collatz(uint64_t N, double* elapsed_ms) {
    unsigned long long* d_sum = nullptr;
    CUDA_CHECK(cudaMalloc(&d_sum, sizeof(unsigned long long)));
    CUDA_CHECK(cudaMemset(d_sum, 0, sizeof(unsigned long long)));
    CUDA_CHECK(cudaDeviceSynchronize());

    double t0 = now_ms();
    collatz_kernel<<<512, 256>>>(N, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t1 = now_ms();
    *elapsed_ms = t1 - t0;

    unsigned long long h_sum = 0;
    CUDA_CHECK(cudaMemcpy(&h_sum, d_sum, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaFree(d_sum));
    return (uint64_t)h_sum;
}

// 2. tuple_accum_sum (sequential recurrence; Hybrid partitioner keeps sequential recurrences on CPU)
uint64_t run_cpu_tuple_accum_sum(uint64_t N, double* elapsed_ms) {
    double t0 = now_ms();
    uint64_t a = 1ULL;
    uint64_t b = 2ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t next_a = a + (i ^ b);
        uint64_t next_b = b + (i * 3ULL + 1ULL);
        a = next_a;
        b = next_b;
    }
    double t1 = now_ms();
    *elapsed_ms = t1 - t0;
    return a ^ b;
}

// 3. sarray_scale_bias CUDA kernel
__global__ void sarray_scale_bias_kernel(uint64_t N, uint64_t* arr) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
    for (uint64_t i = idx; i < N; i += stride) {
        uint64_t v = arr[i];
        v = v * 3ULL + 7ULL;
        v = v * 3ULL + 7ULL;
        arr[i] = v;
    }
}

uint64_t run_cuda_sarray_scale_bias(uint64_t N, uint64_t* h_arr, double* elapsed_ms) {
    uint64_t* d_arr = nullptr;
    CUDA_CHECK(cudaMalloc(&d_arr, N * sizeof(uint64_t)));
    CUDA_CHECK(cudaMemcpy(d_arr, h_arr, N * sizeof(uint64_t), cudaMemcpyHostToDevice));
    // Warm up kernel module load
    sarray_scale_bias_kernel<<<1, 32>>>(0, d_arr);
    CUDA_CHECK(cudaDeviceSynchronize());

    double t0 = now_ms();
    int blocks = (int)((N + 255) / 256);
    if (blocks > 2048) blocks = 2048;
    sarray_scale_bias_kernel<<<blocks, 256>>>(N, d_arr);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t1 = now_ms();
    *elapsed_ms = t1 - t0;

    CUDA_CHECK(cudaMemcpy(h_arr, d_arr, N * sizeof(uint64_t), cudaMemcpyDeviceToHost));
    uint64_t h = FNV_OFFSET;
    for (uint64_t i = 0; i < N; i += 64) {
        h = fnv1a_u64(h, h_arr[i]);
    }
    h = fnv1a_u64(h, h_arr[N - 1]);
    CUDA_CHECK(cudaFree(d_arr));
    return h;
}

// 4. dot_product_u64 CUDA kernel
__global__ void dot_product_u64_kernel(uint64_t N, const uint64_t* __restrict__ A,
                                       const uint64_t* __restrict__ B,
                                       unsigned long long* global_sum) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
    uint64_t local_sum = 0;
    for (uint64_t i = idx; i < N; i += stride) {
        local_sum += A[i] * B[i];
    }
    for (int offset = 16; offset > 0; offset /= 2) {
        local_sum += __shfl_down_sync(0xffffffff, local_sum, offset);
    }
    if ((threadIdx.x & 31) == 0) {
        atomicAdd(global_sum, (unsigned long long)local_sum);
    }
}

uint64_t run_cuda_dot_product(uint64_t N, const uint64_t* h_A, const uint64_t* h_B, double* elapsed_ms) {
    uint64_t *d_A = nullptr, *d_B = nullptr;
    unsigned long long* d_sum = nullptr;
    CUDA_CHECK(cudaMalloc(&d_A, N * sizeof(uint64_t)));
    CUDA_CHECK(cudaMalloc(&d_B, N * sizeof(uint64_t)));
    CUDA_CHECK(cudaMalloc(&d_sum, sizeof(unsigned long long)));
    CUDA_CHECK(cudaMemcpy(d_A, h_A, N * sizeof(uint64_t), cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_B, h_B, N * sizeof(uint64_t), cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemset(d_sum, 0, sizeof(unsigned long long)));
    dot_product_u64_kernel<<<1, 32>>>(0, d_A, d_B, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());

    double t0 = now_ms();
    dot_product_u64_kernel<<<1024, 256>>>(N, d_A, d_B, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t1 = now_ms();
    *elapsed_ms = t1 - t0;

    unsigned long long h_sum = 0;
    CUDA_CHECK(cudaMemcpy(&h_sum, d_sum, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaFree(d_A));
    CUDA_CHECK(cudaFree(d_B));
    CUDA_CHECK(cudaFree(d_sum));
    return (uint64_t)h_sum;
}

// 5. saxpy_kernel CUDA kernel
__global__ void saxpy_u64_kernel(uint64_t N, uint64_t alpha,
                                 const uint64_t* __restrict__ X,
                                 uint64_t* __restrict__ Y) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
    for (uint64_t i = idx; i < N; i += stride) {
        Y[i] = alpha * X[i] + Y[i];
    }
}

uint64_t run_cuda_saxpy(uint64_t N, uint64_t alpha, const uint64_t* h_X, uint64_t* h_Y, double* elapsed_ms) {
    uint64_t *d_X = nullptr, *d_Y = nullptr;
    CUDA_CHECK(cudaMalloc(&d_X, N * sizeof(uint64_t)));
    CUDA_CHECK(cudaMalloc(&d_Y, N * sizeof(uint64_t)));
    CUDA_CHECK(cudaMemcpy(d_X, h_X, N * sizeof(uint64_t), cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_Y, h_Y, N * sizeof(uint64_t), cudaMemcpyHostToDevice));
    // Warm up kernel module load
    saxpy_u64_kernel<<<1, 32>>>(0, alpha, d_X, d_Y);
    CUDA_CHECK(cudaDeviceSynchronize());

    double t0 = now_ms();
    saxpy_u64_kernel<<<2048, 256>>>(N, alpha, d_X, d_Y);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t1 = now_ms();
    *elapsed_ms = t1 - t0;

    CUDA_CHECK(cudaMemcpy(h_Y, d_Y, N * sizeof(uint64_t), cudaMemcpyDeviceToHost));
    uint64_t h = FNV_OFFSET;
    for (uint64_t i = 0; i < N; i += 256) {
        h = fnv1a_u64(h, h_Y[i]);
    }
    h = fnv1a_u64(h, h_Y[N - 1]);
    CUDA_CHECK(cudaFree(d_X));
    CUDA_CHECK(cudaFree(d_Y));
    return h;
}

// 6. matmul_tiled_u64 CUDA shared-memory tiled kernel (16x16 tiles)
#define MM_TILE 16
__global__ void matmul_tiled_u64_kernel(uint32_t M, const uint64_t* __restrict__ A,
                                        const uint64_t* __restrict__ B,
                                        uint64_t* __restrict__ C) {
    __shared__ uint64_t sA[MM_TILE][MM_TILE];
    __shared__ uint64_t sB[MM_TILE][MM_TILE];

    uint32_t row = blockIdx.y * MM_TILE + threadIdx.y;
    uint32_t col = blockIdx.x * MM_TILE + threadIdx.x;
    uint64_t acc = 0ULL;

    for (uint32_t t = 0; t < M; t += MM_TILE) {
        sA[threadIdx.y][threadIdx.x] = (row < M && (t + threadIdx.x) < M) ? A[row * M + t + threadIdx.x] : 0ULL;
        sB[threadIdx.y][threadIdx.x] = ((t + threadIdx.y) < M && col < M) ? B[(t + threadIdx.y) * M + col] : 0ULL;
        __syncthreads();

        #pragma unroll
        for (int k = 0; k < MM_TILE; ++k) {
            acc += sA[threadIdx.y][k] * sB[k][threadIdx.x];
        }
        __syncthreads();
    }

    if (row < M && col < M) {
        C[row * M + col] = acc;
    }
}

uint64_t run_cuda_matmul_tiled(uint64_t M, const uint64_t* h_A, const uint64_t* h_B, double* elapsed_ms) {
    size_t bytes = M * M * sizeof(uint64_t);
    uint64_t *d_A = nullptr, *d_B = nullptr, *d_C = nullptr;
    CUDA_CHECK(cudaMalloc(&d_A, bytes));
    CUDA_CHECK(cudaMalloc(&d_B, bytes));
    CUDA_CHECK(cudaMalloc(&d_C, bytes));
    CUDA_CHECK(cudaMemcpy(d_A, h_A, bytes, cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_B, h_B, bytes, cudaMemcpyHostToDevice));
    matmul_tiled_u64_kernel<<<1, 1>>>(0, d_A, d_B, d_C);
    CUDA_CHECK(cudaDeviceSynchronize());

    dim3 threads(MM_TILE, MM_TILE);
    dim3 blocks((M + MM_TILE - 1) / MM_TILE, (M + MM_TILE - 1) / MM_TILE);

    double t0 = now_ms();
    matmul_tiled_u64_kernel<<<blocks, threads>>>((uint32_t)M, d_A, d_B, d_C);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t1 = now_ms();
    *elapsed_ms = t1 - t0;

    std::vector<uint64_t> h_C(M * M);
    CUDA_CHECK(cudaMemcpy(h_C.data(), d_C, bytes, cudaMemcpyDeviceToHost));
    uint64_t h = FNV_OFFSET;
    for (uint64_t idx = 0; idx < M * M; ++idx) {
        h = fnv1a_u64(h, h_C[idx]);
    }
    CUDA_CHECK(cudaFree(d_A));
    CUDA_CHECK(cudaFree(d_B));
    CUDA_CHECK(cudaFree(d_C));
    return h;
}

// Holdout 1: holdout_bitwise
uint64_t run_holdout_bitwise(uint64_t N, double* elapsed_ms) {
    double t0 = now_ms();
    uint64_t acc = 0x123456789ABCDEF0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t x = i + acc;
        uint64_t v = (x << 3) + x + (x >> 2);
        acc ^= v + (i * 17ULL);
    }
    double t1 = now_ms();
    *elapsed_ms = t1 - t0;
    return acc;
}

// Holdout 2: holdout_loop_bounds
uint64_t run_holdout_loop_bounds(uint64_t N, double* elapsed_ms) {
    double t0 = now_ms();
    uint64_t sum1 = 0ULL;
    uint64_t sum2 = 1ULL;
    for (uint64_t i = 0; i < N; ++i) {
        sum1 += (i * 5ULL + 3ULL) ^ (sum2 & 0xFFULL);
        sum2 = (sum2 * 13ULL + i) ^ (sum1 >> 3);
    }
    double t1 = now_ms();
    *elapsed_ms = t1 - t0;
    return sum1 ^ sum2;
}

int main(int argc, char** argv) {
    setenv("CUDA_MODULE_LOADING", "LAZY", 1);
    std::string filter = (argc > 1) ? argv[1] : "all";

    cudaFree(0);

    if (filter == "all" || filter == "collatz_steps") {
        double dt = 0.0;
        uint64_t c = run_cuda_collatz(5000000ULL, &dt);
        std::printf("BENCH collatz_steps checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }

    if (filter == "all" || filter == "tuple_accum_sum") {
        double dt = 0.0;
        uint64_t c = run_cpu_tuple_accum_sum(50000000ULL, &dt);
        std::printf("BENCH tuple_accum_sum checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }

    if (filter == "all" || filter == "sarray_scale_bias") {
        uint64_t N = 10000000ULL;
        std::vector<uint64_t> arr(N);
        for (uint64_t i = 0; i < N; ++i) {
            arr[i] = (i * 6364136223846793005ULL + 1442695040888963407ULL);
        }
        double dt = 0.0;
        uint64_t c = run_cuda_sarray_scale_bias(N, arr.data(), &dt);
        std::printf("BENCH sarray_scale_bias checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }

    if (filter == "all" || filter == "dot_product_u64") {
        uint64_t N = 10000000ULL;
        std::vector<uint64_t> A(N), B(N);
        for (uint64_t i = 0; i < N; ++i) {
            A[i] = (i * 11400714819323198485ULL + 1ULL) & 0xFFFFFFFFULL;
            B[i] = (i * 14029467366897019727ULL + 3ULL) & 0xFFFFFFFFULL;
        }
        double dt = 0.0;
        uint64_t c = run_cuda_dot_product(N, A.data(), B.data(), &dt);
        std::printf("BENCH dot_product_u64 checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }

    if (filter == "all" || filter == "saxpy_kernel") {
        uint64_t N = 16777216ULL;
        uint64_t alpha = 314159ULL;
        std::vector<uint64_t> X(N), Y(N);
        for (uint64_t i = 0; i < N; ++i) {
            X[i] = i * 2654435761ULL + 7ULL;
            Y[i] = i * 2246822519ULL + 13ULL;
        }
        double dt = 0.0;
        uint64_t c = run_cuda_saxpy(N, alpha, X.data(), Y.data(), &dt);
        std::printf("BENCH saxpy_kernel checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }

    if (filter == "all" || filter == "matmul_tiled_u64") {
        uint64_t M = 512ULL;
        std::vector<uint64_t> A(M * M), B(M * M);
        for (uint64_t i = 0; i < M * M; ++i) {
            A[i] = (i * 6364136223846793005ULL + 1ULL) & 0xFFFFULL;
            B[i] = (i * 2862933555777941757ULL + 3ULL) & 0xFFFFULL;
        }
        double dt = 0.0;
        uint64_t c = run_cuda_matmul_tiled(M, A.data(), B.data(), &dt);
        std::printf("BENCH matmul_tiled_u64 checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }

    if (filter == "all" || filter == "holdout_bitwise") {
        double dt = 0.0;
        uint64_t c = run_holdout_bitwise(10000000ULL, &dt);
        std::printf("BENCH holdout_bitwise checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }

    if (filter == "all" || filter == "holdout_loop_bounds") {
        double dt = 0.0;
        uint64_t c = run_holdout_loop_bounds(10000000ULL, &dt);
        std::printf("BENCH holdout_loop_bounds checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }

    return 0;
}
