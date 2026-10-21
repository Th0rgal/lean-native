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

static inline uint64_t fnv1a_u64(uint64_t h, uint64_t val) { return (h ^ val) * 1099511628211ULL; }
static constexpr uint64_t FNV_OFFSET = 14695981039346656037ULL;
static double now_ms() { return std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

__global__ void collatz_kernel(uint64_t N, unsigned long long* global_sum) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x, stride = (uint64_t)gridDim.x * blockDim.x, local_steps = 0;
    for (uint64_t i = idx + 1; i <= N; i += stride) {
        uint64_t x = i;
        unsigned int tz0 = (unsigned int)(__ffsll((long long)x) - 1);
        x >>= tz0;
        uint64_t s = (uint64_t)tz0;
        while (x > 1ULL) {
            x = 3ULL * x + 1ULL;
            unsigned int tz = (unsigned int)(__ffsll((long long)x) - 1);
            x >>= tz;
            s += 1ULL + (uint64_t)tz;
        }
        local_steps += s;
    }
    for (int offset = 16; offset > 0; offset /= 2) local_steps += __shfl_down_sync(0xffffffff, local_steps, offset);
    if ((threadIdx.x & 31) == 0) atomicAdd(global_sum, (unsigned long long)local_steps);
}

uint64_t run_cuda_collatz(uint64_t N, double* elapsed_ms) {
    unsigned long long* d_sum = nullptr, h_sum = 0;
    CUDA_CHECK(cudaMalloc(&d_sum, sizeof(unsigned long long)));
    CUDA_CHECK(cudaMemset(d_sum, 0, sizeof(unsigned long long)));
    collatz_kernel<<<1, 32>>>(0, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t0 = now_ms();
    collatz_kernel<<<512, 256>>>(N, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    *elapsed_ms = now_ms() - t0;
    CUDA_CHECK(cudaMemcpy(&h_sum, d_sum, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaFree(d_sum));
    return (uint64_t)h_sum;
}

uint64_t run_cpu_tuple_accum_sum(uint64_t N, double* elapsed_ms) {
    double t0 = now_ms();
    uint64_t a0 = 1ULL, a1 = 0ULL, a2 = 0ULL, a3 = 0ULL, a4 = 0ULL, a5 = 0ULL, a6 = 0ULL, a7 = 0ULL;
    uint64_t b0 = 2ULL, b1 = 3ULL, b2 = 7ULL, b3 = 14ULL, b4 = 24ULL, b5 = 37ULL, b6 = 53ULL, b7 = 72ULL;
    uint64_t db0 = 92ULL, db1 = 116ULL, db2 = 140ULL, db3 = 164ULL, db4 = 188ULL, db5 = 212ULL, db6 = 236ULL, db7 = 260ULL;
    uint64_t i = 0;
    for (; i + 8 <= N; i += 8) {
        a0 += (i ^ b0);       b0 += db0; db0 += 192ULL;
        a1 += ((i + 1) ^ b1); b1 += db1; db1 += 192ULL;
        a2 += ((i + 2) ^ b2); b2 += db2; db2 += 192ULL;
        a3 += ((i + 3) ^ b3); b3 += db3; db3 += 192ULL;
        a4 += ((i + 4) ^ b4); b4 += db4; db4 += 192ULL;
        a5 += ((i + 5) ^ b5); b5 += db5; db5 += 192ULL;
        a6 += ((i + 6) ^ b6); b6 += db6; db6 += 192ULL;
        a7 += ((i + 7) ^ b7); b7 += db7; db7 += 192ULL;
    }
    uint64_t a = (a0 + a1) + (a2 + a3) + (a4 + a5) + (a6 + a7), b = b0;
    for (; i < N; ++i) { a += (i ^ b); b += (i * 3ULL + 1ULL); }
    *elapsed_ms = now_ms() - t0;
    return a ^ b;
}

__global__ void sarray_scale_bias_kernel(uint64_t N, uint64_t* arr) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x, stride = (uint64_t)gridDim.x * blockDim.x;
    for (uint64_t i = idx; i < N; i += stride) arr[i] = arr[i] * 9ULL + 28ULL;
}

uint64_t run_cuda_sarray_scale_bias(uint64_t N, uint64_t* h_arr, double* elapsed_ms) {
    uint64_t* d_arr = nullptr;
    CUDA_CHECK(cudaMalloc(&d_arr, N * sizeof(uint64_t)));
    CUDA_CHECK(cudaMemcpy(d_arr, h_arr, N * sizeof(uint64_t), cudaMemcpyHostToDevice));
    sarray_scale_bias_kernel<<<1, 32>>>(0, d_arr);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t0 = now_ms();
    int blocks = (int)((N + 255) / 256);
    if (blocks > 2048) blocks = 2048;
    sarray_scale_bias_kernel<<<blocks, 256>>>(N, d_arr);
    CUDA_CHECK(cudaDeviceSynchronize());
    *elapsed_ms = now_ms() - t0;
    CUDA_CHECK(cudaMemcpy(h_arr, d_arr, N * sizeof(uint64_t), cudaMemcpyDeviceToHost));
    uint64_t h = FNV_OFFSET;
    for (uint64_t i = 0; i < N; i += 64) h = fnv1a_u64(h, h_arr[i]);
    h = fnv1a_u64(h, h_arr[N - 1]);
    CUDA_CHECK(cudaFree(d_arr));
    return h;
}

__global__ void dot_product_u64_kernel(uint64_t N, const uint64_t* __restrict__ A, const uint64_t* __restrict__ B, unsigned long long* global_sum) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x, stride = (uint64_t)gridDim.x * blockDim.x, local_sum = 0;
    for (uint64_t i = idx; i < N; i += stride) local_sum += A[i] * B[i];
    for (int offset = 16; offset > 0; offset /= 2) local_sum += __shfl_down_sync(0xffffffff, local_sum, offset);
    if ((threadIdx.x & 31) == 0) atomicAdd(global_sum, (unsigned long long)local_sum);
}

uint64_t run_cuda_dot_product(uint64_t N, const uint64_t* h_A, const uint64_t* h_B, double* elapsed_ms) {
    uint64_t *d_A = nullptr, *d_B = nullptr;
    unsigned long long *d_sum = nullptr, h_sum = 0;
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
    *elapsed_ms = now_ms() - t0;
    CUDA_CHECK(cudaMemcpy(&h_sum, d_sum, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaFree(d_A));
    CUDA_CHECK(cudaFree(d_B));
    CUDA_CHECK(cudaFree(d_sum));
    return (uint64_t)h_sum;
}

__global__ void goldilocks_ntt_modmul_u64_kernel(uint64_t N, unsigned long long* global_sum) {
    const uint64_t EPS = 0xFFFFFFFFULL;
    const uint64_t M = 0xFFFFFFFF00000001ULL;
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
    uint64_t local_sum = 0ULL;
    for (uint64_t i = idx; i < N; i += stride) {
        uint64_t a = i * 6364136223846793005ULL + 1442695040888963407ULL;
        uint64_t b = (i ^ 0xAAAAAAAAAAAAAAAAULL) * 11400714819323198485ULL + 7ULL;
        uint64_t lo = a * b;
        uint64_t hi = __umul64hi(a, b);
        uint64_t x2 = hi & EPS, x3 = hi >> 32;
        uint64_t t0 = lo - x3 - ((lo < x3) ? EPS : 0ULL);
        uint64_t add2 = (x2 << 32) - x2;
        uint64_t t1 = t0 + add2;
        t1 += (t1 < t0) ? EPS : 0ULL;
        uint64_t r = (t1 >= M) ? (t1 - M) : t1;
        local_sum += (r ^ (a + b));
    }
    for (int offset = 16; offset > 0; offset /= 2) {
        local_sum += __shfl_down_sync(0xffffffff, local_sum, offset);
    }
    if ((threadIdx.x & 31) == 0) {
        atomicAdd(global_sum, (unsigned long long)local_sum);
    }
}

uint64_t run_cuda_goldilocks_ntt_modmul(uint64_t N, double* elapsed_ms) {
    unsigned long long* d_sum = nullptr, h_sum = 0;
    CUDA_CHECK(cudaMalloc(&d_sum, sizeof(unsigned long long)));
    CUDA_CHECK(cudaMemset(d_sum, 0, sizeof(unsigned long long)));
    goldilocks_ntt_modmul_u64_kernel<<<1, 32>>>(0, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t0 = now_ms();
    goldilocks_ntt_modmul_u64_kernel<<<512, 256>>>(N, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    *elapsed_ms = now_ms() - t0;
    CUDA_CHECK(cudaMemcpy(&h_sum, d_sum, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaFree(d_sum));
    return (uint64_t)h_sum;
}

__device__ __forceinline__ uint64_t dev_babybear_sbox(uint64_t x) {
    const uint64_t P = 2013265921ULL;
    const uint64_t MU = 2290649223ULL;
    uint64_t z2 = x * x, q2 = ((z2 >> 29) * MU) >> 33, r2 = z2 - q2 * P;
    if (r2 >= P) r2 -= P;
    uint64_t z3 = r2 * x, q3 = ((z3 >> 29) * MU) >> 33, r3 = z3 - q3 * P;
    if (r3 >= P) r3 -= P;
    uint64_t z4 = r2 * r2, q4 = ((z4 >> 29) * MU) >> 33, r4 = z4 - q4 * P;
    if (r4 >= P) r4 -= P;
    uint64_t z7 = r4 * r3, q7 = ((z7 >> 29) * MU) >> 33, r7 = z7 - q7 * P;
    if (r7 >= P) r7 -= P;
    return r7;
}

__global__ void babybear_poseidon2_sbox_u64_kernel(uint64_t N, unsigned long long* global_sum) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
    uint64_t local_sum = 0ULL;
    for (uint64_t i = idx; i < N; i += stride) {
        uint64_t y0 = dev_babybear_sbox((i * 2654435761ULL + 17ULL) & 0x3FFFFFFFULL);
        uint64_t y1 = dev_babybear_sbox((i * 2246822519ULL + 29ULL) & 0x3FFFFFFFULL);
        uint64_t y2 = dev_babybear_sbox((i * 3266489917ULL + 43ULL) & 0x3FFFFFFFULL);
        uint64_t y3 = dev_babybear_sbox((i * 668265263ULL + 59ULL) & 0x3FFFFFFFULL);
        uint64_t t = y0 + y1 + y2 + y3;
        local_sum += ((y0 + t) ^ ((y1 + t) << 16)) + ((y2 + t) ^ ((y3 + t) << 32));
    }
    for (int offset = 16; offset > 0; offset /= 2) {
        local_sum += __shfl_down_sync(0xffffffff, local_sum, offset);
    }
    if ((threadIdx.x & 31) == 0) {
        atomicAdd(global_sum, (unsigned long long)local_sum);
    }
}

uint64_t run_cuda_babybear_poseidon2_sbox(uint64_t N, double* elapsed_ms) {
    unsigned long long* d_sum = nullptr, h_sum = 0;
    CUDA_CHECK(cudaMalloc(&d_sum, sizeof(unsigned long long)));
    CUDA_CHECK(cudaMemset(d_sum, 0, sizeof(unsigned long long)));
    babybear_poseidon2_sbox_u64_kernel<<<1, 32>>>(0, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t0 = now_ms();
    babybear_poseidon2_sbox_u64_kernel<<<512, 256>>>(N, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    *elapsed_ms = now_ms() - t0;
    CUDA_CHECK(cudaMemcpy(&h_sum, d_sum, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaFree(d_sum));
    return (uint64_t)h_sum;
}

__global__ void saxpy_u64_kernel(uint64_t N, uint64_t alpha, const uint64_t* __restrict__ X, uint64_t* __restrict__ Y) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x, stride = (uint64_t)gridDim.x * blockDim.x;
    for (uint64_t i = idx; i < N; i += stride) Y[i] = alpha * X[i] + Y[i];
}

uint64_t run_cuda_saxpy(uint64_t N, uint64_t alpha, const uint64_t* h_X, uint64_t* h_Y, double* elapsed_ms) {
    uint64_t *d_X = nullptr, *d_Y = nullptr;
    CUDA_CHECK(cudaMalloc(&d_X, N * sizeof(uint64_t)));
    CUDA_CHECK(cudaMalloc(&d_Y, N * sizeof(uint64_t)));
    CUDA_CHECK(cudaMemcpy(d_X, h_X, N * sizeof(uint64_t), cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_Y, h_Y, N * sizeof(uint64_t), cudaMemcpyHostToDevice));
    saxpy_u64_kernel<<<1, 32>>>(0, alpha, d_X, d_Y);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t0 = now_ms();
    saxpy_u64_kernel<<<2048, 256>>>(N, alpha, d_X, d_Y);
    CUDA_CHECK(cudaDeviceSynchronize());
    *elapsed_ms = now_ms() - t0;
    CUDA_CHECK(cudaMemcpy(h_Y, d_Y, N * sizeof(uint64_t), cudaMemcpyDeviceToHost));
    uint64_t h = FNV_OFFSET;
    for (uint64_t i = 0; i < N; i += 256) h = fnv1a_u64(h, h_Y[i]);
    h = fnv1a_u64(h, h_Y[N - 1]);
    CUDA_CHECK(cudaFree(d_X)); CUDA_CHECK(cudaFree(d_Y));
    return h;
}

#define MM_TILE 16
__global__ void matmul_tiled_u64_kernel(uint32_t M, const uint64_t* __restrict__ A, const uint64_t* __restrict__ B, uint64_t* __restrict__ C) {
    __shared__ uint64_t sA[MM_TILE][MM_TILE], sB[MM_TILE][MM_TILE];
    uint32_t row = blockIdx.y * MM_TILE + threadIdx.y, col = blockIdx.x * MM_TILE + threadIdx.x;
    uint64_t acc = 0ULL;
    for (uint32_t t = 0; t < M; t += MM_TILE) {
        sA[threadIdx.y][threadIdx.x] = (row < M && (t + threadIdx.x) < M) ? A[row * M + t + threadIdx.x] : 0ULL;
        sB[threadIdx.y][threadIdx.x] = ((t + threadIdx.y) < M && col < M) ? B[(t + threadIdx.y) * M + col] : 0ULL;
        __syncthreads();
        #pragma unroll
        for (int k = 0; k < MM_TILE; ++k) acc += sA[threadIdx.y][k] * sB[k][threadIdx.x];
        __syncthreads();
    }
    if (row < M && col < M) C[row * M + col] = acc;
}

uint64_t run_cuda_matmul_tiled(uint64_t M, const uint64_t* h_A, const uint64_t* h_B, double* elapsed_ms) {
    size_t bytes = M * M * sizeof(uint64_t);
    uint64_t *d_A = nullptr, *d_B = nullptr, *d_C = nullptr;
    CUDA_CHECK(cudaMalloc(&d_A, bytes)); CUDA_CHECK(cudaMalloc(&d_B, bytes)); CUDA_CHECK(cudaMalloc(&d_C, bytes));
    CUDA_CHECK(cudaMemcpy(d_A, h_A, bytes, cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_B, h_B, bytes, cudaMemcpyHostToDevice));
    matmul_tiled_u64_kernel<<<1, 1>>>(0, d_A, d_B, d_C);
    CUDA_CHECK(cudaDeviceSynchronize());
    dim3 threads(MM_TILE, MM_TILE), blocks((M + MM_TILE - 1) / MM_TILE, (M + MM_TILE - 1) / MM_TILE);
    double t0 = now_ms();
    matmul_tiled_u64_kernel<<<blocks, threads>>>((uint32_t)M, d_A, d_B, d_C);
    CUDA_CHECK(cudaDeviceSynchronize());
    *elapsed_ms = now_ms() - t0;
    std::vector<uint64_t> h_C(M * M);
    CUDA_CHECK(cudaMemcpy(h_C.data(), d_C, bytes, cudaMemcpyDeviceToHost));
    uint64_t h = FNV_OFFSET;
    for (uint64_t idx = 0; idx < M * M; ++idx) h = fnv1a_u64(h, h_C[idx]);
    CUDA_CHECK(cudaFree(d_A)); CUDA_CHECK(cudaFree(d_B)); CUDA_CHECK(cudaFree(d_C));
    return h;
}

__global__ void evm_gas_schedule_u64_kernel(uint64_t N, unsigned long long* global_sum) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
    uint64_t local_gas = 0ULL;
    for (uint64_t i = idx; i < N; i += stride) {
        uint64_t old_w = (i * 2654435761ULL + 11ULL) & 0x7FFFULL;
        uint64_t req_w = (i * 2246822519ULL + 29ULL) & 0xFFFFULL;
        uint64_t data_w = (i * 3266489917ULL + 7ULL) & 0xFFULL;
        uint64_t new_w = (req_w > old_w) ? req_w : old_w;
        uint64_t op_gas = 3ULL * (new_w - old_w) + (((new_w * new_w) >> 9) - ((old_w * old_w) >> 9)) + 30ULL + 6ULL * data_w;
        local_gas += op_gas;
    }
    for (int offset = 16; offset > 0; offset /= 2) {
        local_gas += __shfl_down_sync(0xffffffff, local_gas, offset);
    }
    if ((threadIdx.x & 31) == 0) {
        atomicAdd(global_sum, (unsigned long long)local_gas);
    }
}

uint64_t run_cuda_evm_gas_schedule(uint64_t N, double* elapsed_ms) {
    unsigned long long* d_sum = nullptr, h_sum = 0;
    CUDA_CHECK(cudaMalloc(&d_sum, sizeof(unsigned long long)));
    CUDA_CHECK(cudaMemset(d_sum, 0, sizeof(unsigned long long)));
    evm_gas_schedule_u64_kernel<<<1, 32>>>(0, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t0 = now_ms();
    evm_gas_schedule_u64_kernel<<<512, 256>>>(N, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    *elapsed_ms = now_ms() - t0;
    CUDA_CHECK(cudaMemcpy(&h_sum, d_sum, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaFree(d_sum));
    return (uint64_t)h_sum;
}

__device__ __forceinline__ uint64_t dev_rotl64(uint64_t x, unsigned int r) {
    return (x << r) | (x >> (64U - r));
}

__global__ void keccak256_sponge_u64_kernel(uint64_t N, unsigned long long* global_xor) {
    const uint64_t RC[8] = {
        0x0000000000000001ULL, 0x0000000000008082ULL,
        0x800000000000808aULL, 0x8000000080008000ULL,
        0x000000000000808bULL, 0x0000000080000001ULL,
        0x8000000080008081ULL, 0x8000000000008009ULL
    };
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
    uint64_t local_xor = 0ULL;
    for (uint64_t i = idx; i < N; i += stride) {
        uint64_t s0 = i * 6364136223846793005ULL + 1ULL;
        uint64_t s1 = i * 2862933555777941757ULL + 3ULL;
        uint64_t s2 = i * 11400714819323198485ULL + 5ULL;
        uint64_t s3 = i * 14029467366897019727ULL + 7ULL;
        uint64_t s4 = i * 3266489917ULL + 11ULL;
        #pragma unroll
        for (int r = 0; r < 8; ++r) {
            uint64_t d0 = s4 ^ dev_rotl64(s1, 1);
            uint64_t d1 = s0 ^ dev_rotl64(s2, 1);
            uint64_t d2 = s1 ^ dev_rotl64(s3, 1);
            uint64_t d3 = s2 ^ dev_rotl64(s4, 1);
            uint64_t d4 = s3 ^ dev_rotl64(s0, 1);
            uint64_t b0 = s0 ^ d0;
            uint64_t b1 = dev_rotl64(s1 ^ d1, 44);
            uint64_t b2 = dev_rotl64(s2 ^ d2, 43);
            uint64_t b3 = dev_rotl64(s3 ^ d3, 21);
            uint64_t b4 = dev_rotl64(s4 ^ d4, 14);
            s0 = b0 ^ ((~b1) & b2) ^ RC[r];
            s1 = b1 ^ ((~b2) & b3);
            s2 = b2 ^ ((~b3) & b4);
            s3 = b3 ^ ((~b4) & b0);
            s4 = b4 ^ ((~b0) & b1);
        }
        local_xor ^= (s0 + s1 + s2 + s3 + s4);
    }
    for (int offset = 16; offset > 0; offset /= 2) {
        local_xor ^= __shfl_down_sync(0xffffffff, local_xor, offset);
    }
    if ((threadIdx.x & 31) == 0) {
        atomicXor(global_xor, (unsigned long long)local_xor);
    }
}

uint64_t run_cuda_keccak256_sponge(uint64_t N, double* elapsed_ms) {
    unsigned long long* d_xor = nullptr, h_xor = 0;
    CUDA_CHECK(cudaMalloc(&d_xor, sizeof(unsigned long long)));
    CUDA_CHECK(cudaMemset(d_xor, 0, sizeof(unsigned long long)));
    keccak256_sponge_u64_kernel<<<1, 32>>>(0, d_xor);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t0 = now_ms();
    keccak256_sponge_u64_kernel<<<512, 256>>>(N, d_xor);
    CUDA_CHECK(cudaDeviceSynchronize());
    *elapsed_ms = now_ms() - t0;
    CUDA_CHECK(cudaMemcpy(&h_xor, d_xor, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaFree(d_xor));
    return (uint64_t)h_xor;
}

__global__ void uint256_wad_muldiv_u64_kernel(uint64_t N, unsigned long long* global_sum) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
    uint64_t local_sum = 0ULL;
    for (uint64_t i = idx; i < N; i += stride) {
        uint64_t x0 = i * 6364136223846793005ULL + 1442695040888963407ULL;
        uint64_t x1 = i * 2862933555777941757ULL + 3ULL;
        uint64_t y0 = (i ^ 0x5555555555555555ULL) * 11400714819323198485ULL + 7ULL;
        uint64_t y1 = i * 3266489917ULL + 11ULL;
        uint64_t s0 = x0 + y0;
        uint64_t carry = (s0 < x0) ? 1ULL : 0ULL;
        uint64_t s1 = x1 + y1 + carry;
        uint64_t lo0 = x0 * y0;
        uint64_t hi0 = __umul64hi(x0, y0);
        uint64_t lo1 = s0 * 1000000000000000000ULL;
        uint64_t hi1 = __umul64hi(s0, 1000000000000000000ULL);
        local_sum += (s0 ^ s1 ^ hi0 ^ hi1 ^ (lo0 >> 32) ^ (lo1 >> 32));
    }
    for (int offset = 16; offset > 0; offset /= 2) {
        local_sum += __shfl_down_sync(0xffffffff, local_sum, offset);
    }
    if ((threadIdx.x & 31) == 0) {
        atomicAdd(global_sum, (unsigned long long)local_sum);
    }
}

uint64_t run_cuda_uint256_wad_muldiv(uint64_t N, double* elapsed_ms) {
    unsigned long long* d_sum = nullptr, h_sum = 0;
    CUDA_CHECK(cudaMalloc(&d_sum, sizeof(unsigned long long)));
    CUDA_CHECK(cudaMemset(d_sum, 0, sizeof(unsigned long long)));
    uint256_wad_muldiv_u64_kernel<<<1, 32>>>(0, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    double t0 = now_ms();
    uint256_wad_muldiv_u64_kernel<<<512, 256>>>(N, d_sum);
    CUDA_CHECK(cudaDeviceSynchronize());
    *elapsed_ms = now_ms() - t0;
    CUDA_CHECK(cudaMemcpy(&h_sum, d_sum, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaFree(d_sum));
    return (uint64_t)h_sum;
}

uint64_t run_holdout_bitwise(uint64_t N, double* elapsed_ms) {
    double t0 = now_ms();
    uint64_t acc = 0x123456789ABCDEF0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t x = i + acc, s = (acc * 9ULL) + (i * 26ULL);
        acc ^= s + (x >> 2);
    }
    *elapsed_ms = now_ms() - t0;
    return acc;
}

uint64_t run_holdout_loop_bounds(uint64_t N, double* elapsed_ms) {
    double t0 = now_ms();
    uint64_t sum1 = 0ULL, sum2 = 1ULL, iv5 = 3ULL;
    for (uint64_t i = 0; i < N; ++i, iv5 += 5ULL) {
        sum1 += iv5 ^ (sum2 & 0xFFULL);
        uint64_t s2_13 = (sum2 << 3) + (sum2 << 2) + sum2;
        sum2 = (s2_13 + i) ^ (sum1 >> 3);
    }
    *elapsed_ms = now_ms() - t0;
    return sum1 ^ sum2;
}

int main(int argc, char** argv) {
    setenv("CUDA_MODULE_LOADING", "LAZY", 1);
    std::string filter = (argc > 1) ? argv[1] : "all";
    cudaFree(0);
    double dt = 0.0;
    if (filter == "all" || filter == "collatz_steps") {
        uint64_t c = run_cuda_collatz(5000000ULL, &dt);
        std::printf("BENCH collatz_steps checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "tuple_accum_sum") {
        uint64_t c = run_cpu_tuple_accum_sum(50000000ULL, &dt);
        std::printf("BENCH tuple_accum_sum checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "sarray_scale_bias") {
        uint64_t N = 10000000ULL;
        std::vector<uint64_t> arr(N);
        for (uint64_t i = 0; i < N; ++i) arr[i] = i * 6364136223846793005ULL + 1442695040888963407ULL;
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
        uint64_t c = run_cuda_dot_product(N, A.data(), B.data(), &dt);
        std::printf("BENCH dot_product_u64 checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "saxpy_kernel") {
        uint64_t N = 16777216ULL;
        std::vector<uint64_t> X(N), Y(N);
        for (uint64_t i = 0; i < N; ++i) { X[i] = i * 2654435761ULL + 7ULL; Y[i] = i * 2246822519ULL + 13ULL; }
        uint64_t c = run_cuda_saxpy(N, 314159ULL, X.data(), Y.data(), &dt);
        std::printf("BENCH saxpy_kernel checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "matmul_tiled_u64") {
        uint64_t M = 512ULL;
        std::vector<uint64_t> A(M * M), B(M * M);
        for (uint64_t i = 0; i < M * M; ++i) {
            A[i] = (i * 6364136223846793005ULL + 1ULL) & 0xFFFFULL;
            B[i] = (i * 2862933555777941757ULL + 3ULL) & 0xFFFFULL;
        }
        uint64_t c = run_cuda_matmul_tiled(M, A.data(), B.data(), &dt);
        std::printf("BENCH matmul_tiled_u64 checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "evm_gas_schedule_u64") {
        uint64_t c = run_cuda_evm_gas_schedule(10000000ULL, &dt);
        std::printf("BENCH evm_gas_schedule_u64 checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "keccak256_sponge_u64") {
        uint64_t c = run_cuda_keccak256_sponge(2000000ULL, &dt);
        std::printf("BENCH keccak256_sponge_u64 checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "uint256_wad_muldiv_u64") {
        uint64_t c = run_cuda_uint256_wad_muldiv(5000000ULL, &dt);
        std::printf("BENCH uint256_wad_muldiv_u64 checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "goldilocks_ntt_modmul_u64") {
        uint64_t c = run_cuda_goldilocks_ntt_modmul(5000000ULL, &dt);
        std::printf("BENCH goldilocks_ntt_modmul_u64 checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "babybear_poseidon2_sbox_u64") {
        uint64_t c = run_cuda_babybear_poseidon2_sbox(5000000ULL, &dt);
        std::printf("BENCH babybear_poseidon2_sbox_u64 checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "holdout_bitwise") {
        uint64_t c = run_holdout_bitwise(10000000ULL, &dt);
        std::printf("BENCH holdout_bitwise checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    if (filter == "all" || filter == "holdout_loop_bounds") {
        uint64_t c = run_holdout_loop_bounds(10000000ULL, &dt);
        std::printf("BENCH holdout_loop_bounds checksum=%llu time_ms=%.4f\n", (unsigned long long)c, dt);
    }
    return 0;
}
