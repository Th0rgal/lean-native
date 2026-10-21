/*
 * bench_cpp.cpp
 * Reference C++20 (-O3) baseline for the lean-native Cross-Architecture Benchmark Suite.
 *
 * Implements the 6 core benchmarks with exact deterministic 64-bit outputs:
 *   1. collatz_steps     (N = 5,000,000)
 *   2. tuple_accum_sum   (N = 50,000,000)
 *   3. sarray_scale_bias (N = 10,000,000)
 *   4. dot_product_u64   (N = 10,000,000)
 *   5. saxpy_kernel      (N = 16,777,216)
 *   6. matmul_tiled_u64  (M = N = K = 512)
 *   7. holdout_VerifyBitwiseFold (N = 10,000,000)
 *   8. holdout_VerifyLoopBounds  (N = 10,000,000)
 */

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

static inline uint64_t fnv1a_u64(uint64_t h, uint64_t val) {
    return (h ^ val) * 1099511628211ULL;
}

static constexpr uint64_t FNV_OFFSET = 14695981039346656037ULL;

// 1. collatz_steps (N = 5,000,000)
// Scalar arithmetic, branches, strength reduction (n / 2 -> n >> 1, n % 2 -> n & 1)
uint64_t bench_collatz_steps(uint64_t N) {
    uint64_t total_steps = 0;
    for (uint64_t i = 1; i <= N; ++i) {
        uint64_t x = i;
        uint64_t steps = 0;
        while (x > 1) {
            if ((x & 1ULL) == 0ULL) {
                x >>= 1;
            } else {
                x = 3ULL * x + 1ULL;
            }
            steps++;
        }
        total_steps += steps;
    }
    return total_steps;
}

// 2. tuple_accum_sum (N = 50,000,000)
// Unboxed register tuple state transition (a, b) -> (a + (i ^ b), b + (i * 3 + 1))
uint64_t bench_tuple_accum_sum(uint64_t N) {
    uint64_t a = 1ULL;
    uint64_t b = 2ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t next_a = a + (i ^ b);
        uint64_t next_b = b + (i * 3ULL + 1ULL);
        a = next_a;
        b = next_b;
    }
    return a ^ b;
}

// 3. sarray_scale_bias (N = 10,000,000)
// Contiguous array mutation: arr[i] = arr[i] * 3 + 7 (2 passes)
uint64_t bench_sarray_scale_bias(uint64_t N, uint64_t* arr) {
    for (uint64_t pass = 0; pass < 2; ++pass) {
        for (uint64_t i = 0; i < N; ++i) {
            arr[i] = arr[i] * 3ULL + 7ULL;
        }
    }
    uint64_t h = FNV_OFFSET;
    for (uint64_t i = 0; i < N; i += 64) {
        h = fnv1a_u64(h, arr[i]);
    }
    h = fnv1a_u64(h, arr[N - 1]);
    return h;
}

// 4. dot_product_u64 (N = 10,000,000)
// Contiguous scalar dot product
uint64_t bench_dot_product_u64(uint64_t N, const uint64_t* __restrict__ A, const uint64_t* __restrict__ B) {
    uint64_t sum = 0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        sum += A[i] * B[i];
    }
    return sum;
}

// 5. saxpy_kernel (N = 16,777,216)
// Y[i] = alpha * X[i] + Y[i] in deterministic 64-bit integer / fixed-point arithmetic
uint64_t bench_saxpy_kernel(uint64_t N, uint64_t alpha, const uint64_t* __restrict__ X, uint64_t* __restrict__ Y) {
    for (uint64_t i = 0; i < N; ++i) {
        Y[i] = alpha * X[i] + Y[i];
    }
    uint64_t h = FNV_OFFSET;
    for (uint64_t i = 0; i < N; i += 256) {
        h = fnv1a_u64(h, Y[i]);
    }
    h = fnv1a_u64(h, Y[N - 1]);
    return h;
}

// 6. matmul_tiled_u64 (M = N = K = 512)
// Dense 512x512 matrix multiplication with 32x32 cache tiling
uint64_t bench_matmul_tiled_u64(uint64_t M, const uint64_t* __restrict__ A, const uint64_t* __restrict__ B, uint64_t* __restrict__ C) {
    std::memset(C, 0, M * M * sizeof(uint64_t));
    constexpr uint64_t TILE = 32;
    for (uint64_t i0 = 0; i0 < M; i0 += TILE) {
        for (uint64_t k0 = 0; k0 < M; k0 += TILE) {
            for (uint64_t j0 = 0; j0 < M; j0 += TILE) {
                for (uint64_t i = i0; i < i0 + TILE && i < M; ++i) {
                    for (uint64_t k = k0; k < k0 + TILE && k < M; ++k) {
                        uint64_t a_ik = A[i * M + k];
                        for (uint64_t j = j0; j < j0 + TILE && j < M; ++j) {
                            C[i * M + j] += a_ik * B[k * M + j];
                        }
                    }
                }
            }
        }
    }
    uint64_t h = FNV_OFFSET;
    for (uint64_t idx = 0; idx < M * M; ++idx) {
        h = fnv1a_u64(h, C[idx]);
    }
    return h;
}

// 7. evm_gas_schedule_u64 (N = 10,000,000)
// EVMYulLean 2.0 dynamic quadratic memory expansion + Keccak256 gas schedule (Gas.lean)
uint64_t bench_evm_gas_schedule_u64(uint64_t N) {
    uint64_t total_gas = 0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t old_w = (i * 2654435761ULL + 11ULL) & 0x7FFFULL;
        uint64_t req_w = (i * 2246822519ULL + 29ULL) & 0xFFFFULL;
        uint64_t data_w = (i * 3266489917ULL + 7ULL) & 0xFFULL;
        uint64_t new_w = (req_w > old_w) ? req_w : old_w;
        uint64_t new_cost = 3ULL * new_w + (new_w * new_w) / 512ULL;
        uint64_t old_cost = 3ULL * old_w + (old_w * old_w) / 512ULL;
        uint64_t op_gas = (new_cost - old_cost) + 30ULL + 6ULL * data_w;
        total_gas += op_gas;
    }
    return total_gas;
}

static inline uint64_t rotl64(uint64_t x, unsigned int r) {
    return (x << r) | (x >> (64U - r));
}

// 8. keccak256_sponge_u64 (N = 2,000,000)
// EVMYulLean 2.0 PureKeccak256.lean 5-lane sponge permutation (8 rounds of theta/rho/pi/chi/iota)
uint64_t bench_keccak256_sponge_u64(uint64_t N) {
    static constexpr uint64_t RC[8] = {
        0x0000000000000001ULL, 0x0000000000008082ULL,
        0x800000000000808aULL, 0x8000000080008000ULL,
        0x000000000000808bULL, 0x0000000080000001ULL,
        0x8000000080008081ULL, 0x8000000000008009ULL
    };
    uint64_t total = 0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t s0 = i * 6364136223846793005ULL + 1ULL;
        uint64_t s1 = i * 2862933555777941757ULL + 3ULL;
        uint64_t s2 = i * 11400714819323198485ULL + 5ULL;
        uint64_t s3 = i * 14029467366897019727ULL + 7ULL;
        uint64_t s4 = i * 3266489917ULL + 11ULL;
        for (int r = 0; r < 8; ++r) {
            uint64_t d0 = s4 ^ rotl64(s1, 1);
            uint64_t d1 = s0 ^ rotl64(s2, 1);
            uint64_t d2 = s1 ^ rotl64(s3, 1);
            uint64_t d3 = s2 ^ rotl64(s4, 1);
            uint64_t d4 = s3 ^ rotl64(s0, 1);
            uint64_t b0 = s0 ^ d0;
            uint64_t b1 = rotl64(s1 ^ d1, 44);
            uint64_t b2 = rotl64(s2 ^ d2, 43);
            uint64_t b3 = rotl64(s3 ^ d3, 21);
            uint64_t b4 = rotl64(s4 ^ d4, 14);
            s0 = b0 ^ ((~b1) & b2) ^ RC[r];
            s1 = b1 ^ ((~b2) & b3);
            s2 = b2 ^ ((~b3) & b4);
            s3 = b3 ^ ((~b4) & b0);
            s4 = b4 ^ ((~b0) & b1);
        }
        total ^= (s0 + s1 + s2 + s3 + s4);
    }
    return total;
}

// Holdout 1: holdout_VerifyBitwiseFold (N = 10,000,000)
uint64_t bench_holdout_bitwise(uint64_t N) {
    uint64_t acc = 0x123456789ABCDEF0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t x = i + acc;
        // Tests algebraic identity & strength reduction: (x * 8) + (x & x) - (x ^ x) + (x / 4)
        uint64_t v = (x << 3) + x + (x >> 2);
        acc ^= v + (i * 17ULL);
    }
    return acc;
}

// Holdout 2: holdout_VerifyLoopBounds (N = 10,000,000)
uint64_t bench_holdout_loop_bounds(uint64_t N) {
    uint64_t sum1 = 0ULL;
    uint64_t sum2 = 1ULL;
    for (uint64_t i = 0; i < N; ++i) {
        sum1 += (i * 5ULL + 3ULL) ^ (sum2 & 0xFFULL);
        sum2 = (sum2 * 13ULL + i) ^ (sum1 >> 3);
    }
    return sum1 ^ sum2;
}

static double now_ms() {
    auto now = std::chrono::steady_clock::now().time_since_epoch();
    return std::chrono::duration<double, std::milli>(now).count();
}

int main(int argc, char** argv) {
    std::string filter = (argc > 1) ? argv[1] : "all";

    if (filter == "all" || filter == "collatz_steps") {
        uint64_t N = 5000000ULL;
        double t0 = now_ms();
        uint64_t c = bench_collatz_steps(N);
        double t1 = now_ms();
        std::printf("BENCH collatz_steps checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    if (filter == "all" || filter == "tuple_accum_sum") {
        uint64_t N = 50000000ULL;
        double t0 = now_ms();
        uint64_t c = bench_tuple_accum_sum(N);
        double t1 = now_ms();
        std::printf("BENCH tuple_accum_sum checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    if (filter == "all" || filter == "sarray_scale_bias") {
        uint64_t N = 10000000ULL;
        std::vector<uint64_t> arr(N);
        for (uint64_t i = 0; i < N; ++i) {
            arr[i] = (i * 6364136223846793005ULL + 1442695040888963407ULL);
        }
        double t0 = now_ms();
        uint64_t c = bench_sarray_scale_bias(N, arr.data());
        double t1 = now_ms();
        std::printf("BENCH sarray_scale_bias checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    if (filter == "all" || filter == "dot_product_u64") {
        uint64_t N = 10000000ULL;
        std::vector<uint64_t> A(N), B(N);
        for (uint64_t i = 0; i < N; ++i) {
            A[i] = (i * 11400714819323198485ULL + 1ULL) & 0xFFFFFFFFULL;
            B[i] = (i * 14029467366897019727ULL + 3ULL) & 0xFFFFFFFFULL;
        }
        double t0 = now_ms();
        uint64_t c = bench_dot_product_u64(N, A.data(), B.data());
        double t1 = now_ms();
        std::printf("BENCH dot_product_u64 checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    if (filter == "all" || filter == "saxpy_kernel") {
        uint64_t N = 16777216ULL;
        uint64_t alpha = 314159ULL;
        std::vector<uint64_t> X(N), Y(N);
        for (uint64_t i = 0; i < N; ++i) {
            X[i] = i * 2654435761ULL + 7ULL;
            Y[i] = i * 2246822519ULL + 13ULL;
        }
        double t0 = now_ms();
        uint64_t c = bench_saxpy_kernel(N, alpha, X.data(), Y.data());
        double t1 = now_ms();
        std::printf("BENCH saxpy_kernel checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    if (filter == "all" || filter == "matmul_tiled_u64") {
        uint64_t M = 512ULL;
        std::vector<uint64_t> A(M * M), B(M * M), C(M * M);
        for (uint64_t i = 0; i < M * M; ++i) {
            A[i] = (i * 6364136223846793005ULL + 1ULL) & 0xFFFFULL;
            B[i] = (i * 2862933555777941757ULL + 3ULL) & 0xFFFFULL;
        }
        double t0 = now_ms();
        uint64_t c = bench_matmul_tiled_u64(M, A.data(), B.data(), C.data());
        double t1 = now_ms();
        std::printf("BENCH matmul_tiled_u64 checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    if (filter == "all" || filter == "evm_gas_schedule_u64") {
        uint64_t N = 10000000ULL;
        double t0 = now_ms();
        uint64_t c = bench_evm_gas_schedule_u64(N);
        double t1 = now_ms();
        std::printf("BENCH evm_gas_schedule_u64 checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    if (filter == "all" || filter == "keccak256_sponge_u64") {
        uint64_t N = 2000000ULL;
        double t0 = now_ms();
        uint64_t c = bench_keccak256_sponge_u64(N);
        double t1 = now_ms();
        std::printf("BENCH keccak256_sponge_u64 checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    if (filter == "all" || filter == "holdout_bitwise") {
        uint64_t N = 10000000ULL;
        double t0 = now_ms();
        uint64_t c = bench_holdout_bitwise(N);
        double t1 = now_ms();
        std::printf("BENCH holdout_bitwise checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    if (filter == "all" || filter == "holdout_loop_bounds") {
        uint64_t N = 10000000ULL;
        double t0 = now_ms();
        uint64_t c = bench_holdout_loop_bounds(N);
        double t1 = now_ms();
        std::printf("BENCH holdout_loop_bounds checksum=%llu time_ms=%.4f\n",
                    (unsigned long long)c, t1 - t0);
    }

    return 0;
}
