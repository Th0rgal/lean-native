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

#ifdef __cplusplus
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#else
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define constexpr const
#endif

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
    memset(C, 0, M * M * sizeof(uint64_t));
    const uint64_t TILE = 32;
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

// 9. uint256_wad_muldiv_u64 (N = 5,000,000)
// Verity 2.0 TickLib.wMulDown + UInt256BitVecBridge 128-bit carry & 64x64->128 widening multiply
uint64_t bench_uint256_wad_muldiv_u64(uint64_t N) {
    uint64_t total = 0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t x0 = i * 6364136223846793005ULL + 1442695040888963407ULL;
        uint64_t x1 = i * 2862933555777941757ULL + 3ULL;
        uint64_t y0 = (i ^ 0x5555555555555555ULL) * 11400714819323198485ULL + 7ULL;
        uint64_t y1 = i * 3266489917ULL + 11ULL;
        uint64_t s0 = x0 + y0;
        uint64_t carry = (s0 < x0) ? 1ULL : 0ULL;
        uint64_t s1 = x1 + y1 + carry;
        unsigned __int128 p0 = (unsigned __int128)x0 * (unsigned __int128)y0;
        unsigned __int128 p1 = (unsigned __int128)s0 * 1000000000000000000ULL;
        uint64_t lo0 = (uint64_t)p0, hi0 = (uint64_t)(p0 >> 64);
        uint64_t lo1 = (uint64_t)p1, hi1 = (uint64_t)(p1 >> 64);
        uint64_t step_val = s0 ^ s1 ^ hi0 ^ hi1 ^ (lo0 >> 32) ^ (lo1 >> 32);
        total += step_val;
    }
    return total;
}

// 10. goldilocks_ntt_modmul_u64 (N = 5,000,000)
// Proximity Prize / EIP-8200 Goldilocks prime field (M = 2^64 - 2^32 + 1) modular multiplication
uint64_t bench_goldilocks_ntt_modmul_u64(uint64_t N) {
    const uint64_t EPS = 0xFFFFFFFFULL;
    const uint64_t M = 0xFFFFFFFF00000001ULL;
    uint64_t total = 0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t a = i * 6364136223846793005ULL + 1442695040888963407ULL;
        uint64_t b = (i ^ 0xAAAAAAAAAAAAAAAAULL) * 11400714819323198485ULL + 7ULL;
        unsigned __int128 p = (unsigned __int128)a * (unsigned __int128)b;
        uint64_t lo = (uint64_t)p, hi = (uint64_t)(p >> 64);
        uint64_t x2 = hi & EPS, x3 = hi >> 32;
        uint64_t t0 = lo - x3;
        if (lo < x3) t0 -= EPS;
        uint64_t add2 = (x2 << 32) - x2;
        uint64_t t1 = t0 + add2;
        if (t1 < t0) t1 += EPS;
        uint64_t r = (t1 >= M) ? (t1 - M) : t1;
        total += (r ^ (a + b));
    }
    return total;
}

// 11. babybear_poseidon2_sbox_u64 (N = 5,000,000)
// Proximity Prize / EIP-8200 / Plonky3 BabyBear prime field (P = 2^31 - 2^27 + 1) Poseidon2 S-box (x^7 mod P)
uint64_t bench_babybear_poseidon2_sbox_u64(uint64_t N) {
    const uint64_t P = 2013265921ULL;
    uint64_t total = 0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t x0 = (i * 2654435761ULL + 17ULL) & 0x3FFFFFFFULL;
        uint64_t x1 = (i * 2246822519ULL + 29ULL) & 0x3FFFFFFFULL;
        uint64_t x2 = (i * 3266489917ULL + 43ULL) & 0x3FFFFFFFULL;
        uint64_t x3 = (i * 668265263ULL + 59ULL) & 0x3FFFFFFFULL;
        uint64_t x0_2 = (x0 * x0) % P, x0_3 = (x0_2 * x0) % P, x0_4 = (x0_2 * x0_2) % P, y0 = (x0_4 * x0_3) % P;
        uint64_t x1_2 = (x1 * x1) % P, x1_3 = (x1_2 * x1) % P, x1_4 = (x1_2 * x1_2) % P, y1 = (x1_4 * x1_3) % P;
        uint64_t x2_2 = (x2 * x2) % P, x2_3 = (x2_2 * x2) % P, x2_4 = (x2_2 * x2_2) % P, y2 = (x2_4 * x2_3) % P;
        uint64_t x3_2 = (x3 * x3) % P, x3_3 = (x3_2 * x3) % P, x3_4 = (x3_2 * x3_2) % P, y3 = (x3_4 * x3_3) % P;
        uint64_t t = y0 + y1 + y2 + y3;
        total += ((y0 + t) ^ ((y1 + t) << 16)) + ((y2 + t) ^ ((y3 + t) << 32));
    }
    return total;
}

// 12. mersenne31_circle_butterfly_u64 (N = 5,000,000)
// Proximity Prize / EIP-8200 / Stwo / Plonky3 Mersenne-31 Circle STARK (P = 2^31 - 1) 4-lane butterfly
uint64_t bench_mersenne31_circle_butterfly_u64(uint64_t N) {
    const uint64_t P = 2147483647ULL;
    const uint64_t MASK = 0x3FFFFFFFULL;
    uint64_t total = 0ULL;
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t a = (i * 2654435761ULL + 17ULL) & MASK;
        uint64_t b = (i * 2246822519ULL + 29ULL) & MASK;
        uint64_t c = (i * 3266489917ULL + 43ULL) & MASK;
        uint64_t d = (i * 668265263ULL + 59ULL) & MASK;
        uint64_t w = (i * 1664525ULL + 1013904223ULL) & MASK;
        uint64_t tw_r = (c * w) % P;
        uint64_t tw_i = (d * ((w ^ 0x15555555ULL) & MASK)) % P;
        uint64_t y0 = (a + tw_r) % P;
        uint64_t y1 = (a + P - tw_r) % P;
        uint64_t y2 = (b + tw_i) % P;
        uint64_t y3 = (b + P - tw_i) % P;
        uint64_t s = ((y0 * y2) % P) ^ ((y1 * y3) % P);
        total += s + ((y0 ^ (y1 << 16)) + (y2 ^ (y3 << 32)));
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

static double now_ms(void) {
#ifdef __cplusplus
    auto now = std::chrono::steady_clock::now().time_since_epoch();
    return std::chrono::duration<double, std::milli>(now).count();
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1000000.0;
#endif
}

int main(int argc, char** argv) {
    const char* f = (argc > 1) ? argv[1] : "all";
#define RUN_SCALAR_BENCH(id, expr) do { \
    if (!strcmp(f, "all") || !strcmp(f, id)) { \
        double t0 = now_ms(); uint64_t c = (expr); double t1 = now_ms(); \
        printf("BENCH %s checksum=%llu time_ms=%.4f\n", id, (unsigned long long)c, t1 - t0); \
    } \
} while (0)

    RUN_SCALAR_BENCH("collatz_steps", bench_collatz_steps(5000000ULL));
    RUN_SCALAR_BENCH("tuple_accum_sum", bench_tuple_accum_sum(50000000ULL));

    if (!strcmp(f, "all") || !strcmp(f, "sarray_scale_bias")) {
        uint64_t N = 10000000ULL;
        uint64_t* arr = (uint64_t*)malloc(N * sizeof(uint64_t));
        for (uint64_t i = 0; i < N; ++i) arr[i] = i * 6364136223846793005ULL + 1442695040888963407ULL;
        RUN_SCALAR_BENCH("sarray_scale_bias", bench_sarray_scale_bias(N, arr));
        free(arr);
    }

    if (!strcmp(f, "all") || !strcmp(f, "dot_product_u64")) {
        uint64_t N = 10000000ULL;
        uint64_t* A = (uint64_t*)malloc(N * sizeof(uint64_t));
        uint64_t* B = (uint64_t*)malloc(N * sizeof(uint64_t));
        for (uint64_t i = 0; i < N; ++i) {
            A[i] = (i * 11400714819323198485ULL + 1ULL) & 0xFFFFFFFFULL;
            B[i] = (i * 14029467366897019727ULL + 3ULL) & 0xFFFFFFFFULL;
        }
        RUN_SCALAR_BENCH("dot_product_u64", bench_dot_product_u64(N, A, B));
        free(A); free(B);
    }

    if (!strcmp(f, "all") || !strcmp(f, "saxpy_kernel")) {
        uint64_t N = 16777216ULL;
        uint64_t* X = (uint64_t*)malloc(N * sizeof(uint64_t));
        uint64_t* Y = (uint64_t*)malloc(N * sizeof(uint64_t));
        for (uint64_t i = 0; i < N; ++i) {
            X[i] = i * 2654435761ULL + 7ULL;
            Y[i] = i * 2246822519ULL + 13ULL;
        }
        RUN_SCALAR_BENCH("saxpy_kernel", bench_saxpy_kernel(N, 314159ULL, X, Y));
        free(X); free(Y);
    }

    if (!strcmp(f, "all") || !strcmp(f, "matmul_tiled_u64")) {
        uint64_t M = 512ULL;
        uint64_t* A = (uint64_t*)malloc(M * M * sizeof(uint64_t));
        uint64_t* B = (uint64_t*)malloc(M * M * sizeof(uint64_t));
        uint64_t* C = (uint64_t*)malloc(M * M * sizeof(uint64_t));
        for (uint64_t i = 0; i < M * M; ++i) {
            A[i] = (i * 6364136223846793005ULL + 1ULL) & 0xFFFFULL;
            B[i] = (i * 2862933555777941757ULL + 3ULL) & 0xFFFFULL;
        }
        RUN_SCALAR_BENCH("matmul_tiled_u64", bench_matmul_tiled_u64(M, A, B, C));
        free(A); free(B); free(C);
    }

    RUN_SCALAR_BENCH("evm_gas_schedule_u64", bench_evm_gas_schedule_u64(10000000ULL));
    RUN_SCALAR_BENCH("keccak256_sponge_u64", bench_keccak256_sponge_u64(2000000ULL));
    RUN_SCALAR_BENCH("uint256_wad_muldiv_u64", bench_uint256_wad_muldiv_u64(5000000ULL));
    RUN_SCALAR_BENCH("goldilocks_ntt_modmul_u64", bench_goldilocks_ntt_modmul_u64(5000000ULL));
    RUN_SCALAR_BENCH("babybear_poseidon2_sbox_u64", bench_babybear_poseidon2_sbox_u64(5000000ULL));
    RUN_SCALAR_BENCH("mersenne31_circle_butterfly_u64", bench_mersenne31_circle_butterfly_u64(5000000ULL));
    RUN_SCALAR_BENCH("holdout_bitwise", bench_holdout_bitwise(10000000ULL));
    RUN_SCALAR_BENCH("holdout_loop_bounds", bench_holdout_loop_bounds(10000000ULL));

    return 0;
}
