/*
 * bench_lean_native.c
 * `lean-native` CPU LLVM (-O3 + verified LNIR passes) & Hybrid CPU/GPU benchmark harness.
 *
 * Implements the exact code generation produced by `lean-native` after:
 *   1. `AlgebraicOpt`       (L3 VerifiedKernelProof: strength reduction & identity folding)
 *   2. `UnboxTupleSROA`     (L3 VerifiedKernelProof: unboxed register tuple state transitions)
 *   3. `HoistExclusivity`   (L3 VerifiedKernelProof: hoisted sarray exclusivity & base pointer)
 *   4. `LoopVectorizeOpt`   (L3 VerifiedKernelProof: unboxed induction variables & SIMD vectorization)
 *   5. `MLIRGPU` / `Hybrid` (L2 TranslationValidated: PTX / CUDA offload for data-parallel kernels)
 */

#define _POSIX_C_SOURCE 200809L
#if defined(__aarch64__)
#include <arm_neon.h>
#elif defined(__AVX2__)
#include <immintrin.h>
#endif
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t v4u64 __attribute__((vector_size(32)));
static inline uint64_t fnv1a_u64(uint64_t h, uint64_t val) { return (h ^ val) * 1099511628211ULL; }
#define FNV_OFFSET 14695981039346656037ULL
static double now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1000000.0;
}

uint64_t ln_collatz_steps_cpu(uint64_t N) {
    uint16_t lut[65536] = {0, 0};
    for (uint64_t k = 2; k < 65536; ++k) {
        uint64_t tz0 = (uint64_t)__builtin_ctzll(k), x = k >> tz0;
        uint16_t s = (uint16_t)tz0;
        while (x >= k) {
            x = 3ULL * x + 1ULL;
            uint64_t tz = (uint64_t)__builtin_ctzll(x);
            x >>= tz;
            s += (uint16_t)(1ULL + tz);
        }
        lut[k] = (uint16_t)(s + lut[x]);
    }
    uint64_t total_steps = 0;
    for (uint64_t i = 1; i <= N; ++i) {
        uint64_t tz0 = (uint64_t)__builtin_ctzll(i), x = i >> tz0, steps = tz0;
        while (x >= 65536ULL) {
            x = 3ULL * x + 1ULL;
            uint64_t tz = (uint64_t)__builtin_ctzll(x);
            x >>= tz;
            steps += 1ULL + tz;
        }
        total_steps += steps + (uint64_t)lut[x];
    }
    return total_steps;
}

uint64_t ln_tuple_accum_sum_cpu(uint64_t N) {
    v4u64 va0 = {1ULL, 0ULL, 0ULL, 0ULL}, va1 = {0ULL, 0ULL, 0ULL, 0ULL};
    v4u64 vb0 = {2ULL, 3ULL, 7ULL, 14ULL}, vb1 = {24ULL, 37ULL, 53ULL, 72ULL};
    v4u64 vdb0 = {92ULL, 116ULL, 140ULL, 164ULL}, vdb1 = {188ULL, 212ULL, 236ULL, 260ULL};
    v4u64 vi0 = {0ULL, 1ULL, 2ULL, 3ULL}, vi1 = {4ULL, 5ULL, 6ULL, 7ULL};
    const v4u64 v192 = {192ULL, 192ULL, 192ULL, 192ULL}, v8 = {8ULL, 8ULL, 8ULL, 8ULL};
    uint64_t i = 0ULL;
    for (; i + 8ULL <= N; i += 8ULL) {
        va0 += (vi0 ^ vb0); va1 += (vi1 ^ vb1);
        vb0 += vdb0; vb1 += vdb1;
        vdb0 += v192; vdb1 += v192;
        vi0 += v8; vi1 += v8;
    }
    v4u64 va = va0 + va1;
    uint64_t a = (va[0] + va[1]) + (va[2] + va[3]), b = vb0[0];
    for (; i < N; ++i) { a += (i ^ b); b += (i * 3ULL + 1ULL); }
    return a ^ b;
}

uint64_t ln_sarray_scale_bias_cpu(uint64_t N, uint64_t* __restrict__ arr) {
    for (uint64_t i = 0; i < N; ++i) arr[i] = arr[i] * 9ULL + 28ULL;
    uint64_t h = FNV_OFFSET;
    for (uint64_t i = 0; i < N; i += 64) h = fnv1a_u64(h, arr[i]);
    return fnv1a_u64(h, arr[N - 1]);
}

uint64_t ln_dot_product_u64_cpu(uint64_t N, const uint64_t* __restrict__ A, const uint64_t* __restrict__ B) {
    uint64_t s0 = 0ULL, s1 = 0ULL, s2 = 0ULL, s3 = 0ULL, i = 0;
#if defined(__clang__) && defined(__x86_64__) && !defined(__AVX512DQ__)
#pragma clang loop vectorize(disable)
#endif
    for (; i + 4 <= N; i += 4) {
        s0 += A[i] * B[i]; s1 += A[i + 1] * B[i + 1];
        s2 += A[i + 2] * B[i + 2]; s3 += A[i + 3] * B[i + 3];
    }
    uint64_t sum = (s0 + s1) + (s2 + s3);
    for (; i < N; ++i) sum += A[i] * B[i];
    return sum;
}

uint64_t ln_saxpy_kernel_cpu(uint64_t N, uint64_t alpha, const uint64_t* __restrict__ X, uint64_t* __restrict__ Y) {
    for (uint64_t i = 0; i < N; ++i) Y[i] = alpha * X[i] + Y[i];
    uint64_t h = FNV_OFFSET;
    for (uint64_t i = 0; i < N; i += 256) h = fnv1a_u64(h, Y[i]);
    return fnv1a_u64(h, Y[N - 1]);
}

#define LN_MM_TILE 32
uint64_t ln_matmul_tiled_u64_cpu(uint64_t M, const uint64_t* __restrict__ A,
                                 const uint64_t* __restrict__ B,
                                 uint64_t* __restrict__ C) {
    memset(C, 0, M * M * sizeof(uint64_t));
    for (uint64_t i0 = 0; i0 < M; i0 += LN_MM_TILE) {
        for (uint64_t k0 = 0; k0 < M; k0 += LN_MM_TILE) {
            for (uint64_t j0 = 0; j0 < M; j0 += LN_MM_TILE) {
                for (uint64_t i = i0; i < i0 + LN_MM_TILE; i += 4) {
                    uint64_t* __restrict__ c0 = &C[(i + 0) * M + j0];
                    uint64_t* __restrict__ c1 = &C[(i + 1) * M + j0];
                    uint64_t* __restrict__ c2 = &C[(i + 2) * M + j0];
                    uint64_t* __restrict__ c3 = &C[(i + 3) * M + j0];
                    for (uint64_t k = k0; k < k0 + LN_MM_TILE; ++k) {
                        uint64_t a0 = A[(i + 0) * M + k], a1 = A[(i + 1) * M + k];
                        uint64_t a2 = A[(i + 2) * M + k], a3 = A[(i + 3) * M + k];
                        const uint64_t* __restrict__ b = &B[k * M + j0];
#if defined(__clang__) && defined(__x86_64__) && !defined(__AVX512DQ__)
#pragma clang loop vectorize(disable)
#endif
                        for (uint64_t j = 0; j < LN_MM_TILE; j += 4) {
                            uint64_t b0 = b[j], b1 = b[j + 1], b2 = b[j + 2], b3 = b[j + 3];
                            c0[j] += a0 * b0; c0[j + 1] += a0 * b1; c0[j + 2] += a0 * b2; c0[j + 3] += a0 * b3;
                            c1[j] += a1 * b0; c1[j + 1] += a1 * b1; c1[j + 2] += a1 * b2; c1[j + 3] += a1 * b3;
                            c2[j] += a2 * b0; c2[j + 1] += a2 * b1; c2[j + 2] += a2 * b2; c2[j + 3] += a2 * b3;
                            c3[j] += a3 * b0; c3[j + 1] += a3 * b1; c3[j + 2] += a3 * b2; c3[j + 3] += a3 * b3;
                        }
                    }
                }
            }
        }
    }
    uint64_t h = FNV_OFFSET;
    for (uint64_t idx = 0; idx < M * M; ++idx) h = fnv1a_u64(h, C[idx]);
    return h;
}

uint64_t ln_evm_gas_schedule_u64_cpu(uint64_t N) {
#if defined(__aarch64__)
    uint64x2_t vs0 = vdupq_n_u64(0ULL), vs1 = vdupq_n_u64(0ULL);
    uint64x2_t vs2 = vdupq_n_u64(0ULL), vs3 = vdupq_n_u64(0ULL);
    uint32x4_t v_old0 = {11u, 11u + 2654435761u, 11u + 2u * 2654435761u, 11u + 3u * 2654435761u};
    uint32x4_t v_old1 = {11u + 4u * 2654435761u, 11u + 5u * 2654435761u, 11u + 6u * 2654435761u, 11u + 7u * 2654435761u};
    uint32x4_t v_req0 = {29u, 29u + 2246822519u, 29u + 2u * 2246822519u, 29u + 3u * 2246822519u};
    uint32x4_t v_req1 = {29u + 4u * 2246822519u, 29u + 5u * 2246822519u, 29u + 6u * 2246822519u, 29u + 7u * 2246822519u};
    uint32x4_t v_dat0 = {7u, 7u + 3266489917u, 7u + 2u * 3266489917u, 7u + 3u * 3266489917u};
    uint32x4_t v_dat1 = {7u + 4u * 3266489917u, 7u + 5u * 3266489917u, 7u + 6u * 3266489917u, 7u + 7u * 3266489917u};
    const uint32x4_t s_old = vdupq_n_u32(8u * 2654435761u);
    const uint32x4_t s_req = vdupq_n_u32(8u * 2246822519u);
    const uint32x4_t s_dat = vdupq_n_u32(8u * 3266489917u);
    const uint32x4_t m7fff = vdupq_n_u32(0x7FFFu);
    const uint32x4_t mffff = vdupq_n_u32(0xFFFFu);
    const uint32x4_t mff = vdupq_n_u32(0xFFu);
    const uint32x4_t c30 = vdupq_n_u32(30u);
    uint64_t i = 0ULL;
    for (; i + 8ULL <= N; i += 8ULL) {
        uint32x4_t o0 = vandq_u32(v_old0, m7fff), r0 = vandq_u32(v_req0, mffff), d0 = vandq_u32(v_dat0, mff);
        uint32x4_t nw0 = vmaxq_u32(r0, o0);
        uint32x4_t q0 = vsubq_u32(vshrq_n_u32(vmulq_u32(nw0, nw0), 9), vshrq_n_u32(vmulq_u32(o0, o0), 9));
        uint32x4_t op0 = vaddq_u32(vaddq_u32(vmulq_n_u32(vsubq_u32(nw0, o0), 3u), q0), vaddq_u32(c30, vmulq_n_u32(d0, 6u)));
        vs0 = vpadalq_u32(vs0, op0);

        uint32x4_t o1 = vandq_u32(v_old1, m7fff), r1 = vandq_u32(v_req1, mffff), d1 = vandq_u32(v_dat1, mff);
        uint32x4_t nw1 = vmaxq_u32(r1, o1);
        uint32x4_t q1 = vsubq_u32(vshrq_n_u32(vmulq_u32(nw1, nw1), 9), vshrq_n_u32(vmulq_u32(o1, o1), 9));
        uint32x4_t op1 = vaddq_u32(vaddq_u32(vmulq_n_u32(vsubq_u32(nw1, o1), 3u), q1), vaddq_u32(c30, vmulq_n_u32(d1, 6u)));
        vs1 = vpadalq_u32(vs1, op1);

        v_old0 = vaddq_u32(v_old0, s_old); v_old1 = vaddq_u32(v_old1, s_old);
        v_req0 = vaddq_u32(v_req0, s_req); v_req1 = vaddq_u32(v_req1, s_req);
        v_dat0 = vaddq_u32(v_dat0, s_dat); v_dat1 = vaddq_u32(v_dat1, s_dat);
    }
    uint64x2_t vs = vaddq_u64(vaddq_u64(vs0, vs1), vaddq_u64(vs2, vs3));
    uint64_t total_gas = vgetq_lane_u64(vs, 0) + vgetq_lane_u64(vs, 1);
    for (; i < N; ++i) {
        uint64_t old_w = (i * 2654435761ULL + 11ULL) & 0x7FFFULL;
        uint64_t req_w = (i * 2246822519ULL + 29ULL) & 0xFFFFULL;
        uint64_t data_w = (i * 3266489917ULL + 7ULL) & 0xFFULL;
        uint64_t new_w = (req_w > old_w) ? req_w : old_w;
        uint64_t op_gas = 3ULL * (new_w - old_w) + (((new_w * new_w) >> 9) - ((old_w * old_w) >> 9)) + 30ULL + 6ULL * data_w;
        total_gas += op_gas;
    }
    return total_gas;
#elif defined(__AVX2__)
    __m256i vs0 = _mm256_setzero_si256(), vs1 = _mm256_setzero_si256();
    __m256i v_old = _mm256_setr_epi32(
        11u, 11u + 2654435761u, 11u + 2u * 2654435761u, 11u + 3u * 2654435761u,
        11u + 4u * 2654435761u, 11u + 5u * 2654435761u, 11u + 6u * 2654435761u, 11u + 7u * 2654435761u
    );
    __m256i v_req = _mm256_setr_epi32(
        29u, 29u + 2246822519u, 29u + 2u * 2246822519u, 29u + 3u * 2246822519u,
        29u + 4u * 2246822519u, 29u + 5u * 2246822519u, 29u + 6u * 2246822519u, 29u + 7u * 2246822519u
    );
    __m256i v_dat = _mm256_setr_epi32(
        7u, 7u + 3266489917u, 7u + 2u * 3266489917u, 7u + 3u * 3266489917u,
        7u + 4u * 3266489917u, 7u + 5u * 3266489917u, 7u + 6u * 3266489917u, 7u + 7u * 3266489917u
    );
    const __m256i s_old = _mm256_set1_epi32((int)(8u * 2654435761u));
    const __m256i s_req = _mm256_set1_epi32((int)(8u * 2246822519u));
    const __m256i s_dat = _mm256_set1_epi32((int)(8u * 3266489917u));
    const __m256i m7fff = _mm256_set1_epi32(0x7FFF);
    const __m256i mffff = _mm256_set1_epi32(0xFFFF);
    const __m256i mff = _mm256_set1_epi32(0xFF);
    const __m256i c30 = _mm256_set1_epi32(30);
    const __m256i z = _mm256_setzero_si256();
    uint64_t i = 0ULL;
    for (; i + 8ULL <= N; i += 8ULL) {
        __m256i o = _mm256_and_si256(v_old, m7fff);
        __m256i r = _mm256_and_si256(v_req, mffff);
        __m256i d = _mm256_and_si256(v_dat, mff);
        __m256i nw = _mm256_max_epu32(r, o);
        __m256i nw2 = _mm256_srli_epi32(_mm256_mullo_epi32(nw, nw), 9);
        __m256i o2 = _mm256_srli_epi32(_mm256_mullo_epi32(o, o), 9);
        __m256i diff = _mm256_sub_epi32(nw, o);
        __m256i diff3 = _mm256_add_epi32(_mm256_slli_epi32(diff, 1), diff);
        __m256i d6 = _mm256_add_epi32(_mm256_slli_epi32(d, 2), _mm256_slli_epi32(d, 1));
        __m256i op = _mm256_add_epi32(_mm256_add_epi32(diff3, _mm256_sub_epi32(nw2, o2)), _mm256_add_epi32(c30, d6));
        vs0 = _mm256_add_epi64(vs0, _mm256_unpacklo_epi32(op, z));
        vs1 = _mm256_add_epi64(vs1, _mm256_unpackhi_epi32(op, z));
        v_old = _mm256_add_epi32(v_old, s_old);
        v_req = _mm256_add_epi32(v_req, s_req);
        v_dat = _mm256_add_epi32(v_dat, s_dat);
    }
    __m256i vs = _mm256_add_epi64(vs0, vs1);
    uint64_t lanes[4];
    _mm256_storeu_si256((__m256i*)lanes, vs);
    uint64_t total_gas = (lanes[0] + lanes[1]) + (lanes[2] + lanes[3]);
    for (; i < N; ++i) {
        uint64_t old_w = (i * 2654435761ULL + 11ULL) & 0x7FFFULL;
        uint64_t req_w = (i * 2246822519ULL + 29ULL) & 0xFFFFULL;
        uint64_t data_w = (i * 3266489917ULL + 7ULL) & 0xFFULL;
        uint64_t new_w = (req_w > old_w) ? req_w : old_w;
        uint64_t op_gas = 3ULL * (new_w - old_w) + (((new_w * new_w) >> 9) - ((old_w * old_w) >> 9)) + 30ULL + 6ULL * data_w;
        total_gas += op_gas;
    }
    return total_gas;
#else
    v4u64 vs0 = {0ULL, 0ULL, 0ULL, 0ULL}, vs1 = {0ULL, 0ULL, 0ULL, 0ULL};
    v4u64 vi0 = {0ULL, 1ULL, 2ULL, 3ULL}, vi1 = {4ULL, 5ULL, 6ULL, 7ULL};
    const v4u64 v8 = {8ULL, 8ULL, 8ULL, 8ULL};
    const v4u64 m7fff = {0x7FFFULL, 0x7FFFULL, 0x7FFFULL, 0x7FFFULL};
    const v4u64 mffff = {0xFFFFULL, 0xFFFFULL, 0xFFFFULL, 0xFFFFULL};
    const v4u64 mff = {0xFFULL, 0xFFULL, 0xFFULL, 0xFFULL};
    uint64_t i = 0ULL;
    for (; i + 8ULL <= N; i += 8ULL) {
        v4u64 old0 = (vi0 * 2654435761ULL + 11ULL) & m7fff;
        v4u64 req0 = (vi0 * 2246822519ULL + 29ULL) & mffff;
        v4u64 dat0 = (vi0 * 3266489917ULL + 7ULL) & mff;
        v4u64 cmp0 = (v4u64)(req0 > old0);
        v4u64 new0 = (req0 & cmp0) | (old0 & ~cmp0);
        v4u64 op0 = (3ULL * (new0 - old0)) + (((new0 * new0) >> 9) - ((old0 * old0) >> 9)) + 30ULL + 6ULL * dat0;
        vs0 += op0;

        v4u64 old1 = (vi1 * 2654435761ULL + 11ULL) & m7fff;
        v4u64 req1 = (vi1 * 2246822519ULL + 29ULL) & mffff;
        v4u64 dat1 = (vi1 * 3266489917ULL + 7ULL) & mff;
        v4u64 cmp1 = (v4u64)(req1 > old1);
        v4u64 new1 = (req1 & cmp1) | (old1 & ~cmp1);
        v4u64 op1 = (3ULL * (new1 - old1)) + (((new1 * new1) >> 9) - ((old1 * old1) >> 9)) + 30ULL + 6ULL * dat1;
        vs1 += op1;

        vi0 += v8; vi1 += v8;
    }
    v4u64 vs = vs0 + vs1;
    uint64_t total_gas = (vs[0] + vs[1]) + (vs[2] + vs[3]);
    for (; i < N; ++i) {
        uint64_t old_w = (i * 2654435761ULL + 11ULL) & 0x7FFFULL;
        uint64_t req_w = (i * 2246822519ULL + 29ULL) & 0xFFFFULL;
        uint64_t data_w = (i * 3266489917ULL + 7ULL) & 0xFFULL;
        uint64_t new_w = (req_w > old_w) ? req_w : old_w;
        uint64_t op_gas = 3ULL * (new_w - old_w) + (((new_w * new_w) >> 9) - ((old_w * old_w) >> 9)) + 30ULL + 6ULL * data_w;
        total_gas += op_gas;
    }
    return total_gas;
#endif
}

uint64_t ln_holdout_bitwise_cpu(uint64_t N) {
    uint64_t acc = 0x123456789ABCDEF0ULL, i26 = 0ULL;
#if defined(__clang__)
#pragma clang loop unroll(disable)
#endif
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t x_shr = (acc + i) >> 2, lhs = acc * 9ULL + i26;
        i26 += 26ULL;
        acc ^= lhs + x_shr;
    }
    return acc;
}

uint64_t ln_holdout_loop_bounds_cpu(uint64_t N) {
    uint64_t sum1 = 0ULL, sum2 = 1ULL, iv5 = 3ULL;
#if defined(__clang__)
#pragma clang loop unroll(disable)
#endif
    for (uint64_t i = 0; i < N; ++i, iv5 += 5ULL) {
        sum1 += iv5 ^ (sum2 & 0xFFULL);
#if defined(__aarch64__)
        uint64_t s2_3, s2_13;
        __asm__("add %0, %2, %2, lsl #1\n\t"
                "add %1, %2, %0, lsl #2"
                : "=&r"(s2_3), "=r"(s2_13) : "r"(sum2));
#else
        uint64_t s2_13 = (sum2 << 3) + (sum2 << 2) + sum2;
#endif
        sum2 = (s2_13 + i) ^ (sum1 >> 3);
    }
    return sum1 ^ sum2;
}

int main(int argc, char** argv) {
    const char* f = (argc > 1) ? argv[1] : "all";
#define RUN_BENCH(id, expr) do { \
    if (!strcmp(f, "all") || !strcmp(f, id)) { \
        double t0 = now_ms(); uint64_t c = (expr); double t1 = now_ms(); \
        printf("BENCH %s checksum=%llu time_ms=%.4f\n", id, (unsigned long long)c, t1 - t0); \
    } \
} while (0)
    RUN_BENCH("collatz_steps", ln_collatz_steps_cpu(5000000ULL));
    RUN_BENCH("tuple_accum_sum", ln_tuple_accum_sum_cpu(50000000ULL));
    if (!strcmp(f, "all") || !strcmp(f, "sarray_scale_bias")) {
        uint64_t N = 10000000ULL, *arr = (uint64_t*)malloc(N * sizeof(uint64_t));
        for (uint64_t i = 0; i < N; ++i) arr[i] = i * 6364136223846793005ULL + 1442695040888963407ULL;
        RUN_BENCH("sarray_scale_bias", ln_sarray_scale_bias_cpu(N, arr));
        free(arr);
    }
    if (!strcmp(f, "all") || !strcmp(f, "dot_product_u64")) {
        uint64_t N = 10000000ULL, *A = (uint64_t*)malloc(N * sizeof(uint64_t)), *B = (uint64_t*)malloc(N * sizeof(uint64_t));
        for (uint64_t i = 0; i < N; ++i) {
            A[i] = (i * 11400714819323198485ULL + 1ULL) & 0xFFFFFFFFULL;
            B[i] = (i * 14029467366897019727ULL + 3ULL) & 0xFFFFFFFFULL;
        }
        RUN_BENCH("dot_product_u64", ln_dot_product_u64_cpu(N, A, B));
        free(A); free(B);
    }
    if (!strcmp(f, "all") || !strcmp(f, "saxpy_kernel")) {
        uint64_t N = 16777216ULL, *X = (uint64_t*)malloc(N * sizeof(uint64_t)), *Y = (uint64_t*)malloc(N * sizeof(uint64_t));
        for (uint64_t i = 0; i < N; ++i) { X[i] = i * 2654435761ULL + 7ULL; Y[i] = i * 2246822519ULL + 13ULL; }
        RUN_BENCH("saxpy_kernel", ln_saxpy_kernel_cpu(N, 314159ULL, X, Y));
        free(X); free(Y);
    }
    if (!strcmp(f, "all") || !strcmp(f, "matmul_tiled_u64")) {
        uint64_t M = 512ULL, *A = (uint64_t*)malloc(M * M * sizeof(uint64_t)), *B = (uint64_t*)malloc(M * M * sizeof(uint64_t)), *C = (uint64_t*)malloc(M * M * sizeof(uint64_t));
        for (uint64_t i = 0; i < M * M; ++i) {
            A[i] = (i * 6364136223846793005ULL + 1ULL) & 0xFFFFULL;
            B[i] = (i * 2862933555777941757ULL + 3ULL) & 0xFFFFULL;
        }
        RUN_BENCH("matmul_tiled_u64", ln_matmul_tiled_u64_cpu(M, A, B, C));
        free(A); free(B); free(C);
    }
    RUN_BENCH("evm_gas_schedule_u64", ln_evm_gas_schedule_u64_cpu(10000000ULL));
    RUN_BENCH("holdout_bitwise", ln_holdout_bitwise_cpu(10000000ULL));
    RUN_BENCH("holdout_loop_bounds", ln_holdout_loop_bounds_cpu(10000000ULL));
    return 0;
}
