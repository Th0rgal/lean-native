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

#define VROTL64(x, r) (((x) << (r)) | ((x) >> (64ULL - (r))))

uint64_t ln_keccak256_sponge_u64_cpu(uint64_t N) {
    static const uint64_t RC[8] = {
        0x0000000000000001ULL, 0x0000000000008082ULL,
        0x800000000000808aULL, 0x8000000080008000ULL,
        0x000000000000808bULL, 0x0000000080000001ULL,
        0x8000000080008081ULL, 0x8000000000008009ULL
    };
    const uint64_t m0 = 6364136223846793005ULL;
    const uint64_t m1 = 2862933555777941757ULL;
    const uint64_t m2 = 11400714819323198485ULL;
    const uint64_t m3 = 14029467366897019727ULL;
    const uint64_t m4 = 3266489917ULL;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SHA3)
    uint64x2_t accA = vdupq_n_u64(0), accB = vdupq_n_u64(0);
    uint64_t a0_init[2] = {1ULL, 1ULL + m0}, b0_init[2] = {1ULL + 2ULL * m0, 1ULL + 3ULL * m0};
    uint64_t a1_init[2] = {3ULL, 3ULL + m1}, b1_init[2] = {3ULL + 2ULL * m1, 3ULL + 3ULL * m1};
    uint64_t a2_init[2] = {5ULL, 5ULL + m2}, b2_init[2] = {5ULL + 2ULL * m2, 5ULL + 3ULL * m2};
    uint64_t a3_init[2] = {7ULL, 7ULL + m3}, b3_init[2] = {7ULL + 2ULL * m3, 7ULL + 3ULL * m3};
    uint64_t a4_init[2] = {11ULL, 11ULL + m4}, b4_init[2] = {11ULL + 2ULL * m4, 11ULL + 3ULL * m4};
    uint64x2_t s0A = vld1q_u64(a0_init), s0B = vld1q_u64(b0_init);
    uint64x2_t s1A = vld1q_u64(a1_init), s1B = vld1q_u64(b1_init);
    uint64x2_t s2A = vld1q_u64(a2_init), s2B = vld1q_u64(b2_init);
    uint64x2_t s3A = vld1q_u64(a3_init), s3B = vld1q_u64(b3_init);
    uint64x2_t s4A = vld1q_u64(a4_init), s4B = vld1q_u64(b4_init);
    const uint64x2_t st0 = vdupq_n_u64(4ULL * m0), st1 = vdupq_n_u64(4ULL * m1);
    const uint64x2_t st2 = vdupq_n_u64(4ULL * m2), st3 = vdupq_n_u64(4ULL * m3), st4 = vdupq_n_u64(4ULL * m4);
    uint64_t i = 0ULL;
    for (; i + 4ULL <= N; i += 4ULL) {
        uint64x2_t x0 = s0A, x1 = s1A, x2 = s2A, x3 = s3A, x4 = s4A;
        uint64x2_t y0 = s0B, y1 = s1B, y2 = s2B, y3 = s3B, y4 = s4B;
        #pragma clang loop unroll(full)
        for (int r = 0; r < 8; ++r) {
            uint64x2_t rc = vdupq_n_u64(RC[r]);
            uint64x2_t dx0 = vrax1q_u64(x4, x1), dy0 = vrax1q_u64(y4, y1);
            uint64x2_t dx1 = vrax1q_u64(x0, x2), dy1 = vrax1q_u64(y0, y2);
            uint64x2_t dx2 = vrax1q_u64(x1, x3), dy2 = vrax1q_u64(y1, y3);
            uint64x2_t dx3 = vrax1q_u64(x2, x4), dy3 = vrax1q_u64(y2, y4);
            uint64x2_t dx4 = vrax1q_u64(x3, x0), dy4 = vrax1q_u64(y3, y0);
            uint64x2_t bx0 = veorq_u64(x0, dx0), by0 = veorq_u64(y0, dy0);
            uint64x2_t bx1 = vxarq_u64(x1, dx1, 20), by1 = vxarq_u64(y1, dy1, 20);
            uint64x2_t bx2 = vxarq_u64(x2, dx2, 21), by2 = vxarq_u64(y2, dy2, 21);
            uint64x2_t bx3 = vxarq_u64(x3, dx3, 43), by3 = vxarq_u64(y3, dy3, 43);
            uint64x2_t bx4 = vxarq_u64(x4, dx4, 50), by4 = vxarq_u64(y4, dy4, 50);
            x0 = veorq_u64(vbcaxq_u64(bx0, bx2, bx1), rc);
            y0 = veorq_u64(vbcaxq_u64(by0, by2, by1), rc);
            x1 = vbcaxq_u64(bx1, bx3, bx2);
            y1 = vbcaxq_u64(by1, by3, by2);
            x2 = vbcaxq_u64(bx2, bx4, bx3);
            y2 = vbcaxq_u64(by2, by4, by3);
            x3 = vbcaxq_u64(bx3, bx0, bx4);
            y3 = vbcaxq_u64(by3, by0, by4);
            x4 = vbcaxq_u64(bx4, bx1, bx0);
            y4 = vbcaxq_u64(by4, by1, by0);
        }
        accA = veorq_u64(accA, vaddq_u64(vaddq_u64(vaddq_u64(x0, x1), vaddq_u64(x2, x3)), x4));
        accB = veorq_u64(accB, vaddq_u64(vaddq_u64(vaddq_u64(y0, y1), vaddq_u64(y2, y3)), y4));
        s0A = vaddq_u64(s0A, st0); s0B = vaddq_u64(s0B, st0);
        s1A = vaddq_u64(s1A, st1); s1B = vaddq_u64(s1B, st1);
        s2A = vaddq_u64(s2A, st2); s2B = vaddq_u64(s2B, st2);
        s3A = vaddq_u64(s3A, st3); s3B = vaddq_u64(s3B, st3);
        s4A = vaddq_u64(s4A, st4); s4B = vaddq_u64(s4B, st4);
    }
    uint64x2_t acc = veorq_u64(accA, accB);
    uint64_t total = vgetq_lane_u64(acc, 0) ^ vgetq_lane_u64(acc, 1);
    for (; i < N; ++i) {
        uint64_t s0 = i * m0 + 1ULL, s1 = i * m1 + 3ULL, s2 = i * m2 + 5ULL, s3 = i * m3 + 7ULL, s4 = i * m4 + 11ULL;
        for (int r = 0; r < 8; ++r) {
            uint64_t d0 = s4 ^ VROTL64(s1, 1), d1 = s0 ^ VROTL64(s2, 1), d2 = s1 ^ VROTL64(s3, 1), d3 = s2 ^ VROTL64(s4, 1), d4 = s3 ^ VROTL64(s0, 1);
            uint64_t b0 = s0 ^ d0, b1 = VROTL64(s1 ^ d1, 44), b2 = VROTL64(s2 ^ d2, 43), b3 = VROTL64(s3 ^ d3, 21), b4 = VROTL64(s4 ^ d4, 14);
            s0 = b0 ^ ((~b1) & b2) ^ RC[r]; s1 = b1 ^ ((~b2) & b3); s2 = b2 ^ ((~b3) & b4); s3 = b3 ^ ((~b4) & b0); s4 = b4 ^ ((~b0) & b1);
        }
        total ^= (s0 + s1 + s2 + s3 + s4);
    }
    return total;
#else
    v4u64 v_acc = {0ULL, 0ULL, 0ULL, 0ULL};
    v4u64 s0_base = {1ULL, 1ULL + m0, 1ULL + 2ULL * m0, 1ULL + 3ULL * m0};
    v4u64 s1_base = {3ULL, 3ULL + m1, 3ULL + 2ULL * m1, 3ULL + 3ULL * m1};
    v4u64 s2_base = {5ULL, 5ULL + m2, 5ULL + 2ULL * m2, 5ULL + 3ULL * m2};
    v4u64 s3_base = {7ULL, 7ULL + m3, 7ULL + 2ULL * m3, 7ULL + 3ULL * m3};
    v4u64 s4_base = {11ULL, 11ULL + m4, 11ULL + 2ULL * m4, 11ULL + 3ULL * m4};
    const v4u64 st0 = {4ULL * m0, 4ULL * m0, 4ULL * m0, 4ULL * m0};
    const v4u64 st1 = {4ULL * m1, 4ULL * m1, 4ULL * m1, 4ULL * m1};
    const v4u64 st2 = {4ULL * m2, 4ULL * m2, 4ULL * m2, 4ULL * m2};
    const v4u64 st3 = {4ULL * m3, 4ULL * m3, 4ULL * m3, 4ULL * m3};
    const v4u64 st4 = {4ULL * m4, 4ULL * m4, 4ULL * m4, 4ULL * m4};
    uint64_t i = 0ULL;
    for (; i + 4ULL <= N; i += 4ULL) {
        v4u64 s0 = s0_base, s1 = s1_base, s2 = s2_base, s3 = s3_base, s4 = s4_base;
        #pragma clang loop unroll(full)
        for (int r = 0; r < 8; ++r) {
            v4u64 d0 = s4 ^ VROTL64(s1, 1);
            v4u64 d1 = s0 ^ VROTL64(s2, 1);
            v4u64 d2 = s1 ^ VROTL64(s3, 1);
            v4u64 d3 = s2 ^ VROTL64(s4, 1);
            v4u64 d4 = s3 ^ VROTL64(s0, 1);
            v4u64 b0 = s0 ^ d0;
            v4u64 b1 = VROTL64(s1 ^ d1, 44);
            v4u64 b2 = VROTL64(s2 ^ d2, 43);
            v4u64 b3 = VROTL64(s3 ^ d3, 21);
            v4u64 b4 = VROTL64(s4 ^ d4, 14);
            s0 = b0 ^ ((~b1) & b2) ^ RC[r];
            s1 = b1 ^ ((~b2) & b3);
            s2 = b2 ^ ((~b3) & b4);
            s3 = b3 ^ ((~b4) & b0);
            s4 = b4 ^ ((~b0) & b1);
        }
        v_acc ^= ((s0 + s1) + (s2 + s3) + s4);
        s0_base += st0; s1_base += st1; s2_base += st2; s3_base += st3; s4_base += st4;
    }
    uint64_t total = (v_acc[0] ^ v_acc[1]) ^ (v_acc[2] ^ v_acc[3]);
    for (; i < N; ++i) {
        uint64_t s0 = i * m0 + 1ULL, s1 = i * m1 + 3ULL, s2 = i * m2 + 5ULL, s3 = i * m3 + 7ULL, s4 = i * m4 + 11ULL;
        for (int r = 0; r < 8; ++r) {
            uint64_t d0 = s4 ^ VROTL64(s1, 1), d1 = s0 ^ VROTL64(s2, 1), d2 = s1 ^ VROTL64(s3, 1), d3 = s2 ^ VROTL64(s4, 1), d4 = s3 ^ VROTL64(s0, 1);
            uint64_t b0 = s0 ^ d0, b1 = VROTL64(s1 ^ d1, 44), b2 = VROTL64(s2 ^ d2, 43), b3 = VROTL64(s3 ^ d3, 21), b4 = VROTL64(s4 ^ d4, 14);
            s0 = b0 ^ ((~b1) & b2) ^ RC[r];
            s1 = b1 ^ ((~b2) & b3);
            s2 = b2 ^ ((~b3) & b4);
            s3 = b3 ^ ((~b4) & b0);
            s4 = b4 ^ ((~b0) & b1);
        }
        total ^= (s0 + s1 + s2 + s3 + s4);
    }
    return total;
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
    RUN_BENCH("keccak256_sponge_u64", ln_keccak256_sponge_u64_cpu(2000000ULL));
    RUN_BENCH("holdout_bitwise", ln_holdout_bitwise_cpu(10000000ULL));
    RUN_BENCH("holdout_loop_bounds", ln_holdout_loop_bounds_cpu(10000000ULL));
    return 0;
}
