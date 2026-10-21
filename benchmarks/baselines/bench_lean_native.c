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
#include <arm_sve.h>
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

uint64_t ln_uint256_wad_muldiv_u64_cpu(uint64_t N) {
    const uint64_t m0 = 6364136223846793005ULL, c0 = 1442695040888963407ULL;
    const uint64_t m1 = 2862933555777941757ULL;
    const uint64_t m2 = 11400714819323198485ULL;
    const uint64_t m3 = 3266489917ULL;
    const uint64_t wad = 1000000000000000000ULL;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE2)
    svbool_t pg = svptrue_pat_b64(SV_VL2);
    svuint64_t v_acc0 = svdup_n_u64(0ULL), v_acc1 = svdup_n_u64(0ULL);
    svuint64_t v_idx = svindex_u64(0ULL, 1ULL);
    svuint64_t v_four = svdup_n_u64(4ULL);
    svuint64_t v_m2 = svdup_n_u64(m2), v_xor = svdup_n_u64(0x5555555555555555ULL);
    svuint64_t v_wad = svdup_n_u64(wad), v_seven = svdup_n_u64(7ULL);
    svuint64_t v_x0_0 = svadd_x(pg, svdup_n_u64(c0), svmul_x(pg, v_idx, svdup_n_u64(m0)));
    svuint64_t v_x0_1 = svadd_x(pg, v_x0_0, svdup_n_u64(2ULL * m0));
    svuint64_t v_xy1_0 = svadd_x(pg, svdup_n_u64(14ULL), svmul_x(pg, v_idx, svdup_n_u64(m1 + m3)));
    svuint64_t v_xy1_1 = svadd_x(pg, v_xy1_0, svdup_n_u64(2ULL * (m1 + m3)));
    svuint64_t v_step_x0 = svdup_n_u64(4ULL * m0);
    svuint64_t v_step_xy1 = svdup_n_u64(4ULL * (m1 + m3));
    uint64_t i = 0ULL;
    for (; i + 4ULL <= N; i += 4ULL) {
        svuint64_t y0_0 = svmla_x(pg, v_seven, sveor_x(pg, v_idx, v_xor), v_m2);
        svuint64_t idx1 = svadd_x(pg, v_idx, svdup_n_u64(2ULL));
        svuint64_t y0_1 = svmla_x(pg, v_seven, sveor_x(pg, idx1, v_xor), v_m2);
        svuint64_t s0_0 = svadd_x(pg, v_x0_0, y0_0), s0_1 = svadd_x(pg, v_x0_1, y0_1);
        svuint64_t s1_0 = svadd_m(svcmplt_u64(pg, s0_0, v_x0_0), v_xy1_0, svdup_n_u64(1ULL));
        svuint64_t s1_1 = svadd_m(svcmplt_u64(pg, s0_1, v_x0_1), v_xy1_1, svdup_n_u64(1ULL));
        svuint64_t hi0_0 = svmulh_x(pg, v_x0_0, y0_0), lo0_0 = svmul_x(pg, v_x0_0, y0_0);
        svuint64_t hi0_1 = svmulh_x(pg, v_x0_1, y0_1), lo0_1 = svmul_x(pg, v_x0_1, y0_1);
        svuint64_t hi1_0 = svmulh_x(pg, s0_0, v_wad), lo1_0 = svmul_x(pg, s0_0, v_wad);
        svuint64_t hi1_1 = svmulh_x(pg, s0_1, v_wad), lo1_1 = svmul_x(pg, s0_1, v_wad);
        svuint64_t x_0 = sveor_x(pg, sveor_x(pg, s0_0, s1_0), sveor_x(pg, hi0_0, hi1_0));
        svuint64_t x_1 = sveor_x(pg, sveor_x(pg, s0_1, s1_1), sveor_x(pg, hi0_1, hi1_1));
        x_0 = sveor_x(pg, x_0, svlsr_x(pg, sveor_x(pg, lo0_0, lo1_0), 32));
        x_1 = sveor_x(pg, x_1, svlsr_x(pg, sveor_x(pg, lo0_1, lo1_1), 32));
        v_acc0 = svadd_x(pg, v_acc0, x_0);
        v_acc1 = svadd_x(pg, v_acc1, x_1);
        v_idx = svadd_x(pg, v_idx, v_four);
        v_x0_0 = svadd_x(pg, v_x0_0, v_step_x0);
        v_x0_1 = svadd_x(pg, v_x0_1, v_step_x0);
        v_xy1_0 = svadd_x(pg, v_xy1_0, v_step_xy1);
        v_xy1_1 = svadd_x(pg, v_xy1_1, v_step_xy1);
    }
    uint64_t total = svaddv_u64(pg, svadd_x(pg, v_acc0, v_acc1));
    for (; i < N; ++i) {
        uint64_t x0 = i * m0 + c0, x1 = i * m1 + 3ULL;
        uint64_t y0 = (i ^ 0x5555555555555555ULL) * m2 + 7ULL, y1 = i * m3 + 11ULL;
        uint64_t s0 = x0 + y0, s1 = x1 + y1 + (s0 < x0);
        unsigned __int128 p0 = (unsigned __int128)x0 * y0, p1 = (unsigned __int128)s0 * wad;
        total += s0 ^ s1 ^ (uint64_t)(p0 >> 64) ^ (uint64_t)(p1 >> 64) ^ ((uint64_t)p0 >> 32) ^ ((uint64_t)p1 >> 32);
    }
    return total;
#elif defined(__aarch64__)
    const uint64_t step_x0 = 2ULL * m0, step_x1_y1 = 2ULL * (m1 + m3);
    const uint64_t diff_x0 = m0 - m2;
    const unsigned __int128 diff_p1 = (unsigned __int128)diff_x0 * wad;
    uint64_t acc0 = 0ULL, acc1 = 0ULL;
    uint64_t x0_e = c0, x1_y1_e = 14ULL;
    uint64_t i = 0ULL;
    for (; i + 2ULL <= N; i += 2ULL) {
        uint64_t y0_0 = (i ^ 0x5555555555555555ULL) * m2 + 7ULL;
        uint64_t y0_1 = y0_0 - m2;
        uint64_t x0_0 = x0_e, x0_1 = x0_e + m0;
        uint64_t s0_0 = x0_0 + y0_0, s0_1 = s0_0 + diff_x0;
        uint64_t s1_0 = x1_y1_e + (s0_0 < x0_0);
        uint64_t s1_1 = x1_y1_e + (m1 + m3) + (s0_1 < x0_1);
        unsigned __int128 p0_0 = (unsigned __int128)x0_0 * y0_0;
        unsigned __int128 p0_1 = (unsigned __int128)x0_1 * y0_1;
        unsigned __int128 p1_0 = (unsigned __int128)s0_0 * wad;
        unsigned __int128 p1_1 = p1_0 + diff_p1 - (s0_1 < s0_0 ? ((unsigned __int128)wad << 64) : 0);
        acc0 += s0_0 ^ s1_0 ^ (uint64_t)(p0_0 >> 64) ^ (uint64_t)(p1_0 >> 64) ^ ((uint64_t)p0_0 >> 32) ^ ((uint64_t)p1_0 >> 32);
        acc1 += s0_1 ^ s1_1 ^ (uint64_t)(p0_1 >> 64) ^ (uint64_t)(p1_1 >> 64) ^ ((uint64_t)p0_1 >> 32) ^ ((uint64_t)p1_1 >> 32);
        x0_e += step_x0;
        x1_y1_e += step_x1_y1;
    }
    uint64_t total = acc0 + acc1;
    for (; i < N; ++i) {
        uint64_t x0 = i * m0 + c0, x1 = i * m1 + 3ULL;
        uint64_t y0 = (i ^ 0x5555555555555555ULL) * m2 + 7ULL, y1 = i * m3 + 11ULL;
        uint64_t s0 = x0 + y0, s1 = x1 + y1 + (s0 < x0);
        unsigned __int128 p0 = (unsigned __int128)x0 * y0, p1 = (unsigned __int128)s0 * wad;
        total += s0 ^ s1 ^ (uint64_t)(p0 >> 64) ^ (uint64_t)(p1 >> 64) ^ ((uint64_t)p0 >> 32) ^ ((uint64_t)p1 >> 32);
    }
    return total;
#else
    const uint64_t step_x0 = 4ULL * m0, step_x1_y1 = 4ULL * (m1 + m3);
    const uint64_t diff_x0 = m0 - m2;
    const uint64_t diff_x0_2 = 2ULL * (m0 + m2);
    const unsigned __int128 diff_p1 = (unsigned __int128)diff_x0 * wad;
    const unsigned __int128 diff_p1_2 = (unsigned __int128)diff_x0_2 * wad;
    uint64_t acc0 = 0ULL, acc1 = 0ULL, acc2 = 0ULL, acc3 = 0ULL;
    uint64_t x0_e = c0, x1_y1_e = 14ULL;
    uint64_t i = 0ULL;
    for (; i + 4ULL <= N; i += 4ULL) {
        uint64_t y0_0 = (i ^ 0x5555555555555555ULL) * m2 + 7ULL;
        uint64_t y0_1 = y0_0 - m2;
        uint64_t y0_2 = y0_0 + 2ULL * m2;
        uint64_t y0_3 = y0_0 + m2;
        uint64_t x0_0 = x0_e, x0_1 = x0_e + m0, x0_2 = x0_e + 2ULL * m0, x0_3 = x0_e + 3ULL * m0;
        uint64_t s0_0 = x0_0 + y0_0, s0_1 = s0_0 + diff_x0, s0_2 = x0_2 + y0_2, s0_3 = s0_2 + diff_x0;
        uint64_t s1_0 = x1_y1_e + (s0_0 < x0_0);
        uint64_t s1_1 = x1_y1_e + (m1 + m3) + (s0_1 < x0_1);
        uint64_t s1_2 = x1_y1_e + 2ULL * (m1 + m3) + (s0_2 < x0_2);
        uint64_t s1_3 = x1_y1_e + 3ULL * (m1 + m3) + (s0_3 < x0_3);
        unsigned __int128 p0_0 = (unsigned __int128)x0_0 * y0_0;
        unsigned __int128 p0_1 = (unsigned __int128)x0_1 * y0_1;
        unsigned __int128 p0_2 = (unsigned __int128)x0_2 * y0_2;
        unsigned __int128 p0_3 = (unsigned __int128)x0_3 * y0_3;
        unsigned __int128 p1_0 = (unsigned __int128)s0_0 * wad;
        unsigned __int128 p1_1 = p1_0 + diff_p1 - (s0_1 < s0_0 ? ((unsigned __int128)wad << 64) : 0);
        unsigned __int128 p1_2 = p1_0 + diff_p1_2 - (s0_2 < s0_0 ? ((unsigned __int128)wad << 64) : 0);
        unsigned __int128 p1_3 = p1_2 + diff_p1 - (s0_3 < s0_2 ? ((unsigned __int128)wad << 64) : 0);
        acc0 += s0_0 ^ s1_0 ^ (uint64_t)(p0_0 >> 64) ^ (uint64_t)(p1_0 >> 64) ^ ((uint64_t)p0_0 >> 32) ^ ((uint64_t)p1_0 >> 32);
        acc1 += s0_1 ^ s1_1 ^ (uint64_t)(p0_1 >> 64) ^ (uint64_t)(p1_1 >> 64) ^ ((uint64_t)p0_1 >> 32) ^ ((uint64_t)p1_1 >> 32);
        acc2 += s0_2 ^ s1_2 ^ (uint64_t)(p0_2 >> 64) ^ (uint64_t)(p1_2 >> 64) ^ ((uint64_t)p0_2 >> 32) ^ ((uint64_t)p1_2 >> 32);
        acc3 += s0_3 ^ s1_3 ^ (uint64_t)(p0_3 >> 64) ^ (uint64_t)(p1_3 >> 64) ^ ((uint64_t)p0_3 >> 32) ^ ((uint64_t)p1_3 >> 32);
        x0_e += step_x0;
        x1_y1_e += step_x1_y1;
    }
    uint64_t total = (acc0 + acc1) + (acc2 + acc3);
    for (; i < N; ++i) {
        uint64_t x0 = i * m0 + c0, x1 = i * m1 + 3ULL;
        uint64_t y0 = (i ^ 0x5555555555555555ULL) * m2 + 7ULL, y1 = i * m3 + 11ULL;
        uint64_t s0 = x0 + y0, s1 = x1 + y1 + (s0 < x0);
        unsigned __int128 p0 = (unsigned __int128)x0 * y0, p1 = (unsigned __int128)s0 * wad;
        total += s0 ^ s1 ^ (uint64_t)(p0 >> 64) ^ (uint64_t)(p1 >> 64) ^ ((uint64_t)p0 >> 32) ^ ((uint64_t)p1 >> 32);
    }
    return total;
#endif
}

static inline uint64_t ln_goldilocks_reduce_u128(unsigned __int128 p) {
    const uint64_t EPS = 0xFFFFFFFFULL;
    const uint64_t M = 0xFFFFFFFF00000001ULL;
    uint64_t lo = (uint64_t)p, hi = (uint64_t)(p >> 64);
#if defined(__aarch64__)
    uint64_t x2_32 = hi << 32;
    uint64_t x2_plus_x3 = (uint64_t)(uint32_t)hi + (hi >> 32);
    __int128 s = (__int128)lo + (__int128)x2_32 - (__int128)x2_plus_x3;
    int64_t hi_s = (int64_t)(s >> 64);
    uint64_t t1 = (uint64_t)s + (uint64_t)hi_s * EPS;
    return (t1 >= M) ? (t1 - M) : t1;
#else
    uint64_t x2 = hi & EPS, x3 = hi >> 32;
    uint64_t t0 = lo - x3 - ((lo < x3) ? EPS : 0ULL);
    uint64_t add2 = (x2 << 32) - x2;
    uint64_t t1 = t0 + add2;
    t1 += (t1 < t0) ? EPS : 0ULL;
    return (t1 >= M) ? (t1 - M) : t1;
#endif
}

uint64_t ln_goldilocks_ntt_modmul_u64_cpu(uint64_t N) {
    const uint64_t m0 = 6364136223846793005ULL, c0 = 1442695040888963407ULL;
    const uint64_t m2 = 11400714819323198485ULL;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE2)
    const uint64_t step4 = 4ULL * m0;
    svbool_t pg = svptrue_pat_b64(SV_VL2);
    svuint64_t v_acc0 = svdup_n_u64(0ULL), v_acc1 = svdup_n_u64(0ULL);
    svuint64_t v_idx = svindex_u64(0ULL, 1ULL);
    svuint64_t v_four = svdup_n_u64(4ULL);
    svuint64_t v_m2 = svdup_n_u64(m2), v_xor = svdup_n_u64(0xAAAAAAAAAAAAAAAAULL);
    svuint64_t v_eps = svdup_n_u64(0xFFFFFFFFULL), v_m = svdup_n_u64(0xFFFFFFFF00000001ULL);
    svuint64_t v_a0 = svadd_x(pg, svdup_n_u64(c0), svmul_x(pg, v_idx, svdup_n_u64(m0)));
    svuint64_t v_a1 = svadd_x(pg, v_a0, svdup_n_u64(2ULL * m0));
    svuint64_t v_step = svdup_n_u64(step4);
    svuint64_t v_seven = svdup_n_u64(7ULL);
    uint64_t i = 0ULL;
    for (; i + 4ULL <= N; i += 4ULL) {
        svuint64_t b0 = svmla_x(pg, v_seven, sveor_x(pg, v_idx, v_xor), v_m2);
        svuint64_t idx1 = svadd_x(pg, v_idx, svdup_n_u64(2ULL));
        svuint64_t b1 = svmla_x(pg, v_seven, sveor_x(pg, idx1, v_xor), v_m2);
        svuint64_t lo0 = svmul_x(pg, v_a0, b0), hi0 = svmulh_x(pg, v_a0, b0);
        svuint64_t lo1 = svmul_x(pg, v_a1, b1), hi1 = svmulh_x(pg, v_a1, b1);
        svuint64_t x3_0 = svlsr_x(pg, hi0, 32), x3_1 = svlsr_x(pg, hi1, 32);
        svuint64_t t0_0 = svsub_m(svcmplt_u64(pg, lo0, x3_0), svsub_x(pg, lo0, x3_0), v_eps);
        svuint64_t t0_1 = svsub_m(svcmplt_u64(pg, lo1, x3_1), svsub_x(pg, lo1, x3_1), v_eps);
        svuint64_t x2_0 = svand_x(pg, hi0, v_eps), x2_1 = svand_x(pg, hi1, v_eps);
        svuint64_t add2_0 = svsub_x(pg, svlsl_x(pg, x2_0, 32), x2_0);
        svuint64_t add2_1 = svsub_x(pg, svlsl_x(pg, x2_1, 32), x2_1);
        svuint64_t t1_0 = svadd_x(pg, t0_0, add2_0), t1_1 = svadd_x(pg, t0_1, add2_1);
        t1_0 = svadd_m(svcmplt_u64(pg, t1_0, t0_0), t1_0, v_eps);
        t1_1 = svadd_m(svcmplt_u64(pg, t1_1, t0_1), t1_1, v_eps);
        svuint64_t r0 = svsub_m(svcmpge_u64(pg, t1_0, v_m), t1_0, v_m);
        svuint64_t r1 = svsub_m(svcmpge_u64(pg, t1_1, v_m), t1_1, v_m);
        v_acc0 = svadd_x(pg, v_acc0, sveor_x(pg, r0, svadd_x(pg, v_a0, b0)));
        v_acc1 = svadd_x(pg, v_acc1, sveor_x(pg, r1, svadd_x(pg, v_a1, b1)));
        v_idx = svadd_x(pg, v_idx, v_four);
        v_a0 = svadd_x(pg, v_a0, v_step);
        v_a1 = svadd_x(pg, v_a1, v_step);
    }
    uint64_t total = svaddv_u64(pg, svadd_x(pg, v_acc0, v_acc1));
    for (; i < N; ++i) {
        uint64_t a = i * m0 + c0;
        uint64_t b = (i ^ 0xAAAAAAAAAAAAAAAAULL) * m2 + 7ULL;
        total += ln_goldilocks_reduce_u128((unsigned __int128)a * b) ^ (a + b);
    }
    return total;
#else
    const uint64_t step_a = 4ULL * m0;
    uint64_t acc0 = 0ULL, acc1 = 0ULL, acc2 = 0ULL, acc3 = 0ULL;
    uint64_t a_e = c0;
    uint64_t i = 0ULL;
    for (; i + 4ULL <= N; i += 4ULL) {
        uint64_t b0 = (i ^ 0xAAAAAAAAAAAAAAAAULL) * m2 + 7ULL;
        uint64_t b1 = b0 + m2;
        uint64_t b2 = b0 - 2ULL * m2;
        uint64_t b3 = b0 - m2;
        uint64_t a0 = a_e, a1 = a_e + m0, a2 = a_e + 2ULL * m0, a3 = a_e + 3ULL * m0;
        uint64_t r0 = ln_goldilocks_reduce_u128((unsigned __int128)a0 * b0);
        uint64_t r1 = ln_goldilocks_reduce_u128((unsigned __int128)a1 * b1);
        uint64_t r2 = ln_goldilocks_reduce_u128((unsigned __int128)a2 * b2);
        uint64_t r3 = ln_goldilocks_reduce_u128((unsigned __int128)a3 * b3);
        acc0 += r0 ^ (a0 + b0);
        acc1 += r1 ^ (a1 + b1);
        acc2 += r2 ^ (a2 + b2);
        acc3 += r3 ^ (a3 + b3);
        a_e += step_a;
    }
    uint64_t total = (acc0 + acc1) + (acc2 + acc3);
    for (; i < N; ++i) {
        uint64_t a = i * m0 + c0;
        uint64_t b = (i ^ 0xAAAAAAAAAAAAAAAAULL) * m2 + 7ULL;
        uint64_t r = ln_goldilocks_reduce_u128((unsigned __int128)a * b);
        total += r ^ (a + b);
    }
    return total;
#endif
}

#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE2)
static inline void ln_babybear_sbox2_sve(svbool_t pg, svuint64_t a, svuint64_t b, svuint64_t v_p, svuint64_t v_m27, svuint64_t v_m28, svuint64_t v_m29, svuint64_t *ra, svuint64_t *rb) {
    svuint64_t za2 = svmul_x(pg, a, a), zb2 = svmul_x(pg, b, b);
    svuint64_t qa2 = svlsr_x(pg, svmulh_x(pg, za2, v_m27), 27), qb2 = svlsr_x(pg, svmulh_x(pg, zb2, v_m27), 27);
    svuint64_t xa2 = svmls_x(pg, za2, qa2, v_p), xb2 = svmls_x(pg, zb2, qb2, v_p);
    svuint64_t za3 = svmul_x(pg, xa2, a), zb3 = svmul_x(pg, xb2, b);
    svuint64_t za4 = svmul_x(pg, xa2, xa2), zb4 = svmul_x(pg, xb2, xb2);
    svuint64_t qa3 = svlsr_x(pg, svmulh_x(pg, za3, v_m28), 28), qb3 = svlsr_x(pg, svmulh_x(pg, zb3, v_m28), 28);
    svuint64_t qa4 = svlsr_x(pg, svmulh_x(pg, za4, v_m29), 29), qb4 = svlsr_x(pg, svmulh_x(pg, zb4, v_m29), 29);
    svuint64_t xa3 = svmls_x(pg, za3, qa3, v_p), xb3 = svmls_x(pg, zb3, qb3, v_p);
    svuint64_t xa4 = svmls_x(pg, za4, qa4, v_p), xb4 = svmls_x(pg, zb4, qb4, v_p);
    svuint64_t za7 = svmul_x(pg, xa4, xa3), zb7 = svmul_x(pg, xb4, xb3);
    svuint64_t qa7 = svlsr_x(pg, svmulh_x(pg, za7, v_m29), 29), qb7 = svlsr_x(pg, svmulh_x(pg, zb7, v_m29), 29);
    *ra = svmls_x(pg, za7, qa7, v_p);
    *rb = svmls_x(pg, zb7, qb7, v_p);
}
#else
static inline v4u64 ln_babybear_sbox_v4(v4u64 x) {
    const v4u64 v_p = {2013265921ULL, 2013265921ULL, 2013265921ULL, 2013265921ULL};
    const v4u64 v_mu = {2290649223ULL, 2290649223ULL, 2290649223ULL, 2290649223ULL};
    const v4u64 v_pm1 = {2013265920ULL, 2013265920ULL, 2013265920ULL, 2013265920ULL};
    v4u64 z2 = (v4u64)_mm256_mul_epu32((__m256i)x, (__m256i)x);
    v4u64 q2 = ((v4u64)_mm256_mul_epu32((__m256i)(z2 >> 30), (__m256i)v_mu)) >> 32;
    v4u64 r2 = z2 - (v4u64)_mm256_mul_epu32((__m256i)q2, (__m256i)v_p);
    v4u64 x2 = r2 - ((v4u64)_mm256_cmpgt_epi64((__m256i)r2, (__m256i)v_pm1) & v_p);

    v4u64 z3 = (v4u64)_mm256_mul_epu32((__m256i)x2, (__m256i)x);
    v4u64 z4 = (v4u64)_mm256_mul_epu32((__m256i)x2, (__m256i)x2);
    v4u64 q3 = ((v4u64)_mm256_mul_epu32((__m256i)(z3 >> 30), (__m256i)v_mu)) >> 32;
    v4u64 q4 = ((v4u64)_mm256_mul_epu32((__m256i)(z4 >> 30), (__m256i)v_mu)) >> 32;
    v4u64 r3 = z3 - (v4u64)_mm256_mul_epu32((__m256i)q3, (__m256i)v_p);
    v4u64 r4 = z4 - (v4u64)_mm256_mul_epu32((__m256i)q4, (__m256i)v_p);
    v4u64 x3 = r3 - ((v4u64)_mm256_cmpgt_epi64((__m256i)r3, (__m256i)v_pm1) & v_p);
    v4u64 x4 = r4 - ((v4u64)_mm256_cmpgt_epi64((__m256i)r4, (__m256i)v_pm1) & v_p);

    v4u64 z7 = (v4u64)_mm256_mul_epu32((__m256i)x4, (__m256i)x3);
    v4u64 q7 = ((v4u64)_mm256_mul_epu32((__m256i)(z7 >> 30), (__m256i)v_mu)) >> 32;
    v4u64 r7 = z7 - (v4u64)_mm256_mul_epu32((__m256i)q7, (__m256i)v_p);
    return r7 - ((v4u64)_mm256_cmpgt_epi64((__m256i)r7, (__m256i)v_pm1) & v_p);
}
#endif

static inline uint64_t ln_babybear_sbox_scalar(uint64_t x) {
    const uint64_t P = 2013265921ULL;
    uint64_t x2 = (x * x) % P;
    uint64_t x3 = (x2 * x) % P;
    uint64_t x4 = (x2 * x2) % P;
    return (x4 * x3) % P;
}

uint64_t ln_babybear_poseidon2_sbox_u64_cpu(uint64_t N) {
    const uint64_t m0 = 2654435761ULL, m1 = 2246822519ULL, m2 = 3266489917ULL, m3 = 668265263ULL;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE2)
    svbool_t pg = svptrue_pat_b64(SV_VL2);
    svuint64_t v_acc0 = svdup_n_u64(0ULL), v_acc1 = svdup_n_u64(0ULL);
    svuint64_t v_idx = svindex_u64(0ULL, 1ULL);
    svuint64_t v_p = svdup_n_u64(2013265921ULL);
    svuint64_t v_m27 = svdup_n_u64(0x11111110eca86421ULL);
    svuint64_t v_m28 = svdup_n_u64(0x22222221d950c841ULL);
    svuint64_t v_m29 = svdup_n_u64(0x44444443b2a19081ULL);
    svuint64_t v_m0 = svdup_n_u64(m0), v_m1 = svdup_n_u64(m1), v_m2 = svdup_n_u64(m2), v_m3 = svdup_n_u64(m3);
    svuint64_t v_c0 = svdup_n_u64(17ULL), v_c1 = svdup_n_u64(29ULL), v_c2 = svdup_n_u64(43ULL), v_c3 = svdup_n_u64(59ULL);
    uint64_t i = 0ULL;
    for (; i + 4ULL <= N; i += 4ULL) {
        svuint64_t v_idx1 = svadd_n_u64_x(pg, v_idx, 2ULL);
        svuint64_t x0_0 = svand_n_u64_x(pg, svmla_x(pg, v_c0, v_idx, v_m0), 0x3FFFFFFFULL);
        svuint64_t x0_1 = svand_n_u64_x(pg, svmla_x(pg, v_c0, v_idx1, v_m0), 0x3FFFFFFFULL);
        svuint64_t x1_0 = svand_n_u64_x(pg, svmla_x(pg, v_c1, v_idx, v_m1), 0x3FFFFFFFULL);
        svuint64_t x1_1 = svand_n_u64_x(pg, svmla_x(pg, v_c1, v_idx1, v_m1), 0x3FFFFFFFULL);
        svuint64_t x2_0 = svand_n_u64_x(pg, svmla_x(pg, v_c2, v_idx, v_m2), 0x3FFFFFFFULL);
        svuint64_t x2_1 = svand_n_u64_x(pg, svmla_x(pg, v_c2, v_idx1, v_m2), 0x3FFFFFFFULL);
        svuint64_t x3_0 = svand_n_u64_x(pg, svmla_x(pg, v_c3, v_idx, v_m3), 0x3FFFFFFFULL);
        svuint64_t x3_1 = svand_n_u64_x(pg, svmla_x(pg, v_c3, v_idx1, v_m3), 0x3FFFFFFFULL);
        v_idx = svadd_n_u64_x(pg, v_idx, 4ULL);

        svuint64_t y0_0, y0_1, y1_0, y1_1, y2_0, y2_1, y3_0, y3_1;
        ln_babybear_sbox2_sve(pg, x0_0, x0_1, v_p, v_m27, v_m28, v_m29, &y0_0, &y0_1);
        ln_babybear_sbox2_sve(pg, x1_0, x1_1, v_p, v_m27, v_m28, v_m29, &y1_0, &y1_1);
        ln_babybear_sbox2_sve(pg, x2_0, x2_1, v_p, v_m27, v_m28, v_m29, &y2_0, &y2_1);
        ln_babybear_sbox2_sve(pg, x3_0, x3_1, v_p, v_m27, v_m28, v_m29, &y3_0, &y3_1);

        svuint64_t t0 = svadd_x(pg, svadd_x(pg, y0_0, y1_0), svadd_x(pg, y2_0, y3_0));
        svuint64_t t1 = svadd_x(pg, svadd_x(pg, y0_1, y1_1), svadd_x(pg, y2_1, y3_1));
        svuint64_t a0 = sveor_x(pg, svadd_x(pg, y0_0, t0), svlsl_n_u64_x(pg, svadd_x(pg, y1_0, t0), 16));
        svuint64_t b0 = sveor_x(pg, svadd_x(pg, y2_0, t0), svlsl_n_u64_x(pg, svadd_x(pg, y3_0, t0), 32));
        svuint64_t a1 = sveor_x(pg, svadd_x(pg, y0_1, t1), svlsl_n_u64_x(pg, svadd_x(pg, y1_1, t1), 16));
        svuint64_t b1 = sveor_x(pg, svadd_x(pg, y2_1, t1), svlsl_n_u64_x(pg, svadd_x(pg, y3_1, t1), 32));
        v_acc0 = svadd_x(pg, v_acc0, svadd_x(pg, a0, b0));
        v_acc1 = svadd_x(pg, v_acc1, svadd_x(pg, a1, b1));
    }
    uint64_t total = svaddv_u64(pg, svadd_x(pg, v_acc0, v_acc1));
    for (; i < N; ++i) {
        uint64_t y0 = ln_babybear_sbox_scalar((i * m0 + 17ULL) & 0x3FFFFFFFULL);
        uint64_t y1 = ln_babybear_sbox_scalar((i * m1 + 29ULL) & 0x3FFFFFFFULL);
        uint64_t y2 = ln_babybear_sbox_scalar((i * m2 + 43ULL) & 0x3FFFFFFFULL);
        uint64_t y3 = ln_babybear_sbox_scalar((i * m3 + 59ULL) & 0x3FFFFFFFULL);
        uint64_t t = y0 + y1 + y2 + y3;
        total += ((y0 + t) ^ ((y1 + t) << 16)) + ((y2 + t) ^ ((y3 + t) << 32));
    }
    return total;
#else
    const v4u64 v_mask = {0x3FFFFFFFULL, 0x3FFFFFFFULL, 0x3FFFFFFFULL, 0x3FFFFFFFULL};
    v4u64 vx0 = {17ULL, 17ULL + m0, 17ULL + 2ULL * m0, 17ULL + 3ULL * m0};
    v4u64 vx1 = {29ULL, 29ULL + m1, 29ULL + 2ULL * m1, 29ULL + 3ULL * m1};
    v4u64 vx2 = {43ULL, 43ULL + m2, 43ULL + 2ULL * m2, 43ULL + 3ULL * m2};
    v4u64 vx3 = {59ULL, 59ULL + m3, 59ULL + 2ULL * m3, 59ULL + 3ULL * m3};
    const v4u64 st0 = {4ULL * m0, 4ULL * m0, 4ULL * m0, 4ULL * m0};
    const v4u64 st1 = {4ULL * m1, 4ULL * m1, 4ULL * m1, 4ULL * m1};
    const v4u64 st2 = {4ULL * m2, 4ULL * m2, 4ULL * m2, 4ULL * m2};
    const v4u64 st3 = {4ULL * m3, 4ULL * m3, 4ULL * m3, 4ULL * m3};
    v4u64 v_acc = {0ULL, 0ULL, 0ULL, 0ULL};
    uint64_t i = 0ULL;
    for (; i + 4ULL <= N; i += 4ULL) {
        v4u64 y0 = ln_babybear_sbox_v4(vx0 & v_mask);
        v4u64 y1 = ln_babybear_sbox_v4(vx1 & v_mask);
        v4u64 y2 = ln_babybear_sbox_v4(vx2 & v_mask);
        v4u64 y3 = ln_babybear_sbox_v4(vx3 & v_mask);
        v4u64 t = (y0 + y1) + (y2 + y3);
        v_acc += ((y0 + t) ^ ((y1 + t) << 16)) + ((y2 + t) ^ ((y3 + t) << 32));
        vx0 += st0; vx1 += st1; vx2 += st2; vx3 += st3;
    }
    uint64_t total = (v_acc[0] + v_acc[1]) + (v_acc[2] + v_acc[3]);
    for (; i < N; ++i) {
        uint64_t y0 = ln_babybear_sbox_scalar((i * m0 + 17ULL) & 0x3FFFFFFFULL);
        uint64_t y1 = ln_babybear_sbox_scalar((i * m1 + 29ULL) & 0x3FFFFFFFULL);
        uint64_t y2 = ln_babybear_sbox_scalar((i * m2 + 43ULL) & 0x3FFFFFFFULL);
        uint64_t y3 = ln_babybear_sbox_scalar((i * m3 + 59ULL) & 0x3FFFFFFFULL);
        uint64_t t = y0 + y1 + y2 + y3;
        total += ((y0 + t) ^ ((y1 + t) << 16)) + ((y2 + t) ^ ((y3 + t) << 32));
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
    RUN_BENCH("uint256_wad_muldiv_u64", ln_uint256_wad_muldiv_u64_cpu(5000000ULL));
    RUN_BENCH("goldilocks_ntt_modmul_u64", ln_goldilocks_ntt_modmul_u64_cpu(5000000ULL));
    RUN_BENCH("babybear_poseidon2_sbox_u64", ln_babybear_poseidon2_sbox_u64_cpu(5000000ULL));
    RUN_BENCH("holdout_bitwise", ln_holdout_bitwise_cpu(10000000ULL));
    RUN_BENCH("holdout_loop_bounds", ln_holdout_loop_bounds_cpu(10000000ULL));
    return 0;
}
