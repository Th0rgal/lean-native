# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)

- **Generated At**: `2026-10-21T04:45:19.034185+00:00`
- **Trials per Benchmark**: `7`
- **Differential Verification Status**: `PASSED (100% Exact 64-bit Match)` (`80` cross-backend/cross-architecture assertions verified)

## 1. Executive Summary: Geometric-Mean Speedups

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `cpp_o3` |
| :--- | :--- | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64`)** | ARM Cortex-X925 / Cortex-A725 (20 cores) + NVIDIA GB10 Grace-Blackwell (sm_121) | **58.49x** | **2.02x** | **589.03x** | **20.38x** |
| **`ashur` (`x86_64`)** | Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads) | **35.42x** | **2.25x** | **35.42x** | **2.25x** |

---

## 2. Deterministic 64-Bit Checksum Verification Matrix

| Benchmark | Input Size | Expected Checksum (`uint64_t`) | `spark-de79` (`ARM64` + `GB10`) | `ashur` (`x86_64`) | Status |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `5,000,000` (trajectories) | `740438133` | `MATCH` | `MATCH` | **PASS** |
| `tuple_accum_sum` | `50,000,000` (iterations) | `2430072077297332099` | `MATCH` | `MATCH` | **PASS** |
| `sarray_scale_bias` | `10,000,000` (elements) | `832419940395999471` | `MATCH` | `MATCH` | **PASS** |
| `dot_product_u64` | `10,000,000` (elements) | `9844157271583257408` | `MATCH` | `MATCH` | **PASS** |
| `saxpy_kernel` | `16,777,216` (elements) | `2559223112370776895` | `MATCH` | `MATCH` | **PASS** |
| `matmul_tiled_u64` | `512` (matrix_dim) | `11211282456894907173` | `MATCH` | `MATCH` | **PASS** |
| `holdout_bitwise` | `10,000,000` (iterations) | `17653976101919722312` | `MATCH` | `MATCH` | **PASS** |
| `holdout_loop_bounds` | `10,000,000` (iterations) | `2318209942448586758` | `MATCH` | `MATCH` | **PASS** |

---

## 3. Detailed Results on `spark-de79` (`aarch64`)

- **CPU**: ARM Cortex-X925 / Cortex-A725 (20 cores)
- **GPU**: NVIDIA GB10 Grace-Blackwell (sm_121)
- **Compilation Times (ms)**: `{"official_lean4": 776.0, "cpp_o3": 495.0, "lean_native_cpu": 97.0, "cuda_o3": 996.0, "lean_native_gpu_ptx": 996.0, "lean_native_hybrid": 595.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2002832, "cpp_o3": 264828, "lean_native_cpu": 263600, "cuda_o3": 360468, "lean_native_gpu_ptx": 360468, "lean_native_hybrid": 360468}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`hybrid` vs `lean4`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `407.54 ± 2.56` | `617.34 ± 1.89` | `91.48 ± 0.62` | `1.03 ± 0.38` | `1.03 ± 0.38` | **4.45x** | **394.71x** | `0.002165` |
| `tuple_accum_sum` | `934.25 ± 3.59` | `25.29 ± 0.09` | `6.20 ± 0.06` | `8.73 ± 0.14` | `6.20 ± 0.06` | **150.70x** | **150.70x** | `0.002165` |
| `sarray_scale_bias` | `2086.61 ± 5.44` | `5.63 ± 0.13` | `3.21 ± 0.01` | `0.75 ± 0.26` | `0.75 ± 0.26` | **650.68x** | **2794.07x** | `0.002165` |
| `dot_product_u64` | `49.18 ± 0.81` | `4.29 ± 0.03` | `4.20 ± 0.01` | `0.75 ± 0.12` | `0.75 ± 0.12` | **11.72x** | **65.51x** | `0.002165` |
| `saxpy_kernel` | `1406.87 ± 111.36` | `8.14 ± 0.04` | `8.22 ± 0.05` | `1.80 ± 0.33` | `1.80 ± 0.33` | **171.09x** | **780.30x** | `0.002165` |
| `matmul_tiled_u64` | `931.66 ± 3.37` | `28.66 ± 0.23` | `20.38 ± 0.26` | `0.19 ± 0.16` | `0.19 ± 0.16` | **45.71x** | **4916.40x** | `0.002165` |
| `holdout_bitwise` | `15.20 ± 0.21` | `15.18 ± 0.25` | `12.69 ± 0.21` | `12.94 ± 0.27` | `12.69 ± 0.21` | **1.20x** | **1.20x** | `0.000583` |
| `holdout_loop_bounds` | `10.17 ± 0.07` | `10.19 ± 0.08` | `10.25 ± 0.07` | `10.21 ± 0.14` | `10.25 ± 0.07` | **0.99x** | **0.99x** | `0.000583` |

---

## 3. Detailed Results on `ashur` (`x86_64`)

- **CPU**: Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)
- **GPU**: None (CPU-only host)
- **Compilation Times (ms)**: `{"official_lean4": 1197.0, "cpp_o3": 1056.0, "lean_native_cpu": 173.0, "lean_native_hybrid": 173.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2021640, "cpp_o3": 265684, "lean_native_cpu": 263880, "lean_native_hybrid": 263880}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `cpp_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `618.99 ± 17.01` | `1117.80 ± 6.71` | `124.37 ± 0.94` | `124.37 ± 0.94` | **4.98x** | **8.99x** | `0.002165` |
| `tuple_accum_sum` | `2027.36 ± 55.71` | `36.27 ± 0.05` | `5.14 ± 0.06` | `5.14 ± 0.06` | **394.45x** | **7.06x** | `0.002165` |
| `sarray_scale_bias` | `516.32 ± 11.45` | `12.66 ± 0.18` | `6.84 ± 0.19` | `6.84 ± 0.19` | **75.43x** | **1.85x** | `0.002165` |
| `dot_product_u64` | `81.47 ± 1.79` | `8.16 ± 0.17` | `7.77 ± 0.50` | `7.77 ± 0.50` | **10.48x** | **1.05x** | `0.002165` |
| `saxpy_kernel` | `351.95 ± 41.11` | `16.34 ± 0.20` | `15.57 ± 0.78` | `15.57 ± 0.78` | **22.60x** | **1.05x** | `0.002165` |
| `matmul_tiled_u64` | `2369.66 ± 70.94` | `42.00 ± 2.35` | `42.12 ± 5.93` | `42.12 ± 5.93` | **56.25x** | **1.00x** | `0.002165` |
| `holdout_bitwise` | `13.29 ± 0.58` | `12.14 ± 0.11` | `10.90 ± 0.12` | `10.90 ± 0.12` | **1.22x** | **1.11x** | `0.000583` |
| `holdout_loop_bounds` | `12.38 ± 0.26` | `11.02 ± 0.14` | `11.36 ± 0.12` | `11.36 ± 0.12` | **1.09x** | **0.97x** | `0.000583` |
