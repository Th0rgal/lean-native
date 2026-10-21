# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)

- **Generated At**: `2026-10-21T12:48:42.714451+00:00`
- **Trials per Benchmark**: `7`
- **Differential Verification Status**: `PASSED (100% Exact 64-bit Match)` (`96` cross-backend/cross-architecture assertions verified)

## 1. Executive Summary: Geometric-Mean Speedups

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_cpu` vs `rust_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `rust_o3` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64`)** | ARM Cortex-X925 / Cortex-A725 (20 cores) + NVIDIA GB10 Grace-Blackwell (sm_121) | **49.46x** | **2.02x** | **1.74x** | **425.40x** | **14.96x** |
| **`ashur` (`x86_64`)** | Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads) | **39.40x** | **2.24x** | **2.01x** | **39.40x** | **2.01x** |

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
- **Compilation Times (ms)**: `{"official_lean4": 676.0, "cpp_o3": 535.0, "rust_o3": 246.0, "lean_native_cpu": 111.0, "cuda_o3": 925.0, "lean_native_gpu_ptx": 925.0, "lean_native_hybrid": 573.5}`
- **Peak RSS (KB)**: `{"official_lean4": 2002860, "cpp_o3": 264716, "rust_o3": 263884, "lean_native_cpu": 263600, "cuda_o3": 359988, "lean_native_gpu_ptx": 359988, "lean_native_hybrid": 359988}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `rust_o3`) | Speedup (`hybrid` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `407.69 ± 1.64` | `619.55 ± 2.77` | `407.20 ± 1.50` | `91.53 ± 0.20` | `1.13 ± 0.15` | `1.13 ± 0.15` | **4.45x** | **360.20x** | `0.002165` |
| `tuple_accum_sum` | `933.04 ± 2.87` | `25.40 ± 0.36` | `25.46 ± 0.17` | `6.23 ± 0.02` | `8.75 ± 0.09` | `6.23 ± 0.02` | **4.09x** | **4.09x** | `0.002165` |
| `sarray_scale_bias` | `1614.78 ± 146.32` | `5.56 ± 0.08` | `5.32 ± 0.09` | `3.19 ± 0.01` | `0.98 ± 0.55` | `0.98 ± 0.55` | **1.67x** | **5.44x** | `0.002165` |
| `dot_product_u64` | `48.92 ± 0.39` | `4.30 ± 0.04` | `4.18 ± 0.06` | `4.19 ± 0.04` | `0.75 ± 0.12` | `0.75 ± 0.12` | **1.00x** | **5.60x** | `0.002165` |
| `saxpy_kernel` | `667.72 ± 29.22` | `8.09 ± 0.05` | `8.08 ± 0.07` | `8.19 ± 0.12` | `2.25 ± 0.65` | `2.25 ± 0.65` | **0.99x** | **3.59x** | `0.002165` |
| `matmul_tiled_u64` | `930.18 ± 5.70` | `28.88 ± 0.14` | `18.96 ± 0.27` | `20.45 ± 0.48` | `0.27 ± 0.17` | `0.27 ± 0.17` | **0.93x** | **69.53x** | `0.002165` |
| `holdout_bitwise` | `15.18 ± 0.11` | `15.35 ± 0.12` | `15.44 ± 0.09` | `12.74 ± 0.26` | `12.83 ± 0.21` | `12.74 ± 0.26` | **1.21x** | **1.21x** | `0.000583` |
| `holdout_loop_bounds` | `10.11 ± 0.05` | `10.21 ± 0.14` | `12.88 ± 0.04` | `10.32 ± 0.23` | `10.21 ± 0.09` | `10.32 ± 0.23` | **1.25x** | **1.25x** | `0.000583` |

---

## 3. Detailed Results on `ashur` (`x86_64`)

- **CPU**: Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)
- **GPU**: None (CPU-only host)
- **Compilation Times (ms)**: `{"official_lean4": 2747.0, "cpp_o3": 1961.0, "rust_o3": 497.0, "lean_native_cpu": 320.0, "lean_native_hybrid": 320.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2021676, "cpp_o3": 265656, "rust_o3": 264200, "lean_native_cpu": 263852, "lean_native_hybrid": 263852}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `717.05 ± 25.22` | `1458.63 ± 32.98` | `730.97 ± 26.61` | `141.57 ± 1.55` | `141.57 ± 1.55` | **5.06x** | **5.16x** | `0.002165` |
| `tuple_accum_sum` | `3577.74 ± 265.99` | `46.77 ± 1.27` | `39.53 ± 3.66` | `8.98 ± 0.69` | `8.98 ± 0.69` | **398.33x** | **4.40x** | `0.002165` |
| `sarray_scale_bias` | `816.49 ± 49.75` | `19.53 ± 2.27` | `19.38 ± 2.27` | `9.83 ± 1.02` | `9.83 ± 1.02` | **83.10x** | **1.97x** | `0.002165` |
| `dot_product_u64` | `139.52 ± 5.39` | `11.79 ± 1.57` | `11.82 ± 2.95` | `11.53 ± 1.72` | `11.53 ± 1.72` | **12.10x** | **1.03x** | `0.002165` |
| `saxpy_kernel` | `603.97 ± 63.64` | `23.83 ± 3.68` | `23.91 ± 5.30` | `22.38 ± 0.55` | `22.38 ± 0.55` | **26.99x** | **1.07x** | `0.002165` |
| `matmul_tiled_u64` | `4167.98 ± 373.41` | `66.83 ± 1.33` | `82.92 ± 3.73` | `61.03 ± 3.44` | `61.03 ± 3.44` | **68.29x** | **1.36x** | `0.002165` |
| `holdout_bitwise` | `14.08 ± 0.11` | `13.98 ± 0.05` | `14.77 ± 0.06` | `13.91 ± 0.86` | `13.91 ± 0.86` | **1.01x** | **1.06x** | `0.000583` |
| `holdout_loop_bounds` | `13.71 ± 0.18` | `13.96 ± 0.52` | `14.76 ± 0.28` | `14.51 ± 0.47` | `14.51 ± 0.47` | **0.94x** | **1.02x** | `0.000583` |
