# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)

- **Generated At**: `2026-10-21T14:27:42.217398+00:00`
- **Trials per Benchmark**: `7`
- **Differential Verification Status**: `PASSED (100% Exact 64-bit Match)` (`108` cross-backend/cross-architecture assertions verified)

## 1. Executive Summary: Geometric-Mean Speedups

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_cpu` vs `rust_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `rust_o3` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64`)** | ARM Cortex-X925 / Cortex-A725 (20 cores) + NVIDIA GB10 Grace-Blackwell (sm_121) | **60.86x** | **2.20x** | **1.97x** | **634.20x** | **20.48x** |
| **`ashur` (`x86_64`)** | Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads) | **42.88x** | **2.71x** | **2.14x** | **42.88x** | **2.14x** |

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
| `evm_gas_schedule_u64` | `10,000,000` (transactions) | `23299983278533` | `MATCH` | `MATCH` | **PASS** |
| `holdout_bitwise` | `10,000,000` (iterations) | `17653976101919722312` | `MATCH` | `MATCH` | **PASS** |
| `holdout_loop_bounds` | `10,000,000` (iterations) | `2318209942448586758` | `MATCH` | `MATCH` | **PASS** |

---

## 3. Detailed Results on `spark-de79` (`aarch64`)

- **CPU**: ARM Cortex-X925 / Cortex-A725 (20 cores)
- **GPU**: NVIDIA GB10 Grace-Blackwell (sm_121)
- **Compilation Times (ms)**: `{"official_lean4": 896.0, "cpp_o3": 553.0, "rust_o3": 238.0, "lean_native_cpu": 160.0, "cuda_o3": 1024.0, "lean_native_gpu_ptx": 1024.0, "lean_native_hybrid": 672.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2002648, "cpp_o3": 264912, "rust_o3": 263880, "lean_native_cpu": 263604, "cuda_o3": 360236, "lean_native_gpu_ptx": 360236, "lean_native_hybrid": 360236}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `rust_o3`) | Speedup (`hybrid` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `404.38 ± 2.31` | `621.68 ± 1.64` | `406.77 ± 1.31` | `92.02 ± 0.99` | `1.14 ± 0.29` | `1.14 ± 0.29` | **4.42x** | **357.75x** | `0.002165` |
| `tuple_accum_sum` | `943.61 ± 3.37` | `25.36 ± 0.27` | `25.46 ± 0.46` | `6.23 ± 0.07` | `8.78 ± 0.14` | `6.23 ± 0.07` | **4.09x** | **4.09x** | `0.002165` |
| `sarray_scale_bias` | `2119.76 ± 106.76` | `5.75 ± 0.05` | `5.38 ± 0.03` | `3.31 ± 0.04` | `1.07 ± 0.44` | `1.07 ± 0.44` | **1.63x** | **5.04x** | `0.002165` |
| `dot_product_u64` | `50.15 ± 2.59` | `4.32 ± 0.02` | `4.22 ± 0.07` | `4.17 ± 0.04` | `0.73 ± 0.28` | `0.73 ± 0.28` | **1.01x** | **5.80x** | `0.002165` |
| `saxpy_kernel` | `1724.34 ± 37.71` | `8.30 ± 0.03` | `8.36 ± 0.04` | `8.40 ± 0.07` | `2.00 ± 0.54` | `2.00 ± 0.54` | **0.99x** | **4.17x** | `0.002165` |
| `matmul_tiled_u64` | `929.77 ± 8.50` | `28.79 ± 0.39` | `18.92 ± 0.23` | `20.45 ± 0.17` | `0.21 ± 0.12` | `0.21 ± 0.12` | **0.93x** | **88.09x** | `0.002165` |
| `evm_gas_schedule_u64` | `166.77 ± 1.91` | `9.33 ± 0.11` | `10.67 ± 0.11` | `2.58 ± 0.05` | `0.11 ± 0.04` | `0.11 ± 0.04` | **4.13x** | **96.14x** | `0.002165` |
| `holdout_bitwise` | `15.10 ± 0.09` | `15.22 ± 0.11` | `15.42 ± 0.20` | `12.65 ± 0.15` | `12.84 ± 0.05` | `12.65 ± 0.15` | **1.22x** | **1.22x** | `0.000583` |
| `holdout_loop_bounds` | `10.14 ± 0.13` | `10.19 ± 0.11` | `12.88 ± 0.11` | `10.33 ± 0.12` | `10.21 ± 0.06` | `10.33 ± 0.12` | **1.25x** | **1.25x** | `0.000583` |

---

## 3. Detailed Results on `ashur` (`x86_64`)

- **CPU**: Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)
- **GPU**: None (CPU-only host)
- **Compilation Times (ms)**: `{"official_lean4": 1281.0, "cpp_o3": 1081.0, "rust_o3": 274.0, "lean_native_cpu": 492.0, "lean_native_hybrid": 492.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2021712, "cpp_o3": 265700, "rust_o3": 264152, "lean_native_cpu": 263880, "lean_native_hybrid": 263880}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `581.32 ± 6.62` | `1122.74 ± 4.13` | `596.96 ± 2.98` | `122.26 ± 0.44` | `122.26 ± 0.44` | **4.75x** | **4.88x** | `0.002165` |
| `tuple_accum_sum` | `2075.10 ± 5.87` | `36.31 ± 0.25` | `32.53 ± 0.19` | `5.14 ± 0.11` | `5.14 ± 0.11` | **403.47x** | **6.32x** | `0.002165` |
| `sarray_scale_bias` | `525.93 ± 3.84` | `12.57 ± 0.12` | `12.58 ± 0.09` | `6.80 ± 0.10` | `6.80 ± 0.10` | **77.33x** | **1.85x** | `0.002165` |
| `dot_product_u64` | `81.27 ± 0.79` | `8.07 ± 0.05` | `7.97 ± 0.12` | `7.57 ± 0.20` | `7.57 ± 0.20` | **10.74x** | **1.05x** | `0.002165` |
| `saxpy_kernel` | `364.93 ± 1.01` | `16.35 ± 0.17` | `15.96 ± 0.05` | `15.32 ± 0.31` | `15.32 ± 0.31` | **23.82x** | **1.04x** | `0.002165` |
| `matmul_tiled_u64` | `2365.45 ± 6.26` | `40.62 ± 0.57` | `50.62 ± 0.92` | `42.04 ± 0.76` | `42.04 ± 0.76` | **56.27x** | **1.20x** | `0.002165` |
| `evm_gas_schedule_u64` | `333.76 ± 1.70` | `21.88 ± 0.16` | `7.21 ± 0.19` | `2.68 ± 0.08` | `2.68 ± 0.08` | **124.73x** | **2.70x** | `0.002165` |
| `holdout_bitwise` | `13.27 ± 0.12` | `12.07 ± 0.06` | `13.89 ± 0.16` | `10.83 ± 0.21` | `10.83 ± 0.21` | **1.22x** | **1.28x** | `0.000583` |
| `holdout_loop_bounds` | `12.20 ± 0.09` | `11.03 ± 0.12` | `13.70 ± 0.15` | `11.33 ± 0.21` | `11.33 ± 0.21` | **1.08x** | **1.21x** | `0.000583` |
