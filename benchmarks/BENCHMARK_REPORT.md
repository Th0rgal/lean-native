# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)

- **Generated At**: `2026-10-21T15:31:37.131542+00:00`
- **Trials per Benchmark**: `7`
- **Differential Verification Status**: `PASSED (100% Exact 64-bit Match)` (`120` cross-backend/cross-architecture assertions verified)

## 1. Executive Summary: Geometric-Mean Speedups

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_cpu` vs `rust_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `rust_o3` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64`)** | ARM Cortex-X925 / Cortex-A725 (20 cores) + NVIDIA GB10 Grace-Blackwell (sm_121) | **48.45x** | **2.28x** | **1.84x** | **716.91x** | **27.29x** |
| **`ashur` (`x86_64`)** | Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads) | **34.99x** | **2.46x** | **1.97x** | **34.99x** | **1.97x** |

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
| `keccak256_sponge_u64` | `2,000,000` (blocks) | `13792606934134369666` | `MATCH` | `MATCH` | **PASS** |
| `holdout_bitwise` | `10,000,000` (iterations) | `17653976101919722312` | `MATCH` | `MATCH` | **PASS** |
| `holdout_loop_bounds` | `10,000,000` (iterations) | `2318209942448586758` | `MATCH` | `MATCH` | **PASS** |

---

## 3. Detailed Results on `spark-de79` (`aarch64`)

- **CPU**: ARM Cortex-X925 / Cortex-A725 (20 cores)
- **GPU**: NVIDIA GB10 Grace-Blackwell (sm_121)
- **Compilation Times (ms)**: `{"official_lean4": 1074.0, "cpp_o3": 591.0, "rust_o3": 298.0, "lean_native_cpu": 176.0, "cuda_o3": 1080.0, "lean_native_gpu_ptx": 1080.0, "lean_native_hybrid": 716.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2002780, "cpp_o3": 264596, "rust_o3": 263880, "lean_native_cpu": 263560, "cuda_o3": 360940, "lean_native_gpu_ptx": 360940, "lean_native_hybrid": 360940}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `rust_o3`) | Speedup (`hybrid` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `405.33 ± 0.78` | `624.94 ± 1.75` | `405.51 ± 1.24` | `91.60 ± 0.71` | `1.04 ± 0.01` | `1.04 ± 0.01` | **4.43x** | **389.50x** | `0.002165` |
| `tuple_accum_sum` | `933.39 ± 8.68` | `25.29 ± 0.21` | `25.71 ± 0.18` | `6.21 ± 0.13` | `8.72 ± 0.12` | `6.21 ± 0.13` | **4.14x** | **4.14x** | `0.002165` |
| `sarray_scale_bias` | `2544.55 ± 237.33` | `5.71 ± 0.05` | `5.38 ± 0.11` | `3.24 ± 0.03` | `0.73 ± 0.79` | `0.73 ± 0.79` | **1.66x** | **7.36x** | `0.002165` |
| `dot_product_u64` | `49.23 ± 0.99` | `4.31 ± 0.07` | `4.22 ± 0.08` | `4.17 ± 0.03` | `0.71 ± 0.12` | `0.71 ± 0.12` | **1.01x** | **5.95x** | `0.002165` |
| `saxpy_kernel` | `1878.11 ± 30.99` | `8.18 ± 0.04` | `8.15 ± 0.14` | `8.25 ± 0.04` | `1.93 ± 0.32` | `1.93 ± 0.32` | **0.99x** | **4.22x** | `0.002165` |
| `matmul_tiled_u64` | `926.48 ± 6.33` | `28.67 ± 0.42` | `18.85 ± 0.15` | `20.44 ± 0.17` | `0.19 ± 0.10` | `0.19 ± 0.10` | **0.92x** | **100.63x** | `0.002165` |
| `evm_gas_schedule_u64` | `167.30 ± 1.00` | `9.26 ± 0.06` | `10.70 ± 0.02` | `2.54 ± 0.04` | `0.08 ± 0.04` | `0.08 ± 0.04` | **4.22x** | **135.38x** | `0.002165` |
| `keccak256_sponge_u64` | `61.71 ± 0.42` | `23.99 ± 0.51` | `9.65 ± 0.03` | `8.54 ± 0.08` | `0.13 ± 0.02` | `0.13 ± 0.02` | **1.13x** | **75.76x** | `0.002141` |
| `holdout_bitwise` | `15.20 ± 0.08` | `15.16 ± 0.26` | `15.38 ± 0.09` | `12.65 ± 0.12` | `12.82 ± 0.09` | `12.65 ± 0.12` | **1.22x** | **1.22x** | `0.000583` |
| `holdout_loop_bounds` | `10.10 ± 0.06` | `10.16 ± 0.05` | `12.87 ± 0.05` | `10.26 ± 0.15` | `10.17 ± 0.15` | `10.26 ± 0.15` | **1.25x** | **1.25x** | `0.000583` |

---

## 3. Detailed Results on `ashur` (`x86_64`)

- **CPU**: Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)
- **GPU**: None (CPU-only host)
- **Compilation Times (ms)**: `{"official_lean4": 1549.0, "cpp_o3": 1160.0, "rust_o3": 333.0, "lean_native_cpu": 538.0, "lean_native_hybrid": 538.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2021644, "cpp_o3": 265676, "rust_o3": 264168, "lean_native_cpu": 263860, "lean_native_hybrid": 263860}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `614.41 ± 6.30` | `1166.90 ± 2.27` | `581.86 ± 4.20` | `122.00 ± 1.41` | `122.00 ± 1.41` | **5.04x** | **4.77x** | `0.002165` |
| `tuple_accum_sum` | `2065.40 ± 7.37` | `36.20 ± 0.11` | `32.58 ± 0.21` | `5.15 ± 0.06` | `5.15 ± 0.06` | **400.92x** | **6.32x** | `0.002141` |
| `sarray_scale_bias` | `524.54 ± 6.41` | `12.64 ± 0.77` | `12.58 ± 0.18` | `6.87 ± 0.32` | `6.87 ± 0.32` | **76.37x** | **1.83x** | `0.002165` |
| `dot_product_u64` | `81.32 ± 0.38` | `8.16 ± 0.20` | `8.11 ± 0.44` | `7.60 ± 0.61` | `7.60 ± 0.61` | **10.70x** | **1.07x** | `0.002165` |
| `saxpy_kernel` | `365.78 ± 3.48` | `16.35 ± 0.11` | `15.96 ± 0.12` | `15.59 ± 0.85` | `15.59 ± 0.85` | **23.46x** | **1.02x** | `0.002165` |
| `matmul_tiled_u64` | `2366.81 ± 7.14` | `40.56 ± 1.93` | `52.21 ± 1.53` | `42.11 ± 1.26` | `42.11 ± 1.26` | **56.20x** | **1.24x** | `0.002165` |
| `evm_gas_schedule_u64` | `334.77 ± 0.79` | `21.86 ± 0.15` | `7.30 ± 0.18` | `2.65 ± 0.03` | `2.65 ± 0.03` | **126.12x** | **2.75x** | `0.002165` |
| `keccak256_sponge_u64` | `141.86 ± 2.67` | `20.79 ± 0.25` | `19.41 ± 0.36` | `17.33 ± 0.09` | `17.33 ± 0.09` | **8.18x** | **1.12x** | `0.002165` |
| `holdout_bitwise` | `13.30 ± 0.09` | `12.07 ± 0.09` | `14.03 ± 0.49` | `10.86 ± 0.12` | `10.86 ± 0.12` | **1.22x** | **1.29x** | `0.000583` |
| `holdout_loop_bounds` | `12.17 ± 0.08` | `10.87 ± 0.07` | `13.79 ± 0.50` | `11.30 ± 0.16` | `11.30 ± 0.16` | **1.08x** | **1.22x** | `0.000583` |
