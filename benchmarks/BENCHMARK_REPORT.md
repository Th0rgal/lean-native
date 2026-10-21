# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)

- **Generated At**: `2026-10-21T18:10:41.772606+00:00`
- **Trials per Benchmark**: `7`
- **Differential Verification Status**: `PASSED (100% Exact 64-bit Match)` (`144` cross-backend/cross-architecture assertions verified)

## 1. Executive Summary: Geometric-Mean Speedups

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_cpu` vs `rust_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `rust_o3` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64`)** | ARM Cortex-X925 / Cortex-A725 (20 cores) + NVIDIA GB10 Grace-Blackwell (sm_121) | **44.66x** | **2.31x** | **1.91x** | **664.87x** | **28.51x** |
| **`ashur` (`x86_64`)** | Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads) | **30.49x** | **2.25x** | **1.77x** | **30.49x** | **1.77x** |

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
| `uint256_wad_muldiv_u64` | `5,000,000` (operations) | `12624251146278196429` | `MATCH` | `MATCH` | **PASS** |
| `goldilocks_ntt_modmul_u64` | `5,000,000` (operations) | `17681648824075000351` | `MATCH` | `MATCH` | **PASS** |
| `holdout_bitwise` | `10,000,000` (iterations) | `17653976101919722312` | `MATCH` | `MATCH` | **PASS** |
| `holdout_loop_bounds` | `10,000,000` (iterations) | `2318209942448586758` | `MATCH` | `MATCH` | **PASS** |

---

## 3. Detailed Results on `spark-de79` (`aarch64`)

- **CPU**: ARM Cortex-X925 / Cortex-A725 (20 cores)
- **GPU**: NVIDIA GB10 Grace-Blackwell (sm_121)
- **Compilation Times (ms)**: `{"official_lean4": 1056.0, "cpp_o3": 835.0, "rust_o3": 345.0, "lean_native_cpu": 325.0, "cuda_o3": 1110.0, "lean_native_gpu_ptx": 1110.0, "lean_native_hybrid": 880.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2002812, "cpp_o3": 264544, "rust_o3": 263928, "lean_native_cpu": 263564, "cuda_o3": 360056, "lean_native_gpu_ptx": 360056, "lean_native_hybrid": 360056}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `rust_o3`) | Speedup (`hybrid` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `407.16 ± 1.67` | `617.66 ± 3.93` | `405.77 ± 2.66` | `91.96 ± 0.45` | `1.46 ± 0.25` | `1.46 ± 0.25` | **4.41x** | **278.82x** | `0.002165` |
| `tuple_accum_sum` | `922.97 ± 2.46` | `25.35 ± 0.41` | `25.45 ± 0.30` | `6.27 ± 0.08` | `8.74 ± 0.05` | `6.27 ± 0.08` | **4.06x** | **4.06x** | `0.002165` |
| `sarray_scale_bias` | `2116.83 ± 167.55` | `5.64 ± 0.04` | `5.34 ± 0.05` | `2.94 ± 0.02` | `1.01 ± 0.32` | `1.01 ± 0.32` | **1.81x** | **5.27x** | `0.002165` |
| `dot_product_u64` | `49.48 ± 0.42` | `4.30 ± 0.04` | `4.19 ± 0.11` | `4.30 ± 0.01` | `0.74 ± 0.20` | `0.74 ± 0.20` | **0.97x** | **5.66x** | `0.002165` |
| `saxpy_kernel` | `1961.81 ± 167.59` | `8.18 ± 0.04` | `8.15 ± 0.05` | `8.20 ± 0.05` | `2.29 ± 0.43` | `2.29 ± 0.43` | **0.99x** | **3.56x** | `0.002165` |
| `matmul_tiled_u64` | `931.79 ± 7.45` | `28.71 ± 0.38` | `19.03 ± 0.30` | `13.98 ± 0.13` | `0.19 ± 0.01` | `0.19 ± 0.01` | **1.36x** | **101.35x** | `0.002165` |
| `evm_gas_schedule_u64` | `168.08 ± 0.80` | `9.26 ± 0.15` | `10.67 ± 0.14` | `2.55 ± 0.04` | `0.08 ± 0.30` | `0.08 ± 0.30` | **4.19x** | **136.13x** | `0.002165` |
| `keccak256_sponge_u64` | `61.02 ± 0.29` | `24.12 ± 0.14` | `9.65 ± 0.15` | `8.65 ± 0.10` | `0.13 ± 0.02` | `0.13 ± 0.02` | **1.12x** | **75.99x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `85.84 ± 0.98` | `5.56 ± 0.10` | `6.10 ± 0.07` | `2.89 ± 0.08` | `0.11 ± 0.04` | `0.11 ± 0.04` | **2.11x** | **57.15x** | `0.002141` |
| `goldilocks_ntt_modmul_u64` | `88.01 ± 0.91` | `6.81 ± 0.12` | `5.21 ± 0.08` | `3.32 ± 0.08` | `0.11 ± 0.04` | `0.11 ± 0.04` | **1.57x** | **49.29x** | `0.002165` |
| `holdout_bitwise` | `15.14 ± 0.12` | `15.20 ± 0.21` | `15.43 ± 0.18` | `12.69 ± 0.11` | `12.80 ± 0.07` | `12.69 ± 0.11` | **1.22x** | **1.22x** | `0.000583` |
| `holdout_loop_bounds` | `10.12 ± 0.20` | `10.16 ± 0.13` | `12.86 ± 0.21` | `10.19 ± 0.15` | `10.12 ± 0.05` | `10.19 ± 0.15` | **1.26x** | **1.26x** | `0.000583` |

---

## 3. Detailed Results on `ashur` (`x86_64`)

- **CPU**: Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)
- **GPU**: None (CPU-only host)
- **Compilation Times (ms)**: `{"official_lean4": 1770.0, "cpp_o3": 1323.0, "rust_o3": 352.0, "lean_native_cpu": 646.0, "lean_native_hybrid": 646.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2021780, "cpp_o3": 265676, "rust_o3": 264200, "lean_native_cpu": 263964, "lean_native_hybrid": 263964}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `620.65 ± 12.43` | `1127.16 ± 14.59` | `583.26 ± 5.03` | `124.09 ± 0.51` | `124.09 ± 0.51` | **5.00x** | **4.70x** | `0.002165` |
| `tuple_accum_sum` | `2073.62 ± 20.72` | `36.23 ± 0.43` | `32.22 ± 0.38` | `5.11 ± 0.08` | `5.11 ± 0.08` | **405.53x** | **6.30x** | `0.002165` |
| `sarray_scale_bias` | `521.91 ± 2.32` | `12.75 ± 0.14` | `12.64 ± 0.11` | `7.02 ± 0.15` | `7.02 ± 0.15` | **74.32x** | **1.80x** | `0.002165` |
| `dot_product_u64` | `81.46 ± 0.43` | `8.13 ± 0.13` | `7.95 ± 0.19` | `8.10 ± 0.60` | `8.10 ± 0.60` | **10.05x** | **0.98x** | `0.002165` |
| `saxpy_kernel` | `375.86 ± 10.05` | `16.43 ± 0.04` | `16.49 ± 0.46` | `15.89 ± 0.49` | `15.89 ± 0.49` | **23.66x** | **1.04x** | `0.002165` |
| `matmul_tiled_u64` | `2381.83 ± 8.24` | `43.44 ± 2.21` | `52.01 ± 2.02` | `41.99 ± 3.44` | `41.99 ± 3.44` | **56.73x** | **1.24x** | `0.002165` |
| `evm_gas_schedule_u64` | `331.48 ± 3.53` | `21.78 ± 0.18` | `7.38 ± 0.53` | `2.68 ± 0.13` | `2.68 ± 0.13` | **123.46x** | **2.75x** | `0.002165` |
| `keccak256_sponge_u64` | `141.79 ± 6.27` | `20.90 ± 0.99` | `19.58 ± 0.39` | `17.38 ± 0.12` | `17.38 ± 0.12` | **8.16x** | **1.13x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `194.76 ± 6.70` | `10.21 ± 0.16` | `12.24 ± 0.33` | `10.36 ± 0.44` | `10.36 ± 0.44` | **18.81x** | **1.18x** | `0.002165` |
| `goldilocks_ntt_modmul_u64` | `180.71 ± 3.94` | `27.13 ± 0.18` | `12.34 ± 0.83` | `10.03 ± 0.23` | `10.03 ± 0.23` | **18.01x** | **1.23x** | `0.002165` |
| `holdout_bitwise` | `13.32 ± 0.30` | `12.17 ± 0.27` | `13.98 ± 0.27` | `10.92 ± 0.13` | `10.92 ± 0.13` | **1.22x** | **1.28x** | `0.000583` |
| `holdout_loop_bounds` | `12.25 ± 0.12` | `11.06 ± 0.13` | `13.84 ± 0.29` | `11.26 ± 0.04` | `11.26 ± 0.04` | **1.09x** | **1.23x** | `0.000583` |
