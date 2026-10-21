# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)

- **Generated At**: `2026-10-21T23:31:14.705422+00:00`
- **Trials per Benchmark**: `7`
- **Differential Verification Status**: `PASSED (100% Exact 64-bit Match)` (`196` cross-backend/cross-architecture assertions verified)

## 1. Executive Summary: Geometric-Mean Speedups

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `c_o3` | `lean_native_cpu` vs `cpp_o3` | `lean_native_cpu` vs `rust_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `rust_o3` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64`)** | ARM Cortex-X925 / Cortex-A725 (20 cores) + NVIDIA GB10 Grace-Blackwell (sm_121) | **30.12x** | **2.48x** | **2.48x** | **1.80x** | **649.99x** | **38.76x** |
| **`ashur` (`x86_64`)** | Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads) | **32.99x** | **2.47x** | **2.46x** | **1.79x** | **32.99x** | **1.79x** |

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
| `babybear_poseidon2_sbox_u64` | `5,000,000` (states) | `11514767664959043523` | `MATCH` | `MATCH` | **PASS** |
| `mersenne31_circle_butterfly_u64` | `5,000,000` (butterflies) | `13605335436704834831` | `MATCH` | `MATCH` | **PASS** |
| `holdout_bitwise` | `10,000,000` (iterations) | `17653976101919722312` | `MATCH` | `MATCH` | **PASS** |
| `holdout_loop_bounds` | `10,000,000` (iterations) | `2318209942448586758` | `MATCH` | `MATCH` | **PASS** |

---

## 3. Detailed Results on `spark-de79` (`aarch64`)

- **CPU**: ARM Cortex-X925 / Cortex-A725 (20 cores)
- **GPU**: NVIDIA GB10 Grace-Blackwell (sm_121)
- **Compilation Times (ms)**: `{"official_lean4": 4368.0, "c_o3": 484.0, "cpp_o3": 881.0, "rust_o3": 716.0, "lean_native_cpu": 586.0, "cuda_o3": 1459.0, "lean_native_gpu_ptx": 1459.0, "lean_native_hybrid": 1315.5}`
- **Peak RSS (KB)**: `{"official_lean4": 2008444, "c_o3": 263472, "cpp_o3": 264728, "rust_o3": 263868, "lean_native_cpu": 263568, "cuda_o3": 362304, "lean_native_gpu_ptx": 362304, "lean_native_hybrid": 362304}`

| Benchmark | `official_lean4` (ms ± IQR) | `c_o3` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `rust_o3`) | Speedup (`hybrid` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `406.33 ± 2.59` | `580.64 ± 3.59` | `621.03 ± 1.82` | `406.75 ± 2.37` | `91.35 ± 0.75` | `1.04 ± 0.53` | `1.04 ± 0.53` | **4.45x** | **391.22x** | `0.002165` |
| `tuple_accum_sum` | `943.76 ± 2.68` | `25.34 ± 0.23` | `25.30 ± 0.16` | `25.42 ± 0.12` | `6.22 ± 0.08` | `8.71 ± 0.05` | `6.22 ± 0.08` | **4.08x** | **4.08x** | `0.002165` |
| `sarray_scale_bias` | `270.96 ± 15.23` | `5.66 ± 0.04` | `5.66 ± 0.01` | `5.39 ± 0.07` | `2.96 ± 0.07` | `0.98 ± 0.60` | `0.98 ± 0.60` | **1.82x** | **5.47x** | `0.002165` |
| `dot_product_u64` | `48.76 ± 0.80` | `4.27 ± 0.03` | `4.27 ± 0.05` | `4.21 ± 0.03` | `4.30 ± 0.07` | `0.76 ± 0.20` | `0.76 ± 0.20` | **0.98x** | **5.57x** | `0.002165` |
| `saxpy_kernel` | `2653.11 ± 198.24` | `8.20 ± 0.07` | `8.22 ± 0.05` | `8.17 ± 0.07` | `8.42 ± 0.23` | `2.25 ± 0.58` | `2.25 ± 0.58` | **0.97x** | **3.64x** | `0.002165` |
| `matmul_tiled_u64` | `933.48 ± 4.59` | `29.26 ± 0.26` | `29.10 ± 0.15` | `19.06 ± 0.19` | `13.86 ± 0.13` | `0.18 ± 0.01` | `0.18 ± 0.01` | **1.37x** | **104.01x** | `0.002165` |
| `evm_gas_schedule_u64` | `166.84 ± 1.21` | `9.31 ± 0.16` | `9.29 ± 0.11` | `10.68 ± 0.02` | `2.55 ± 0.05` | `0.08 ± 0.03` | `0.08 ± 0.03` | **4.18x** | **135.36x** | `0.002165` |
| `keccak256_sponge_u64` | `61.44 ± 0.83` | `24.13 ± 0.52` | `24.17 ± 0.07` | `9.65 ± 0.02` | `8.53 ± 0.09` | `0.13 ± 0.00` | `0.13 ± 0.00` | **1.13x** | **75.47x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `85.37 ± 0.97` | `5.57 ± 0.11` | `5.52 ± 0.05` | `6.09 ± 0.01` | `2.87 ± 0.03` | `0.08 ± 0.04` | `0.08 ± 0.04` | **2.12x** | **80.13x** | `0.002165` |
| `goldilocks_ntt_modmul_u64` | `88.55 ± 0.79` | `6.95 ± 0.16` | `6.79 ± 0.09` | `5.22 ± 0.01` | `3.33 ± 0.03` | `0.08 ± 0.00` | `0.08 ± 0.00` | **1.57x** | **69.13x** | `0.002165` |
| `babybear_poseidon2_sbox_u64` | `108.99 ± 0.59` | `45.14 ± 0.63` | `45.05 ± 0.35` | `18.35 ± 0.17` | `16.60 ± 0.07` | `0.18 ± 0.00` | `0.18 ± 0.00` | **1.11x** | **101.13x** | `0.002141` |
| `mersenne31_circle_butterfly_u64` | `92.73 ± 1.06` | `28.22 ± 0.47` | `28.16 ± 0.31` | `9.05 ± 0.01` | `6.05 ± 0.08` | `0.08 ± 0.00` | `0.08 ± 0.00` | **1.50x** | **109.21x** | `0.002165` |
| `holdout_bitwise` | `15.11 ± 0.10` | `15.35 ± 0.30` | `15.24 ± 0.15` | `15.40 ± 0.08` | `12.60 ± 0.23` | `12.78 ± 0.17` | `12.60 ± 0.23` | **1.22x** | **1.22x** | `0.000583` |
| `holdout_loop_bounds` | `10.28 ± 0.10` | `10.16 ± 0.21` | `10.17 ± 0.06` | `12.88 ± 0.07` | `10.22 ± 0.19` | `10.18 ± 0.08` | `10.22 ± 0.19` | **1.26x** | **1.26x** | `0.000583` |

---

## 3. Detailed Results on `ashur` (`x86_64`)

- **CPU**: Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)
- **GPU**: None (CPU-only host)
- **Compilation Times (ms)**: `{"official_lean4": 5748.0, "c_o3": 876.0, "cpp_o3": 1701.0, "rust_o3": 855.0, "lean_native_cpu": 900.0, "lean_native_hybrid": 900.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2005168, "c_o3": 263764, "cpp_o3": 265652, "rust_o3": 264208, "lean_native_cpu": 263968, "lean_native_hybrid": 263968}`

| Benchmark | `official_lean4` (ms ± IQR) | `c_o3` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `639.22 ± 10.33` | `1105.32 ± 3.60` | `1147.59 ± 21.61` | `625.33 ± 5.08` | `129.51 ± 0.41` | `129.51 ± 0.41` | **4.94x** | **4.83x** | `0.002165` |
| `tuple_accum_sum` | `2411.89 ± 58.72` | `39.05 ± 2.29` | `39.22 ± 2.73` | `33.76 ± 2.62` | `5.18 ± 1.20` | `5.18 ± 1.20` | **465.89x** | **6.52x** | `0.002165` |
| `sarray_scale_bias` | `1340.11 ± 154.32` | `13.27 ± 5.60` | `13.01 ± 1.24` | `13.01 ± 3.65` | `7.09 ± 2.78` | `7.09 ± 2.78` | **189.12x** | **1.84x** | `0.002165` |
| `dot_product_u64` | `90.00 ± 5.92` | `8.59 ± 2.21` | `8.30 ± 0.20` | `8.22 ± 0.15` | `8.10 ± 2.58` | `8.10 ± 2.58` | **11.12x** | **1.02x** | `0.002165` |
| `saxpy_kernel` | `1366.96 ± 204.04` | `18.35 ± 3.41` | `18.35 ± 5.31` | `18.45 ± 5.57` | `18.65 ± 10.78` | `18.65 ± 10.78` | **73.29x** | **0.99x** | `0.002165` |
| `matmul_tiled_u64` | `2784.86 ± 71.51` | `55.50 ± 8.54` | `48.58 ± 2.56` | `58.40 ± 1.38` | `41.50 ± 6.82` | `41.50 ± 6.82` | **67.11x** | **1.41x** | `0.002165` |
| `evm_gas_schedule_u64` | `389.57 ± 18.25` | `22.26 ± 1.53` | `23.41 ± 2.39` | `7.61 ± 0.22` | `2.74 ± 0.09` | `2.74 ± 0.09` | **142.14x** | **2.78x** | `0.002165` |
| `keccak256_sponge_u64` | `160.27 ± 11.68` | `21.43 ± 0.86` | `21.21 ± 1.76` | `19.67 ± 2.37` | `17.87 ± 2.32` | `17.87 ± 2.32` | **8.97x** | **1.10x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `231.08 ± 21.33` | `10.45 ± 3.95` | `11.35 ± 3.13` | `12.46 ± 0.52` | `10.59 ± 2.10` | `10.59 ± 2.10` | **21.82x** | **1.18x** | `0.002165` |
| `goldilocks_ntt_modmul_u64` | `212.96 ± 10.96` | `28.29 ± 2.75` | `29.43 ± 1.29` | `14.08 ± 1.82` | `10.60 ± 0.91` | `10.60 ± 0.91` | **20.08x** | **1.33x** | `0.002165` |
| `babybear_poseidon2_sbox_u64` | `250.00 ± 14.81` | `87.16 ± 5.50` | `87.34 ± 6.20` | `49.48 ± 1.39` | `44.11 ± 2.50` | `44.11 ± 2.50` | **5.67x** | **1.12x** | `0.002165` |
| `mersenne31_circle_butterfly_u64` | `222.69 ± 43.27` | `61.08 ± 2.90` | `58.11 ± 2.83` | `24.91 ± 1.87` | `10.09 ± 1.39` | `10.09 ± 1.39` | **22.08x** | **2.47x** | `0.002165` |
| `holdout_bitwise` | `13.61 ± 0.42` | `12.26 ± 0.09` | `12.32 ± 0.36` | `14.35 ± 0.37` | `11.00 ± 0.69` | `11.00 ± 0.69` | **1.24x** | **1.30x** | `0.000583` |
| `holdout_loop_bounds` | `12.55 ± 0.80` | `11.24 ± 0.18` | `11.08 ± 0.14` | `13.93 ± 0.30` | `11.58 ± 1.25` | `11.58 ± 1.25` | **1.08x** | **1.20x** | `0.000583` |
