# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)

- **Generated At**: `2026-10-21T20:19:04.353282+00:00`
- **Trials per Benchmark**: `7`
- **Differential Verification Status**: `PASSED (100% Exact 64-bit Match)` (`168` cross-backend/cross-architecture assertions verified)

## 1. Executive Summary: Geometric-Mean Speedups

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_cpu` vs `rust_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `rust_o3` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64`)** | ARM Cortex-X925 / Cortex-A725 (20 cores) + NVIDIA GB10 Grace-Blackwell (sm_121) | **29.86x** | **2.48x** | **1.80x** | **629.37x** | **37.89x** |
| **`ashur` (`x86_64`)** | Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads) | **30.57x** | **2.39x** | **1.76x** | **30.57x** | **1.76x** |

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
- **Compilation Times (ms)**: `{"official_lean4": 4083.0, "cpp_o3": 901.0, "rust_o3": 730.0, "lean_native_cpu": 332.0, "cuda_o3": 1574.0, "lean_native_gpu_ptx": 1574.0, "lean_native_hybrid": 1119.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2008364, "cpp_o3": 264724, "rust_o3": 263880, "lean_native_cpu": 263564, "cuda_o3": 362264, "lean_native_gpu_ptx": 362264, "lean_native_hybrid": 362264}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `rust_o3`) | Speedup (`hybrid` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `407.62 ± 2.51` | `620.82 ± 1.90` | `406.17 ± 1.54` | `91.45 ± 0.52` | `1.13 ± 0.27` | `1.13 ± 0.27` | **4.44x** | **359.34x** | `0.002165` |
| `tuple_accum_sum` | `943.56 ± 4.40` | `25.37 ± 0.06` | `25.55 ± 0.36` | `6.26 ± 0.07` | `8.70 ± 0.11` | `6.26 ± 0.07` | **4.08x** | **4.08x** | `0.002165` |
| `sarray_scale_bias` | `266.81 ± 14.77` | `5.65 ± 0.05` | `5.39 ± 0.06` | `2.96 ± 0.04` | `0.91 ± 0.65` | `0.91 ± 0.65` | **1.82x** | **5.92x** | `0.002165` |
| `dot_product_u64` | `49.84 ± 1.25` | `4.27 ± 0.04` | `4.20 ± 0.08` | `4.31 ± 0.04` | `0.71 ± 0.15` | `0.71 ± 0.15` | **0.98x** | **5.91x** | `0.002165` |
| `saxpy_kernel` | `2339.60 ± 171.04` | `8.15 ± 0.05` | `8.15 ± 0.05` | `8.21 ± 0.04` | `2.03 ± 0.64` | `2.03 ± 0.64` | **0.99x** | **4.01x** | `0.002165` |
| `matmul_tiled_u64` | `930.48 ± 2.48` | `28.66 ± 0.37` | `19.04 ± 0.49` | `13.84 ± 0.07` | `0.27 ± 0.10` | `0.27 ± 0.10` | **1.38x** | **70.56x** | `0.002165` |
| `evm_gas_schedule_u64` | `167.22 ± 1.13` | `9.26 ± 0.07` | `10.68 ± 0.21` | `2.55 ± 0.04` | `0.08 ± 0.04` | `0.08 ± 0.04` | **4.19x** | **128.68x** | `0.002165` |
| `keccak256_sponge_u64` | `61.54 ± 0.69` | `24.11 ± 0.19` | `9.65 ± 0.03` | `8.55 ± 0.03` | `0.13 ± 0.10` | `0.13 ± 0.10` | **1.13x** | **75.47x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `85.39 ± 1.02` | `5.52 ± 0.12` | `6.09 ± 0.07` | `2.88 ± 0.02` | `0.07 ± 0.00` | `0.07 ± 0.00` | **2.11x** | **81.25x** | `0.002165` |
| `goldilocks_ntt_modmul_u64` | `88.77 ± 0.50` | `6.74 ± 0.13` | `5.21 ± 0.09` | `3.34 ± 0.04` | `0.07 ± 0.00` | `0.07 ± 0.00` | **1.56x** | **69.56x** | `0.002165` |
| `babybear_poseidon2_sbox_u64` | `109.11 ± 1.29` | `44.82 ± 0.18` | `18.38 ± 0.25` | `16.60 ± 0.12` | `0.18 ± 0.00` | `0.18 ± 0.00` | **1.11x** | **101.27x** | `0.002165` |
| `mersenne31_circle_butterfly_u64` | `92.41 ± 1.33` | `28.03 ± 0.04` | `9.05 ± 0.10` | `6.03 ± 0.08` | `0.08 ± 0.00` | `0.08 ± 0.00` | **1.50x** | **108.34x** | `0.002141` |
| `holdout_bitwise` | `15.14 ± 0.25` | `15.14 ± 0.13` | `15.42 ± 0.12` | `12.66 ± 0.16` | `12.91 ± 0.20` | `12.66 ± 0.16` | **1.22x** | **1.22x** | `0.000583` |
| `holdout_loop_bounds` | `10.31 ± 0.13` | `10.17 ± 0.05` | `12.82 ± 0.07` | `10.28 ± 0.17` | `10.31 ± 0.17` | `10.28 ± 0.17` | **1.25x** | **1.25x** | `0.000583` |

---

## 3. Detailed Results on `ashur` (`x86_64`)

- **CPU**: Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)
- **GPU**: None (CPU-only host)
- **Compilation Times (ms)**: `{"official_lean4": 2163.0, "cpp_o3": 1383.0, "rust_o3": 377.0, "lean_native_cpu": 697.0, "lean_native_hybrid": 697.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2001548, "cpp_o3": 265652, "rust_o3": 264204, "lean_native_cpu": 263968, "lean_native_hybrid": 263968}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `621.65 ± 8.36` | `1148.01 ± 15.08` | `608.02 ± 1.53` | `126.31 ± 0.56` | `126.31 ± 0.56` | **4.92x** | **4.81x** | `0.002165` |
| `tuple_accum_sum` | `2106.78 ± 15.92` | `36.92 ± 0.77` | `32.74 ± 1.35` | `5.14 ± 0.10` | `5.14 ± 0.10` | **409.70x** | **6.37x** | `0.002165` |
| `sarray_scale_bias` | `1457.06 ± 92.41` | `12.88 ± 0.26` | `12.91 ± 0.24` | `7.04 ± 0.69` | `7.04 ± 0.69` | **207.11x** | **1.84x** | `0.002165` |
| `dot_product_u64` | `83.28 ± 1.79` | `8.33 ± 0.33` | `8.29 ± 2.04` | `8.00 ± 0.60` | `8.00 ± 0.60` | **10.41x** | **1.04x** | `0.002165` |
| `saxpy_kernel` | `1201.41 ± 59.63` | `16.64 ± 0.30` | `16.35 ± 0.66` | `15.96 ± 0.31` | `15.96 ± 0.31` | **75.30x** | **1.02x** | `0.002165` |
| `matmul_tiled_u64` | `2436.07 ± 15.37` | `43.39 ± 3.28` | `54.18 ± 1.47` | `43.11 ± 1.96` | `43.11 ± 1.96` | **56.51x** | **1.26x** | `0.002165` |
| `evm_gas_schedule_u64` | `340.13 ± 3.82` | `22.01 ± 0.62` | `7.30 ± 0.60` | `2.73 ± 0.12` | `2.73 ± 0.12` | **124.37x** | **2.67x** | `0.002165` |
| `keccak256_sponge_u64` | `144.74 ± 3.82` | `21.30 ± 0.73` | `19.56 ± 0.09` | `17.47 ± 0.41` | `17.47 ± 0.41` | **8.29x** | **1.12x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `197.27 ± 5.85` | `10.34 ± 0.41` | `12.32 ± 0.39` | `10.50 ± 0.59` | `10.50 ± 0.59` | **18.79x** | **1.17x** | `0.002165` |
| `goldilocks_ntt_modmul_u64` | `187.09 ± 5.29` | `27.29 ± 0.87` | `11.82 ± 0.58` | `10.15 ± 0.25` | `10.15 ± 0.25` | **18.44x** | **1.16x** | `0.002165` |
| `babybear_poseidon2_sbox_u64` | `215.47 ± 4.13` | `78.33 ± 1.31` | `48.25 ± 2.71` | `42.55 ± 0.60` | `42.55 ± 0.60` | **5.06x** | **1.13x** | `0.002165` |
| `mersenne31_circle_butterfly_u64` | `195.16 ± 4.22` | `54.37 ± 1.05` | `24.41 ± 0.78` | `9.79 ± 0.76` | `9.79 ± 0.76` | **19.93x** | **2.49x** | `0.002165` |
| `holdout_bitwise` | `13.35 ± 0.28` | `12.18 ± 0.13` | `14.11 ± 0.18` | `10.93 ± 0.12` | `10.93 ± 0.12` | **1.22x** | **1.29x** | `0.000583` |
| `holdout_loop_bounds` | `12.37 ± 0.32` | `11.21 ± 0.34` | `13.78 ± 0.22` | `11.35 ± 0.42` | `11.35 ± 0.42` | **1.09x** | **1.21x** | `0.000583` |
