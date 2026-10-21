# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)

- **Generated At**: `2026-10-21T19:23:14.428515+00:00`
- **Trials per Benchmark**: `7`
- **Differential Verification Status**: `PASSED (100% Exact 64-bit Match)` (`156` cross-backend/cross-architecture assertions verified)

## 1. Executive Summary: Geometric-Mean Speedups

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_cpu` vs `rust_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `rust_o3` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64`)** | ARM Cortex-X925 / Cortex-A725 (20 cores) + NVIDIA GB10 Grace-Blackwell (sm_121) | **31.79x** | **2.35x** | **1.82x** | **563.50x** | **32.22x** |
| **`ashur` (`x86_64`)** | Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads) | **34.55x** | **2.28x** | **1.69x** | **34.55x** | **1.69x** |

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
| `holdout_bitwise` | `10,000,000` (iterations) | `17653976101919722312` | `MATCH` | `MATCH` | **PASS** |
| `holdout_loop_bounds` | `10,000,000` (iterations) | `2318209942448586758` | `MATCH` | `MATCH` | **PASS** |

---

## 3. Detailed Results on `spark-de79` (`aarch64`)

- **CPU**: ARM Cortex-X925 / Cortex-A725 (20 cores)
- **GPU**: NVIDIA GB10 Grace-Blackwell (sm_121)
- **Compilation Times (ms)**: `{"official_lean4": 3867.0, "cpp_o3": 981.0, "rust_o3": 773.0, "lean_native_cpu": 580.0, "cuda_o3": 1609.0, "lean_native_gpu_ptx": 1609.0, "lean_native_hybrid": 1384.5}`
- **Peak RSS (KB)**: `{"official_lean4": 2008352, "cpp_o3": 264784, "rust_o3": 263880, "lean_native_cpu": 263568, "cuda_o3": 361760, "lean_native_gpu_ptx": 361760, "lean_native_hybrid": 361760}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `rust_o3`) | Speedup (`hybrid` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `406.13 ± 1.90` | `621.62 ± 2.60` | `405.65 ± 2.10` | `92.14 ± 0.42` | `1.12 ± 0.10` | `1.12 ± 0.10` | **4.40x** | **360.77x** | `0.002165` |
| `tuple_accum_sum` | `934.29 ± 3.78` | `25.27 ± 0.22` | `25.65 ± 0.28` | `6.21 ± 0.07` | `8.73 ± 0.04` | `6.21 ± 0.07` | **4.13x** | **4.13x** | `0.002165` |
| `sarray_scale_bias` | `281.33 ± 15.71` | `5.65 ± 0.03` | `5.33 ± 0.07` | `2.95 ± 0.02` | `1.34 ± 0.82` | `1.34 ± 0.82` | **1.81x** | **3.99x** | `0.002165` |
| `dot_product_u64` | `50.51 ± 0.87` | `4.27 ± 0.01` | `4.18 ± 0.07` | `4.29 ± 0.05` | `0.75 ± 0.26` | `0.75 ± 0.26` | **0.97x** | **5.54x** | `0.002165` |
| `saxpy_kernel` | `2337.07 ± 138.86` | `8.18 ± 0.03` | `8.15 ± 0.04` | `8.20 ± 0.02` | `2.02 ± 0.33` | `2.02 ± 0.33` | **0.99x** | **4.03x** | `0.002165` |
| `matmul_tiled_u64` | `927.44 ± 8.24` | `28.87 ± 0.47` | `18.98 ± 0.15` | `13.91 ± 0.24` | `0.18 ± 0.01` | `0.18 ± 0.01` | **1.36x** | **104.06x** | `0.002141` |
| `evm_gas_schedule_u64` | `167.45 ± 0.72` | `9.40 ± 0.14` | `10.62 ± 0.10` | `2.57 ± 0.06` | `0.08 ± 0.05` | `0.08 ± 0.05` | **4.14x** | **125.88x** | `0.002165` |
| `keccak256_sponge_u64` | `61.64 ± 0.63` | `24.47 ± 0.46` | `9.62 ± 0.10` | `8.55 ± 0.18` | `0.12 ± 0.02` | `0.12 ± 0.02` | **1.13x** | **81.81x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `86.30 ± 0.79` | `5.61 ± 0.01` | `6.08 ± 0.06` | `2.92 ± 0.04` | `0.10 ± 0.04` | `0.10 ± 0.04` | **2.09x** | **58.04x** | `0.002165` |
| `goldilocks_ntt_modmul_u64` | `87.22 ± 0.38` | `6.82 ± 0.21` | `5.21 ± 0.02` | `3.34 ± 0.06` | `0.11 ± 0.05` | `0.11 ± 0.05` | **1.56x** | **49.21x** | `0.002165` |
| `babybear_poseidon2_sbox_u64` | `108.74 ± 0.42` | `45.18 ± 0.65` | `18.17 ± 0.25` | `16.67 ± 0.05` | `0.19 ± 0.09` | `0.19 ± 0.09` | **1.09x** | **95.76x** | `0.002165` |
| `holdout_bitwise` | `15.19 ± 0.34` | `15.33 ± 0.28` | `15.26 ± 0.13` | `12.60 ± 0.05` | `12.82 ± 0.12` | `12.60 ± 0.05` | **1.21x** | **1.21x** | `0.000583` |
| `holdout_loop_bounds` | `10.30 ± 0.19` | `10.35 ± 0.19` | `12.73 ± 0.14` | `10.24 ± 0.15` | `10.24 ± 0.14` | `10.24 ± 0.15` | **1.24x** | **1.24x** | `0.000583` |

---

## 3. Detailed Results on `ashur` (`x86_64`)

- **CPU**: Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)
- **GPU**: None (CPU-only host)
- **Compilation Times (ms)**: `{"official_lean4": 3298.0, "cpp_o3": 2450.0, "rust_o3": 595.0, "lean_native_cpu": 1151.0, "lean_native_hybrid": 1151.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2021784, "cpp_o3": 265676, "rust_o3": 264176, "lean_native_cpu": 263960, "lean_native_hybrid": 263960}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `687.54 ± 2.26` | `1410.80 ± 23.51` | `721.52 ± 3.30` | `136.29 ± 0.81` | `136.29 ± 0.81` | **5.04x** | **5.29x** | `0.002165` |
| `tuple_accum_sum` | `4139.67 ± 33.96` | `43.65 ± 0.86` | `38.66 ± 0.44` | `6.84 ± 0.18` | `6.84 ± 0.18` | **605.12x** | **5.65x** | `0.002165` |
| `sarray_scale_bias` | `891.28 ± 3.46` | `21.33 ± 0.54` | `21.10 ± 0.67` | `11.39 ± 0.28` | `11.39 ± 0.28` | **78.27x** | **1.85x** | `0.002165` |
| `dot_product_u64` | `144.54 ± 8.25` | `13.70 ± 0.42` | `13.84 ± 0.85` | `13.56 ± 0.38` | `13.56 ± 0.38` | **10.66x** | **1.02x** | `0.002165` |
| `saxpy_kernel` | `697.94 ± 96.84` | `26.52 ± 0.52` | `26.51 ± 0.53` | `25.61 ± 0.95` | `25.61 ± 0.95` | **27.25x** | **1.03x** | `0.002165` |
| `matmul_tiled_u64` | `4523.99 ± 256.47` | `63.28 ± 2.78` | `77.81 ± 2.00` | `57.15 ± 1.49` | `57.15 ± 1.49` | **79.16x** | **1.36x** | `0.002165` |
| `evm_gas_schedule_u64` | `687.35 ± 63.05` | `26.40 ± 0.22` | `8.77 ± 0.72` | `3.69 ± 0.11` | `3.69 ± 0.11` | **186.48x** | **2.38x** | `0.002165` |
| `keccak256_sponge_u64` | `260.19 ± 19.95` | `25.53 ± 0.23` | `23.25 ± 0.28` | `21.30 ± 0.41` | `21.30 ± 0.41` | **12.22x** | **1.09x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `405.43 ± 34.72` | `16.57 ± 1.51` | `15.61 ± 0.33` | `15.00 ± 0.48` | `15.00 ± 0.48` | **27.03x** | **1.04x** | `0.002165` |
| `goldilocks_ntt_modmul_u64` | `369.27 ± 32.70` | `33.17 ± 0.62` | `15.35 ± 0.49` | `12.00 ± 0.42` | `12.00 ± 0.42` | **30.76x** | **1.28x** | `0.002165` |
| `babybear_poseidon2_sbox_u64` | `415.78 ± 37.77` | `118.32 ± 4.35` | `58.81 ± 1.89` | `51.60 ± 0.94` | `51.60 ± 0.94` | **8.06x** | **1.14x** | `0.002165` |
| `holdout_bitwise` | `14.05 ± 0.08` | `12.76 ± 0.02` | `14.69 ± 0.03` | `12.73 ± 0.07` | `12.73 ± 0.07` | **1.10x** | **1.15x** | `0.000583` |
| `holdout_loop_bounds` | `13.71 ± 0.14` | `13.23 ± 0.29` | `14.56 ± 0.03` | `13.30 ± 0.07` | `13.30 ± 0.07` | **1.03x** | **1.10x** | `0.000583` |
