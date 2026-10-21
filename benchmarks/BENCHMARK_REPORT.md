# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)

- **Generated At**: `2026-10-21T16:45:19.489999+00:00`
- **Trials per Benchmark**: `7`
- **Differential Verification Status**: `PASSED (100% Exact 64-bit Match)` (`132` cross-backend/cross-architecture assertions verified)

## 1. Executive Summary: Geometric-Mean Speedups

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_cpu` vs `rust_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `rust_o3` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64`)** | ARM Cortex-X925 / Cortex-A725 (20 cores) + NVIDIA GB10 Grace-Blackwell (sm_121) | **41.96x** | **2.06x** | **1.71x** | **717.00x** | **29.24x** |
| **`ashur` (`x86_64`)** | Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads) | **32.58x** | **2.25x** | **1.85x** | **32.58x** | **1.85x** |

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
| `holdout_bitwise` | `10,000,000` (iterations) | `17653976101919722312` | `MATCH` | `MATCH` | **PASS** |
| `holdout_loop_bounds` | `10,000,000` (iterations) | `2318209942448586758` | `MATCH` | `MATCH` | **PASS** |

---

## 3. Detailed Results on `spark-de79` (`aarch64`)

- **CPU**: ARM Cortex-X925 / Cortex-A725 (20 cores)
- **GPU**: NVIDIA GB10 Grace-Blackwell (sm_121)
- **Compilation Times (ms)**: `{"official_lean4": 981.0, "cpp_o3": 762.0, "rust_o3": 331.0, "lean_native_cpu": 200.0, "cuda_o3": 1119.0, "lean_native_gpu_ptx": 1119.0, "lean_native_hybrid": 759.5}`
- **Peak RSS (KB)**: `{"official_lean4": 2002848, "cpp_o3": 264796, "rust_o3": 263884, "lean_native_cpu": 263560, "cuda_o3": 361480, "lean_native_gpu_ptx": 361480, "lean_native_hybrid": 361480}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `rust_o3`) | Speedup (`hybrid` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `405.90 ± 2.21` | `624.74 ± 2.35` | `404.83 ± 1.96` | `91.55 ± 0.64` | `1.03 ± 0.11` | `1.03 ± 0.11` | **4.42x** | **391.33x** | `0.002165` |
| `tuple_accum_sum` | `935.58 ± 4.98` | `25.28 ± 0.26` | `25.48 ± 0.46` | `6.25 ± 0.05` | `8.83 ± 0.03` | `6.25 ± 0.05` | **4.08x** | **4.08x** | `0.002165` |
| `sarray_scale_bias` | `2123.31 ± 197.21` | `5.72 ± 0.04` | `5.33 ± 0.10` | `3.27 ± 0.02` | `0.72 ± 0.28` | `0.72 ± 0.28` | **1.63x** | **7.38x** | `0.002165` |
| `dot_product_u64` | `49.94 ± 0.54` | `4.30 ± 0.06` | `4.18 ± 0.09` | `4.18 ± 0.04` | `0.76 ± 0.15` | `0.76 ± 0.15` | **1.00x** | **5.52x** | `0.002165` |
| `saxpy_kernel` | `2029.28 ± 49.38` | `8.32 ± 0.02` | `8.32 ± 0.06` | `8.39 ± 0.06` | `1.88 ± 0.28` | `1.88 ± 0.28` | **0.99x** | **4.43x** | `0.002165` |
| `matmul_tiled_u64` | `931.70 ± 5.29` | `28.87 ± 0.34` | `18.75 ± 0.34` | `20.53 ± 0.12` | `0.19 ± 0.09` | `0.19 ± 0.09` | **0.91x** | **96.98x** | `0.002165` |
| `evm_gas_schedule_u64` | `168.81 ± 1.03` | `9.34 ± 0.13` | `10.50 ± 0.09` | `2.58 ± 0.03` | `0.11 ± 0.03` | `0.11 ± 0.03` | **4.07x** | **96.63x** | `0.002165` |
| `keccak256_sponge_u64` | `61.74 ± 0.41` | `24.23 ± 0.27` | `9.53 ± 0.15` | `8.61 ± 0.10` | `0.13 ± 0.01` | `0.13 ± 0.01` | **1.11x** | **75.59x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `87.32 ± 2.16` | `5.43 ± 0.11` | `6.03 ± 0.10` | `5.74 ± 0.10` | `0.08 ± 0.04` | `0.08 ± 0.04` | **1.05x** | **76.56x** | `0.002165` |
| `holdout_bitwise` | `15.16 ± 0.12` | `15.31 ± 0.19` | `15.24 ± 0.26` | `12.61 ± 0.07` | `12.94 ± 0.21` | `12.61 ± 0.07` | **1.21x** | **1.21x** | `0.000583` |
| `holdout_loop_bounds` | `10.37 ± 0.07` | `10.20 ± 0.09` | `12.72 ± 0.17` | `10.24 ± 0.08` | `10.30 ± 0.21` | `10.24 ± 0.08` | **1.24x** | **1.24x** | `0.000583` |

---

## 3. Detailed Results on `ashur` (`x86_64`)

- **CPU**: Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)
- **GPU**: None (CPU-only host)
- **Compilation Times (ms)**: `{"official_lean4": 1658.0, "cpp_o3": 1232.0, "rust_o3": 358.0, "lean_native_cpu": 587.0, "lean_native_hybrid": 587.0}`
- **Peak RSS (KB)**: `{"official_lean4": 2021720, "cpp_o3": 265656, "rust_o3": 264200, "lean_native_cpu": 263960, "lean_native_hybrid": 263960}`

| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `rust_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `rust_o3`) | `p`-value (MWU) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `collatz_steps` | `640.42 ± 11.22` | `1185.75 ± 12.46` | `600.15 ± 2.50` | `124.58 ± 0.95` | `124.58 ± 0.95` | **5.14x** | **4.82x** | `0.002165` |
| `tuple_accum_sum` | `2091.86 ± 6.94` | `37.26 ± 0.64` | `32.44 ± 0.24` | `5.15 ± 0.11` | `5.15 ± 0.11` | **406.34x** | **6.30x** | `0.002165` |
| `sarray_scale_bias` | `517.99 ± 10.25` | `12.96 ± 0.22` | `12.59 ± 0.15` | `6.82 ± 0.18` | `6.82 ± 0.18` | **75.99x** | **1.85x** | `0.002165` |
| `dot_product_u64` | `81.83 ± 1.80` | `8.34 ± 0.30` | `7.96 ± 0.14` | `7.72 ± 0.27` | `7.72 ± 0.27` | **10.59x** | **1.03x** | `0.002165` |
| `saxpy_kernel` | `369.35 ± 16.95` | `16.88 ± 0.33` | `16.10 ± 0.09` | `15.54 ± 0.44` | `15.54 ± 0.44` | **23.78x** | **1.04x** | `0.002165` |
| `matmul_tiled_u64` | `2411.23 ± 38.01` | `41.80 ± 1.62` | `51.89 ± 0.87` | `42.06 ± 2.14` | `42.06 ± 2.14` | **57.32x** | **1.23x** | `0.002165` |
| `evm_gas_schedule_u64` | `331.68 ± 4.16` | `22.12 ± 0.42` | `7.32 ± 0.45` | `2.74 ± 0.10` | `2.74 ± 0.10` | **121.22x** | **2.67x** | `0.002165` |
| `keccak256_sponge_u64` | `140.41 ± 2.70` | `21.17 ± 0.57` | `19.36 ± 0.18` | `17.44 ± 0.60` | `17.44 ± 0.60` | **8.05x** | **1.11x** | `0.002165` |
| `uint256_wad_muldiv_u64` | `196.64 ± 1.69` | `10.43 ± 0.28` | `12.25 ± 0.13` | `10.65 ± 0.34` | `10.65 ± 0.34` | **18.47x** | **1.15x** | `0.002165` |
| `holdout_bitwise` | `13.32 ± 0.08` | `12.28 ± 0.19` | `13.94 ± 0.22` | `10.89 ± 0.05` | `10.89 ± 0.05` | **1.22x** | **1.28x** | `0.000583` |
| `holdout_loop_bounds` | `12.24 ± 0.11` | `11.21 ± 0.11` | `13.73 ± 0.14` | `11.28 ± 0.23` | `11.28 ± 0.23` | **1.09x** | **1.22x** | `0.000583` |
