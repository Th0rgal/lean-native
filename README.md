# Lean Native (`lean-native` v0.4)

**Lean Native (`lean-native`)** is a high-performance, formally validated, self-optimizing native compiler and counterexample engine for **Lean 4** (`leanprover/lean4:v4.31.0`) targeting **x86-64**, **ARM64**, **NVIDIA CUDA (MLIR / NVVM / PTX 8.0)**, and **Apple Metal (MSL 3.0)** with native **256-bit EVM/Verity (`u256`/`i256`/`StorageMap`)** support, achieving performance approaching or exceeding optimized Rust/C++ while preserving Lean's semantics through **67 machine-checked kernel proofs** (`0 sorryAx`) and Alive2-style symbolic translation validation.

---

## Highlights & Real Hardware Results (v0.4)

### 1. Cross-Architecture Runtime Speedups (`spark-de79` ARM64+GB10 & `ashur` x86-64)
Across our workload suite (`collatz_steps`, `tuple_accum_sum`, `sarray_scale_bias`, `dot_product_u64`, `saxpy_kernel`, `matmul_tiled_u64`, plus 256-bit EVM/Verity kernels `evm_erc20_transfer_u256` and `evm_muldiv_wad_u256`) and immutable holdout tests (`holdout_bitwise`, `holdout_loop_bounds`), verified with **80/80 exact 64-bit deterministic checksum matches** (`7` trials per target, `p = 0.002165 < 0.05` via Mann-Whitney U):

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `cpp_o3` | Peak RSS Reduction |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64` + `CUDA`)** | 20-core ARM Cortex-X925/A725 + NVIDIA GB10 Grace-Blackwell (`sm_121` / `sm_90` PTX) | **25.09x** | **1.22x** | **165.02x** | **8.01x** | **7.6x** (`263 MB` vs `2,004 MB`) |
| **`ashur` (`x86_64`)** | 8-thread Intel Core i7-7700 @ 3.60 GHz | **20.07x** | **1.29x** | **20.07x** | **1.29x** | **7.7x** (`264 MB` vs `2,022 MB`) |

### 2. `lean-native-core` (`libleanrt`-Only) Cold-Start & Persistent JSON-RPC Worker Latency
By decoupling [`LeanNative/Core.lean`](LeanNative/Core.lean) (23 compiler, semantics, proof, transform, superoptimizer, GPU IR, backend, and adapter modules with **zero `import Lean`**) and unifying CLI/worker dispatch in [`LeanNative/Driver/CoreCLI.lean`](LeanNative/Driver/CoreCLI.lean), `lean-native-core` links solely against `libleanrt.a` and standard C libraries (eliminating the ~230 MB `libleanshared.so` dependency):

| Metric | `lean-native` (Full Frontend + `libleanshared.so`) | `lean-native-core` (`libleanrt.a` Only, `spark-de79` ARM64) | `lean-native-core` (`libleanrt.a` Only, `ashur` x86-64) | Improvement |
| :--- | :---: | :---: | :---: | :---: |
| **Binary Size (Stripped / Unstripped)** | `238 MB` | **`3.7 MB`** (`6.2 MB` unstripped) | **`3.7 MB`** (`5.6 MB` unstripped) | **64.3x smaller** |
| **Cold-Start CLI Latency (`--help`)** | `29.34 ms` | **`2.45 ms`** | **`9.08 ms`** | **12.0x faster** |
| **Cold-Start 8-Kernel `compile-llvm`** | `36.40 ms` | **`5.99 ms`** | **`25.89 ms`** | **6.1x faster** |
| **Persistent `worker` JSON-RPC Latency** | `0.075 ms / req` | **`0.0716 ms / req` (`13,973 req/s`)** | **`0.2154 ms / req` (`4,643 req/s`)** | **409x faster than cold CLI** |

See [`benchmarks/BENCHMARK_REPORT.md`](benchmarks/BENCHMARK_REPORT.md) and [`benchmarks/results/latest_benchmarks.json`](benchmarks/results/latest_benchmarks.json) for full per-benchmark medians, IQRs, and p-values.

---

## Architecture (v0.4)

`lean-native` reuses Lean 4's frontend, elaborator, 3-phase `LCNF` pipeline (`Phase.base` → `Phase.mono` → `Phase.impure`), and C/FFI runtime while introducing a formally specified intermediate representation (`LNIR`) with verified optimization passes, enumerative superoptimization, and multi-target CPU/GPU backends:

1. **Zero-Redundancy Core & $O(N)$ LCNF Ingestion Bridge ([`LeanNative/Core.lean`](LeanNative/Core.lean), [`LeanNative/Driver/CoreCLI.lean`](LeanNative/Driver/CoreCLI.lean), [`LeanNative/IR/Codec.lean`](LeanNative/IR/Codec.lean), [`LeanNative/IR/Bridge.lean`](LeanNative/IR/Bridge.lean))**:
   - [`CoreCLI.lean`](LeanNative/Driver/CoreCLI.lean): Single shared CLI parser, subcommand dispatcher, and persistent JSON-RPC `worker` loop parameterized by an optional frontend elaboration hook (`FrontendHooks`), reducing [`CoreMain.lean`](LeanNative/Driver/CoreMain.lean) to 24 lines and [`Main.lean`](LeanNative/Driver/Main.lean) to 88 lines (~2,900 lines of duplicated code eliminated across the repository in v0.4).
   - [`Bridge.lean`](LeanNative/IR/Bridge.lean): Strictly linear $O(N)$ LCNF `.impure`/`.mono` lowering (erasing non-recursive join points on first splice to prevent $O(2^k)$ branching explosion) and `build-exe` compilation emitting `@lean_native_abi_*` C-ABI unboxing/boxing wrapper thunks.
2. **Formally Specified IR with Native 256-Bit EVM & Storage Maps ([`LeanNative/IR/Types.lean`](LeanNative/IR/Types.lean), [`LeanNative/IR/AST.lean`](LeanNative/IR/AST.lean))**:
   - Models unboxed scalars (`i1`, `i8`, `i16`, `i32`, `i64`, `usize`, `f32`, `f64`), **256-bit EVM words (`u256`, `i256` / `UInt256`)**, **persistent 256-bit key-value storage maps (`storageMap`)**, register-resident tuples (`tuple`), contiguous scalar buffers (`sarray`, `rawPtr`), checked 256-bit arithmetic (`addChecked256`, `subChecked256`, `mulChecked256`), 512-bit intermediate fixed-point scaling (`mulDivDown`, `mulDivUp`), `clz256`, `sar`, and `storageLoad` / `storageStore`.
3. **Unified Pass Proofs, Symbolic TV & 67 Machine-Checked Theorems ([`LeanNative/Semantics/`](LeanNative/Semantics/), [`LeanNative/Proofs/`](LeanNative/Proofs/))**:
   - [`PeepholeProofs.lean`](LeanNative/Proofs/PeepholeProofs.lean) & [`AlgebraicOpt.lean`](LeanNative/Transform/AlgebraicOpt.lean): Unified so the executed `AlgebraicOpt` pass directly invokes the kernel-verified `LeanNative.Proofs.rewriteScalarVerified` (`rewriteScalarPeephole` + `rewriteConstFoldBinOp`), backed by `evalBinOp_const_fold_sound` and `rewriteScalarVerified_sound`.
   - [`FastCheck.lean`](LeanNative/Backend/FastCheck.lean): Proves equality constraint-propagation soundness (`substScalarExpr_nil`, `substSingleConstraint_sound`, `propagatePrecondition_letBind_sound`) alongside `certifyCounterexample_no_false_positive`.
   - [`AxiomAudit.lean`](LeanNative/Proofs/AxiomAudit.lean): Compile-time (`#verify_lean_native_axioms`) and runtime (`lean-native audit-axioms`) in-kernel transitive axiom auditor verifying all **67 machine-checked kernel theorems** (`0 sorryAx`, `0 trustCompiler`, `0 native_decide`).
4. **Cost-Guided Enumerative Superoptimizer ([`LeanNative/Transform/Superopt.lean`](LeanNative/Transform/Superopt.lean))**:
   - Hardware-parameterized instruction cost models (`x86_64`, `arm64`, `cuda_ptx`, `apple_metal`) with enumerative algebraic/bitwise synthesis (distributive factoring `x*a + x*b -> x*(a+b)`, shift composition `(x <<< k1) <<< k2 -> x <<< (k1+k2)`, power-of-two division collapse `(x / d1) / d2 -> x >>> (k1+k2)`, FMA fusion) gated by two-stage verification (`fastCheckScalarEquiv` + `symCheckScalarEquiv`), cutting canonical scalar latency from **`54 -> 24` cycles** on `x86_64` and **`66 -> 22` cycles** on `apple_metal`.
5. **Unified GPU Kernel IR (`GPUIR.lean`), NVIDIA PTX 8.0 (`MLIRGPU.lean`) & Apple Metal MSL 3.0 (`Metal.lean`)**:
   - [`GPUIR.lean`](LeanNative/Backend/GPUIR.lean): Shared `GPUKernelDescriptor` & `GPUKernelArchetype` representation across CUDA PTX 8.0, MLIR (`gpu`/`nvvm`), and Apple Metal (MSL 3.0).
   - [`Metal.lean`](LeanNative/Backend/Metal.lean) & [`runtime/lean_native_metal.m`](runtime/lean_native_metal.m): Emits 18 Apple Metal MSL 3.0 compute kernels (`[[buffer(i)]]`, `[[thread_position_in_grid]]`, `threadgroup` shared-memory tree reduction & 16×16 tiled MatMul with `threadgroup_barrier(mem_flags::mem_threadgroup)`, 4-limb `ln_u256` carry-chain EVM arithmetic, and `lean_native_fastcheck_metal_kernel`), dispatched with zero-copy unified memory (`newBufferWithBytesNoCopy` / `MTLResourceStorageModeShared`) on Apple Silicon and validated via [`runtime/metal_compat_check.h`](runtime/metal_compat_check.h).
6. **Orthogonal Test Suite ([`tests/test_runner.lean`](tests/test_runner.lean)) & Curated Showcase Examples ([`examples/`](examples/))**:
   - [`tests/test_runner.lean`](tests/test_runner.lean): Non-redundant 6-family boundary & regression suite (`FNV1A_CHECKSUM64=0x6f66afdade214a0c`) covering 256-bit multi-limb carries, 512-bit `mulDivDown`/`mulDivUp` rounding, `sar` sign extension & `clz256`, EVM storage slot collisions, shared-array (`m_rc > 1`) COW preservation under `HoistExclusivity`, and multi-constructor tag dispatch.
   - Curated end-to-end examples: [`examples/verity_amm_vault.lean`](examples/verity_amm_vault.lean) (ERC-4626 Vault & AMM `u256` solvency + FastCheck counterexample detection), [`examples/saxpy_matmul_gpu.lean`](examples/saxpy_matmul_gpu.lean), and [`examples/persistent_tuple_tree.lean`](examples/persistent_tuple_tree.lean).
7. **Autonomous Multi-Agent Optimization Loop ([`autoresearch/`](autoresearch/))**:
   - Evaluates **30 optimization, superoptimization, Apple Metal & FastCheck hypotheses** (`21 ACCEPTED`, `9 REJECTED`) inside isolated git worktrees gated by 100k-state fuzzing, the 67-theorem axiom audit + `validate-tv`, and cross-architecture benchmarks, logging BLAKE3-chained receipts to [`autoresearch/ledger/experiments.jsonl`](autoresearch/ledger/experiments.jsonl) and [`autoresearch/RESEARCH_LOG.md`](autoresearch/RESEARCH_LOG.md).

---

## Quick Start & CLI Usage

### Build Both `lean-native-core` (`3.7 MB`, `2.45 ms` Cold Start) and `lean-native`
```bash
lake build lean-native-core lean-native
./.lake/build/bin/lean-native-core self-test
./.lake/build/bin/lean-native self-test
```

### Compile Orthogonal Tests & Showcase Examples to Native Executables
```bash
./.lake/build/bin/lean-native build-exe tests/test_runner.lean -o /tmp/test_runner && /tmp/test_runner
./.lake/build/bin/lean-native build-exe examples/verity_amm_vault.lean -o /tmp/verity_amm_vault && /tmp/verity_amm_vault
./.lake/build/bin/lean-native build-exe examples/saxpy_matmul_gpu.lean -o /tmp/saxpy_matmul_gpu && /tmp/saxpy_matmul_gpu
./.lake/build/bin/lean-native build-exe examples/persistent_tuple_tree.lean -o /tmp/persistent_tuple_tree && /tmp/persistent_tuple_tree
```

### Run Cost-Guided Superoptimizer & Emit Apple Metal MSL 3.0 / NVIDIA PTX 8.0 / FastCheck Kernels
```bash
./.lake/build/bin/lean-native-core superopt --arch x86_64
./.lake/build/bin/lean-native-core superopt --arch apple_metal
./.lake/build/bin/lean-native-core compile-metal -o /tmp/kernels.metal
./.lake/build/bin/lean-native-core compile-fastcheck --emit-metal -o /tmp/fastcheck.metal
./.lake/build/bin/lean-native-core compile-fastcheck --samples 1024
```

### Run Persistent Sub-Millisecond JSON-RPC Worker (`< 0.1 ms` / request)
```bash
printf '{"id":1,"method":"ping"}\n{"id":2,"method":"superopt","params":{"arch":"apple_metal"}}\n{"id":3,"method":"compile-metal"}\n{"id":4,"method":"shutdown"}\n' \
  | ./.lake/build/bin/lean-native-core worker
```

### Verify All 67 Formal Proofs, Symbolic TV, Certificates, and 30-Experiment Autoresearch Loop
```bash
./.lake/build/bin/lean-native audit-axioms
./.lake/build/bin/lean-native-core validate-tv
./.lake/build/bin/lean-native-core verify-certs
python3 autoresearch/loop.py --iterations 30
```
