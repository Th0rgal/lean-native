# Lean Native (`lean-native` v0.3)

**Lean Native (`lean-native`)** is a high-performance, formally validated, self-optimizing native compiler and counterexample engine for **Lean 4** (`leanprover/lean4:v4.31.0`) targeting **x86-64**, **ARM64**, and **NVIDIA CUDA (MLIR / NVVM / PTX 8.0)** with native **256-bit EVM/Verity (`u256`/`i256`/`StorageMap`)** support, achieving performance approaching or exceeding optimized Rust/C++ while preserving Lean's semantics through **61 machine-checked kernel proofs** (`0 sorryAx`) and Alive2-style symbolic translation validation.

---

## Highlights & Real Hardware Results (v0.3)

### 1. Cross-Architecture Runtime Speedups (`spark-de79` ARM64+GB10 & `ashur` x86-64)
Across our workload suite (`collatz_steps`, `tuple_accum_sum`, `sarray_scale_bias`, `dot_product_u64`, `saxpy_kernel`, `matmul_tiled_u64`, plus 256-bit EVM/Verity kernels `evm_erc20_transfer_u256` and `evm_muldiv_wad_u256`) and immutable holdout tests (`holdout_bitwise`, `holdout_loop_bounds`), verified with **80/80 exact 64-bit deterministic checksum matches** (`7` trials per target, `p = 0.002165 < 0.05` via Mann-Whitney U):

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `cpp_o3` | Peak RSS Reduction |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64` + `CUDA`)** | 20-core ARM Cortex-X925/A725 + NVIDIA GB10 Grace-Blackwell (`sm_121` / `sm_90` PTX) | **25.09x** | **1.22x** | **165.02x** | **8.01x** | **7.6x** (`263 MB` vs `2,004 MB`) |
| **`ashur` (`x86_64`)** | 8-thread Intel Core i7-7700 @ 3.60 GHz | **20.07x** | **1.29x** | **20.07x** | **1.29x** | **7.7x** (`264 MB` vs `2,022 MB`) |

### 2. `lean-native-core` (`libleanrt`-Only) Cold-Start & Persistent JSON-RPC Worker Latency
By decoupling [`LeanNative/Core.lean`](LeanNative/Core.lean) (20 compiler, semantics, proof, transform, backend, and adapter modules with **zero `import Lean`**) from the Lean frontend, `lean-native-core` links solely against `libleanrt.a` and standard C libraries (eliminating the ~230 MB `libleanshared.so` dependency):

| Metric | `lean-native` (Full Frontend + `libleanshared.so`) | `lean-native-core` (`libleanrt.a` Only, `spark-de79` ARM64) | `lean-native-core` (`libleanrt.a` Only, `ashur` x86-64) | Improvement |
| :--- | :---: | :---: | :---: | :---: |
| **Binary Size (Stripped / Unstripped)** | `238 MB` | **`3.7 MB`** (`6.2 MB` unstripped) | **`3.7 MB`** (`5.6 MB` unstripped) | **64.3x smaller** |
| **Cold-Start CLI Latency (`--help`)** | `29.34 ms` | **`2.45 ms`** | **`9.08 ms`** | **12.0x faster** |
| **Cold-Start 8-Kernel `compile-llvm`** | `36.40 ms` | **`5.99 ms`** | **`25.89 ms`** | **6.1x faster** |
| **Persistent `worker` JSON-RPC Latency** | `0.075 ms / req` | **`0.0716 ms / req` (`13,973 req/s`)** | **`0.2154 ms / req` (`4,643 req/s`)** | **409x faster than cold CLI** |

See [`benchmarks/BENCHMARK_REPORT.md`](benchmarks/BENCHMARK_REPORT.md) and [`benchmarks/results/latest_benchmarks.json`](benchmarks/results/latest_benchmarks.json) for full per-benchmark medians, IQRs, and p-values.

---

## Architecture (v0.3)

`lean-native` reuses Lean 4's frontend, elaborator, 3-phase `LCNF` pipeline (`Phase.base` → `Phase.mono` → `Phase.impure`), and C/FFI runtime while introducing a formally specified intermediate representation (`LNIR`) with verified optimization passes and multi-target backends:

1. **Decoupled Core & LCNF Ingestion Bridge ([`LeanNative/Core.lean`](LeanNative/Core.lean), [`LeanNative/IR/Codec.lean`](LeanNative/IR/Codec.lean), [`LeanNative/IR/Bridge.lean`](LeanNative/IR/Bridge.lean))**:
   - [`Codec.lean`](LeanNative/IR/Codec.lean): Lossless `LNIR_WIRE_V1` wire and JSON serialization/deserialization (`LNIRModule.toWire`, `LNIRModule.fromWire?`, `LNIRModule.toJson`, `LNIRModule.fromJson?`) plus 8 canonical kernels (`collatz_steps`, `tuple_accum_sum`, `sarray_scale_bias`, `dot_product_u64`, `saxpy_kernel`, `matmul_tiled_u64`, `evm_erc20_transfer_u256`, `evm_muldiv_wad_u256`).
   - [`Bridge.lean`](LeanNative/IR/Bridge.lean): Lowers `LCNF .impure` & `.mono` declarations (multi-branch `cases` → `switch`, multi-parameter tail-recursive `.jp`/`.jmp` → `seqFor` loops, intra-module helper calls preserving `VerifiedKernelProof`, and standalone native executable compilation via `lean-native build-exe <file.lean> -o <bin>`). Fails explicitly with non-zero status if `--input <file.lean>` yields 0 declarations.
2. **Formally Specified IR with Native 256-Bit EVM & Storage Maps ([`LeanNative/IR/Types.lean`](LeanNative/IR/Types.lean), [`LeanNative/IR/AST.lean`](LeanNative/IR/AST.lean))**:
   - Models unboxed scalars (`i1`, `i8`, `i16`, `i32`, `i64`, `usize`, `f32`, `f64`), **256-bit EVM words (`u256`, `i256` / `UInt256`)**, **persistent 256-bit key-value storage maps (`storageMap`)**, register-resident tuples (`tuple`), contiguous scalar buffers (`sarray`, `rawPtr`), checked 256-bit arithmetic (`addChecked256`, `subChecked256`, `mulChecked256`), 512-bit intermediate fixed-point scaling (`mulDivDown`, `mulDivUp`), `clz256`, `sar`, and `storageLoad` / `storageStore`.
3. **Formal Semantics, Symbolic TV & 61 Machine-Checked Proofs ([`LeanNative/Semantics/`](LeanNative/Semantics/), [`LeanNative/Proofs/`](LeanNative/Proofs/))**:
   - [`Value.lean`](LeanNative/Semantics/Value.lean), [`Eval.lean`](LeanNative/Semantics/Eval.lean), [`Refinement.lean`](LeanNative/Semantics/Refinement.lean): Total operational/denotational semantics over `Val` (including `.u256` and `.storageMapId`), `VarEnv`, and `HeapState` (`StorageMapBuffer` with `lookupSlot_writeSlot_same` and `lookupSlot_writeSlot_ne`).
   - [`PeepholeProofs.lean`](LeanNative/Proofs/PeepholeProofs.lean), [`LoopOptProofs.lean`](LeanNative/Proofs/LoopOptProofs.lean), [`SymbolicTV.lean`](LeanNative/Proofs/SymbolicTV.lean), [`FastCheck.lean`](LeanNative/Backend/FastCheck.lean): **61 machine-checked kernel theorems** proving end-to-end recursive `CodeRefines` pass soundness (`rewriteCodePeephole_refines`, `unboxTupleLetChain_refines`, `hoistExclusivityPreheader_refines`), 256-bit & EVM storage store-to-load forwarding (`storageStore_load_same_sound`, `storageStore_load_ne_sound`), Alive2-style symbolic translation validation (`validate-tv`), and zero-false-positive counterexample certification (`certifyCounterexample_no_false_positive`).
   - [`AxiomAudit.lean`](LeanNative/Proofs/AxiomAudit.lean): Compile-time (`#verify_lean_native_axioms`) and runtime (`lean-native audit-axioms`) in-kernel transitive axiom auditor enforcing `{propext, Quot.sound, Classical.choice}` only (`0 sorryAx`, `0 trustCompiler`, `0 native_decide`).
4. **Constraint-Propagating Fuzzing Kernel Generator ([`LeanNative/Backend/FastCheck.lean`](LeanNative/Backend/FastCheck.lean))**:
   - Eliminates `VacuousPass` failure modes on equality-constrained preconditions (`x_i == expr`) by propagating `x_i := expr` directly into the generator (`propagatePreconditionEqualities`).
   - Combines deterministic 64-bit & 256-bit boundary value tables ($0, 1, 2, 2^{64}-1, 2^{128}-1, 2^{255}, 2^{256}-1$, WAD $10^{18}$), pairwise parameter collision sampling ($x_i = x_j$), and parallel SplitMix64 streams.
   - Emits vectorized LLVM 18 CPU SIMD (`@lean_native_fastcheck_simd`) and NVIDIA PTX 8.0 (`lean_native_fastcheck_kernel`) harnesses tracking `satisfied_preconditions_count`, and certifies every counterexample via `LeanNative.Semantics.Eval.evalCode`.
5. **CPU (`i256`/`i512`), GPU (PTX 8.0 Carry-Chain & `.shared` Tiled), and Hybrid Backends ([`LeanNative/Backend/`](LeanNative/Backend/), [`runtime/`](runtime/))**:
   - [`LLVM.lean`](LeanNative/Backend/LLVM.lean): Emits LLVM 18 IR for `x86_64` and `ARM64` with native `i256` arithmetic, `@llvm.uadd/usub/umul.with.overflow.i256`, `@llvm.ctlz.i256`, `i512` `mulDivDown`/`mulDivUp`, multi-way `switch i64`, and `@lean_native_evm_sload`/`@lean_native_evm_sstore`.
   - [`MLIRGPU.lean`](LeanNative/Backend/MLIRGPU.lean): Synthesizes 15 **NVIDIA PTX 8.0 (`sm_90`)** kernels including 4-limb `.reg .u64` 256-bit hardware carry-chain arithmetic (`add.cc.u64`/`addc.cc.u64`, `sub.cc.u64`/`subc.u64`, `mad.lo.cc.u64`), `.shared` tree reduction (`dot_reduce_u64`), 2D 16×16 `.shared` tiled matrix multiplication (`matmul_tiled_u64`), and IEEE-754 `f64`/`f32` kernels — loaded dynamically via `cuModuleLoadDataEx` and `cuLaunchKernel` in [`runtime/lean_native_cuda.cu`](runtime/lean_native_cuda.cu).
6. **Zero-Python Native BLAKE3 & Turbo Lean Adapter ([`LeanNative/TurboLean/Adapter.lean`](LeanNative/TurboLean/Adapter.lean))**:
   - Pure-Lean RFC-compliant **BLAKE3** implementation (`blake3Hex`, `blake3Bytes`, verified against official test vectors) and native sub-4ms 64/256-bit counterexample search with zero `python3` subprocess dependencies.
7. **Autonomous Multi-Agent Optimization Loop ([`autoresearch/`](autoresearch/))**:
   - Evaluates **24 optimization & FastCheck hypotheses** inside isolated git worktrees (`git worktree add --detach`) gated by Stage 1 (100k-state fuzzing), Stage 2 (61-theorem axiom audit + `lean-native-core validate-tv`), and Stage 3 (`spark-de79` + `ashur` benchmarks), logging BLAKE3-chained receipts to [`autoresearch/ledger/experiments.jsonl`](autoresearch/ledger/experiments.jsonl) and [`autoresearch/RESEARCH_LOG.md`](autoresearch/RESEARCH_LOG.md).

---

## Quick Start & CLI Usage

### Build Both `lean-native-core` (`3.7 MB`, `2.45 ms` Cold Start) and `lean-native`
```bash
lake build lean-native-core lean-native
./.lake/build/bin/lean-native-core self-test
./.lake/build/bin/lean-native self-test
```

### Compile a `.lean` Program Directly to a Standalone Native Executable
```bash
./.lake/build/bin/lean-native build-exe tests/general_lean4_suite.lean -o /tmp/general_suite_native
/tmp/general_suite_native
```

### Run Constraint-Propagating FastCheck & Emit SIMD / PTX 8.0 Fuzzing Kernels
```bash
./.lake/build/bin/lean-native-core compile-fastcheck --samples 1024
./.lake/build/bin/lean-native-core compile-fastcheck --emit-llvm -o /tmp/fastcheck_simd.ll
./.lake/build/bin/lean-native-core compile-fastcheck --emit-ptx --sm sm_90 -o /tmp/fastcheck_gpu.ptx
```

### Run Persistent Sub-Millisecond JSON-RPC Worker (`< 0.1 ms` / request)
```bash
printf '{"id":1,"method":"ping"}\n{"id":2,"method":"eval-cex"}\n{"id":3,"method":"shutdown"}\n' \
  | ./.lake/build/bin/lean-native-core worker
```

### Verify Formal Proofs, Symbolic TV, Certificates, and Autonomous Research Loop
```bash
./.lake/build/bin/lean-native audit-axioms
./.lake/build/bin/lean-native-core validate-tv
./.lake/build/bin/lean-native-core verify-certs
python3 autoresearch/loop.py --iterations 24
```
