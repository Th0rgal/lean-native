# Lean Native (`lean-native`)

**Lean Native (`lean-native`)** is a high-performance, formally validated, self-optimizing native compiler for **Lean 4** (`leanprover/lean4:v4.31.0`) targeting **x86-64**, **ARM64**, and **NVIDIA CUDA (MLIR / NVVM / PTX)** with performance approaching or exceeding optimized Rust/C++, while preserving Lean's semantics through machine-checkable kernel proofs and translation-validation certificates.

---

## Highlights & Real Hardware Results

Across our 6-benchmark workload suite (`collatz_steps`, `tuple_accum_sum`, `sarray_scale_bias`, `dot_product_u64`, `saxpy_kernel`, `matmul_tiled_u64`) and 2 immutable holdout tests (`holdout_bitwise`, `holdout_loop_bounds`), verified with **80/80 exact 64-bit deterministic checksum matches** (`7` trials per target, `p = 0.002165 < 0.05` via Mann-Whitney U):

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `cpp_o3` | Peak RSS Reduction |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64` + `CUDA`)** | 20-core ARM Cortex-X925/A725 + NVIDIA GB10 Grace-Blackwell (`sm_121` / `sm_90` PTX) | **25.09x** | **1.22x** | **165.02x** | **8.01x** | **7.6x** (`263 MB` vs `2,004 MB`) |
| **`ashur` (`x86_64`)** | 8-thread Intel Core i7-7700 @ 3.60 GHz | **20.07x** | **1.29x** | **20.07x** | **1.29x** | **7.7x** (`264 MB` vs `2,022 MB`) |

See [`benchmarks/BENCHMARK_REPORT.md`](benchmarks/BENCHMARK_REPORT.md) and [`benchmarks/results/latest_benchmarks.json`](benchmarks/results/latest_benchmarks.json) for full per-benchmark medians, IQRs, and p-values.

---

## Architecture

`lean-native` reuses Lean 4's frontend, elaborator, 3-phase `LCNF` pipeline (`Phase.base` → `Phase.mono` → `Phase.impure`), and C/FFI runtime while introducing a formally specified intermediate representation (`LNIR`) with verified optimization passes and multi-target backends:

1. **LCNF Ingestion Bridge ([`LeanNative/IR/Bridge.lean`](LeanNative/IR/Bridge.lean))**:
   - Ingests `LCNF.Decl .pure` (`Phase.mono`, before container type erasure) and `LCNF.Decl .impure` (`Phase.impure`, after `InferBorrow`, `ResetReuse`, and `ExplicitRC`).
   - Classifies `@[extern]` C/Rust FFI functions explicitly as `AssuranceLevel.unverifiedFallback`.
2. **Formally Specified Intermediate Representation ([`LeanNative/IR/Types.lean`](LeanNative/IR/Types.lean), [`LeanNative/IR/AST.lean`](LeanNative/IR/AST.lean))**:
   - Models unboxed scalars (`i1`, `i8`, `i16`, `i32`, `i64`, `usize`, `f32`, `f64`), register-resident tuples (`tuple`), contiguous scalar buffers (`sarray`, `rawPtr`), heap pointers (`objPtr`, `taggedPtr`), structured counted loops (`seqFor`), and data-parallel kernels (`parFor`).
3. **Formal Semantics & Machine-Checked Proofs ([`LeanNative/Semantics/`](LeanNative/Semantics/), [`LeanNative/Proofs/`](LeanNative/Proofs/))**:
   - [`Value.lean`](LeanNative/Semantics/Value.lean), [`Eval.lean`](LeanNative/Semantics/Eval.lean), [`Refinement.lean`](LeanNative/Semantics/Refinement.lean): Total operational/denotational semantics over `Val`, `VarEnv`, and `HeapState` with explicit Undefined Behavior (`UBError`) vs defined value refinement (`ScalarExprEquiv`, `ExprRefines`, `CodeRefines`).
   - [`PeepholeProofs.lean`](LeanNative/Proofs/PeepholeProofs.lean) & [`LoopOptProofs.lean`](LeanNative/Proofs/LoopOptProofs.lean): **21 machine-checked soundness theorems** proving semantic preservation for strength reduction, algebraic/bitwise identities, tuple unboxing (SROA), exclusive scalar array base-pointer hoisting (`sarrayEnsureExclusive`), and unboxed loop accumulators.
   - [`AxiomAudit.lean`](LeanNative/Proofs/AxiomAudit.lean): Compile-time (`#verify_lean_native_axioms`) and runtime (`lean-native audit-axioms`) in-kernel transitive axiom auditor (`Lean.collectAxioms`) enforcing that all proofs depend strictly on `{propext, Quot.sound, Classical.choice}` (`0 sorryAx`, `0 trustCompiler`, `0 native_decide`).
   - [`CertChecker.lean`](LeanNative/Proofs/CertChecker.lean): Independent hash-chain and theorem-registry certificate verifier (`lean-native verify-certs`).
4. **Verified Optimization Passes ([`LeanNative/Transform/`](LeanNative/Transform/))**:
   - [`AlgebraicOpt.lean`](LeanNative/Transform/AlgebraicOpt.lean): Power-of-two strength reduction, identity/idempotence folding, constant propagation, and branch simplification.
   - [`UnboxTupleSROA.lean`](LeanNative/Transform/UnboxTupleSROA.lean): Scalar Replacement of Aggregates (SROA) eliminating intermediate heap constructor / tuple allocations across let-bindings and tail-recursive join points (**38.3x–64.0x** speedup on `tuple_accum_sum`).
   - [`HoistExclusivity.lean`](LeanNative/Transform/HoistExclusivity.lean): Hoists `lean_sarray_ensure_exclusive` (`m_rc == 1` COW check) and `m_data` pointer resolution out of non-escaping loops, converting opaque per-element `uset` calls into direct `noalias` pointer stores (**66.6x–226.1x** CPU speedup on `sarray_scale_bias`).
   - [`LoopVectorizeOpt.lean`](LeanNative/Transform/LoopVectorizeOpt.lean): FMA contraction, redundant borrow RC pair elimination, and SIMD vectorization promotion (`AVX2` on `x86-64`, `NEON` on `ARM64`).
5. **CPU, GPU, and Hybrid Backends ([`LeanNative/Backend/`](LeanNative/Backend/), [`runtime/`](runtime/))**:
   - [`LLVM.lean`](LeanNative/Backend/LLVM.lean): Emits modern LLVM 18 opaque-pointer IR (`ptr`) for `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu` with `@llvm.expect.i1` single-threaded RC fast-paths, `noalias` attributes, and `!llvm.loop.vectorize.enable`.
   - [`MLIRGPU.lean`](LeanNative/Backend/MLIRGPU.lean): Static GPU eligibility analyzer, MLIR (`gpu`/`scf`/`arith`/`memref`/`nvvm` dialect) emitter, and direct **NVIDIA PTX 8.0 (`.version 8.0`, `.target sm_90`)** emitter verified with `ptxas`.
   - [`Hybrid.lean`](LeanNative/Backend/Hybrid.lean) & [`runtime/`](runtime/): Automatic CPU/GPU partitioner, transfer scheduler (`unifiedMemoryZeroCopy` on Grace-Blackwell GB10 / `pinnedAsyncHostToDevice`), adaptive cost-model dispatcher (`N >= 65536`), and seamless CPU fallback.
6. **Turbo Lean Integration ([`LeanNative/TurboLean/Adapter.lean`](LeanNative/TurboLean/Adapter.lean), [`scripts/turbo_lean_bridge.py`](scripts/turbo_lean_bridge.py))**:
   - Capability-probed, zero-hard-dependency integration with [`Th0rgal/turbo-lean`](https://github.com/Th0rgal/turbo-lean) supporting `theorem-shard-v1:` BLAKE3 shard keys, warm `ZygoteWorker` `/check-shard` verification, sub-4ms 100,000-state counterexample rejection (`--fast-check-rewrite`), and `turbo-lean-verification-receipt-v1` cryptographic receipts.
7. **Autonomous Multi-Agent Optimization Loop ([`autoresearch/`](autoresearch/))**:
   - [`evaluator.py`](autoresearch/evaluator.py) & [`loop.py`](autoresearch/loop.py): 3-stage independent acceptance gate (Stage 1: 100k-state counterexample fuzzing; Stage 2: Lean kernel proof & `sorryAx`-free axiom audit; Stage 3: cross-architecture `ARM64`+`GPU` and `x86-64` benchmark & holdout regression gate) logging BLAKE3-chained experiment records to [`autoresearch/ledger/experiments.jsonl`](autoresearch/ledger/experiments.jsonl) and [`autoresearch/RESEARCH_LOG.md`](autoresearch/RESEARCH_LOG.md).

---

## Quick Start & CLI Usage

### Build & Run End-to-End Self-Test
```bash
lake build
./.lake/build/bin/lean-native self-test
```

### Verify Formal Proofs, Transitive Axioms, and Translation Certificates
```bash
./.lake/build/bin/lean-native audit-axioms
./.lake/build/bin/lean-native verify-certs -o /tmp/certs.json
./.lake/build/bin/lean-native turbo-status
```

### Compile to LLVM 18 IR (`x86_64` & `ARM64`), MLIR, NVIDIA PTX 8.0, and Hybrid C/CUDA Glue
```bash
./.lake/build/bin/lean-native compile-llvm --arch x86_64 -o /tmp/module_x86_64.ll
./.lake/build/bin/lean-native compile-llvm --arch arm64  -o /tmp/module_arm64.ll
./.lake/build/bin/lean-native compile-mlir -o /tmp/module_gpu.mlir
./.lake/build/bin/lean-native compile-ptx --sm sm_90 -o /tmp/module_gpu.ptx
./.lake/build/bin/lean-native compile-hybrid -o /tmp/module_hybrid_glue.c
```

### Run Cross-Architecture Benchmarks & Autonomous Optimization Loop
```bash
python3 benchmarks/run_benchmarks.py
python3 autoresearch/evaluator.py --self-test
python3 autoresearch/loop.py
```

---

## Documentation

- [`docs/AUDIT_REPORT.md`](docs/AUDIT_REPORT.md) — Technical audit of `leanprover/lean4` (`v4.31.0` LCNF/IR/runtime), `Th0rgal/turbo-lean`, `opencompl/lean-mlir`, Alive2, and Vellvm.
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — `LNIR` intermediate representation, verified passes, LLVM/MLIR/PTX backends, and hybrid runtime architecture.
- [`docs/TRUST_BOUNDARIES.md`](docs/TRUST_BOUNDARIES.md) — Formal assurance levels (`VerifiedKernelProof`, `TranslationValidated`, `UnverifiedFallback`) and explicit TCB boundaries.
- [`benchmarks/BENCHMARK_REPORT.md`](benchmarks/BENCHMARK_REPORT.md) — Reproducible cross-architecture (`x86-64`, `ARM64`, `NVIDIA GB10 CUDA/PTX`) benchmark report.
- [`autoresearch/RESEARCH_LOG.md`](autoresearch/RESEARCH_LOG.md) — Autonomous optimization loop log (accepted optimizations, rejected unsound/regressing hypotheses, counterexamples, and BLAKE3 receipts).
