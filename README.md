# Lean Native (`lean-native` v0.5)

**Lean Native (`lean-native`)** is a high-performance, formally validated, self-optimizing native compiler and counterexample engine for **Lean 4** (`leanprover/lean4:v4.35.0`) targeting **x86-64**, **ARM64**, **NVIDIA CUDA (MLIR / NVVM / PTX 8.0)**, and **Apple Metal (MSL 3.0)** with native **256-bit EVM/Verity (`u256`/`i256`/`StorageMap`)** support, achieving performance approaching or exceeding optimized Rust/C++ while preserving Lean's semantics through **153 machine-checked in-kernel proofs** (`0 sorryAx`, `64/64` tight specs in `LeanNative/Spec.lean` audited by `turbo-lean audit-spec`), a **pinned formal executable specification ([`LeanNative/Spec.lean`](LeanNative/Spec.lean))**, **segregated optimization plugins ([`LeanNative/Transform/Plugins.lean`](LeanNative/Transform/Plugins.lean))**, and **Season 8 `turbo-lean` integration**.

---

## Highlights & Real Hardware Results (v0.5)

### 1. Cross-Architecture Runtime Speedups (`spark-de79` ARM64+GB10 & `ashur` x86-64)
Across our workload suite (`collatz_steps`, `tuple_accum_sum`, `sarray_scale_bias`, `dot_product_u64`, `saxpy_kernel`, `matmul_tiled_u64`, plus 256-bit EVM/Verity kernels `evm_erc20_transfer_u256` and `evm_muldiv_wad_u256`) and immutable holdout tests (`holdout_bitwise`, `holdout_loop_bounds`), verified with **80/80 exact 64-bit deterministic checksum matches** (`7` trials per target, `p = 0.002165 < 0.05` via Mann-Whitney U):

| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `cpp_o3` | Peak RSS Reduction |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`spark-de79` (`aarch64` + `CUDA`)** | 20-core ARM Cortex-X925/A725 + NVIDIA GB10 Grace-Blackwell (`sm_121` / `sm_90` PTX) | **25.09x** | **1.22x** | **165.02x** | **8.01x** | **7.6x** (`263 MB` vs `2,004 MB`) |
| **`ashur` (`x86_64`)** | 8-thread Intel Core i7-7700 @ 3.60 GHz | **20.07x** | **1.29x** | **20.07x** | **1.29x** | **7.7x** (`264 MB` vs `2,022 MB`) |

### 2. `lean-native-core` (`libleanrt`-Only) Cold-Start & Persistent JSON-RPC Worker Latency
By decoupling [`LeanNative/Core.lean`](LeanNative/Core.lean) (25 compiler, spec, semantics, proof, transform, plugin, superoptimizer, GPU IR, backend, and adapter modules with **zero `import Lean`**) and unifying CLI/worker dispatch in [`LeanNative/Driver/CoreCLI.lean`](LeanNative/Driver/CoreCLI.lean), `lean-native-core` links solely against `libleanrt.a` and standard C libraries (eliminating the ~230 MB `libleanshared.so` dependency):

| Metric | `lean-native` (Full Frontend + `libleanshared.so`) | `lean-native-core` (`libleanrt.a` Only, `spark-de79` ARM64) | `lean-native-core` (`libleanrt.a` Only, `ashur` x86-64) | Improvement |
| :--- | :---: | :---: | :---: | :---: |
| **Binary Size (Stripped / Unstripped)** | `238 MB` | **`3.7 MB`** (`6.2 MB` unstripped) | **`3.7 MB`** (`5.6 MB` unstripped) | **64.3x smaller** |
| **Cold-Start CLI Latency (`--help`)** | `29.34 ms` | **`2.45 ms`** | **`9.08 ms`** | **12.0x faster** |
| **Cold-Start 8-Kernel `compile-llvm`** | `36.40 ms` | **`5.99 ms`** | **`25.89 ms`** | **6.1x faster** |
| **Persistent `worker` JSON-RPC Latency** | `0.075 ms / req` | **`0.0716 ms / req` (`13,973 req/s`)** | **`0.2154 ms / req` (`4,643 req/s`)** | **409x faster than cold CLI** |

See [`benchmarks/BENCHMARK_REPORT.md`](benchmarks/BENCHMARK_REPORT.md) and [`benchmarks/results/latest_benchmarks.json`](benchmarks/results/latest_benchmarks.json) for full per-benchmark medians, IQRs, and p-values.

---

## Architecture (v0.5)

`lean-native` v0.5 adopts the **"Pinned Formal Spec vs. Segregated Optimization Plugin"** architecture of [`Th0rgal/turbo-lean`](https://github.com/Th0rgal/turbo-lean) (Season 8) so any contributor PR or automated optimization pass can aggressively optimize compiler passes without ever risking soundness regressions:

1. **Pinned Formal Executable Specification ([`LeanNative/Spec.lean`](LeanNative/Spec.lean)) — 64 Tight Audited Specs & 153 In-Kernel Audited Proofs**:
   - Zero `import Lean`, zero `sorryAx`, audited in `0.14 ms` as **64/64 non-vacuous and tight** by `turbo-lean audit-spec LeanNative/Spec.lean`:
     - **Law 1 (Untrusted Optimization Plugin Soundness)**: `untrusted_opt_plugin_tv_gate_sound`, `untrusted_opt_plugin_code_refines`, `untrusted_opt_plugin_timeout_fallback`, `untrusted_opt_plugin_reject_fallback`.
     - **Law 2 (Optimization Pipeline Composition)**: `opt_pipeline_two_step_refines`, `opt_pipeline_chain_refines`.
     - **Law 3 (Non-Vacuous FastCheck & Tightness)**: `fastcheck_rejects_vacuous_precondition`, `fastcheck_non_vacuous_tightness_law`.
     - **Law 4 (C-ABI Scalar Tagging Round-Trip)**: `c_abi_box_zero_eq_one`, `c_abi_unbox_box_zero`, `c_abi_unbox_box_one`.
     - **Law 5 (PR Spec-Pinning & Anti-Tampering Gate)**: `pr_spec_pinning_blocks_spec_tampering`, `pr_spec_pinning_blocks_test_tampering`, `pr_spec_pinning_blocks_forbidden_axioms`, `pr_spec_pinning_gate_sound`.
2. **Segregated Optimization Plugins ([`LeanNative/Transform/Plugins.lean`](LeanNative/Transform/Plugins.lean), [`.lean-native/plugins.json`](.lean-native/plugins.json))**:
   - Wraps all built-in passes (`builtin:algebraic-peephole`, `builtin:unbox-tuple-sroa`, `builtin:hoist-exclusivity`, `builtin:loop-vectorize`, `builtin:enumerative-superopt`) and external out-of-process JSONL-stdio plugins inside `LeanNative.Spec.evalWithUntrustedOptPlugin` (`verifyOptPluginGate`: Alive2 `SymbolicTV` + 64-state concrete `evalCode` + cycle cost non-regression).
   - Includes a built-in adversarial test plugin (`adversarial:unsound-alu-corruptor`) verified on every `self-test` and CI run to prove that unsound rewrites are deterministically rejected (`rejected=3, adversarialRejected=true`).
3. **Season 8 `turbo-lean` Integration ([`LeanNative/TurboLean/Adapter.lean`](LeanNative/TurboLean/Adapter.lean), [`.turbo-lean/accelerators.json`](.turbo-lean/accelerators.json))**:
   - Exposes `lean-native-core turbo-plugin` speaking `turbo-lean`'s `ExternalProcessAccelerator` JSONL-stdio protocol (`counterexample_found` / `rewritten_proof` certificates in `< 1 ms`).
   - Integrates `turbo-lean pr-verify --mode untrusted`, `turbo-lean audit-spec`, and `turbo-lean agent-step` into `lean-native pr-verify`.
4. **Automated 5-Gate CI & Contributor PR Verification ([`.github/workflows/ci.yml`](.github/workflows/ci.yml), [`scripts/ci_verify.sh`](scripts/ci_verify.sh))**:
   - Automatically verifies: (1) Spec & Test Suite Pinning (`--disallow-spec-changes` on PRs) + `turbo-lean audit-spec`, (2) 153-Theorem In-Kernel Transitive Axiom Audit (`0 sorryAx`), (3) Segregated Optimization Plugins & Adversarial Rejection Gate, (4) Multi-Backend Codegen (`opt -O3`, Apple Metal MSL 3.0, NVIDIA PTX 8.0 `ptxas`), and (5) Orthogonal Native Executable Test Suite (`tests/test_runner.lean`), Matryoshka TRM C-Runtime Parity (`lean_native_trm_matryoshka_parity_selftest`), & Showcase Examples (`examples/*.lean`).
5. **Unified GPU Kernel IR (`GPUIR.lean`), NVIDIA PTX 8.0 (`MLIRGPU.lean`), Apple Metal MSL 3.0 (`Metal.lean`) & 256-Bit EVM Support**:
   - Shared `GPUKernelDescriptor` across CUDA PTX 8.0, MLIR, and Apple Metal 3.0 (`18` kernels including `threadgroup` shared-memory reduction, 16×16 tiled MatMul, 4-limb `ln_u256` EVM batch arithmetic, and parallel FastCheck fuzzing).
6. **Autonomous Multi-Agent Optimization Loop ([`autoresearch/`](autoresearch/))**:
   - Evaluates **36 optimization, superoptimization, plugin-segregation, spec-pinning, Apple Metal & FastCheck hypotheses** (`24 ACCEPTED`, `12 REJECTED`) inside isolated git worktrees, plus continuous overnight multi-architecture sweeps (`--until`), logging BLAKE3-chained receipts to [`autoresearch/ledger/experiments.jsonl`](autoresearch/ledger/experiments.jsonl) and [`autoresearch/RESEARCH_LOG.md`](autoresearch/RESEARCH_LOG.md).

---

## Quick Start & CLI Usage

### Build & Run Full 5-Gate Automated CI Verification Suite
```bash
lake build lean-native-core lean-native
./scripts/ci_verify.sh HEAD
```

### Run PR Spec-Pinning & Segregated Optimization Plugin Gate
```bash
./.lake/build/bin/lean-native pr-verify --base HEAD
./.lake/build/bin/lean-native-core plugins --test-adversarial
echo '{"decl_name":"evm_constrained_buggy_prop","stmt_src":"x0 < 1000000","body_src":"by simp","budget_ms":50}' \
  | ./.lake/build/bin/lean-native-core turbo-plugin
```

### Compile Orthogonal Tests & Showcase Examples to Native Executables
```bash
./.lake/build/bin/lean-native build-exe tests/test_runner.lean -o /tmp/test_runner && /tmp/test_runner
./.lake/build/bin/lean-native build-exe examples/verity_amm_vault.lean -o /tmp/verity_amm_vault && /tmp/verity_amm_vault
./.lake/build/bin/lean-native build-exe examples/saxpy_matmul_gpu.lean -o /tmp/saxpy_matmul_gpu && /tmp/saxpy_matmul_gpu
./.lake/build/bin/lean-native build-exe examples/persistent_tuple_tree.lean -o /tmp/persistent_tuple_tree && /tmp/persistent_tuple_tree
```

### Verify All 153 Formal Proofs, Symbolic TV, Certificates, and 36-Experiment Autoresearch Loop
```bash
./.lake/build/bin/lean-native audit-axioms
./.lake/build/bin/lean-native-core validate-tv
./.lake/build/bin/lean-native-core verify-certs
python3 autoresearch/loop.py --iterations 36
```
