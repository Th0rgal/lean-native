# AGENTS.md — Architectural Charter (`lean-native` ⟷ `turbo-lean`)

## 1. Symbiosis & Architectural Roles

`lean-native` and `turbo-lean` form a co-designed native compilation, hardware fast-check, and incremental verification stack for Lean 4:

- **`lean-native` (Verified Native Codegen, Translation Validation & Hardware Fast-Check)**:
  Lowers Lean/LNIR into verified zero-boxing C-ABI SIMD (`--c-abi`), LLVM IR, NVIDIA CUDA PTX, Apple Metal MSL, and Cloud TPU XLA/StableHLO kernels (including 512-bit `mulDivDown`/`mulDivUp` and 256-bit bit-scan primitives). Certifies counterexamples (`0` false positives) and specification non-vacuity via executable operational semantics (`evalCode`) and Alive2-style symbolic translation validation (`CodeRefines`).
- **`turbo-lean` (Incremental Verification, Zygote Elaboration & Federated Orchestration)**:
  Partitions Lean modules into dependency cones and `have` sub-proof cuts, invokes `lean-native` as its Stage-1 counterexample and C-ABI fast-check engine, races tactic accelerators inside warm `ZygoteWorker` snapshots, and enforces an in-kernel soundness gate (`0 sorryAx`, `0 native_decide`, `0 trustCompiler`).
- **Shared Canonical 10-Term Glossary**: Follows the 10-term Certified Research glossary defined in `Th0rgal/maxwell` (`AGENTS.md` §2: *Certified Research*, *Raw Inference*, *`[Conjecture -> Specification -> Certification]`*, *Recursive Decomposition (`effort_p50 <= 6000`)*, *Zero-Trust Oracle*, *The Maxwell Gate*, *`MetaGateSpec` & `SpeculativeGate`*, *Verified Knowledge*, *Burned Paths*, *Self-Refining Loop*).

```
Lean / LNIR Source ──► Stage 1: Certified Fast-Check & Vacuity Audit (`lean-native` SIMD/GPU/TPU)
                   ──► Stage 2: Gated Optimization Pipeline (`SpeculativeGate` + `SymbolicTV`)
                   ──► Stage 3: Multi-Target Emission (C-ABI / LLVM / PTX / Metal / StableHLO)
                   ──► Stage 4: In-Kernel Axiom Audit & `turbo-lean` Replay (`AxiomAudit.lean`)
```

---

## 2. Six Non-Negotiable Engineering Rules

1. **Zero Model-Code Gap via Direct C-ABI (`@[export]` / `--c-abi`)**:
   Executable decision gates, cost models, and hardware placement rules live in `Spec.lean` and `Hybrid.lean` (zero compiler-frontend dependencies, linked against `libleanrt.a` only) and emit unboxed C-ABI primitives directly callable by `turbo-lean` and native runtimes without shadow re-implementations.

2. **Two-Layer Specification Compression (`Layer I` Meta-Specs vs. `Layer II` Corollaries ≤ 3 Lines)**:
   - **Layer I (Universal Meta-Specifications & Combinators)**: Structural reasoning is factored into reusable combinators (`MetaGateSpec`, `MetaAlgorithmSpec`, `SpeculativeGate`, `VerifiedTransformContract`, `ClockedStepBudget`).
   - **Layer II (Declarative Corollaries)**: Concrete pass, ABI, partitioner, and PR-gate properties are expressed as `MetaGateSpec` bundles or corollaries of **≤ 3 lines** instantiating Layer I.

3. **Hermetic Segregation of Formal Kernel vs. Untrusted Optimization Plugins behind `SpeculativeGate`**:
   All optimization plugins, superoptimizer rules, and hardware kernel emitters are untrusted proposals gated by `SpeculativeGate` (`evalWithUntrustedOptPlugin`) and verified by `SymbolicTV` / `CodeRefines` (`0 sorryAx`, `0 native_decide`), falling back transparently to the unoptimized IR on timeout or rejection.

4. **Mathlib4 Algebraic Proof Style**:
   Proofs in `Spec.lean` and `LeanNative/Proofs/` must use concise Mathlib4 algebraic idioms (`split <;> simp_all`, `simpa`, `omega`, `iff` equivalences, and structural combinators). Verbose `cases <;> cases` cascades and repetitive tactical boilerplate are forbidden.

5. **LOC Reduction Ratchet**:
   Every refactoring, bug fix, or feature addition must compress or factor existing code and specifications. New capabilities must generalize Layer I meta-theorems or shared backend passes rather than accreting ad-hoc lines of code.

6. **Doc & Context Ratchet (`--sync-docs`)**:
   Any commit that adds or modifies theorems in `LeanNative/Proofs/AxiomAudit.lean` (`<!-- inventory:leannative_audited_theorems -->195<!-- /inventory:leannative_audited_theorems -->/<!-- inventory:leannative_audited_theorems -->195<!-- /inventory:leannative_audited_theorems -->` audited theorems) or tight specs in `LeanNative/Spec.lean` (`<!-- inventory:leannative_spec_tight -->106<!-- /inventory:leannative_spec_tight -->/<!-- inventory:leannative_spec_tight -->106<!-- /inventory:leannative_spec_tight -->` tight specs) must keep `README.md`, `AGENTS.md`, and `scripts/ci_verify.sh` synchronized; `./scripts/ci_verify.sh --sync-docs` verifies that doc theorem/spec counters match the in-kernel audit.

7. **End-to-End Amdahl & Ablation Ratchet (`ΔE2E >= 1%` or Delete)**:
   - **No Micro-Benchmark-Only Optimizations**: No hardware backend, cascade tier, heuristic pass, or rewrite rule lands without a measured wall-clock speedup on the full end-to-end pipeline. Every optimization must state its stage fraction $f$ and stage speedup $s$ (`[f=..., s=... -> E2E=...]`).
   - **Transport-Aware Offload Gate**:
     - Synchronous offload is forbidden unless stage share $f \ge 10\%$ AND $\text{p95}(T_{\text{transport}} + T_{\text{serialize}} + T_{\text{device}} + T_{\text{recert}}) < 0.5 \cdot \text{p95}(T_{\text{CPU}})$.
     - Asynchronous ("Fire-and-Forget") offload must demonstrate a statistically significant $\ge 1\%$ reduction in end-to-end campaign time-to-certified-result (including host queue/interrupt overhead).
   - **Mandatory Ablation Flag & Pruning**: Every non-trivial optimization must be toggleable via env/flag. Any optimization, cascade tier, or superopt rule with $0$ hits on the canonical corpus or whose ablation degrades E2E geomean by $< 1\%$ (95% CI) must be deleted to enforce $\Delta\text{LOC} \le 0$.

---

## 3. Repository Layout & Verification Entrypoints

- **Formal Specifications**: [`LeanNative/Spec.lean`](LeanNative/Spec.lean) & [`TurboLean/Spec.lean`](../turbo-lean/lean/TurboLean/Spec.lean)
- **Operational Semantics & Proofs**: [`LeanNative/Semantics/`](LeanNative/Semantics/), [`LeanNative/Proofs/AxiomAudit.lean`](LeanNative/Proofs/AxiomAudit.lean)
- **Multi-Target Backends**: [`LeanNative/Backend/FastCheck.lean`](LeanNative/Backend/FastCheck.lean), [`LeanNative/Backend/Hybrid.lean`](LeanNative/Backend/Hybrid.lean), [`LeanNative/Backend/MLIRGPU.lean`](LeanNative/Backend/MLIRGPU.lean)
- **CI & Federated Worker Entrypoints**: [`scripts/ci_verify.sh`](scripts/ci_verify.sh), [`scripts/accelerator_worker.py`](scripts/accelerator_worker.py) (and compatibility wrapper [`scripts/colab_gpu_worker.py`](scripts/colab_gpu_worker.py))

---

## 4. Optimization Objectives & Resource Envelopes (`ObjectiveReceipt`)

Autonomous research on `lean-native` separates **Layer 1 (Formal Admissibility)** from **Layer 2 (Lexicographic Empirical Fitness)**:

1. **Layer 1 — Hard Formal Gate (`Spec.lean`, `G(x) = true`)**:
   - `untrusted_opt_plugin_tv_gate_sound` (`SymbolicTV` / `CodeRefines` + 64-state checksum equivalence), `opt_pipeline_chain_refines`, `0 sorryAx`, `0 vacuous` specs (`turbo-lean --json audit-spec LeanNative/Spec.lean`).
2. **Layer 2 — Lexicographic Objective (`J_native`)**:
   - **Primary**: Maximize compiled execution speedup geomean ($\text{Geomean}(\text{Speedup}_{\text{exec}})$, Mann-Whitney $p < 0.05$).
   - **Secondary**: Minimize compilation latency ($\text{ms}$) and emitted binary/kernel footprint.
   - **Resource Envelope**: `spills == 0`, `registers <= profile.max_regs`, `cache_trm_tier <= max_footprint_bytes`, `ΔLOC <= 0`.
