# Trust Boundaries and Formal Assurance Levels

## 1. Explicit Assurance Classification

Every declaration, optimization pass, and lowered artifact in `lean-native` is tagged with an explicit `AssuranceLevel` (`LeanNative.IR.Types.AssuranceLevel`):

| Level | Tag | Meaning | Verification Mechanism |
| :--- | :--- | :--- | :--- |
| **L3 (Highest)** | `VerifiedKernelProof` | Transformation is proved semantics-preserving for all inputs in the Lean 4 kernel (`Refines src tgt`). | Checked by Lean 4 kernel + `Lean.collectAxioms` audit (`propext`, `Quot.sound`, `Classical.choice` only; zero `sorryAx`, zero `trustCompiler`). |
| **L2** | `TranslationValidated` | Specific compilation instance is validated by an independent certificate checker / SMT / bounded symbolic evaluator (`CertChecker` / `fast-check`). | Checked by `lean-native verify-certs` and differential / counterexample execution before acceptance. |
| **L1 (Fallback)** | `UnverifiedFallback` | Uses external C/Rust FFI (`@[extern]`), runtime system calls (`IO`), or unverified fallback lowering (`EmitC` / `libleanshared`). | Explicitly recorded in compilation manifest and `VerificationReceipt`; isolated from L3/L2 claims. |

---

## 2. Trusted Computing Base (TCB) & Explicit Trust Boundaries

### Inside the Verified Boundary (Formally Specified & Checked)
1. **`LNIR` Operational & Denotational Semantics (`LeanNative.Semantics`)**:
   - Formal evaluation of scalar arithmetic (`UInt64`, `Int64`, `Bool`), tuple packing/unpacking (`mkTuple`, `projTuple`), exclusive array mutation (`sarrayEnsureExclusive`, `rawLoad`, `rawStore`), and structured loops (`seqFor`, `parFor`).
2. **Verified Optimization Passes (`LeanNative.Transform` + `LeanNative.Proofs`)**:
   - `AlgebraicOpt` (strength reduction, constant/identity folding, dead-branch elimination)
   - `UnboxTupleSROA` (scalar replacement of aggregates / tuple unboxing)
   - `HoistExclusivity` (loop-invariant array exclusivity & base-pointer hoisting)
   - `LoopVectorizeOpt` (unboxed induction variable & accumulator equivalence)
3. **In-Kernel Axiom Gate (`LeanNative.Proofs.AxiomAudit`)**:
   - Enforces at both build time and runtime (`lean-native audit-axioms`) that every soundness theorem in `LeanNative.Proofs` has zero dependency on `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or `Lean.trustCompiler`.

### Explicit Trust Boundaries (Below LLVM IR / PTX)
1. **Lean 4 Frontend & Kernel (`leanprover/lean4:v4.31.0`)**:
   - Elaboration and initial `ToLCNF` lowering are trusted to match Lean 4's kernel semantics.
2. **Backend Machine-Code Generation (`LLVM 18` & `NVIDIA ptxas / CUDA Driver`)**:
   - Semantic preservation is targeted down to `LNIR` and emitted LLVM IR / PTX structure. Subsequent lowering from LLVM IR to `x86_64` / `aarch64` machine code (`opt` / `llc` / `clang`) and from PTX to NVIDIA SASS (`ptxas`) is treated as an **explicitly documented trust boundary**, mitigated empirically by cross-architecture differential testing (`x86-64` vs `ARM64` vs `CUDA` vs official Lean interpreter/compiler).
3. **Runtime Memory & FFI Boundary (`libleanshared.so` & `lean_native_runtime.c`)**:
   - Custom `@[extern]` C/Rust functions and OS I/O calls are automatically classified as `AssuranceLevel.UnverifiedFallback`.
