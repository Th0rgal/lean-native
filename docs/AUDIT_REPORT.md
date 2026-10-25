# Technical Audit Report: Lean 4 Compiler Internals, Turbo Lean, and Formal Verification Ecosystem

## 1. Executive Summary

Before designing `lean-native`, we audited:
1. **`leanprover/lean4` (`v4.31.0`)**: The unified 3-phase `LCNF` compiler pipeline (`Phase.base` → `Phase.mono` → `Phase.impure`), the production C backend (`src/Lean/Compiler/LCNF/EmitC.lean`), the legacy/unmaintained LLVM backend (`src/Lean/Compiler/IR/EmitLLVM.lean`), and the runtime object model (`src/include/lean/lean.h`, `src/runtime/object.cpp`).
2. **`Th0rgal/turbo-lean` (`9ec1e9a`)**: Distributed, incremental Lean verification infrastructure, persistent in-memory `ZygoteWorker` pool, content-addressed `TheoremShard` store, CUDA/CPU `fast-check` counterexample transpiler, `.tlpack` cross-architecture CAS, in-kernel transitive axiom auditor (`TurboLean.Inspector`), and cryptographic `VerificationReceipt` protocol.
3. **Formal Compiler Verification Ecosystem**: `opencompl/lean-mlir` (intrinsically typed SSA dialects, `PoisonOr` refinement, `SLLVM`, `ScfFunctor`), `AliveToolkit/alive2` (symbolic execution & 6-part refinement translation validation for LLVM IR), and `vellvm/vellvm` (Interaction Tree stratified semantics for LLVM IR).

---

## 2. Audit of `leanprover/lean4` (`v4.31.0`)

### 2.1 The Unified 3-Phase `LCNF` Pipeline (`src/Lean/Compiler/LCNF/`)

In Lean 4.31.0, the compiler pipeline is unified into `Lean.Compiler.LCNF`, indexed by `inductive Purity | pure | impure` (`src/Lean/Compiler/LCNF/Basic.lean`):

1. **`Phase.base` (`Purity.pure`)**:
   - Lowers kernel `Expr` via `ToLCNF.toLCNF`, erasing proofs and dependent type arguments to `lcErased` (`◾`).
   - Runs `pullInstances`, `cse`, `simp`, `floatLetIn`, `findJoinPoints`, `pullFunDecls`, `reduceJpArity`, `eagerLambdaLifting`, `specialize`, and `saveBase` (`baseExt`).
2. **`Phase.mono` (`Purity.pure`)**:
   - Erases universe parameters (`toMonoType`), unwraps single-field trivial structures (`hasTrivialStructure?`), runs `structProjCases`, `extendJoinPointContext`, `reduceArity`, `commonJoinPointArgs`, `lambdaLifting`, splits strongly connected components (`splitScc`), runs `elimDeadBranches`, `cse`, `saveMono` (`monoExt`), and `extractClosed`.
   - **Critical Observation**: At `saveMono`, all functions are monomorphic and lambda-lifted (only tail-recursive `.jp` join points remain local), while high-level type structure (`Array Float`, `Array UInt64`, `Prod UInt64 UInt64`, `Option α`, `Nat`) is **still intact** before `toImpure` erases container type parameters to `ImpureType.object`.
3. **`Phase.impure` (`Purity.impure`)**:
   - `toImpure` converts declarations to `Purity.impure` with `ImpureType` (`uint8`, `uint16`, `uint32`, `uint64`, `usize`, `float`, `float32`, `object`, `tagged`, `tobject`, `erased`, `void`).
   - Runs `pushProj`, `insertResetReuse` ("Counting Immutable Beans"), `elimDeadVars`, `simpCase`, `inferBorrow`, `explicitBoxing`, `explicitRc`, `expandResetReuse`, `coalesceRC`, `detectSimpleGround`, `toposortPass`, and `saveImpure` (`impureExt`).
   - `EmitC.lean` emits C directly from `Array (LCNF.Decl .impure)`.

### 2.2 Why Official `EmitLLVM.lean` Is Unmaintained & Insufficient

`src/Lean/Compiler/IR/EmitLLVM.lean` is explicitly marked dysfunctional in Lean 4's source (`EmitLLVM.lean:25-36`):
- It consumes legacy `Lean.IR` (`ToIR.lean`) rather than `LCNF.Decl .impure`.
- It does not implement `ImpureType.void` (`IO.RealWorld`) parameter elimination, causing ABI mismatches with current Lean runtime and `_init_` functions.
- It lacks `SimpleGroundExpr` static constant compilation (`detectSimpleGround`), `lean_dec_ref_known`, and `ClosedTermCache` (`lean_obj_once`).
- `IRType.struct` and `IRType.union` trigger `panic! "not implemented yet"`.
- Most importantly, it lowered IR ops to opaque `@lean_*` calls linked against `lean.h.bc`, providing LLVM with no higher-level alias, exclusivity, or unboxed container/loop invariants beyond `EmitC.lean` + `clang -O3`.

### 2.3 Root Causes of Runtime Overhead in `EmitC` + `clang -O3`

1. **Heap Boxing of 64-Bit Scalars & Multi-Field Return Tuples**:
   - `lean_box_uint64`, `lean_box_usize`, `lean_box_float`, and `lean_box_float32` (`lean.h:3148-3212`) heap-allocate 16-byte `lean_ctor_object` instances (`lean_alloc_ctor(0, 0, 8)`).
   - Functions or join points returning `Prod UInt64 UInt64`, `Option UInt64`, or `StateM` pairs allocate heap constructors on every step unless unboxed by SROA.
2. **Parametric `Array α` Indirection & Per-Element Reference Counting**:
   - `Array Float` and `Array UInt64` compile to `lean_array_object` (`lean_object* m_data[]`), where every element is a heap-allocated box.
   - `FloatArray` and `ByteArray` use `lean_sarray_object` (`uint8_t m_data[]`), storing unboxed scalars contiguously, but every mutation `lean_float_array_uset(a, i, v)` performs an opaque `lean_sarray_ensure_exclusive(a)` (`m_rc == 1`) check and reloads `m_data` on every loop iteration.
3. **Per-Operation `Nat` / `Int` Scalar Tag Checks**:
   - Small `Nat` values (`< 2^63`) are tagged pointers `((n << 1) | 1)`. Every `lean_nat_add`, `lean_nat_sub`, `lean_nat_mul`, `lean_nat_dec_lt` checks `lean_is_scalar(a) && lean_is_scalar(b)`, untags, checks overflow, and retags, blocking LLVM `LoopVectorize` and `SLPVectorizer`.
4. **Sequential CPU Execution of Data-Parallel Numerical Kernels**:
   - Map, zipWith, reduction, stencil, SAXPY, dot-product, and matrix multiplication over scalar arrays execute sequentially on a single CPU core with no MLIR/NVVM/PTX offload path.

---

## 3. Audit of `Th0rgal/turbo-lean` & Integration Surface

`Th0rgal/turbo-lean` provides:
- **Content-Addressed Theorem Shards (`splitter.rs`, `main.rs`)**:
  - Domain-separated key: `BLAKE3("theorem-shard-v1:" || toolchain || ":" || prefix_env_hash || ":" || stmt_hash || ":" || proof_hash)`.
- **Persistent In-Memory `ZygoteWorker` (`ZygoteWorker.lean`, `zygote.rs`, `pack.rs`)**:
  - Evaluates candidate theorem shards against warm `Lean.Environment` + `Command.State` checkpoints over `POST /check-shard` in `~1.9–25 ms` with 0 µs rollback cost.
- **Fast Counterexample Rejection (`gpu_fastcheck.rs`)**:
  - `turbo-lean --json fast-check <file.lean> --transpile-lean <decl>` transpiles Lean 4 propositions into CUDA (`nvcc`) or native C++ (`clang -O3`) harnesses evaluating 100k–10M states in `< 25 ms`.
- **In-Kernel Transitive Axiom Auditing (`Inspector.lean`)**:
  - Verifies via `Lean.collectAxioms` that theorems depend only on `propext`, `Quot.sound`, and `Classical.choice`, rejecting `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, and `Lean.trustCompiler`.
- **Cryptographic Verification Receipts (`pr_verify.rs`)**:
  - Domain-separated `BLAKE3` commitment (`turbo-lean-verification-receipt-v1`) over `schema_version`, `mode`, `interface_hash`, `action_key`, `files_audited`, `theorem_shards`, `forbidden_constructs_found`, and `per_file_interfaces`.

`lean-native` is unified directly inside `Th0rgal/turbo-lean` (`lean/LeanNative/`) and integrates via **in-process C-ABI linking (`LeanNative/Spec.lean`) and unified FastCheck (`LeanNative/Backend/FastCheck.lean`)**:
- When `turbo-lean` (CLI or warm Zygote HTTP daemon) is present, `lean-native` accelerates proof shard checking, counterexample rejection, and `.tlpack` cache synchronization.
- When `turbo-lean` is absent, `lean-native` natively computes and verifies the exact `theorem-shard-v1:` and `turbo-lean-verification-receipt-v1` schemas, performs in-kernel transitive axiom audits via `Lean.collectAxioms`, and runs CPU/CUDA counterexample search directly.

---

## 4. Formal Verification Strategy (`lean-mlir`, Alive2, Vellvm)

1. **Intrinsically Typed / Denotational IR Semantics in Lean 4 (`LeanNative.Semantics`)**:
   - Following `opencompl/lean-mlir` (`Com.denote`, `PoisonOr`, `EffectM`), `LNIR` defines formal evaluation semantics `evalExpr` / `evalCode` over explicit scalar bitvectors (`UInt64` / `BitVec 64`), tuples, and bounded heap/array states (`HeapState`), separating defined values from explicit `UBError`.
2. **Kernel-Checked Proof-Producing Transformations (`LeanNative.Proofs`)**:
   - Every core optimization rule in `lean-native` (algebraic strength reduction, identity/zero folding, branch simplification, unboxed tuple SROA equivalence, exclusive array base-pointer hoisting, and unboxed loop accumulator equivalence) has a **machine-checked Lean 4 theorem** proving `Refines src tgt` (`∀ env st, eval src env st = .ok (v, st') → eval tgt env st = .ok (v, st')`), verified clean of `sorryAx` and `trustCompiler` by `LeanNative.Proofs.AxiomAudit`.
3. **Translation Validation Certificates (`LeanNative.Proofs.CertChecker`)**:
   - Every compilation unit emits a machine-checkable JSON certificate recording each pass's input/output IR hashes, applied theorem names or translation-validation obligations, and explicit assurance level (`VerifiedKernelProof`, `TranslationValidated`, or `UnverifiedFallback`).
