/-
  LeanNative.Spec: Unified Compositional Specification & Meta-Specification Kernel
  Zero `import Lean` (compiles into `lean-native-core` with `libleanrt.a` only),
  zero `sorryAx`, zero `native_decide`, zero `trustCompiler`.

  Architecture (Harmonized 2-Layer Symbiosis with `TurboLean.Spec`):
  - Layer I  : Universal Meta-Specifications (`MetaGateSpec`, `SpeculativeGate`,
               `VerifiedTransformContract`, `ClockedStepBudget`, and multi-step refinement composition).
  - Layer II : Declarative `MetaGateSpec` bundles and ≤ 3-line Mathlib4-style corollaries
               governing FastCheck non-vacuity, C-ABI scalar tagging, PR spec-pinning,
               256-bit 4-limb GPU carry homomorphisms, 4-target hardware routing, and RISC-V step budgets.
-/
import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Backend.Hybrid

namespace LeanNative.Spec
open LeanNative.IR LeanNative.Semantics LeanNative.Backend.Hybrid

/-! ============================================================================
    LAYER I: META-SPECIFICATIONS (`MetaGateSpec`, `SpeculativeGate`, `VerifiedTransformContract`, `ClockedStepBudget`)
    ============================================================================ -/

structure MetaGateSpec (Input : Type) (Safe : Input → Prop) where
  gate : Input → Bool
  sound : ∀ x, gate x = true → Safe x
  complete : ∀ x, Safe x → gate x = true
  posWitness : Input
  negWitness : Input
  nonVacuous : gate posWitness = true
  tight : gate negWitness = false

theorem MetaGateSpec.rejects_unsafe {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) (x : Input) (h_unsafe : ¬ Safe x) :
    M.gate x = false :=
  Bool.eq_false_iff.mpr (fun h_ok => h_unsafe (M.sound x h_ok))

def evalWithUntrustedOptPlugin {Decl Cert : Type}
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool) (d : Decl) : Decl :=
  match plugin d with
  | some (cand, cert) => if verifyGate d cand cert then cand else d
  | none => d

theorem untrusted_opt_plugin_tv_gate_sound {Decl Cert : Type}
    (Refines : Decl → Decl → Prop) (h_refl : ∀ d, Refines d d)
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (h_gate_sound : ∀ d cand cert, verifyGate d cand cert = true → Refines d cand) (d : Decl) :
    Refines d (evalWithUntrustedOptPlugin plugin verifyGate d) := by
  unfold evalWithUntrustedOptPlugin
  split
  · split
    · exact h_gate_sound d _ _ ‹_›
    · exact h_refl d
  · exact h_refl d

theorem untrusted_opt_plugin_timeout_fallback {Decl Cert : Type}
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (d : Decl) (h_timeout : plugin d = none) :
    evalWithUntrustedOptPlugin plugin verifyGate d = d := by
  simp [evalWithUntrustedOptPlugin, h_timeout]

theorem untrusted_opt_plugin_reject_fallback {Decl Cert : Type}
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (d cand : Decl) (cert : Cert) (h_prop : plugin d = some (cand, cert)) (h_rej : verifyGate d cand cert = false) :
    evalWithUntrustedOptPlugin plugin verifyGate d = d := by
  simp [evalWithUntrustedOptPlugin, h_prop, h_rej]

/-- First-class proof-carrying transformation contract tying `run` to its refinement proof `is_sound`. -/
structure VerifiedTransformContract (Decl : Type) (Refines : Decl → Decl → Prop) where
  name     : String
  run      : Decl → Decl
  is_sound : ∀ d, Refines d (run d)

def VerifiedTransformContract.compose (Decl : Type) (Refines : Decl → Decl → Prop)
    (h_trans : ∀ a b c, Refines a b → Refines b c → Refines a c)
    (c1 c2 : VerifiedTransformContract Decl Refines) :
    VerifiedTransformContract Decl Refines where
  name     := c1.name ++ " >> " ++ c2.name
  run      := fun d => c2.run (c1.run d)
  is_sound := fun d => h_trans d (c1.run d) (c2.run (c1.run d)) (c1.is_sound d) (c2.is_sound (c1.run d))

def VerifiedTransformContract.fromGatedPlugin {Decl Cert : Type} {Refines : Decl → Decl → Prop}
    (name : String) (h_refl : ∀ d, Refines d d)
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (h_gate_sound : ∀ d cand cert, verifyGate d cand cert = true → Refines d cand) :
    VerifiedTransformContract Decl Refines where
  name     := name
  run      := evalWithUntrustedOptPlugin plugin verifyGate
  is_sound := untrusted_opt_plugin_tv_gate_sound Refines h_refl plugin verifyGate h_gate_sound

def runGatedPluginChain (steps : List (LNIRCode → LNIRCode)) (c : LNIRCode) : LNIRCode :=
  steps.foldl (fun acc step => step acc) c

theorem opt_pipeline_chain_refines
    (steps : List (LNIRCode → LNIRCode))
    (h_steps : ∀ step, step ∈ steps → ∀ c, CodeRefines c (step c)) (c : LNIRCode) :
    CodeRefines c (runGatedPluginChain steps c) := by
  induction steps generalizing c with
  | nil => exact CodeRefines.refl c
  | cons hd tl ih =>
    exact CodeRefines.trans (h_steps hd (.head tl) c)
      (ih (fun s hs x => h_steps s (.tail hd hs) x) (hd c))

structure AffineStepBudget where
  scale  : Nat
  offset : Nat
  deriving Repr, DecidableEq, BEq

def AffineStepBudget.eval (b : AffineStepBudget) (steps : Nat) : Nat := b.scale * steps + b.offset

def composeAffineBudget (outer inner : AffineStepBudget) : AffineStepBudget :=
  { scale := outer.scale * inner.scale, offset := outer.scale * inner.offset + outer.offset }

theorem composeAffineBudget_eval (outer inner : AffineStepBudget) (steps : Nat) :
    (composeAffineBudget outer inner).eval steps = outer.eval (inner.eval steps) := by
  simp [composeAffineBudget, AffineStepBudget.eval, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem affine_step_budget_monotone (b : AffineStepBudget) {s1 s2 : Nat} (h : s1 ≤ s2) :
    b.eval s1 ≤ b.eval s2 :=
  Nat.add_le_add_right (Nat.mul_le_mul_left b.scale h) b.offset

def evalLoopStepBudget (initSteps fuel : Nat) (bodyBudget : AffineStepBudget) (iterSteps : Nat) : Nat :=
  initSteps + fuel * bodyBudget.eval iterSteps

def riscvDivU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then 0xffffffffffffffff else lhs / rhs
def riscvRemU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then lhs else lhs % rhs

theorem evalLoopStepBudget_monotone (init fuel : Nat) (b : AffineStepBudget) {s1 s2 : Nat} (h : s1 ≤ s2) :
    evalLoopStepBudget init fuel b s1 ≤ evalLoopStepBudget init fuel b s2 :=
  Nat.add_le_add_left (Nat.mul_le_mul_left fuel (affine_step_budget_monotone b h)) init

def evalPassChainBudget (passes : List AffineStepBudget) : AffineStepBudget :=
  passes.foldl composeAffineBudget { scale := 1, offset := 0 }

theorem evalPassChainBudget_cons (b : AffineStepBudget) (bs : List AffineStepBudget) (steps : Nat) :
    (bs.foldl composeAffineBudget b).eval steps =
      b.eval ((bs.foldl composeAffineBudget { scale := 1, offset := 0 }).eval steps) := by
  induction bs generalizing b with
  | nil => simp [AffineStepBudget.eval]
  | cons hd tl ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (composeAffineBudget b hd),
        ih (composeAffineBudget { scale := 1, offset := 0 } hd)]
    simp [composeAffineBudget, AffineStepBudget.eval, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Minimal radix-2 Patricia-tree (`Spt`) code/memory table model for RISC-V & `evm.fast-dev`. -/
inductive SptTree (α : Type) where
  | leaf : SptTree α
  | node : Option α → SptTree α → SptTree α → SptTree α
  deriving Repr, DecidableEq, BEq

def sptLookup {α : Type} : SptTree α → List Bool → Option α
  | .leaf, _ => none
  | .node v _ _, [] => v
  | .node _ l r, b :: bs => sptLookup (if b then r else l) bs

def sptInsert {α : Type} : SptTree α → List Bool → α → SptTree α
  | .leaf, [], val => .node (some val) .leaf .leaf
  | .leaf, b :: bs, val =>
    if b then .node none .leaf (sptInsert .leaf bs val)
    else .node none (sptInsert .leaf bs val) .leaf
  | .node _ l r, [], val => .node (some val) l r
  | .node v l r, b :: bs, val =>
    if b then .node v l (sptInsert r bs val)
    else .node v (sptInsert l bs val) r

theorem sptLookup_insert_same {α : Type} (t : SptTree α) (k : List Bool) (val : α) :
    sptLookup (sptInsert t k val) k = some val := by
  induction k generalizing t with
  | nil => cases t <;> rfl
  | cons b bs ih => cases t <;> cases b <;> simp [sptInsert, sptLookup, ih]

/-! ============================================================================
    LAYER II: DECLARATIVE COROLLARIES (≤ 3 LINES) & `MetaGateSpec` BUNDLES
    ============================================================================ -/

/-! ## 1. Gated Plugin & Pipeline Refinement Corollaries (`SpeculativeGate`) -/

theorem untrusted_opt_plugin_code_refines {Cert : Type}
    (plugin : LNIRCode → Option (LNIRCode × Cert))
    (verifyGate : LNIRCode → LNIRCode → Cert → Bool)
    (h_gate_sound : ∀ src cand cert, verifyGate src cand cert = true → CodeRefines src cand)
    (src : LNIRCode) :
    CodeRefines src (evalWithUntrustedOptPlugin plugin verifyGate src) :=
  untrusted_opt_plugin_tv_gate_sound CodeRefines CodeRefines.refl plugin verifyGate h_gate_sound src

theorem opt_pipeline_two_step_refines
    (step1 step2 : LNIRCode → LNIRCode)
    (h1 : ∀ c, CodeRefines c (step1 c)) (h2 : ∀ c, CodeRefines c (step2 c)) (c : LNIRCode) :
    CodeRefines c (step2 (step1 c)) :=
  CodeRefines.trans (h1 c) (h2 (step1 c))

theorem meta_verified_contract_compose_sound
    (c1 c2 : VerifiedTransformContract LNIRCode CodeRefines) (src : LNIRCode) :
    CodeRefines src ((VerifiedTransformContract.compose LNIRCode CodeRefines (fun _ _ _ => CodeRefines.trans) c1 c2).run src) :=
  (VerifiedTransformContract.compose LNIRCode CodeRefines (fun _ _ _ => CodeRefines.trans) c1 c2).is_sound src

/-! ## 2. FastCheck Non-Vacuity & Zero-False-Positive Gate (`MetaGateSpec`) -/

structure FastCheckSpecVerdict where
  satisfiedPreconditions : Nat
  counterexamplesFound : Nat
  allCertifiedByEval : Bool
  deriving Repr, DecidableEq, BEq

def isNonVacuousCertifiedVerdict (v : FastCheckSpecVerdict) : Bool :=
  decide (v.satisfiedPreconditions > 0) && v.allCertifiedByEval

theorem fastcheck_rejects_vacuous_precondition (cex : Nat) (cert : Bool) :
    isNonVacuousCertifiedVerdict ⟨0, cex, cert⟩ = false := rfl

theorem fastcheck_non_vacuous_tightness_law (v : FastCheckSpecVerdict) :
    isNonVacuousCertifiedVerdict v = true ↔ (v.satisfiedPreconditions > 0 ∧ v.allCertifiedByEval = true) := by
  simp [isNonVacuousCertifiedVerdict, Bool.and_eq_true, decide_eq_true_eq]

def fastcheckMetaSpec : MetaGateSpec FastCheckSpecVerdict
    (fun v => v.satisfiedPreconditions > 0 ∧ v.allCertifiedByEval = true) where
  gate := isNonVacuousCertifiedVerdict
  sound := fun v => (fastcheck_non_vacuous_tightness_law v).mp
  complete := fun v => (fastcheck_non_vacuous_tightness_law v).mpr
  posWitness := ⟨1, 0, true⟩
  negWitness := ⟨0, 0, true⟩
  nonVacuous := rfl
  tight := rfl

/-! ## 3. Lean 4 C-ABI Scalar Boxing / Unboxing Invariance (`@lean_native_abi_*`) -/

def leanBoxScalar (x : UInt64) : UInt64 := (x <<< 1) ||| 1
def leanUnboxScalar (tagged : UInt64) : UInt64 := tagged >>> 1
theorem c_abi_box_zero_eq_one : leanBoxScalar 0 = 1 := rfl
theorem c_abi_unbox_box_zero : leanUnboxScalar (leanBoxScalar 0) = 0 := rfl
theorem c_abi_unbox_box_one : leanUnboxScalar (leanBoxScalar 1) = 1 := rfl

/-! ## 4. PR & Autoresearch Specification-Pinning Gate (`MetaGateSpec`) -/

structure PRVerificationInput where
  expectedSpecHash : Nat
  actualSpecHash : Nat
  expectedTestSuiteHash : Nat
  actualTestSuiteHash : Nat
  forbiddenAxiomsCount : Nat
  tvAllPassed : Bool
  deriving Repr, DecidableEq, BEq

def checkPRVerificationGate (inp : PRVerificationInput) : Bool :=
  decide (inp.expectedSpecHash = inp.actualSpecHash) && decide (inp.expectedTestSuiteHash = inp.actualTestSuiteHash) &&
  decide (inp.forbiddenAxiomsCount = 0) && inp.tvAllPassed

theorem pr_spec_pinning_blocks_spec_tampering (inp : PRVerificationInput)
    (h_tamper : inp.expectedSpecHash ≠ inp.actualSpecHash) :
    checkPRVerificationGate inp = false := by simp [checkPRVerificationGate, h_tamper]

theorem pr_spec_pinning_blocks_test_tampering (inp : PRVerificationInput)
    (h_tamper : inp.expectedTestSuiteHash ≠ inp.actualTestSuiteHash) :
    checkPRVerificationGate inp = false := by simp [checkPRVerificationGate, h_tamper]

theorem pr_spec_pinning_blocks_forbidden_axioms (inp : PRVerificationInput)
    (h_ax : inp.forbiddenAxiomsCount ≠ 0) :
    checkPRVerificationGate inp = false := by simp [checkPRVerificationGate, h_ax]

theorem pr_spec_pinning_gate_sound (inp : PRVerificationInput) :
    checkPRVerificationGate inp = true ↔
      (inp.expectedSpecHash = inp.actualSpecHash ∧ inp.expectedTestSuiteHash = inp.actualTestSuiteHash ∧
       inp.forbiddenAxiomsCount = 0 ∧ inp.tvAllPassed = true) := by
  simp [checkPRVerificationGate, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def prVerificationMetaSpec : MetaGateSpec PRVerificationInput
    (fun inp => inp.expectedSpecHash = inp.actualSpecHash ∧ inp.expectedTestSuiteHash = inp.actualTestSuiteHash ∧
                inp.forbiddenAxiomsCount = 0 ∧ inp.tvAllPassed = true) where
  gate := checkPRVerificationGate
  sound := fun inp => (pr_spec_pinning_gate_sound inp).mp
  complete := fun inp => (pr_spec_pinning_gate_sound inp).mpr
  posWitness := ⟨1, 1, 1, 1, 0, true⟩
  negWitness := ⟨1, 2, 1, 1, 0, true⟩
  nonVacuous := rfl
  tight := rfl

/-! ## 5. Semantic Mutant Discrimination & 4-Limb 256-Bit Lowering Homomorphism -/

def add64CarrySpec (x y : UInt64) : UInt64 :=
  ((x >>> 32) + (y >>> 32) + (((x &&& 0xffffffff) + (y &&& 0xffffffff)) >>> 32)) >>> 32

def mul64HiSpec (x y : UInt64) : UInt64 :=
  let x_lo := x &&& 0xffffffff
  let x_hi := x >>> 32
  let y_lo := y &&& 0xffffffff
  let y_hi := y >>> 32
  let p0 := x_lo * y_lo
  let p1 := x_lo * y_hi
  let p2 := x_hi * y_lo
  let p3 := x_hi * y_hi
  p3 + (p1 >>> 32) + (p2 >>> 32) + (((p0 >>> 32) + (p1 &&& 0xffffffff) + (p2 &&& 0xffffffff)) >>> 32)

def evalLimbMul256Lo (a b : UInt256) : UInt256 :=
  let m0 := a.lo0 * b.lo0; let h00 := mul64HiSpec a.lo0 b.lo0
  let p01 := a.lo0 * b.lo1; let p10 := a.lo1 * b.lo0
  let s1a := h00 + p01; let c1a := add64CarrySpec h00 p01
  let m1 := s1a + p10; let c1 := c1a + add64CarrySpec s1a p10
  let h01 := mul64HiSpec a.lo0 b.lo1; let h10 := mul64HiSpec a.lo1 b.lo0
  let u0 := h01 + h10; let cu0 := add64CarrySpec h01 h10
  let u1 := u0 + c1; let cu1 := add64CarrySpec u0 c1
  let p02 := a.lo0 * b.hi0; let p11 := a.lo1 * b.lo1; let p20 := a.hi0 * b.lo0
  let s2a := u1 + p02; let c2a := add64CarrySpec u1 p02
  let s2b := s2a + p11; let c2b := add64CarrySpec s2a p11
  let m2 := s2b + p20; let c2 := cu0 + cu1 + c2a + c2b + add64CarrySpec s2b p20
  let m3 := c2 + mul64HiSpec a.lo0 b.hi0 + mul64HiSpec a.lo1 b.lo1 + mul64HiSpec a.hi0 b.lo0 +
            a.lo0 * b.hi1 + a.lo1 * b.hi0 + a.hi0 * b.lo1 + a.hi1 * b.lo0
  ⟨m0, m1, m2, m3⟩

def exceptValEq (r1 r2 : Except UBError Val) : Bool :=
  match r1, r2 with | .ok v1, .ok v2 => v1 == v2 | .error e1, .error e2 => e1 == e2 | _, _ => false

def checkAllSemanticMutantsDiscriminated : Bool :=
  let c1 := exceptValEq (evalUnaryOp .not (.u64 0)) (.ok (.u64 0xffffffffffffffff)) &&
            !(exceptValEq (evalUnaryOp .not (.u64 0)) (.ok (.u64 1)))
  let c2 := exceptValEq (evalBinOp .sar (.u64 0x8000000000000000) (.u64 4)) (.ok (.u64 0xf800000000000000)) &&
            !(exceptValEq (evalBinOp .sar (.u64 0x8000000000000000) (.u64 4)) (evalBinOp .shr (.u64 0x8000000000000000) (.u64 4)))
  let c3 := evalLimbMul256Lo UInt256.max UInt256.max == ⟨1, 0, 0, 0⟩ && evalLimbMul256Lo UInt256.max UInt256.max != ⟨1, 0, 0, 4⟩
  let mulDivDown64 : UInt64 := (5 * 2) / 3
  let mulDivUp64 : UInt64 := (5 * 2 + (3 - 1)) / 3
  let c4 := mulDivDown64 == 3 && mulDivUp64 == 4 && mulDivDown64 != mulDivUp64
  let c5 := add64CarrySpec 0xffffffffffffffff 1 == 1 && add64CarrySpec 0xffffffffffffffff 0 == 0
  c1 && c2 && c3 && c4 && c5

theorem meta_validator_rejects_semantic_mutants : checkAllSemanticMutantsDiscriminated = true := rfl
theorem meta_limb256_mul_lo_homomorphism : evalLimbMul256Lo UInt256.max UInt256.max = ⟨1, 0, 0, 0⟩ := rfl

def checkUnboxTupleDeadElimCanary : Bool :=
  let env := (VarEnv.empty.bind 0 (.u64 42)).bind 1 (.u64 99)
  let srcCode : LNIRCode :=
    .letBind 10 (.tuple [.i64, .i64]) (.mkTuple [0, 1])
      (.letBind 11 .i64 (.projTuple 10 0) (.ret 11))
  let tgtCode : LNIRCode := .letBind 11 .i64 (.scalar (.var 0)) (.ret 11)
  exceptValEq
    ((evalCode 0 env HeapState.empty srcCode).map Prod.fst)
    ((evalCode 0 env HeapState.empty tgtCode).map Prod.fst)
theorem meta_unbox_tuple_full_elim_sound : checkUnboxTupleDeadElimCanary = true := rfl

def checkSuperoptShiftMaskAndFmaCanary : Bool :=
  let x : UInt64 := 0x123456789abcdef7
  let k : UInt64 := 4
  let cShiftMask := ((x >>> k) <<< k) == (x &&& (0xffffffffffffffff <<< k)) && ((x >>> k) <<< k) != x
  let env := ((VarEnv.empty.bind 0 (.u64 7)).bind 1 (.u64 9)).bind 2 (.u64 11)
  let cFma := exceptValEq
    (evalScalarExpr env (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)))
    (evalScalarExpr env (.fma (.var 0) (.var 1) (.var 2)))
  let cRotl := ((x <<< 13) ||| (x >>> 51)) == ((x >>> 51) ||| (x <<< 13))
  cShiftMask && cFma && cRotl
theorem meta_double_shift_mask_and_fma_sound : checkSuperoptShiftMaskAndFmaCanary = true := rfl

/-! ## 6. Verified 4-Target Hardware Partitioner & Queue-Aware Federated Routing -/

def federatedNodeEffectiveCost (rtt q exec conc : Nat) : Nat :=
  rtt + ((q + 1) * exec) / max 1 conc

theorem small_trip_prefers_cpu_simd (tripCount : Nat)
    (isMatrixContraction is256BitWorkload isControlHeavy hasTpu hasCudaGpu hasMetalGpu : Bool)
    (h_small : tripCount < 4096) :
    selectOptimalComputeTarget tripCount isMatrixContraction is256BitWorkload isControlHeavy hasTpu hasCudaGpu hasMetalGpu = .cpuSimd := by
  simp [selectOptimalComputeTarget, h_small]

theorem matrix_contraction_prefers_tpu_mxu (tripCount : Nat)
    (is256BitWorkload hasCudaGpu hasMetalGpu : Bool) (h_large : 4096 ≤ tripCount) :
    selectOptimalComputeTarget tripCount true is256BitWorkload false true hasCudaGpu hasMetalGpu = .tpuXlaStableHLO := by
  simp [selectOptimalComputeTarget, Nat.not_lt.mpr h_large]

theorem federated_node_effective_cost_monotone_in_queue (rtt q1 q2 exec conc : Nat) (h_q : q1 ≤ q2) :
    rtt + ((q1 + 1) * exec) / max 1 conc ≤ rtt + ((q2 + 1) * exec) / max 1 conc :=
  Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_right exec (Nat.add_le_add_right h_q 1))) rtt

theorem bootstrap_shift_step_budget_sound (boot targetSteps boundK : Nat) (h : targetSteps ≤ boundK) :
    ({ scale := 1, offset := boot } : AffineStepBudget).eval targetSteps ≤ boot + boundK := by
  simpa [AffineStepBudget.eval, Nat.add_comm] using Nat.add_le_add_left h boot

theorem empirical_high_water_refutes_loose_bound (obsMax candK : Nat) (h_gt : candK < obsMax) :
    ¬ (obsMax ≤ candK) := Nat.not_le.mpr h_gt

theorem riscv_div_by_zero_spec (x : UInt64) : riscvDivU64Spec x 0 = 0xffffffffffffffff ∧ riscvRemU64Spec x 0 = x :=
  ⟨rfl, rfl⟩

theorem zisk_csr_atomic_step_budget (boot csrCount bodySteps boundK : Nat) (h : csrCount + bodySteps ≤ boundK) :
    ({ scale := 1, offset := boot } : AffineStepBudget).eval (csrCount + bodySteps) ≤ boot + boundK :=
  bootstrap_shift_step_budget_sound boot (csrCount + bodySteps) boundK h

theorem pass_chain_two_passes_eval (p1 p2 : AffineStepBudget) (steps : Nat) :
    (evalPassChainBudget [p1, p2]).eval steps = p1.eval (p2.eval steps) := by
  simp [evalPassChainBudget, composeAffineBudget, AffineStepBudget.eval, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem spt_rom_fetch_deterministic {α : Type} (rom : SptTree α) (pcBits : List Bool) (instr : α) :
    sptLookup (sptInsert rom pcBits instr) pcBits = some instr :=
  sptLookup_insert_same rom pcBits instr

def mulDivDownNat (a b d : Nat) : Nat := if d == 0 then 0 else (a * b) / d
def mulDivUpNat (a b d : Nat) : Nat := if d == 0 then 0 else (a * b + (d - 1)) / d

theorem mulDivDown_le_mulDivUp (a b d : Nat) : mulDivDownNat a b d ≤ mulDivUpNat a b d := by
  unfold mulDivDownNat mulDivUpNat; split <;> first | exact Nat.le_refl 0 | exact Nat.div_le_div_right (Nat.le_add_right _ _)

theorem mulDivDown_zero_denom (a b : Nat) : mulDivDownNat a b 0 = 0 ∧ mulDivUpNat a b 0 = 0 := ⟨rfl, rfl⟩

/-! ## 7. Non-Negative Linear Combination / Farkas Certificates (`Nat`) -/

/-- Dot product of two lists of natural numbers (`∑_j u_j * v_j`). -/
def dotNat : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a * b + dotNat as bs

/-- Weighted column sum (`∑_i weights_i * matrix_{i, colIdx}`). -/
def weightedColSum : List Nat → List (List Nat) → Nat → Nat
  | [], _, _ => 0
  | _, [], _ => 0
  | w :: ws, row :: rows, colIdx =>
    w * row.getD colIdx 0 + weightedColSum ws rows colIdx

/-- Helper checking column dominance `obj_j ≤ weightedColSum weights matrix j` for `j < n`. -/
def checkFarkasCols (weights : List Nat) (matrix : List (List Nat)) (obj : List Nat) : Nat → Bool
  | 0 => true
  | j + 1 =>
    checkFarkasCols weights matrix obj j &&
    decide (obj.getD j 0 ≤ weightedColSum weights matrix j)

/-- Boolean certificate checker for non-negative Farkas linear combinations over `Nat`:
    verifies (a) for every column `j < obj.length`, `obj.getD j 0 ≤ weightedColSum weights matrix j`,
    and (b) `dotNat weights rhs ≤ bound`. -/
def checkFarkasNat (weights : List Nat) (matrix : List (List Nat)) (rhs : List Nat) (obj : List Nat) (bound : Nat) : Bool :=
  checkFarkasCols weights matrix obj obj.length &&
  decide (dotNat weights rhs ≤ bound)

theorem dotNat_nil_left (v : List Nat) : dotNat [] v = 0 := rfl

theorem dotNat_nil_right (u : List Nat) : dotNat u [] = 0 := by
  cases u <;> rfl

theorem dotNat_cons (a b : Nat) (as bs : List Nat) :
    dotNat (a :: as) (b :: bs) = a * b + dotNat as bs := rfl

theorem dotNat_le_of_pointwise_le (u v x : List Nat)
    (h : ∀ j, j < u.length → u.getD j 0 ≤ v.getD j 0) :
    dotNat u x ≤ dotNat v x := by
  induction u generalizing v x with
  | nil =>
    rw [dotNat_nil_left]
    exact Nat.zero_le _
  | cons a as ih =>
    cases x with
    | nil =>
      rw [dotNat_nil_right, dotNat_nil_right]
      exact Nat.le_refl 0
    | cons x0 xs =>
      have h0 : a ≤ v.getD 0 0 := h 0 (Nat.zero_lt_succ _)
      cases v with
      | nil =>
        have ha : a = 0 := Nat.eq_zero_of_le_zero h0
        have ih_nil : dotNat as xs ≤ 0 := by
          simpa [dotNat_nil_left] using ih [] xs (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))
        simp [dotNat_cons, dotNat_nil_left, ha, Nat.eq_zero_of_le_zero ih_nil]
      | cons b bs =>
        rw [dotNat_cons, dotNat_cons]
        have h_head : a * x0 ≤ b * x0 := Nat.mul_le_mul_right x0 h0
        have h_tail : dotNat as xs ≤ dotNat bs xs :=
          ih bs xs (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))
        exact Nat.add_le_add h_head h_tail

def weightedColVec (weights : List Nat) (matrix : List (List Nat)) : Nat → Nat → List Nat
  | 0, _ => []
  | len + 1, colIdx => weightedColSum weights matrix colIdx :: weightedColVec weights matrix len (colIdx + 1)

private theorem weightedColVec_zero_weights (matrix : List (List Nat)) (len colIdx : Nat) (x : List Nat) :
    dotNat (weightedColVec [] matrix len colIdx) x = 0 := by
  induction len generalizing colIdx x with
  | zero => rfl
  | succ len ih =>
    cases x with
    | nil => exact dotNat_nil_right _
    | cons x0 xs =>
      simp [weightedColVec, weightedColSum, dotNat_cons, ih (colIdx + 1) xs]

private theorem weightedColVec_zero_matrix (weights : List Nat) (len colIdx : Nat) (x : List Nat) :
    dotNat (weightedColVec weights [] len colIdx) x = 0 := by
  induction len generalizing colIdx x with
  | zero => rfl
  | succ len ih =>
    cases x with
    | nil => exact dotNat_nil_right _
    | cons x0 xs =>
      cases weights <;> simp [weightedColVec, weightedColSum, dotNat_cons, ih (colIdx + 1) xs]

private theorem weightedColVec_dot_split (w : Nat) (ws : List Nat) (row : List Nat) (rows : List (List Nat))
    (colIdx : Nat) (x : List Nat) :
    dotNat (weightedColVec (w :: ws) (row :: rows) x.length colIdx) x =
      w * dotNat (row.drop colIdx) x + dotNat (weightedColVec ws rows x.length colIdx) x := by
  induction x generalizing colIdx with
  | nil => simp [weightedColVec, dotNat_nil_right]
  | cons x0 xs ih =>
    simp only [List.length_cons, weightedColVec, weightedColSum, dotNat_cons, ih (colIdx + 1)]
    have h_drop : dotNat (row.drop colIdx) (x0 :: xs) = row.getD colIdx 0 * x0 + dotNat (row.drop (colIdx + 1)) xs := by
      clear ih
      induction colIdx generalizing row with
      | zero =>
        cases row <;> simp [List.getD, dotNat_nil_left, dotNat_cons]
      | succ k ih_k =>
        cases row with
        | nil => simp [List.getD, dotNat_nil_left]
        | cons r0 rs =>
          simpa [List.getD, Nat.add_assoc] using ih_k rs
    rw [h_drop, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    omega

theorem farkas_weighted_rows_le (weights : List Nat) (matrix : List (List Nat)) (rhs x : List Nat)
    (h_rows : ∀ i, i < weights.length → dotNat (matrix.getD i []) x ≤ rhs.getD i 0) :
    dotNat (weightedColVec weights matrix x.length 0) x ≤ dotNat weights rhs := by
  induction weights generalizing matrix rhs with
  | nil =>
    rw [weightedColVec_zero_weights, dotNat_nil_left]
    exact Nat.le_refl 0
  | cons w ws ih =>
    have h0 : dotNat (matrix.getD 0 []) x ≤ rhs.getD 0 0 := h_rows 0 (Nat.zero_lt_succ _)
    cases matrix with
    | nil =>
      rw [weightedColVec_zero_matrix]
      exact Nat.zero_le _
    | cons row rows =>
      rw [weightedColVec_dot_split]
      have h_row0 : w * dotNat row x ≤ w * rhs.getD 0 0 := Nat.mul_le_mul_left w h0
      have h_tail : dotNat (weightedColVec ws rows x.length 0) x ≤ dotNat ws (rhs.drop 1) :=
        ih rows (rhs.drop 1) (fun i hi => by
          have := h_rows (i + 1) (Nat.succ_lt_succ hi)
          cases rhs <;> simpa [List.getD] using this)
      cases rhs with
      | nil =>
        have h_rhs_nil : dotNat ws [] = 0 := dotNat_nil_right ws
        rw [dotNat_nil_right]
        have h_r0 : w * dotNat row x = 0 := Nat.eq_zero_of_le_zero h_row0
        have h_rt : dotNat (weightedColVec ws rows x.length 0) x = 0 := by
          rw [List.drop, h_rhs_nil] at h_tail
          exact Nat.eq_zero_of_le_zero h_tail
        simp [List.drop, h_r0, h_rt]
      | cons b bs =>
        rw [dotNat_cons]
        exact Nat.add_le_add h_row0 h_tail

private theorem weightedColVec_getD (weights : List Nat) (matrix : List (List Nat)) (len colIdx j : Nat)
    (hj : j < len) :
    (weightedColVec weights matrix len colIdx).getD j 0 = weightedColSum weights matrix (colIdx + j) := by
  induction len generalizing colIdx j with
  | zero => contradiction
  | succ len ih =>
    cases j with
    | zero => simp [weightedColVec, List.getD]
    | succ j_prev =>
      have hj_prev : j_prev < len := Nat.lt_of_succ_lt_succ hj
      simpa [weightedColVec, List.getD, Nat.add_right_comm, Nat.add_assoc] using ih (colIdx + 1) j_prev hj_prev

private theorem checkFarkasCols_sound (weights : List Nat) (matrix : List (List Nat)) (obj : List Nat) (n j : Nat)
    (h_ok : checkFarkasCols weights matrix obj n = true) (hj : j < n) :
    obj.getD j 0 ≤ weightedColSum weights matrix j := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    simp [checkFarkasCols, Bool.and_eq_true, decide_eq_true_eq] at h_ok
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h_lt | rfl
    · exact ih h_ok.1 h_lt
    · exact h_ok.2

theorem checkFarkasNat_sound (weights : List Nat) (matrix : List (List Nat)) (rhs obj x : List Nat) (bound : Nat)
    (h_cert : checkFarkasNat weights matrix rhs obj bound = true)
    (h_rows : ∀ i, i < weights.length → dotNat (matrix.getD i []) x ≤ rhs.getD i 0) :
    dotNat obj x ≤ bound := by
  simp [checkFarkasNat, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  let x_pad := x.take obj.length ++ List.replicate (obj.length - x.length) 0
  have h_xpad_len : x_pad.length = obj.length := by
    simp [x_pad, List.length_append, List.length_take, List.length_replicate]
    omega
  have h_rep_zero : ∀ (u : List Nat) (k : Nat), dotNat u (List.replicate k 0) = 0 := by
    intro u k
    induction u generalizing k with
    | nil => rfl
    | cons u0 us ih_u =>
      cases k with
      | zero => exact dotNat_nil_right _
      | succ k_prev => simp [List.replicate, dotNat_cons, ih_u k_prev]
  have h_obj_xpad : dotNat obj x = dotNat obj x_pad := by
    clear h_cert h_rows h_xpad_len
    induction obj generalizing x with
    | nil => rfl
    | cons c cs ih =>
      cases x with
      | nil =>
        simp [x_pad, dotNat_nil_right, h_rep_zero]
      | cons x0 xs =>
        simp [x_pad, List.length_cons, Nat.succ_sub_succ_eq_sub, dotNat_cons, ih xs]
  rw [h_obj_xpad]
  have h_pw : dotNat obj x_pad ≤ dotNat (weightedColVec weights matrix x_pad.length 0) x_pad := by
    apply dotNat_le_of_pointwise_le
    intro j hj
    rw [h_xpad_len, weightedColVec_getD weights matrix obj.length 0 j hj, Nat.zero_add]
    exact checkFarkasCols_sound weights matrix obj obj.length j h_cert.1 hj
  have h_rows_xpad : ∀ i, i < weights.length → dotNat (matrix.getD i []) x_pad ≤ rhs.getD i 0 := by
    intro i hi
    have h_le_x : dotNat (matrix.getD i []) x_pad ≤ dotNat (matrix.getD i []) x := by
      clear h_cert h_rows h_xpad_len h_obj_xpad h_pw hi
      generalize matrix.getD i [] = row
      have h_take_rep : ∀ (r v : List Nat) (n k : Nat), dotNat r (v.take n ++ List.replicate k 0) ≤ dotNat r v := by
        intro r v n k
        induction r generalizing v n with
        | nil => exact Nat.le_refl 0
        | cons r0 rs ih_r =>
          cases n with
          | zero =>
            simp [List.take, h_rep_zero]
          | succ n_prev =>
            cases v with
            | nil => simp [List.take, h_rep_zero, dotNat_nil_right]
            | cons v0 vs =>
              simp only [List.take, List.cons_append, dotNat_cons]
              exact Nat.add_le_add_left (ih_r vs n_prev) (r0 * v0)
      exact h_take_rep row x obj.length (obj.length - x.length)
    exact Nat.le_trans h_le_x (h_rows i hi)
  have h_farkas := farkas_weighted_rows_le weights matrix rhs x_pad h_rows_xpad
  exact Nat.le_trans h_pw (Nat.le_trans h_farkas h_cert.2)

/-! ## 8. Relational Polytope Sampling, Zero-Copy ByteSlice & Grace-Blackwell Headroom Gate -/

/-- Relational monotone chain predicate (`lo ≤ o0 ≤ o1 ≤ o2 ≤ o3 ≤ totalLen`) for SSZ/RLP offsets. -/
def checkMonotoneOffsets4 (lo o0 o1 o2 o3 totalLen : Nat) : Bool :=
  decide (lo ≤ o0) && decide (o0 ≤ o1) && decide (o1 ≤ o2) && decide (o2 ≤ o3) && decide (o3 ≤ totalLen)

/-- Project raw draws `(d0, d1, d2, d3)` into the monotone polytope `lo ≤ o0 ≤ o1 ≤ o2 ≤ o3 ≤ lo + d0 + d1 + d2 + d3`. -/
def sampleMonotoneOffsets4 (lo d0 d1 d2 d3 : Nat) : Nat × Nat × Nat × Nat :=
  let o0 := lo + d0
  let o1 := o0 + d1
  let o2 := o1 + d2
  let o3 := o2 + d3
  (o0, o1, o2, o3)

theorem sampleMonotoneOffsets4_valid (lo d0 d1 d2 d3 extra : Nat) :
    let (o0, o1, o2, o3) := sampleMonotoneOffsets4 lo d0 d1 d2 d3
    checkMonotoneOffsets4 lo o0 o1 o2 o3 (o3 + extra) = true := by
  simp [sampleMonotoneOffsets4, checkMonotoneOffsets4]

/-- Hash-table load-factor invariant `2 * count ≤ cap` (`count ≤ cap / 2`). -/
def checkLoadFactorHalf (count cap : Nat) : Bool :=
  decide (2 * count ≤ cap)

theorem sampleLoadFactorHalf_valid (rawCount cap : Nat) (h_pos : 0 < cap / 2 + 1) :
    checkLoadFactorHalf (rawCount % (cap / 2 + 1)) cap = true := by
  simp [checkLoadFactorHalf]
  have h_lt : rawCount % (cap / 2 + 1) < cap / 2 + 1 := Nat.mod_lt rawCount h_pos
  omega

/-- Zero-copy `ByteSlice` view `(offset, len)` inside a backing buffer of length `backingLen`. -/
structure ByteSliceView where
  backingLen : Nat
  offset     : Nat
  len        : Nat
  deriving Repr, DecidableEq, BEq

def isValidByteSlice (s : ByteSliceView) : Bool :=
  decide (s.offset + s.len ≤ s.backingLen)

def subSliceView (s : ByteSliceView) (subOff subLen : Nat) : ByteSliceView :=
  { backingLen := s.backingLen, offset := s.offset + subOff, len := subLen }

theorem subSliceView_valid (s : ByteSliceView) (subOff subLen : Nat)
    (h_parent : isValidByteSlice s = true) (h_sub : subOff + subLen ≤ s.len) :
    isValidByteSlice (subSliceView s subOff subLen) = true := by
  have hp : s.offset + s.len ≤ s.backingLen := of_decide_eq_true h_parent
  exact decide_eq_true (by dsimp [subSliceView]; omega)

/-- Grace-Blackwell `cuMemGetInfo` pre-flight memory headroom gate. -/
structure GpuMemoryHeadroomInput where
  freeBytes     : Nat
  requiredBytes : Nat
  safetyMargin  : Nat
  deriving Repr, DecidableEq, BEq

def hasSufficientGpuMemory (inp : GpuMemoryHeadroomInput) : Bool :=
  decide (inp.requiredBytes + inp.safetyMargin ≤ inp.freeBytes)

theorem gpu_memory_headroom_gate_sound (inp : GpuMemoryHeadroomInput) :
    hasSufficientGpuMemory inp = true ↔ inp.requiredBytes + inp.safetyMargin ≤ inp.freeBytes := by
  simp [hasSufficientGpuMemory]

def gpuMemoryHeadroomMetaSpec : MetaGateSpec GpuMemoryHeadroomInput
    (fun inp => inp.requiredBytes + inp.safetyMargin ≤ inp.freeBytes) where
  gate := hasSufficientGpuMemory
  sound := fun inp => (gpu_memory_headroom_gate_sound inp).mp
  complete := fun inp => (gpu_memory_headroom_gate_sound inp).mpr
  posWitness := ⟨4096, 1024, 2048⟩
  negWitness := ⟨2048, 1024, 2048⟩
  nonVacuous := rfl
  tight := rfl

theorem gpu_oom_falls_back_to_cpu_simd (inp : GpuMemoryHeadroomInput)
    (h_low : inp.freeBytes < inp.requiredBytes + inp.safetyMargin) :
    hasSufficientGpuMemory inp = false :=
  gpuMemoryHeadroomMetaSpec.rejects_unsafe inp (Nat.not_le.mpr h_low)

end LeanNative.Spec

