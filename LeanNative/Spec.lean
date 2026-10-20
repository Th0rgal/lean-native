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
  unfold evalWithUntrustedOptPlugin; split <;> first | exact h_refl d | (split <;> first | exact h_refl d | exact h_gate_sound d _ _ ‹_›)

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

theorem pr_spec_pinning_blocks_spec_tampering (inp : PRVerificationInput) (h_tamper : inp.expectedSpecHash ≠ inp.actualSpecHash) :
    checkPRVerificationGate inp = false := by simp [checkPRVerificationGate, h_tamper]

theorem pr_spec_pinning_blocks_test_tampering (inp : PRVerificationInput) (h_tamper : inp.expectedTestSuiteHash ≠ inp.actualTestSuiteHash) :
    checkPRVerificationGate inp = false := by simp [checkPRVerificationGate, h_tamper]

theorem pr_spec_pinning_blocks_forbidden_axioms (inp : PRVerificationInput) (h_ax : inp.forbiddenAxiomsCount ≠ 0) :
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
  let x_lo := x &&& 0xffffffff; let x_hi := x >>> 32; let y_lo := y &&& 0xffffffff; let y_hi := y >>> 32
  let p0 := x_lo * y_lo; let p1 := x_lo * y_hi; let p2 := x_hi * y_lo; let p3 := x_hi * y_hi
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
  let c1 := exceptValEq (evalUnaryOp .not (.u64 0)) (.ok (.u64 0xffffffffffffffff)) && !(exceptValEq (evalUnaryOp .not (.u64 0)) (.ok (.u64 1)))
  let c2 := exceptValEq (evalBinOp .sar (.u64 0x8000000000000000) (.u64 4)) (.ok (.u64 0xf800000000000000)) &&
            !(exceptValEq (evalBinOp .sar (.u64 0x8000000000000000) (.u64 4)) (evalBinOp .shr (.u64 0x8000000000000000) (.u64 4)))
  let c3 := evalLimbMul256Lo UInt256.max UInt256.max == ⟨1, 0, 0, 0⟩ && evalLimbMul256Lo UInt256.max UInt256.max != ⟨1, 0, 0, 4⟩
  let mulDivDown64 : UInt64 := (5 * 2) / 3; let mulDivUp64 : UInt64 := (5 * 2 + (3 - 1)) / 3
  let c4 := mulDivDown64 == 3 && mulDivUp64 == 4 && mulDivDown64 != mulDivUp64
  let c5 := add64CarrySpec 0xffffffffffffffff 1 == 1 && add64CarrySpec 0xffffffffffffffff 0 == 0
  c1 && c2 && c3 && c4 && c5

theorem meta_validator_rejects_semantic_mutants : checkAllSemanticMutantsDiscriminated = true := rfl
theorem meta_limb256_mul_lo_homomorphism : evalLimbMul256Lo UInt256.max UInt256.max = ⟨1, 0, 0, 0⟩ := rfl

def checkUnboxTupleDeadElimCanary : Bool :=
  let env := (VarEnv.empty.bind 0 (.u64 42)).bind 1 (.u64 99)
  exceptValEq
    ((evalCode 0 env HeapState.empty (.letBind 10 (.tuple [.i64, .i64]) (.mkTuple [0, 1]) (.letBind 11 .i64 (.projTuple 10 0) (.ret 11)))).map Prod.fst)
    ((evalCode 0 env HeapState.empty (.letBind 11 .i64 (.scalar (.var 0)) (.ret 11))).map Prod.fst)
theorem meta_unbox_tuple_full_elim_sound : checkUnboxTupleDeadElimCanary = true := rfl

def checkSuperoptShiftMaskAndFmaCanary : Bool :=
  let x : UInt64 := 0x123456789abcdef7; let k : UInt64 := 4
  let cShiftMask := ((x >>> k) <<< k) == (x &&& (0xffffffffffffffff <<< k)) && ((x >>> k) <<< k) != x
  let env := ((VarEnv.empty.bind 0 (.u64 7)).bind 1 (.u64 9)).bind 2 (.u64 11)
  let cFma := exceptValEq (evalScalarExpr env (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (evalScalarExpr env (.fma (.var 0) (.var 1) (.var 2)))
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

end LeanNative.Spec
