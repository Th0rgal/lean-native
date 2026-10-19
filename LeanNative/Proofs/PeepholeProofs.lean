import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## Kernel-Checked Bitvector & UInt64 Algebraic Identities -/

theorem uint64_add_zero (a : UInt64) : a + (0 : UInt64) = a := UInt64.add_zero a
theorem uint64_zero_add (a : UInt64) : (0 : UInt64) + a = a := UInt64.zero_add a
theorem uint64_sub_zero (a : UInt64) : a - (0 : UInt64) = a := UInt64.sub_zero a
theorem uint64_mul_one (a : UInt64) : a * (1 : UInt64) = a := UInt64.mul_one a
theorem uint64_one_mul (a : UInt64) : (1 : UInt64) * a = a := UInt64.one_mul a
theorem uint64_xor_zero (a : UInt64) : a ^^^ (0 : UInt64) = a := UInt64.xor_zero
theorem uint64_zero_xor (a : UInt64) : (0 : UInt64) ^^^ a = a := UInt64.zero_xor
theorem uint64_and_self (a : UInt64) : a &&& a = a := UInt64.and_self
theorem uint64_or_self (a : UInt64) : a ||| a = a := UInt64.or_self
theorem uint64_or_zero (a : UInt64) : a ||| (0 : UInt64) = a := UInt64.or_zero
theorem uint64_zero_or (a : UInt64) : (0 : UInt64) ||| a = a := UInt64.zero_or

theorem uint64_mul_two (a : UInt64) : a * (2 : UInt64) = a <<< (1 : UInt64) := by
  cases a with
  | ofBitVec bv =>
    apply congrArg UInt64.ofBitVec
    change bv * 2#64 = bv <<< (1#64).toNat
    have h1 : (1#64).toNat = 1 := rfl
    rw [h1, BitVec.shiftLeft_eq_mul_twoPow]
    rfl

theorem uint64_mul_four (a : UInt64) : a * (4 : UInt64) = a <<< (2 : UInt64) := by
  cases a with
  | ofBitVec bv =>
    apply congrArg UInt64.ofBitVec
    change bv * 4#64 = bv <<< (2#64).toNat
    have h1 : (2#64).toNat = 2 := rfl
    rw [h1, BitVec.shiftLeft_eq_mul_twoPow]
    rfl

theorem uint64_mul_eight (a : UInt64) : a * (8 : UInt64) = a <<< (3 : UInt64) := by
  cases a with
  | ofBitVec bv =>
    apply congrArg UInt64.ofBitVec
    change bv * 8#64 = bv <<< (3#64).toNat
    have h1 : (3#64).toNat = 3 := rfl
    rw [h1, BitVec.shiftLeft_eq_mul_twoPow]
    rfl

/-! ## Semantic Lemmas for `evalBinOp` -/

@[simp]
theorem evalBinOp_add_zero (v : Val) : evalBinOp .add v (.u64 0) = .ok v := by
  cases v <;> simp [evalBinOp]

@[simp]
theorem evalBinOp_zero_add (v : Val) : evalBinOp .add (.u64 0) v = .ok v := by
  cases v <;> simp [evalBinOp]

@[simp]
theorem evalBinOp_sub_zero (v : Val) : evalBinOp .sub v (.u64 0) = .ok v := by
  cases v <;> simp [evalBinOp]

@[simp]
theorem evalBinOp_mul_one (v : Val) : evalBinOp .mul v (.u64 1) = .ok v := by
  cases v <;> simp [evalBinOp]

@[simp]
theorem evalBinOp_one_mul (v : Val) : evalBinOp .mul (.u64 1) v = .ok v := by
  cases v <;> simp [evalBinOp]

@[simp]
theorem evalBinOp_xor_zero (v : Val) : evalBinOp .bitXor v (.u64 0) = .ok v := by
  cases v <;> simp [evalBinOp]

@[simp]
theorem evalBinOp_zero_xor (v : Val) : evalBinOp .bitXor (.u64 0) v = .ok v := by
  cases v <;> simp [evalBinOp]

@[simp]
theorem evalBinOp_or_zero (v : Val) : evalBinOp .bitOr v (.u64 0) = .ok v := by
  cases v <;> simp [evalBinOp]

@[simp]
theorem evalBinOp_zero_or (v : Val) : evalBinOp .bitOr (.u64 0) v = .ok v := by
  cases v <;> simp [evalBinOp]

@[simp]
theorem evalBinOp_and_self (v : Val) : evalBinOp .bitAnd v v = .ok v := by
  cases v <;> simp [evalBinOp, Val.beq_self]

@[simp]
theorem evalBinOp_or_self (v : Val) : evalBinOp .bitOr v v = .ok v := by
  cases v with
  | u64 a => simp [evalBinOp]
  | bool b => simp [evalBinOp, Val.beq_self]
  | tuple vs => simp [evalBinOp, Val.beq_self]
  | objPtr p => simp [evalBinOp, Val.beq_self]
  | sarrayId s => simp [evalBinOp, Val.beq_self]
  | rawPtrId r => simp [evalBinOp, Val.beq_self]
  | unit => simp [evalBinOp, Val.beq_self]

theorem evalBinOp_mul_two (v : Val) :
    evalBinOp .mul v (.u64 2) = evalBinOp .shl v (.u64 1) := by
  cases v with
  | u64 a =>
    simp only [evalBinOp]
    rw [uint64_mul_two]
  | bool _ | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | unit => rfl

theorem evalBinOp_mul_four (v : Val) :
    evalBinOp .mul v (.u64 4) = evalBinOp .shl v (.u64 2) := by
  cases v with
  | u64 a =>
    simp only [evalBinOp]
    rw [uint64_mul_four]
  | bool _ | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | unit => rfl

theorem evalBinOp_mul_eight (v : Val) :
    evalBinOp .mul v (.u64 8) = evalBinOp .shl v (.u64 3) := by
  cases v with
  | u64 a =>
    simp only [evalBinOp]
    rw [uint64_mul_eight]
  | bool _ | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | unit => rfl

/-! ## Verified Scalar Peephole Rewriter -/

/-- Verified algebraic rewrite step for binary scalar operations. -/
def rewriteBinOpStep (op : BinOp) (lhs rhs : ScalarExpr) : ScalarExpr :=
  match op with
  | .add =>
    if rhs = .constU64 0 then lhs
    else if lhs = .constU64 0 then rhs
    else .binOp .add lhs rhs
  | .sub =>
    if rhs = .constU64 0 then lhs
    else .binOp .sub lhs rhs
  | .mul =>
    if rhs = .constU64 1 then lhs
    else if lhs = .constU64 1 then rhs
    else if rhs = .constU64 2 then .binOp .shl lhs (.constU64 1)
    else if rhs = .constU64 4 then .binOp .shl lhs (.constU64 2)
    else if rhs = .constU64 8 then .binOp .shl lhs (.constU64 3)
    else .binOp .mul lhs rhs
  | .bitXor =>
    if rhs = .constU64 0 then lhs
    else if lhs = .constU64 0 then rhs
    else .binOp .bitXor lhs rhs
  | .bitAnd =>
    if lhs = rhs then lhs
    else .binOp .bitAnd lhs rhs
  | .bitOr =>
    if lhs = rhs then lhs
    else if rhs = .constU64 0 then lhs
    else if lhs = .constU64 0 then rhs
    else .binOp .bitOr lhs rhs
  | _ => .binOp op lhs rhs

/-- Verified branch-folding step for `select`. -/
def rewriteSelectStep (cond thenVal elseVal : ScalarExpr) : ScalarExpr :=
  if cond = .constBool true then thenVal
  else if cond = .constBool false then elseVal
  else .select cond thenVal elseVal

/-- Single-step verified peephole rewrite on `ScalarExpr`. -/
def rewriteScalarPeepholeStep : ScalarExpr → ScalarExpr
  | .binOp op lhs rhs => rewriteBinOpStep op lhs rhs
  | .select cond thenVal elseVal => rewriteSelectStep cond thenVal elseVal
  | .fma a b c => .binOp .add (.binOp .mul a b) c
  | other => other

/-- Recursive verified scalar peephole optimizer on `ScalarExpr`. -/
def rewriteScalarPeephole : ScalarExpr → ScalarExpr
  | .constU64 val => .constU64 val
  | .constBool val => .constBool val
  | .var id => .var id
  | .binOp op lhs rhs =>
    rewriteScalarPeepholeStep (.binOp op (rewriteScalarPeephole lhs) (rewriteScalarPeephole rhs))
  | .unaryOp op arg =>
    rewriteScalarPeepholeStep (.unaryOp op (rewriteScalarPeephole arg))
  | .select cond thenVal elseVal =>
    rewriteScalarPeepholeStep (.select (rewriteScalarPeephole cond) (rewriteScalarPeephole thenVal) (rewriteScalarPeephole elseVal))
  | .fma a b c =>
    rewriteScalarPeepholeStep (.fma (rewriteScalarPeephole a) (rewriteScalarPeephole b) (rewriteScalarPeephole c))

/-- Lift `rewriteScalarPeephole` to `LNIRExpr`. -/
def rewriteLNIRExpr : LNIRExpr → LNIRExpr
  | .scalar e => .scalar (rewriteScalarPeephole e)
  | other => other

/-! ## Machine-Checked Soundness Proofs -/

theorem evalScalarExpr_add_zero_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .add lhs (.constU64 0)) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_add_zero v

theorem evalScalarExpr_add_zero_left (env : VarEnv) (rhs : ScalarExpr) :
    evalScalarExpr env (.binOp .add (.constU64 0) rhs) = evalScalarExpr env rhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env rhs with
  | error err => rfl
  | ok v => exact evalBinOp_zero_add v

theorem evalScalarExpr_sub_zero_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .sub lhs (.constU64 0)) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_sub_zero v

theorem evalScalarExpr_mul_one_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul lhs (.constU64 1)) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_mul_one v

theorem evalScalarExpr_mul_one_left (env : VarEnv) (rhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul (.constU64 1) rhs) = evalScalarExpr env rhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env rhs with
  | error err => rfl
  | ok v => exact evalBinOp_one_mul v

theorem evalScalarExpr_mul_two_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul lhs (.constU64 2)) =
    evalScalarExpr env (.binOp .shl lhs (.constU64 1)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_mul_two v

theorem evalScalarExpr_mul_four_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul lhs (.constU64 4)) =
    evalScalarExpr env (.binOp .shl lhs (.constU64 2)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_mul_four v

theorem evalScalarExpr_mul_eight_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul lhs (.constU64 8)) =
    evalScalarExpr env (.binOp .shl lhs (.constU64 3)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_mul_eight v

theorem evalScalarExpr_xor_zero_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .bitXor lhs (.constU64 0)) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_xor_zero v

theorem evalScalarExpr_xor_zero_left (env : VarEnv) (rhs : ScalarExpr) :
    evalScalarExpr env (.binOp .bitXor (.constU64 0) rhs) = evalScalarExpr env rhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env rhs with
  | error err => rfl
  | ok v => exact evalBinOp_zero_xor v

theorem evalScalarExpr_or_zero_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .bitOr lhs (.constU64 0)) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_or_zero v

theorem evalScalarExpr_or_zero_left (env : VarEnv) (rhs : ScalarExpr) :
    evalScalarExpr env (.binOp .bitOr (.constU64 0) rhs) = evalScalarExpr env rhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env rhs with
  | error err => rfl
  | ok v => exact evalBinOp_zero_or v

theorem evalScalarExpr_and_self (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .bitAnd lhs lhs) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_and_self v

theorem evalScalarExpr_or_self (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .bitOr lhs lhs) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_or_self v

theorem rewriteBinOpStep_sound (op : BinOp) (lhs rhs : ScalarExpr) :
    ScalarExprEquiv (.binOp op lhs rhs) (rewriteBinOpStep op lhs rhs) := by
  intro env
  cases op with
  | add =>
    simp only [rewriteBinOpStep]
    by_cases h1 : rhs = .constU64 0
    · subst h1; simp [evalScalarExpr_add_zero_right]
    · rw [if_neg h1]
      by_cases h2 : lhs = .constU64 0
      · subst h2; simp [evalScalarExpr_add_zero_left]
      · rw [if_neg h2]
  | sub =>
    simp only [rewriteBinOpStep]
    by_cases h1 : rhs = .constU64 0
    · subst h1; simp [evalScalarExpr_sub_zero_right]
    · rw [if_neg h1]
  | mul =>
    simp only [rewriteBinOpStep]
    by_cases h1 : rhs = .constU64 1
    · subst h1; simp [evalScalarExpr_mul_one_right]
    · rw [if_neg h1]
      by_cases h2 : lhs = .constU64 1
      · subst h2; simp [evalScalarExpr_mul_one_left]
      · rw [if_neg h2]
        by_cases h3 : rhs = .constU64 2
        · subst h3; simp [evalScalarExpr_mul_two_right]
        · rw [if_neg h3]
          by_cases h4 : rhs = .constU64 4
          · subst h4; simp [evalScalarExpr_mul_four_right]
          · rw [if_neg h4]
            by_cases h5 : rhs = .constU64 8
            · subst h5; simp [evalScalarExpr_mul_eight_right]
            · rw [if_neg h5]
  | bitXor =>
    simp only [rewriteBinOpStep]
    by_cases h1 : rhs = .constU64 0
    · subst h1; simp [evalScalarExpr_xor_zero_right]
    · rw [if_neg h1]
      by_cases h2 : lhs = .constU64 0
      · subst h2; simp [evalScalarExpr_xor_zero_left]
      · rw [if_neg h2]
  | bitAnd =>
    simp only [rewriteBinOpStep]
    by_cases h1 : lhs = rhs
    · subst h1; simp [evalScalarExpr_and_self]
    · rw [if_neg h1]
  | bitOr =>
    simp only [rewriteBinOpStep]
    by_cases h1 : lhs = rhs
    · subst h1; simp [evalScalarExpr_or_self]
    · rw [if_neg h1]
      by_cases h2 : rhs = .constU64 0
      · subst h2; simp [evalScalarExpr_or_zero_right]
      · rw [if_neg h2]
        by_cases h3 : lhs = .constU64 0
        · subst h3; simp [evalScalarExpr_or_zero_left]
        · rw [if_neg h3]
  | div | mod | shl | shr | eq | lt | le =>
    rfl

theorem rewriteSelectStep_sound (cond thenVal elseVal : ScalarExpr) :
    ScalarExprEquiv (.select cond thenVal elseVal) (rewriteSelectStep cond thenVal elseVal) := by
  intro env
  simp only [rewriteSelectStep]
  by_cases h1 : cond = .constBool true
  · subst h1; simp [evalScalarExpr]
  · rw [if_neg h1]
    by_cases h2 : cond = .constBool false
    · subst h2; simp [evalScalarExpr]
    · rw [if_neg h2]

theorem rewriteScalarPeepholeStep_sound (e : ScalarExpr) :
    ScalarExprEquiv e (rewriteScalarPeepholeStep e) := by
  intro env
  cases e with
  | constU64 _ | constBool _ | var _ | unaryOp _ _ => rfl
  | binOp op lhs rhs => exact rewriteBinOpStep_sound op lhs rhs env
  | select cond thenVal elseVal => exact rewriteSelectStep_sound cond thenVal elseVal env
  | fma a b c =>
    simp only [rewriteScalarPeepholeStep, evalScalarExpr]
    cases evalScalarExpr env a <;> cases evalScalarExpr env b <;> rfl

/-- Machine-checked soundness theorem for `rewriteScalarPeephole`:
    recursive algebraic & strength-reduction peephole optimization preserves exact scalar semantics. -/
theorem rewriteScalarPeephole_sound (e : ScalarExpr) :
    ScalarExprEquiv e (rewriteScalarPeephole e) := by
  intro env
  induction e with
  | constU64 _ => rfl
  | constBool _ => rfl
  | var _ => rfl
  | binOp op lhs rhs ihl ihr =>
    simp only [rewriteScalarPeephole]
    rw [← rewriteScalarPeepholeStep_sound (.binOp op (rewriteScalarPeephole lhs) (rewriteScalarPeephole rhs)) env]
    simp only [evalScalarExpr, ← ihl, ← ihr]
  | unaryOp op arg iha =>
    simp only [rewriteScalarPeephole]
    rw [← rewriteScalarPeepholeStep_sound (.unaryOp op (rewriteScalarPeephole arg)) env]
    simp only [evalScalarExpr, ← iha]
  | select cond thenVal elseVal ihc iht ihe =>
    simp only [rewriteScalarPeephole]
    rw [← rewriteScalarPeepholeStep_sound (.select (rewriteScalarPeephole cond) (rewriteScalarPeephole thenVal) (rewriteScalarPeephole elseVal)) env]
    simp only [evalScalarExpr, ← ihc, ← iht, ← ihe]
  | fma a b c iha ihb ihc =>
    simp only [rewriteScalarPeephole]
    rw [← rewriteScalarPeepholeStep_sound (.fma (rewriteScalarPeephole a) (rewriteScalarPeephole b) (rewriteScalarPeephole c)) env]
    simp only [evalScalarExpr, ← iha, ← ihb, ← ihc]

/-- Machine-checked soundness theorem for `rewriteLNIRExpr`:
    rewriting scalar expressions inside `LNIRExpr` refines the original expression. -/
theorem rewriteLNIRExpr_sound (e : LNIRExpr) :
    ExprRefines e (rewriteLNIRExpr e) := by
  cases e with
  | scalar se =>
    simp only [rewriteLNIRExpr]
    exact ExprRefines.of_scalar_equiv (rewriteScalarPeephole_sound se)
  | mkTuple _ | projTuple _ _ | allocCtor _ _ _ | ctorGetObj _ _ | ctorGetScalar _ _ _
  | isExclusive _ | sarrayLen _ | sarrayDataPtr _ _ | sarrayEnsureExclusive _ _
  | sarrayGet _ _ _ | sarraySet _ _ _ _ | rawLoad _ _ _ | boxScalar _ _
  | unboxScalar _ _ | call _ _ _ _ =>
    exact ExprRefines.refl _

/-- Equality form of `rewriteLNIRExpr_sound` (`evalExpr_optimizeExpr_eq`). -/
theorem evalExpr_optimizeExpr_eq (env : VarEnv) (st : HeapState) (e : LNIRExpr) :
    evalExpr env st (rewriteLNIRExpr e) = evalExpr env st e := by
  cases e with
  | scalar se =>
    simp only [rewriteLNIRExpr, evalExpr, ← rewriteScalarPeephole_sound se env]
  | _ => rfl

namespace PeepholeProofs
  abbrev rewriteScalarPeephole_sound := @LeanNative.Proofs.rewriteScalarPeephole_sound
  abbrev rewriteLNIRExpr_sound := @LeanNative.Proofs.rewriteLNIRExpr_sound
  abbrev evalExpr_optimizeExpr_eq := @LeanNative.Proofs.evalExpr_optimizeExpr_eq
end PeepholeProofs

end LeanNative.Proofs
