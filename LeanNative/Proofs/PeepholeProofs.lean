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

theorem uint64_mul_sixteen (a : UInt64) : a * (16 : UInt64) = a <<< (4 : UInt64) := by
  cases a with
  | ofBitVec bv =>
    apply congrArg UInt64.ofBitVec
    change bv * 16#64 = bv <<< (4#64).toNat
    have h1 : (4#64).toNat = 4 := rfl
    rw [h1, BitVec.shiftLeft_eq_mul_twoPow]
    rfl

theorem uint64_mul_thirtytwo (a : UInt64) : a * (32 : UInt64) = a <<< (5 : UInt64) := by
  cases a with
  | ofBitVec bv =>
    apply congrArg UInt64.ofBitVec
    change bv * 32#64 = bv <<< (5#64).toNat
    have h1 : (5#64).toNat = 5 := rfl
    rw [h1, BitVec.shiftLeft_eq_mul_twoPow]
    rfl

theorem uint64_two_mul (a : UInt64) : (2 : UInt64) * a = a <<< (1 : UInt64) := by
  rw [UInt64.mul_comm, uint64_mul_two]

theorem uint64_four_mul (a : UInt64) : (4 : UInt64) * a = a <<< (2 : UInt64) := by
  rw [UInt64.mul_comm, uint64_mul_four]

theorem uint64_eight_mul (a : UInt64) : (8 : UInt64) * a = a <<< (3 : UInt64) := by
  rw [UInt64.mul_comm, uint64_mul_eight]

theorem uint64_div_two (a : UInt64) : a / (2 : UInt64) = a >>> (1 : UInt64) := by
  cases a with
  | ofBitVec bv =>
    rcases bv with ⟨n, hn⟩
    apply congrArg UInt64.ofBitVec
    apply BitVec.eq_of_toNat_eq
    change n / 2 = n >>> 1
    rw [Nat.shiftRight_eq_div_pow]

theorem uint64_div_four (a : UInt64) : a / (4 : UInt64) = a >>> (2 : UInt64) := by
  cases a with
  | ofBitVec bv =>
    rcases bv with ⟨n, hn⟩
    apply congrArg UInt64.ofBitVec
    apply BitVec.eq_of_toNat_eq
    change n / 4 = n >>> 2
    rw [Nat.shiftRight_eq_div_pow]

theorem uint64_div_eight (a : UInt64) : a / (8 : UInt64) = a >>> (3 : UInt64) := by
  cases a with
  | ofBitVec bv =>
    rcases bv with ⟨n, hn⟩
    apply congrArg UInt64.ofBitVec
    apply BitVec.eq_of_toNat_eq
    change n / 8 = n >>> 3
    rw [Nat.shiftRight_eq_div_pow]

theorem uint64_add_self_shl_one (a : UInt64) : a + a = a <<< (1 : UInt64) := by
  rw [← uint64_mul_two]
  cases a with
  | ofBitVec bv =>
    apply congrArg UInt64.ofBitVec
    change bv + bv = bv * 2#64
    rw [BitVec.mul_two]

theorem uint64_add_assoc_const (a c1 c2 : UInt64) : (a + c1) + c2 = a + (c1 + c2) :=
  UInt64.add_assoc a c1 c2

theorem uint64_and_mask_coalesce (a m1 m2 : UInt64) : (a &&& m1) &&& m2 = a &&& (m1 &&& m2) := by
  cases a with | ofBitVec bva =>
  cases m1 with | ofBitVec bvm1 =>
  cases m2 with | ofBitVec bvm2 =>
    apply congrArg UInt64.ofBitVec
    exact BitVec.and_assoc bva bvm1 bvm2

theorem uint64_or_mask_coalesce (a m1 m2 : UInt64) : (a ||| m1) ||| m2 = a ||| (m1 ||| m2) := by
  cases a with | ofBitVec bva =>
  cases m1 with | ofBitVec bvm1 =>
  cases m2 with | ofBitVec bvm2 =>
    apply congrArg UInt64.ofBitVec
    exact BitVec.or_assoc bva bvm1 bvm2

theorem uint64_xor_mask_coalesce (a m1 m2 : UInt64) : (a ^^^ m1) ^^^ m2 = a ^^^ (m1 ^^^ m2) := by
  cases a with | ofBitVec bva =>
  cases m1 with | ofBitVec bvm1 =>
  cases m2 with | ofBitVec bvm2 =>
    apply congrArg UInt64.ofBitVec
    exact BitVec.xor_assoc bva bvm1 bvm2

theorem uint64_mul_add_distrib_const (a b c : UInt64) : a * b + a * c = a * (b + c) := by
  cases a with | ofBitVec bva =>
  cases b with | ofBitVec bvb =>
  cases c with | ofBitVec bvc =>
    apply congrArg UInt64.ofBitVec
    exact BitVec.mul_add.symm

/-! ## Semantic Lemmas for `evalBinOp` -/

@[simp]
theorem evalBinOp_add_zero (v : Val) : evalBinOp .add v (.u64 0) = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_zero_add (v : Val) : evalBinOp .add (.u64 0) v = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_sub_zero (v : Val) : evalBinOp .sub v (.u64 0) = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_mul_one (v : Val) : evalBinOp .mul v (.u64 1) = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_one_mul (v : Val) : evalBinOp .mul (.u64 1) v = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_xor_zero (v : Val) : evalBinOp .bitXor v (.u64 0) = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_zero_xor (v : Val) : evalBinOp .bitXor (.u64 0) v = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_or_zero (v : Val) : evalBinOp .bitOr v (.u64 0) = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_zero_or (v : Val) : evalBinOp .bitOr (.u64 0) v = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_and_self (v : Val) : evalBinOp .bitAnd v v = .ok v := by
  unfold evalBinOp; cases v <;> simp [Val.beq_self]

@[simp]
theorem evalBinOp_or_self (v : Val) : evalBinOp .bitOr v v = .ok v := by
  unfold evalBinOp; cases v <;> simp [Val.beq_self]

theorem evalBinOp_mul_two (v : Val) :
    evalBinOp .mul v (.u64 2) = evalBinOp .shl v (.u64 1) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_mul_two]
  | _ => rfl

theorem evalBinOp_mul_four (v : Val) :
    evalBinOp .mul v (.u64 4) = evalBinOp .shl v (.u64 2) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_mul_four]
  | _ => rfl

theorem evalBinOp_mul_eight (v : Val) :
    evalBinOp .mul v (.u64 8) = evalBinOp .shl v (.u64 3) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_mul_eight]
  | _ => rfl

theorem evalBinOp_mul_sixteen (v : Val) :
    evalBinOp .mul v (.u64 16) = evalBinOp .shl v (.u64 4) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_mul_sixteen]
  | _ => rfl

theorem evalBinOp_mul_thirtytwo (v : Val) :
    evalBinOp .mul v (.u64 32) = evalBinOp .shl v (.u64 5) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_mul_thirtytwo]
  | _ => rfl

theorem evalBinOp_two_mul (v : Val) :
    evalBinOp .mul (.u64 2) v = evalBinOp .shl v (.u64 1) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_two_mul]
  | _ => rfl

theorem evalBinOp_four_mul (v : Val) :
    evalBinOp .mul (.u64 4) v = evalBinOp .shl v (.u64 2) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_four_mul]
  | _ => rfl

theorem evalBinOp_eight_mul (v : Val) :
    evalBinOp .mul (.u64 8) v = evalBinOp .shl v (.u64 3) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_eight_mul]
  | _ => rfl

@[simp]
theorem evalBinOp_div_one (v : Val) : evalBinOp .div v (.u64 1) = .ok v := by
  unfold evalBinOp; cases v <;> simp

theorem evalBinOp_div_two (v : Val) :
    evalBinOp .div v (.u64 2) = evalBinOp .shr v (.u64 1) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_div_two]
  | _ => rfl

theorem evalBinOp_div_four (v : Val) :
    evalBinOp .div v (.u64 4) = evalBinOp .shr v (.u64 2) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_div_four]
  | _ => rfl

theorem evalBinOp_div_eight (v : Val) :
    evalBinOp .div v (.u64 8) = evalBinOp .shr v (.u64 3) := by
  unfold evalBinOp
  cases v with
  | u64 a => simp [uint64_div_eight]
  | _ => rfl

@[simp]
theorem evalBinOp_shl_zero (v : Val) : evalBinOp .shl v (.u64 0) = .ok v := by
  unfold evalBinOp; cases v <;> simp

@[simp]
theorem evalBinOp_shr_zero (v : Val) : evalBinOp .shr v (.u64 0) = .ok v := by
  unfold evalBinOp; cases v <;> simp

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
    else if rhs = .constU64 16 then .binOp .shl lhs (.constU64 4)
    else if rhs = .constU64 32 then .binOp .shl lhs (.constU64 5)
    else if lhs = .constU64 2 then .binOp .shl rhs (.constU64 1)
    else if lhs = .constU64 4 then .binOp .shl rhs (.constU64 2)
    else if lhs = .constU64 8 then .binOp .shl rhs (.constU64 3)
    else .binOp .mul lhs rhs
  | .div =>
    if rhs = .constU64 1 then lhs
    else if rhs = .constU64 2 then .binOp .shr lhs (.constU64 1)
    else if rhs = .constU64 4 then .binOp .shr lhs (.constU64 2)
    else if rhs = .constU64 8 then .binOp .shr lhs (.constU64 3)
    else .binOp .div lhs rhs
  | .shl =>
    if rhs = .constU64 0 then lhs
    else .binOp .shl lhs rhs
  | .shr =>
    if rhs = .constU64 0 then lhs
    else .binOp .shr lhs rhs
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

theorem evalScalarExpr_mul_sixteen_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul lhs (.constU64 16)) =
    evalScalarExpr env (.binOp .shl lhs (.constU64 4)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_mul_sixteen v

theorem evalScalarExpr_mul_thirtytwo_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul lhs (.constU64 32)) =
    evalScalarExpr env (.binOp .shl lhs (.constU64 5)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_mul_thirtytwo v

theorem evalScalarExpr_mul_two_left (env : VarEnv) (rhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul (.constU64 2) rhs) =
    evalScalarExpr env (.binOp .shl rhs (.constU64 1)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env rhs with
  | error err => rfl
  | ok v => exact evalBinOp_two_mul v

theorem evalScalarExpr_mul_four_left (env : VarEnv) (rhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul (.constU64 4) rhs) =
    evalScalarExpr env (.binOp .shl rhs (.constU64 2)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env rhs with
  | error err => rfl
  | ok v => exact evalBinOp_four_mul v

theorem evalScalarExpr_mul_eight_left (env : VarEnv) (rhs : ScalarExpr) :
    evalScalarExpr env (.binOp .mul (.constU64 8) rhs) =
    evalScalarExpr env (.binOp .shl rhs (.constU64 3)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env rhs with
  | error err => rfl
  | ok v => exact evalBinOp_eight_mul v

theorem evalScalarExpr_div_one_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .div lhs (.constU64 1)) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_div_one v

theorem evalScalarExpr_div_two_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .div lhs (.constU64 2)) =
    evalScalarExpr env (.binOp .shr lhs (.constU64 1)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_div_two v

theorem evalScalarExpr_div_four_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .div lhs (.constU64 4)) =
    evalScalarExpr env (.binOp .shr lhs (.constU64 2)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_div_four v

theorem evalScalarExpr_div_eight_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .div lhs (.constU64 8)) =
    evalScalarExpr env (.binOp .shr lhs (.constU64 3)) := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_div_eight v

theorem evalScalarExpr_shl_zero_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .shl lhs (.constU64 0)) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_shl_zero v

theorem evalScalarExpr_shr_zero_right (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp .shr lhs (.constU64 0)) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]
  cases evalScalarExpr env lhs with
  | error err => rfl
  | ok v => exact evalBinOp_shr_zero v

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
              by_cases h6 : rhs = .constU64 16
              · subst h6; simp [evalScalarExpr_mul_sixteen_right]
              · rw [if_neg h6]
                by_cases h7 : rhs = .constU64 32
                · subst h7; simp [evalScalarExpr_mul_thirtytwo_right]
                · rw [if_neg h7]
                  by_cases h8 : lhs = .constU64 2
                  · subst h8; simp [evalScalarExpr_mul_two_left]
                  · rw [if_neg h8]
                    by_cases h9 : lhs = .constU64 4
                    · subst h9; simp [evalScalarExpr_mul_four_left]
                    · rw [if_neg h9]
                      by_cases h10 : lhs = .constU64 8
                      · subst h10; simp [evalScalarExpr_mul_eight_left]
                      · rw [if_neg h10]
  | div =>
    simp only [rewriteBinOpStep]
    by_cases h1 : rhs = .constU64 1
    · subst h1; simp [evalScalarExpr_div_one_right]
    · rw [if_neg h1]
      by_cases h2 : rhs = .constU64 2
      · subst h2; simp [evalScalarExpr_div_two_right]
      · rw [if_neg h2]
        by_cases h3 : rhs = .constU64 4
        · subst h3; simp [evalScalarExpr_div_four_right]
        · rw [if_neg h3]
          by_cases h4 : rhs = .constU64 8
          · subst h4; simp [evalScalarExpr_div_eight_right]
          · rw [if_neg h4]
  | shl =>
    simp only [rewriteBinOpStep]
    by_cases h1 : rhs = .constU64 0
    · subst h1; simp [evalScalarExpr_shl_zero_right]
    · rw [if_neg h1]
  | shr =>
    simp only [rewriteBinOpStep]
    by_cases h1 : rhs = .constU64 0
    · subst h1; simp [evalScalarExpr_shr_zero_right]
    · rw [if_neg h1]
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
  | mod | sar | eq | lt | le | addChecked256 | subChecked256 | mulChecked256 =>
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
  | constU256 _ | mulDivDown _ _ _ | mulDivUp _ _ _ | storageLoad _ _ | storageStore _ _ _
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

/-- Recursive verified code-level peephole optimizer on `LNIRCode`.
    Applies `rewriteLNIRExpr` to every `.letBind` and recurses through `.rawStore`,
    `.incRef`, `.decRef`, `.ite`, `.seqFor`, `.parFor`, `.ret`, and `.unreachable`. -/
def rewriteCodePeephole : LNIRCode → LNIRCode
  | .letBind dst ty val k =>
    .letBind dst ty (rewriteLNIRExpr val) (rewriteCodePeephole k)
  | .rawStore ptrVar idxVar valVar elemTy k =>
    .rawStore ptrVar idxVar valVar elemTy (rewriteCodePeephole k)
  | .incRef objVar count k =>
    .incRef objVar count (rewriteCodePeephole k)
  | .decRef objVar count k =>
    .decRef objVar count (rewriteCodePeephole k)
  | .ite condVar thenBranch elseBranch =>
    .ite condVar (rewriteCodePeephole thenBranch) (rewriteCodePeephole elseBranch)
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    .seqFor idxVar loVar hiVar accVar accInit accTy (rewriteCodePeephole stepBody) (rewriteCodePeephole k)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    .parFor outVar lenVar inputs elemTy kernel (rewriteCodePeephole k)
  | .ret v => .ret v
  | .unreachable => .unreachable

/-- Exact operational evaluation equality for recursive `rewriteCodePeephole` across `LNIRCode`. -/
theorem evalCode_rewriteCodePeephole_eq (c : LNIRCode) :
    ∀ (fuel : Nat) (env : VarEnv) (st : HeapState),
      evalCode fuel env st (rewriteCodePeephole c) = evalCode fuel env st c := by
  induction c with
  | letBind dst ty val k ih =>
    intro fuel env st
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      simp only [rewriteCodePeephole, evalCode, evalExpr_optimizeExpr_eq]
      cases evalExpr env st val with
      | error err => rfl
      | ok pair => exact ih fuel' (env.bind dst pair.1) pair.2
  | rawStore ptrVar idxVar valVar elemTy k ih =>
    intro fuel env st
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      simp only [rewriteCodePeephole, evalCode]
      cases env ptrVar with
      | none => rfl
      | some pval =>
        cases env idxVar with
        | none => cases pval <;> rfl
        | some ival =>
          cases env valVar with
          | none => cases pval <;> cases ival <;> rfl
          | some vval =>
            cases pval <;> cases ival <;> cases vval <;> try rfl
            all_goals
              simp only
              cases st.writeElemExclusive _ _ _ with
              | error err => rfl
              | ok st1 => exact ih fuel' env st1
  | incRef objVar count k ih =>
    intro fuel env st
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      simp only [rewriteCodePeephole, evalCode]
      exact ih fuel' env st
  | decRef objVar count k ih =>
    intro fuel env st
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      simp only [rewriteCodePeephole, evalCode]
      exact ih fuel' env st
  | ite condVar thenBranch elseBranch iht ihe =>
    intro fuel env st
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      simp only [rewriteCodePeephole, evalCode]
      cases env condVar with
      | none => rfl
      | some cval =>
        cases cval with
        | bool b =>
          cases b with
          | true => exact iht fuel' env st
          | false => exact ihe fuel' env st
        | u64 n =>
          simp only
          by_cases hn : (n != 0) = true
          · rw [if_pos hn, if_pos hn]; exact iht fuel' env st
          · rw [if_neg hn, if_neg hn]; exact ihe fuel' env st
        | u256 w =>
          simp only
          by_cases hw : (w != UInt256.zero) = true
          · rw [if_pos hw, if_pos hw]; exact iht fuel' env st
          · rw [if_neg hw, if_neg hw]; exact ihe fuel' env st
        | _ => rfl
  | seqFor idxVar loVar hiVar accVar accInit accTy stepBody k ihs ihk =>
    intro fuel env st
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      simp only [rewriteCodePeephole, evalCode]
      have hstep : (fun stepEnv stepSt => evalCode fuel' stepEnv stepSt (rewriteCodePeephole stepBody)) =
                   (fun stepEnv stepSt => evalCode fuel' stepEnv stepSt stepBody) := by
        funext stepEnv stepSt
        exact ihs fuel' stepEnv stepSt
      rw [hstep]
      cases env loVar with
      | none => rfl
      | some loval =>
        cases env hiVar with
        | none => cases loval <;> rfl
        | some hival =>
          cases env accInit with
          | none => cases loval <;> cases hival <;> rfl
          | some initVal =>
            cases loval <;> cases hival <;> try rfl
            simp only
            cases evalSeqLoop _ _ idxVar accVar initVal env st (fun stepEnv stepSt => evalCode fuel' stepEnv stepSt stepBody) with
            | error err => rfl
            | ok pair => exact ihk fuel' (env.bind accVar pair.1) pair.2
  | parFor outVar lenVar inputs elemTy kernel k ih =>
    intro fuel env st
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      simp only [rewriteCodePeephole, evalCode]
      exact ih fuel' (env.bind outVar (.sarrayId 0)) st
  | ret v =>
    intro fuel env st
    cases fuel <;> rfl
  | unreachable =>
    intro fuel env st
    cases fuel <;> rfl

/-- End-to-end recursive `LNIRCode` pass refinement theorem (`rewriteCodePeephole_refines`):
    applying `rewriteCodePeephole` across an entire `LNIRCode` block refines the original code. -/
theorem rewriteCodePeephole_refines (c : LNIRCode) :
    CodeRefines c (rewriteCodePeephole c) := by
  intro fuel env st v st' hsrc
  rw [evalCode_rewriteCodePeephole_eq c fuel env st]
  exact hsrc

/-! ## 256-Bit (`UInt256` / `EVMWord`) & EVM Storage Map Soundness Theorems -/

theorem evalBinOp_u256_and_self (w : UInt256) :
    evalBinOp .bitAnd (.u256 w) (.u256 w) = .ok (.u256 w) := by
  unfold evalBinOp; simp

theorem evalBinOp_u256_or_self (w : UInt256) :
    evalBinOp .bitOr (.u256 w) (.u256 w) = .ok (.u256 w) := by
  unfold evalBinOp; simp

theorem evalBinOp_u256_xor_zero (w : UInt256) :
    evalBinOp .bitXor (.u256 w) (.u256 UInt256.zero) = .ok (.u256 w) := by
  unfold evalBinOp; simp

theorem evalBinOp_u256_or_zero (w : UInt256) :
    evalBinOp .bitOr (.u256 w) (.u256 UInt256.zero) = .ok (.u256 w) := by
  unfold evalBinOp; simp

/-- EVM `SLOAD` after `SSTORE` to the same 256-bit slot returns the stored `UInt256` value (`storageStore_load_same_sound`). -/
theorem storageStore_load_same_sound (env : VarEnv) (st : HeapState)
    (mapVar slotVar valVar : VarId) (mapId : Nat) (slot val : UInt256)
    (hmap : env mapVar = some (.storageMapId mapId))
    (hslot : env slotVar = some (.u256 slot))
    (hval : env valVar = some (.u256 val)) :
    (match evalExpr env st (.storageStore mapVar slotVar valVar) with
     | .ok (_, st1) => evalExpr env st1 (.storageLoad mapVar slotVar)
     | .error err => .error err) =
    .ok (.u256 val, st.storageStore mapId slot val) := by
  unfold evalExpr
  simp [Val.toU256?, hmap, hslot, hval]

/-- EVM `SLOAD` after `SSTORE` to a distinct 256-bit slot preserves the prior slot value (`storageStore_load_ne_sound`). -/
theorem storageStore_load_ne_sound (env : VarEnv) (st : HeapState)
    (mapVar slot1Var slot2Var valVar : VarId) (mapId : Nat) (slot1 slot2 val : UInt256)
    (hmap : env mapVar = some (.storageMapId mapId))
    (hslot1 : env slot1Var = some (.u256 slot1))
    (hslot2 : env slot2Var = some (.u256 slot2))
    (hval : env valVar = some (.u256 val))
    (hne : (slot1 == slot2) = false) :
    (match evalExpr env st (.storageStore mapVar slot1Var valVar) with
     | .ok (_, st1) => evalExpr env st1 (.storageLoad mapVar slot2Var)
     | .error err => .error err) =
    .ok (.u256 (st.storageLoad mapId slot2), st.storageStore mapId slot1 val) := by
  unfold evalExpr
  simp [Val.toU256?, hmap, hslot1, hslot2, hval, HeapState.storageLoad_after_storageStore_ne st mapId slot1 slot2 val hne]

/-! ## Verified Binary Constant Folding (`rewriteConstFoldBinOp`) -/

theorem uint64_and_63_mod_64 (b : UInt64) : (b &&& 63).mod 64 = b.mod 64 := by
  cases b with
  | ofBitVec bv =>
    rcases bv with ⟨n, hn⟩
    apply congrArg UInt64.ofBitVec
    apply BitVec.eq_of_toNat_eq
    change (n &&& (2 ^ 6 - 1)) % 64 = n % 64
    rw [Nat.and_two_pow_sub_one_eq_mod n 6]
    exact Nat.mod_mod n 64

@[simp]
theorem uint64_shiftLeft_and_63 (a b : UInt64) : a <<< (b &&& 63) = a <<< b := by
  change UInt64.shiftLeft a (b &&& 63) = UInt64.shiftLeft a b
  unfold UInt64.shiftLeft
  rw [uint64_and_63_mod_64]

@[simp]
theorem uint64_shiftRight_and_63 (a b : UInt64) : a >>> (b &&& 63) = a >>> b := by
  change UInt64.shiftRight a (b &&& 63) = UInt64.shiftRight a b
  unfold UInt64.shiftRight
  rw [uint64_and_63_mod_64]

/-- Verified binary constant folding on `UInt64` scalar literals. -/
def rewriteConstFoldBinOp (op : BinOp) (a b : UInt64) : ScalarExpr :=
  match op with
  | .add => .constU64 (a + b)
  | .sub => .constU64 (a - b)
  | .mul => .constU64 (a * b)
  | .bitAnd => .constU64 (a &&& b)
  | .bitOr => .constU64 (a ||| b)
  | .bitXor => .constU64 (a ^^^ b)
  | .shl => .constU64 (a <<< (b &&& 63))
  | .shr => .constU64 (a >>> (b &&& 63))
  | .eq => .constBool (a == b)
  | .lt => .constBool (a < b)
  | .le => .constBool (a ≤ b)
  | other => .binOp other (.constU64 a) (.constU64 b)

/-- Machine-checked soundness theorem for `rewriteConstFoldBinOp`:
    constant folding on `UInt64` binary operations preserves exact scalar evaluation semantics. -/
theorem evalBinOp_const_fold_sound (op : BinOp) (a b : UInt64) (env : VarEnv) :
    evalScalarExpr env (rewriteConstFoldBinOp op a b) =
    evalScalarExpr env (.binOp op (.constU64 a) (.constU64 b)) := by
  cases op <;> unfold rewriteConstFoldBinOp evalScalarExpr evalBinOp <;> try (unfold evalScalarExpr; simp)

/-- Single-step verified constant-folding wrapper on `ScalarExpr`. -/
def rewriteConstFoldStep : ScalarExpr → ScalarExpr
  | .binOp op (.constU64 a) (.constU64 b) => rewriteConstFoldBinOp op a b
  | other => other

theorem rewriteConstFoldStep_sound (e : ScalarExpr) :
    ScalarExprEquiv e (rewriteConstFoldStep e) := by
  intro env
  cases e with
  | binOp op lhs rhs =>
    cases lhs <;> cases rhs <;> try rfl
    case constU64.constU64 a b =>
      simp only [rewriteConstFoldStep]
      exact (evalBinOp_const_fold_sound op a b env).symm
  | _ => rfl

/-- Composed verified scalar peephole + binary constant-folding rewriter. -/
def rewriteScalarVerified (e : ScalarExpr) : ScalarExpr :=
  rewriteConstFoldStep (rewriteScalarPeephole e)

/-- Machine-checked soundness theorem for `rewriteScalarVerified`. -/
theorem rewriteScalarVerified_sound (e : ScalarExpr) :
    ScalarExprEquiv e (rewriteScalarVerified e) :=
  ScalarExprEquiv.trans
    (rewriteScalarPeephole_sound e)
    (rewriteConstFoldStep_sound (rewriteScalarPeephole e))

namespace PeepholeProofs
  abbrev rewriteScalarPeephole_sound := @LeanNative.Proofs.rewriteScalarPeephole_sound
  abbrev rewriteLNIRExpr_sound := @LeanNative.Proofs.rewriteLNIRExpr_sound
  abbrev evalExpr_optimizeExpr_eq := @LeanNative.Proofs.evalExpr_optimizeExpr_eq
  abbrev evalCode_rewriteCodePeephole_eq := @LeanNative.Proofs.evalCode_rewriteCodePeephole_eq
  abbrev rewriteCodePeephole_refines := @LeanNative.Proofs.rewriteCodePeephole_refines
  abbrev evalBinOp_u256_and_self := @LeanNative.Proofs.evalBinOp_u256_and_self
  abbrev evalBinOp_u256_or_self := @LeanNative.Proofs.evalBinOp_u256_or_self
  abbrev evalBinOp_u256_xor_zero := @LeanNative.Proofs.evalBinOp_u256_xor_zero
  abbrev evalBinOp_u256_or_zero := @LeanNative.Proofs.evalBinOp_u256_or_zero
  abbrev storageStore_load_same_sound := @LeanNative.Proofs.storageStore_load_same_sound
  abbrev storageStore_load_ne_sound := @LeanNative.Proofs.storageStore_load_ne_sound
  abbrev evalBinOp_const_fold_sound := @LeanNative.Proofs.evalBinOp_const_fold_sound
  abbrev rewriteConstFoldStep_sound := @LeanNative.Proofs.rewriteConstFoldStep_sound
  abbrev rewriteScalarVerified_sound := @LeanNative.Proofs.rewriteScalarVerified_sound
end PeepholeProofs

end LeanNative.Proofs

