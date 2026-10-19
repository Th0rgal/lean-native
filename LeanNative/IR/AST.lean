import LeanNative.IR.Types

namespace LeanNative.IR

/-- Binary arithmetic, bitwise, comparison, and checked 256-bit EVM operators in LNIR. -/
inductive BinOp where
  | add
  | sub
  | mul
  | div
  | mod
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | sar            -- Arithmetic shift right (64-bit / 256-bit EVM SAR)
  | eq
  | lt
  | le
  | addChecked256  -- 256-bit checked addition (traps/errors on overflow >= 2^256)
  | subChecked256  -- 256-bit checked subtraction (traps/errors on underflow < 0)
  | mulChecked256  -- 256-bit checked multiplication (traps/errors on overflow >= 2^256)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Unary operators in LNIR. -/
inductive UnaryOp where
  | not
  | neg
  | clz256         -- 256-bit count leading zeros (EVM/Verity CLZ256)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Pure / scalar SSA expression in LNIR (verified core fragment). -/
inductive ScalarExpr where
  | constU64 (val : UInt64)
  | constBool (val : Bool)
  | var (id : VarId)
  | binOp (op : BinOp) (lhs rhs : ScalarExpr)
  | unaryOp (op : UnaryOp) (arg : ScalarExpr)
  | select (cond thenVal elseVal : ScalarExpr)
  | fma (a b c : ScalarExpr) -- a * b + c
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Data-parallel kernel pattern for GPU (MLIR/NVVM/PTX) and CPU SIMD lowering. -/
inductive ParallelKernelKind where
  | mapScaleAdd (scale : UInt64) (bias : UInt64)  -- out[i] = in0[i] * scale + bias
  | zipAdd                                        -- out[i] = in0[i] + in1[i]
  | zipMul                                        -- out[i] = in0[i] * in1[i]
  | saxpy (alphaBits : UInt64)                    -- out[i] = alpha * x[i] + y[i]
  | dotProduct                                    -- sum_i (in0[i] * in1[i])
  | stencil1D3Pt (wLeft wCenter wRight : UInt64)  -- 3-point 1D stencil
  | customScalar (idxVar : VarId) (inVars : List VarId) (body : ScalarExpr)
  deriving Repr, Inhabited, BEq

/-- Right-hand side of a let-binding in LNIR (including 256-bit EVM words and Storage Maps). -/
inductive LNIRExpr where
  | scalar (e : ScalarExpr)
  | constU256 (val : UInt256)
  | mulDivDown (aVar : VarId) (bVar : VarId) (denomVar : VarId)
  | mulDivUp (aVar : VarId) (bVar : VarId) (denomVar : VarId)
  | storageLoad (mapVar : VarId) (slotVar : VarId)
  | storageStore (mapVar : VarId) (slotVar : VarId) (valVar : VarId)
  | mkTuple (fields : List VarId)
  | projTuple (tupleVar : VarId) (idx : Nat)
  | allocCtor (tag : Nat) (objFields : List VarId) (scalarFields : List VarId)
  | ctorGetObj (ctorVar : VarId) (idx : Nat)
  | ctorGetScalar (ctorVar : VarId) (idx : Nat) (ty : LNIRType)
  | isExclusive (objVar : VarId)
  | sarrayLen (arrVar : VarId)
  | sarrayDataPtr (arrVar : VarId) (elemTy : LNIRType)
  | sarrayEnsureExclusive (arrVar : VarId) (elemTy : LNIRType)
  | sarrayGet (arrVar : VarId) (idxVar : VarId) (elemTy : LNIRType)
  | sarraySet (arrVar : VarId) (idxVar : VarId) (valVar : VarId) (elemTy : LNIRType)
  | rawLoad (ptrVar : VarId) (idxVar : VarId) (elemTy : LNIRType)
  | boxScalar (valVar : VarId) (ty : LNIRType)
  | unboxScalar (boxVar : VarId) (ty : LNIRType)
  | call (fnName : String) (args : List VarId) (retTy : LNIRType) (isExtern : Bool := false)
  deriving Repr, Inhabited, BEq

/-- Parameter in an LNIR function or join point. -/
structure LNIRParam where
  id     : VarId
  name   : String
  ty     : LNIRType
  borrow : Bool := false
  deriving Repr, Inhabited, BEq

/-- Structured ANF / SSA code block in LNIR. -/
inductive LNIRCode where
  | letBind (dst : VarId) (ty : LNIRType) (val : LNIRExpr) (k : LNIRCode)
  | rawStore (ptrVar : VarId) (idxVar : VarId) (valVar : VarId) (elemTy : LNIRType) (k : LNIRCode)
  | incRef (objVar : VarId) (count : Nat) (k : LNIRCode)
  | decRef (objVar : VarId) (count : Nat) (k : LNIRCode)
  | ite (condVar : VarId) (thenBranch : LNIRCode) (elseBranch : LNIRCode)
  | seqFor (idxVar : VarId) (loVar hiVar : VarId) (accVar : VarId) (accInit : VarId)
      (accTy : LNIRType) (stepBody : LNIRCode) (k : LNIRCode)
  | parFor (outVar : VarId) (lenVar : VarId) (inputs : List VarId) (elemTy : LNIRType)
      (kernel : ParallelKernelKind) (k : LNIRCode)
  | ret (var : VarId)
  | unreachable
  deriving Repr, Inhabited, BEq

/-- Top-level function declaration in LNIR. -/
structure LNIRDecl where
  name       : String
  params     : List LNIRParam
  retTy      : LNIRType
  body       : LNIRCode
  assurance  : AssuranceLevel := .verifiedKernelProof
  isGpuCand  : Bool := false
  deriving Repr, Inhabited, BEq

/-- Complete compilation module in LNIR. -/
structure LNIRModule where
  moduleName : String
  decls      : List LNIRDecl
  deriving Repr, Inhabited, BEq

/-- Deterministic FNV-1a 64-bit structural fingerprint of an LNIR declaration for translation validation certificates. -/
def hashStringFNV64 (s : String) : String :=
  let prime : UInt64 := 1099511628211
  let offset : UInt64 := 14695981039346656037
  let h := s.toUTF8.foldl (fun acc b => (acc ^^^ b.toUInt64) * prime) offset
  let hexChars := "0123456789abcdef".toList
  let rec toHex (n : Nat) (val : UInt64) (acc : List Char) : String :=
    match n with
    | 0 => String.ofList acc
    | n' + 1 =>
      let nib := (val &&& 0xf).toNat
      let c := hexChars[nib]?.getD '0'
      toHex n' (val >>> 4) (c :: acc)
  toHex 16 h []

def LNIRDecl.structuralHash (d : LNIRDecl) : String :=
  hashStringFNV64 (reprStr d)

end LeanNative.IR
