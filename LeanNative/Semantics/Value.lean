import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.Semantics

open LeanNative.IR

/-- Formal runtime value domain for LNIR operational & denotational evaluation. -/
inductive Val where
  | u64      : UInt64 → Val
  | bool     : Bool → Val
  | tuple    : List Val → Val
  | objPtr   : Nat → Val
  | sarrayId : Nat → Val
  | rawPtrId : Nat → Val
  | unit     : Val
  deriving Repr, Inhabited

namespace Val

mutual
  def beq : Val → Val → Bool
    | .u64 a, .u64 b => a == b
    | .bool a, .bool b => a == b
    | .tuple as, .tuple bs => beqList as bs
    | .objPtr a, .objPtr b => a == b
    | .sarrayId a, .sarrayId b => a == b
    | .rawPtrId a, .rawPtrId b => a == b
    | .unit, .unit => true
    | _, _ => false

  def beqList : List Val → List Val → Bool
    | [], [] => true
    | a :: as, b :: bs => beq a b && beqList as bs
    | _, _ => false
end

instance : BEq Val := ⟨Val.beq⟩

mutual
  theorem beq_refl : ∀ (v : Val), Val.beq v v = true
    | .u64 a => by simp [Val.beq]
    | .bool a => by simp [Val.beq]
    | .tuple as => by simp [Val.beq, beqList_refl as]
    | .objPtr a => by simp [Val.beq]
    | .sarrayId a => by simp [Val.beq]
    | .rawPtrId a => by simp [Val.beq]
    | .unit => rfl

  theorem beqList_refl : ∀ (vs : List Val), Val.beqList vs vs = true
    | [] => rfl
    | v :: vs => by simp [Val.beqList, beq_refl v, beqList_refl vs]
end

@[simp]
theorem beq_self (v : Val) : (v == v) = true :=
  beq_refl v

end Val

/-- Explicit undefined behavior / runtime trap conditions in LNIR semantics. -/
inductive UBError where
  | unboundVar        : VarId → UBError
  | typeError         : String → UBError
  | outOfBounds       : Nat → Nat → UBError
  | nonExclusiveWrite : Nat → UBError
  | divisionByZero    : UBError
  deriving Repr, DecidableEq, Inhabited, BEq

/-- SSA/ANF variable environment mapping `VarId` to optional runtime values. -/
abbrev VarEnv := VarId → Option Val

namespace VarEnv

/-- Empty variable environment where all variables are unbound. -/
def empty : VarEnv := fun _ => none

/-- Bind variable `x` to value `v` in environment `env`. -/
def bind (env : VarEnv) (x : VarId) (v : Val) : VarEnv :=
  fun y => if y == x then some v else env y

@[simp]
theorem bind_apply (env : VarEnv) (x y : VarId) (v : Val) :
    (env.bind x v) y = if y == x then some v else env y := rfl

@[simp]
theorem bind_self (env : VarEnv) (x : VarId) (v : Val) :
    (env.bind x v) x = some v := by
  simp [bind]

theorem bind_ne (env : VarEnv) (x y : VarId) (v : Val) (h : (y == x) = false) :
    (env.bind x v) y = env y := by
  simp [bind, h]

end VarEnv

/-- Model of a contiguous unboxed scalar array (`lean_sarray_object`) in the heap. -/
structure ArrayBuffer where
  id        : Nat
  exclusive : Bool
  data      : Array UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Abstract heap state tracking contiguous scalar array buffers and allocation IDs. -/
structure HeapState where
  buffers : List ArrayBuffer
  nextId  : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

namespace HeapState

def empty : HeapState :=
  { buffers := [], nextId := 0 }

/-- Look up an `ArrayBuffer` by its buffer identifier. -/
def findBuffer (st : HeapState) (bufId : Nat) : Option ArrayBuffer :=
  st.buffers.find? (fun b => b.id == bufId)

/-- Update an existing `ArrayBuffer` in the heap state. -/
def updateBuffer (st : HeapState) (buf : ArrayBuffer) : HeapState :=
  { st with
    buffers := st.buffers.map (fun b => if b.id == buf.id then buf else b) }

/-- Ensure that buffer `bufId` is marked exclusive (`m_rc == 1` / copy-on-write). -/
def ensureExclusive (st : HeapState) (bufId : Nat) : Except UBError HeapState :=
  match st.findBuffer bufId with
  | none => .error (.typeError s!"unknown sarray buffer {bufId}")
  | some _ =>
    .ok { st with
      buffers := st.buffers.map (fun b => if b.id == bufId then { b with exclusive := true } else b) }

/-- Read an element at `idx` from buffer `bufId`. -/
def readElem (st : HeapState) (bufId : Nat) (idx : Nat) : Except UBError UInt64 :=
  match st.findBuffer bufId with
  | none => .error (.typeError s!"unknown sarray buffer {bufId}")
  | some buf =>
    if h : idx < buf.data.size then
      .ok buf.data[idx]
    else
      .error (.outOfBounds idx buf.data.size)

/-- Write an element in-place at `idx` in buffer `bufId`, requiring `exclusive == true`. -/
def writeElemExclusive (st : HeapState) (bufId : Nat) (idx : Nat) (val : UInt64) : Except UBError HeapState :=
  match st.findBuffer bufId with
  | none => .error (.typeError s!"unknown sarray buffer {bufId}")
  | some buf =>
    if !buf.exclusive then
      .error (.nonExclusiveWrite bufId)
    else if _h : idx < buf.data.size then
      .ok { st with
        buffers := st.buffers.map (fun b => if b.id == bufId then { b with data := b.data.set! idx val } else b) }
    else
      .error (.outOfBounds idx buf.data.size)

end HeapState

end LeanNative.Semantics
