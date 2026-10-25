import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.Semantics

open LeanNative.IR

/-- Formal runtime value domain for LNIR operational & denotational evaluation
    (including 256-bit `UInt256` EVM words and `storageMapId` persistent storage maps). -/
inductive Val where
  | u64          : UInt64 → Val
  | u256         : UInt256 → Val
  | bool         : Bool → Val
  | tuple        : List Val → Val
  | objPtr       : Nat → Val
  | sarrayId     : Nat → Val
  | rawPtrId     : Nat → Val
  | storageMapId : Nat → Val
  | unit         : Val
  deriving Repr, Inhabited

namespace Val

mutual
  def beq : Val → Val → Bool
    | .u64 a, .u64 b => a == b
    | .u256 a, .u256 b => a == b
    | .bool a, .bool b => a == b
    | .tuple as, .tuple bs => beqList as bs
    | .objPtr a, .objPtr b => a == b
    | .sarrayId a, .sarrayId b => a == b
    | .rawPtrId a, .rawPtrId b => a == b
    | .storageMapId a, .storageMapId b => a == b
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
    | .u256 a => by simp [Val.beq]
    | .bool a => by simp [Val.beq]
    | .tuple as => by simp [Val.beq, beqList_refl as]
    | .objPtr a => by simp [Val.beq]
    | .sarrayId a => by simp [Val.beq]
    | .rawPtrId a => by simp [Val.beq]
    | .storageMapId a => by simp [Val.beq]
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
  | unboundVar         : VarId → UBError
  | typeError          : String → UBError
  | outOfBounds        : Nat → Nat → UBError
  | nonExclusiveWrite  : Nat → UBError
  | divisionByZero     : UBError
  | arithmeticOverflow : String → UBError
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

/-- Model of a 256-bit EVM/Verity persistent key-value storage map (`uint256 -> uint256`).
    Uninitialized slots default to `UInt256.zero` per EVM SLOAD semantics. -/
structure StorageMapBuffer where
  id      : Nat
  entries : List (UInt256 × UInt256) := []
  deriving Repr, DecidableEq, Inhabited, BEq

namespace StorageMapBuffer

def lookupSlot (m : StorageMapBuffer) (slot : UInt256) : UInt256 :=
  match m.entries.find? (fun (k, _) => k == slot) with
  | some (_, v) => v
  | none => UInt256.zero

def writeSlot (m : StorageMapBuffer) (slot val : UInt256) : StorageMapBuffer :=
  { m with entries := (slot, val) :: m.entries.filter (fun (k, _) => k != slot) }

@[simp]
theorem lookupSlot_writeSlot_same (m : StorageMapBuffer) (slot val : UInt256) :
    (m.writeSlot slot val).lookupSlot slot = val := by
  simp [writeSlot, lookupSlot]

theorem lookupSlot_writeSlot_ne (m : StorageMapBuffer) (slot1 slot2 val : UInt256)
    (hne : (slot1 == slot2) = false) :
    (m.writeSlot slot1 val).lookupSlot slot2 = m.lookupSlot slot2 := by
  unfold writeSlot lookupSlot
  simp only [List.find?, hne]
  induction m.entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hk1 : (k != slot1) = true
    · simp only [List.filter, hk1, List.find?]
      cases k == slot2
      · exact ih
      · rfl
    · have hk_eq : (k == slot1) = true := by
        cases h : k == slot1
        · simp [bne, h] at hk1
        · rfl
      have hk2 : (k == slot2) = false := by
        have heq1 : k = slot1 := of_decide_eq_true hk_eq
        subst heq1
        exact hne
      simp only [List.filter, hk1, List.find?, hk2]
      exact ih

end StorageMapBuffer

/-- Abstract heap state tracking contiguous scalar array buffers, EVM storage maps, allocation IDs, and reference counts. -/
structure HeapState where
  buffers     : List ArrayBuffer
  nextId      : Nat
  storageMaps : List StorageMapBuffer := []
  refCounts   : List (Nat × Nat) := []
  deriving Repr, DecidableEq, Inhabited, BEq

namespace HeapState

def empty : HeapState :=
  { buffers := [], nextId := 0, storageMaps := [], refCounts := [] }

/-- Look up the current reference count of buffer `bufId` (defaults to `1` for live unshared buffers). -/
def getRefCount (st : HeapState) (bufId : Nat) : Nat :=
  match st.refCounts.find? (fun (id, _) => id == bufId) with
  | some (_, rc) => rc
  | none => 1

/-- Increment the reference count of buffer `bufId` by `count`. -/
def incRefBuf (st : HeapState) (bufId count : Nat) : HeapState :=
  if count == 0 then st
  else
    let rc' := st.getRefCount bufId + count
    { st with refCounts := (bufId, rc') :: st.refCounts.filter (fun (id, _) => id != bufId) }

/-- Decrement the reference count of buffer `bufId` by `count`, freeing the buffer if the count reaches `0`. -/
def decRefBuf (st : HeapState) (bufId count : Nat) : HeapState :=
  if count == 0 then st
  else
    let rc := st.getRefCount bufId
    let rc' := rc - count
    let refs' := st.refCounts.filter (fun (id, _) => id != bufId)
    if rc' == 0 then
      { st with buffers := st.buffers.filter (fun b => b.id != bufId), refCounts := refs' }
    else if rc' == 1 then
      { st with refCounts := refs' }
    else
      { st with refCounts := (bufId, rc') :: refs' }

/-- Evaluate an `incRef` instruction on an optional runtime value. -/
def evalIncRef (st : HeapState) (v? : Option Val) (count : Nat) : HeapState :=
  match v? with
  | some (.sarrayId bufId) | some (.objPtr bufId) => st.incRefBuf bufId count
  | _ => st

/-- Evaluate a `decRef` instruction on an optional runtime value. -/
def evalDecRef (st : HeapState) (v? : Option Val) (count : Nat) : HeapState :=
  match v? with
  | some (.sarrayId bufId) | some (.objPtr bufId) => st.decRefBuf bufId count
  | _ => st

@[simp]
theorem incRefBuf_decRefBuf_cancel (st : HeapState) (bufId count : Nat)
    (h_empty : st.refCounts = []) :
    (st.incRefBuf bufId count).decRefBuf bufId count = st := by
  cases st; simp only at h_empty; subst h_empty
  cases count with
  | zero => rfl
  | succ c =>
    unfold incRefBuf decRefBuf getRefCount
    simp [Nat.add_sub_cancel 1 (c + 1)]

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

/-- Read a 256-bit slot from EVM storage map `mapId` (uninitialized maps/slots return `UInt256.zero`). -/
def storageLoad (st : HeapState) (mapId : Nat) (slot : UInt256) : UInt256 :=
  match st.storageMaps.find? (fun m => m.id == mapId) with
  | some m => m.lookupSlot slot
  | none => UInt256.zero

/-- Write a 256-bit value to `slot` in EVM storage map `mapId`. -/
def storageStore (st : HeapState) (mapId : Nat) (slot val : UInt256) : HeapState :=
  match st.storageMaps.find? (fun m => m.id == mapId) with
  | some m =>
    let m' : StorageMapBuffer := { id := mapId, entries := (slot, val) :: m.entries.filter (fun (k, _) => k != slot) }
    { st with storageMaps := m' :: st.storageMaps.filter (fun x => x.id != mapId) }
  | none =>
    let m' : StorageMapBuffer := { id := mapId, entries := [(slot, val)] }
    { st with storageMaps := m' :: st.storageMaps }

@[simp]
theorem storageLoad_after_storageStore_same (st : HeapState) (mapId : Nat) (slot val : UInt256) :
    (st.storageStore mapId slot val).storageLoad mapId slot = val := by
  unfold storageStore storageLoad
  cases st.storageMaps.find? (fun m => m.id == mapId) <;>
    simp [StorageMapBuffer.lookupSlot]

theorem storageLoad_after_storageStore_ne (st : HeapState) (mapId : Nat) (slot1 slot2 val : UInt256)
    (hne : (slot1 == slot2) = false) :
    (st.storageStore mapId slot1 val).storageLoad mapId slot2 = st.storageLoad mapId slot2 := by
  unfold storageStore storageLoad
  cases hfind : st.storageMaps.find? (fun m => m.id == mapId) with
  | none =>
    simp [StorageMapBuffer.lookupSlot, hne]
  | some m =>
    simp only [List.find?, beq_self_eq_true]
    exact StorageMapBuffer.lookupSlot_writeSlot_ne m slot1 slot2 val hne

end HeapState

end LeanNative.Semantics
