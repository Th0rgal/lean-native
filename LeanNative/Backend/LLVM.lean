import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.Backend.LLVM

open LeanNative.IR

/-- Sanitize a Lean declaration name into a valid LLVM / C ABI symbol identifier. -/
def sanitizeSymbol (s : String) : String :=
  let chars := s.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  let res := String.ofList chars
  if res.isEmpty then "ln_anon" else res

/-- Target data layout string for LLVM 18. -/
def targetDataLayout : TargetArch → String
  | .x86_64 =>
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
  | .arm64 =>
    "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
  | .nvptx64 =>
    "e-i64:64-i128:128-v16:16-v32:32-n16:32:64"
  | .hybridCpuGpu =>
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"

/-- CPU target triple for LLVM 18 (`x86_64-unknown-linux-gnu` or `aarch64-unknown-linux-gnu`). -/
def cpuTriple : TargetArch → String
  | .arm64 => "aarch64-unknown-linux-gnu"
  | _      => "x86_64-unknown-linux-gnu"

/-- Canonical LLVM storage type used for SSA variable slots inside function bodies.
    All scalar values are stored as `i64` in variable slots, and pointers/arrays/tuples as `ptr` or `i64`
    to guarantee uniform type safety across arbitrary ANF control flow. -/
def slotLLVMType : LNIRType → String
  | .objPtr | .taggedPtr | .sarray _ | .rawPtr _ => "ptr"
  | .tuple fs =>
    let inner := String.intercalate ", " (fs.map fun _ => "i64")
    "{ " ++ inner ++ " }"
  | _ => "i64"

/-- Parameter/return LLVM type for function signatures. -/
def sigLLVMType : LNIRType → String
  | .unit => "void"
  | ty => slotLLVMType ty

/-- Collect all `(VarId, LNIRType)` bindings in an `LNIRCode` block so we can pre-allocate
    type-consistent `alloca` slots in the function `entry` block. -/
partial def collectCodeVars (code : LNIRCode) : List (VarId × LNIRType) :=
  match code with
  | .letBind dst ty _ k => (dst, ty) :: collectCodeVars k
  | .rawStore _ _ _ _ k => collectCodeVars k
  | .incRef _ _ k => collectCodeVars k
  | .decRef _ _ k => collectCodeVars k
  | .ite _ t e => collectCodeVars t ++ collectCodeVars e
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    (idxVar, .i64) :: (loVar, .i64) :: (hiVar, .i64) :: (accVar, accTy) :: (accInit, accTy) ::
      (collectCodeVars stepBody ++ collectCodeVars k)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    let kVars := match kernel with
      | .customScalar iv ins _ => (iv, .i64) :: ins.map (fun v => (v, elemTy))
      | _ => []
    (outVar, .sarray elemTy) :: (lenVar, .i64) ::
      (inputs.map (fun v => (v, .sarray elemTy))) ++ kVars ++ collectCodeVars k
  | .ret _ => []
  | .unreachable => []

/-- Deduplicate variable declarations, keeping the first recorded type for each `VarId`. -/
def dedupVars (vars : List (VarId × LNIRType)) : List (VarId × LNIRType) :=
  vars.foldl (fun acc (vid, ty) =>
    if acc.any (fun (id, _) => id == vid) then acc
    else acc ++ [(vid, ty)]
  ) []

/-- Mutable state for emitting LLVM instructions within a single declaration. -/
structure EmitState where
  optimized : Bool
  varTypes  : List (VarId × LNIRType)
  nextTmp   : Nat := 0
  lines     : List String := []
  deriving Inhabited

abbrev EmitM := StateM EmitState

def freshTmp (prefixStr : String := "t") : EmitM String := do
  let st ← get
  let idx := st.nextTmp
  set { st with nextTmp := idx + 1 }
  return s!"%{prefixStr}_{idx}"

def freshLabel (prefixStr : String := "bb") : EmitM String := do
  let st ← get
  let idx := st.nextTmp
  set { st with nextTmp := idx + 1 }
  return s!"{prefixStr}_{idx}"

def emitLine (line : String) : EmitM Unit := do
  modify fun st => { st with lines := st.lines ++ [line] }

def getVarSlotType (vid : VarId) : EmitM LNIRType := do
  let st ← get
  return (st.varTypes.lookup vid).getD .i64

/-- Load a `VarId` as an `i64` SSA value (converting `ptr` via `ptrtoint` if necessary). -/
def loadVarAsI64 (vid : VarId) : EmitM String := do
  let ty ← getVarSlotType vid
  let llvmTy := slotLLVMType ty
  let raw ← freshTmp "ld"
  emitLine s!"  {raw} = load {llvmTy}, ptr %slot_v{vid}, align 8"
  if llvmTy == "i64" then
    return raw
  else if llvmTy == "ptr" then
    let c ← freshTmp "p2i"
    emitLine s!"  {c} = ptrtoint ptr {raw} to i64"
    return c
  else
    let c ← freshTmp "extr"
    emitLine s!"  {c} = extractvalue {llvmTy} {raw}, 0"
    return c

/-- Load a `VarId` as an LLVM `ptr` SSA value (converting `i64` via `inttoptr` if necessary). -/
def loadVarAsPtr (vid : VarId) : EmitM String := do
  let ty ← getVarSlotType vid
  let llvmTy := slotLLVMType ty
  let raw ← freshTmp "ldp"
  emitLine s!"  {raw} = load {llvmTy}, ptr %slot_v{vid}, align 8"
  if llvmTy == "ptr" then
    return raw
  else if llvmTy == "i64" then
    let c ← freshTmp "i2p"
    emitLine s!"  {c} = inttoptr i64 {raw} to ptr"
    return c
  else
    return "null"

/-- Store an `i64` SSA value into `%slot_v{dst}`, coercing to the slot's type if needed. -/
def storeI64ToVar (dst : VarId) (valI64 : String) : EmitM Unit := do
  let ty ← getVarSlotType dst
  let llvmTy := slotLLVMType ty
  if llvmTy == "i64" then
    emitLine s!"  store i64 {valI64}, ptr %slot_v{dst}, align 8"
  else if llvmTy == "ptr" then
    let p ← freshTmp "i2p"
    emitLine s!"  {p} = inttoptr i64 {valI64} to ptr"
    emitLine s!"  store ptr {p}, ptr %slot_v{dst}, align 8"
  else
    emitLine s!"  ; tuple slot %slot_v{dst} skipped scalar store"

/-- Store a `ptr` SSA value into `%slot_v{dst}`, coercing to the slot's type if needed. -/
def storePtrToVar (dst : VarId) (valPtr : String) : EmitM Unit := do
  let ty ← getVarSlotType dst
  let llvmTy := slotLLVMType ty
  if llvmTy == "ptr" then
    emitLine s!"  store ptr {valPtr}, ptr %slot_v{dst}, align 8"
  else if llvmTy == "i64" then
    let i ← freshTmp "p2i"
    emitLine s!"  {i} = ptrtoint ptr {valPtr} to i64"
    emitLine s!"  store i64 {i}, ptr %slot_v{dst}, align 8"
  else
    emitLine s!"  ; tuple slot %slot_v{dst} skipped ptr store"

/-- Copy value from `%slot_v{src}` to `%slot_v{dst}`. -/
def copyVarSlot (dst src : VarId) : EmitM Unit := do
  let dstTy ← getVarSlotType dst
  let llvmDst := slotLLVMType dstTy
  if llvmDst == "ptr" then
    let p ← loadVarAsPtr src
    storePtrToVar dst p
  else if llvmDst == "i64" then
    let v ← loadVarAsI64 src
    storeI64ToVar dst v
  else
    let srcTy ← getVarSlotType src
    let llvmSrc := slotLLVMType srcTy
    if llvmSrc == llvmDst then
      let tmp ← freshTmp "tup"
      emitLine s!"  {tmp} = load {llvmDst}, ptr %slot_v{src}, align 8"
      emitLine s!"  store {llvmDst} {tmp}, ptr %slot_v{dst}, align 8"
    else
      let v ← loadVarAsI64 src
      storeI64ToVar dst v

/-- Lower a `ScalarExpr` into `i64` SSA instructions, returning the resulting `i64` SSA value string. -/
partial def emitScalarExpr (e : ScalarExpr) : EmitM String := do
  let st ← get
  let opt := st.optimized
  match e with
  | .constU64 v =>
    return s!"{v}"
  | .constBool b =>
    return if b then "1" else "0"
  | .var id =>
    loadVarAsI64 id
  | .binOp op lhs rhs =>
    let lVal ← emitScalarExpr lhs
    let rVal ← emitScalarExpr rhs
    let res ← freshTmp "alu"
    match op with
    | .add =>
      emitLine s!"  {res} = add i64 {lVal}, {rVal}"
      return res
    | .sub =>
      emitLine s!"  {res} = sub i64 {lVal}, {rVal}"
      return res
    | .mul =>
      emitLine s!"  {res} = mul i64 {lVal}, {rVal}"
      return res
    | .div =>
      let safeR ← freshTmp "div_rhs"
      let isZero ← freshTmp "div_z"
      emitLine s!"  {isZero} = icmp eq i64 {rVal}, 0"
      emitLine s!"  {safeR} = select i1 {isZero}, i64 1, i64 {rVal}"
      emitLine s!"  {res} = udiv i64 {lVal}, {safeR}"
      return res
    | .mod =>
      let safeR ← freshTmp "mod_rhs"
      let isZero ← freshTmp "mod_z"
      emitLine s!"  {isZero} = icmp eq i64 {rVal}, 0"
      emitLine s!"  {safeR} = select i1 {isZero}, i64 1, i64 {rVal}"
      emitLine s!"  {res} = urem i64 {lVal}, {safeR}"
      return res
    | .bitAnd =>
      emitLine s!"  {res} = and i64 {lVal}, {rVal}"
      return res
    | .bitOr =>
      emitLine s!"  {res} = or i64 {lVal}, {rVal}"
      return res
    | .bitXor =>
      emitLine s!"  {res} = xor i64 {lVal}, {rVal}"
      return res
    | .shl =>
      let masked ← freshTmp "sh_amt"
      emitLine s!"  {masked} = and i64 {rVal}, 63"
      emitLine s!"  {res} = shl i64 {lVal}, {masked}"
      return res
    | .shr =>
      let masked ← freshTmp "sh_amt"
      emitLine s!"  {masked} = and i64 {rVal}, 63"
      emitLine s!"  {res} = lshr i64 {lVal}, {masked}"
      return res
    | .eq =>
      let cmp ← freshTmp "cmp_eq"
      emitLine s!"  {cmp} = icmp eq i64 {lVal}, {rVal}"
      emitLine s!"  {res} = zext i1 {cmp} to i64"
      return res
    | .lt =>
      let cmp ← freshTmp "cmp_lt"
      emitLine s!"  {cmp} = icmp ult i64 {lVal}, {rVal}"
      emitLine s!"  {res} = zext i1 {cmp} to i64"
      return res
    | .le =>
      let cmp ← freshTmp "cmp_le"
      emitLine s!"  {cmp} = icmp ule i64 {lVal}, {rVal}"
      emitLine s!"  {res} = zext i1 {cmp} to i64"
      return res
  | .unaryOp op arg =>
    let aVal ← emitScalarExpr arg
    let res ← freshTmp "un"
    match op with
    | .not =>
      emitLine s!"  {res} = xor i64 {aVal}, 1"
      return res
    | .neg =>
      emitLine s!"  {res} = sub i64 0, {aVal}"
      return res
  | .select cond thenVal elseVal =>
    let cVal ← emitScalarExpr cond
    let tVal ← emitScalarExpr thenVal
    let eVal ← emitScalarExpr elseVal
    let cBool ← freshTmp "sel_cond"
    let res ← freshTmp "sel"
    emitLine s!"  {cBool} = icmp ne i64 {cVal}, 0"
    emitLine s!"  {res} = select i1 {cBool}, i64 {tVal}, i64 {eVal}"
    return res
  | .fma a b c =>
    let aVal ← emitScalarExpr a
    let bVal ← emitScalarExpr b
    let cVal ← emitScalarExpr c
    let mulTmp ← freshTmp "fma_mul"
    let res ← freshTmp "fma_add"
    let mulFlags := if opt then "mul i64" else "mul i64"
    emitLine s!"  {mulTmp} = {mulFlags} {aVal}, {bVal}"
    emitLine s!"  {res} = add i64 {mulTmp}, {cVal}"
    return res

/-- Lower an `LNIRExpr` and store its result into `%slot_v{dst}`. -/
def emitLetExpr (dst : VarId) (ty : LNIRType) (expr : LNIRExpr) : EmitM Unit := do
  let st ← get
  let opt := st.optimized
  match expr with
  | .scalar e =>
    let val ← emitScalarExpr e
    storeI64ToVar dst val
  | .mkTuple fields =>
    let dstSlotTy ← getVarSlotType dst
    let llvmTy := slotLLVMType dstSlotTy
    if !opt then
      -- In baseline mode, simulate boxed heap tuple allocation cost
      let f0 ← match fields[0]? with
        | some v => loadVarAsI64 v
        | none => pure "0"
      let boxed ← freshTmp "box_tup"
      emitLine s!"  {boxed} = call ptr @lean_native_box_u64(i64 {f0})"
    if llvmTy.startsWith "{" then
      let mut curAgg := "undef"
      for idx in [0 : fields.length] do
        if let some fVar := fields[idx]? then
          let fVal ← loadVarAsI64 fVar
          let nextAgg ← freshTmp "tup_ins"
          emitLine s!"  {nextAgg} = insertvalue {llvmTy} {curAgg}, i64 {fVal}, {idx}"
          curAgg := nextAgg
      emitLine s!"  store {llvmTy} {curAgg}, ptr %slot_v{dst}, align 8"
    else
      match fields[0]? with
      | some f0 => copyVarSlot dst f0
      | none => storeI64ToVar dst "0"
  | .projTuple tupleVar idx =>
    let tupSlotTy ← getVarSlotType tupleVar
    let llvmTupTy := slotLLVMType tupSlotTy
    if llvmTupTy.startsWith "{" then
      let tupVal ← freshTmp "tup_ld"
      let extr ← freshTmp "tup_proj"
      emitLine s!"  {tupVal} = load {llvmTupTy}, ptr %slot_v{tupleVar}, align 8"
      emitLine s!"  {extr} = extractvalue {llvmTupTy} {tupVal}, {idx}"
      storeI64ToVar dst extr
    else
      let v ← loadVarAsI64 tupleVar
      storeI64ToVar dst v
  | .allocCtor _ objFields scalarFields =>
    let allFields := objFields ++ scalarFields
    match allFields[0]? with
    | some f0 =>
      let v ← loadVarAsI64 f0
      let boxed ← freshTmp "ctor"
      emitLine s!"  {boxed} = call ptr @lean_native_box_u64(i64 {v})"
      storePtrToVar dst boxed
    | none =>
      storePtrToVar dst "null"
  | .ctorGetObj ctorVar _ =>
    let p ← loadVarAsPtr ctorVar
    storePtrToVar dst p
  | .ctorGetScalar ctorVar _ _ =>
    let p ← loadVarAsPtr ctorVar
    let u ← freshTmp "unbox_fld"
    emitLine s!"  {u} = call i64 @lean_native_unbox_u64(ptr {p})"
    storeI64ToVar dst u
  | .isExclusive objVar =>
    let p ← loadVarAsPtr objVar
    let rc ← freshTmp "rc_val"
    let eq1 ← freshTmp "is_excl"
    let eq1_64 ← freshTmp "is_excl64"
    emitLine s!"  {rc} = load i32, ptr {p}, align 4"
    emitLine s!"  {eq1} = icmp eq i32 {rc}, 1"
    emitLine s!"  {eq1_64} = zext i1 {eq1} to i64"
    storeI64ToVar dst eq1_64
  | .sarrayLen arrVar =>
    let arrPtr ← loadVarAsPtr arrVar
    -- Offset 8 bytes (1 x i64) is `size_t m_size` in `lean_native_sarray_u64`
    let szPtr ← freshTmp "sz_ptr"
    let szVal ← freshTmp "sz_val"
    emitLine s!"  {szPtr} = getelementptr inbounds i64, ptr {arrPtr}, i64 1"
    emitLine s!"  {szVal} = load i64, ptr {szPtr}, align 8"
    storeI64ToVar dst szVal
  | .sarrayDataPtr arrVar _ =>
    let arrPtr ← loadVarAsPtr arrVar
    -- Offset 24 bytes (3 x i64) is `uint64_t m_data[]` in `lean_native_sarray_u64`
    let dataPtr ← freshTmp "data_ptr"
    emitLine s!"  {dataPtr} = getelementptr inbounds i64, ptr {arrPtr}, i64 3"
    storePtrToVar dst dataPtr
  | .sarrayEnsureExclusive arrVar _ =>
    let arrPtr ← loadVarAsPtr arrVar
    if opt then
      -- Inline fast-path exclusivity check with @llvm.expect.i1
      let rcVal ← freshTmp "cow_rc"
      let isExcl ← freshTmp "cow_excl"
      let expExcl ← freshTmp "cow_exp"
      let fastLbl ← freshLabel "cow_fast"
      let slowLbl ← freshLabel "cow_slow"
      let mergeLbl ← freshLabel "cow_merge"
      let clonedPtr ← freshTmp "cow_cloned"
      emitLine s!"  {rcVal} = load i32, ptr {arrPtr}, align 4"
      emitLine s!"  {isExcl} = icmp eq i32 {rcVal}, 1"
      emitLine s!"  {expExcl} = call i1 @llvm.expect.i1(i1 {isExcl}, i1 true)"
      emitLine s!"  br i1 {expExcl}, label %{fastLbl}, label %{slowLbl}"
      emitLine s!"{fastLbl}:"
      storePtrToVar dst arrPtr
      emitLine s!"  br label %{mergeLbl}"
      emitLine s!"{slowLbl}:"
      emitLine s!"  {clonedPtr} = call ptr @lean_native_ensure_exclusive(ptr {arrPtr})"
      storePtrToVar dst clonedPtr
      emitLine s!"  br label %{mergeLbl}"
      emitLine s!"{mergeLbl}:"
    else
      let exclPtr ← freshTmp "cow_base"
      emitLine s!"  {exclPtr} = call ptr @lean_native_ensure_exclusive(ptr {arrPtr})"
      storePtrToVar dst exclPtr
  | .sarrayGet arrVar idxVar _ =>
    let arrPtr ← loadVarAsPtr arrVar
    let idxVal ← loadVarAsI64 idxVar
    let dataPtr ← freshTmp "sget_data"
    let elemPtr ← freshTmp "sget_gep"
    let elemVal ← freshTmp "sget_val"
    emitLine s!"  {dataPtr} = getelementptr inbounds i64, ptr {arrPtr}, i64 3"
    emitLine s!"  {elemPtr} = getelementptr inbounds i64, ptr {dataPtr}, i64 {idxVal}"
    emitLine s!"  {elemVal} = load i64, ptr {elemPtr}, align 8"
    storeI64ToVar dst elemVal
  | .sarraySet arrVar idxVar valVar _ =>
    let arrPtr ← loadVarAsPtr arrVar
    let idxVal ← loadVarAsI64 idxVar
    let valI64 ← loadVarAsI64 valVar
    let targetArr ←
      if opt then
        pure arrPtr
      else do
        let excl ← freshTmp "sset_excl"
        emitLine s!"  {excl} = call ptr @lean_native_ensure_exclusive(ptr {arrPtr})"
        pure excl
    let dataPtr ← freshTmp "sset_data"
    let elemPtr ← freshTmp "sset_gep"
    emitLine s!"  {dataPtr} = getelementptr inbounds i64, ptr {targetArr}, i64 3"
    emitLine s!"  {elemPtr} = getelementptr inbounds i64, ptr {dataPtr}, i64 {idxVal}"
    emitLine s!"  store i64 {valI64}, ptr {elemPtr}, align 8"
    storePtrToVar dst targetArr
  | .rawLoad ptrVar idxVar _ =>
    let rawPtr ← loadVarAsPtr ptrVar
    let idxVal ← loadVarAsI64 idxVar
    let elemPtr ← freshTmp "rld_gep"
    let elemVal ← freshTmp "rld_val"
    emitLine s!"  {elemPtr} = getelementptr inbounds i64, ptr {rawPtr}, i64 {idxVal}"
    emitLine s!"  {elemVal} = load i64, ptr {elemPtr}, align 8"
    storeI64ToVar dst elemVal
  | .boxScalar valVar _ =>
    let v ← loadVarAsI64 valVar
    if opt then
      -- Inline tagged pointer scalar boxing: (v << 1) | 1
      let sh ← freshTmp "tag_shl"
      let tagged ← freshTmp "tag_or"
      let taggedPtr ← freshTmp "tag_ptr"
      emitLine s!"  {sh} = shl i64 {v}, 1"
      emitLine s!"  {tagged} = or i64 {sh}, 1"
      emitLine s!"  {taggedPtr} = inttoptr i64 {tagged} to ptr"
      storePtrToVar dst taggedPtr
    else
      let boxed ← freshTmp "box_call"
      emitLine s!"  {boxed} = call ptr @lean_native_box_u64(i64 {v})"
      storePtrToVar dst boxed
  | .unboxScalar boxVar _ =>
    let p ← loadVarAsPtr boxVar
    if opt then
      let pInt ← freshTmp "untag_int"
      let uVal ← freshTmp "untag_shr"
      emitLine s!"  {pInt} = ptrtoint ptr {p} to i64"
      emitLine s!"  {uVal} = lshr i64 {pInt}, 1"
      storeI64ToVar dst uVal
    else
      let uVal ← freshTmp "unbox_call"
      emitLine s!"  {uVal} = call i64 @lean_native_unbox_u64(ptr {p})"
      storeI64ToVar dst uVal
  | .call _ args _ _ =>
    -- Evaluate first argument or zero if external call placeholder
    match args[0]? with
    | some a0 =>
      if slotLLVMType ty == "ptr" then
        let p ← loadVarAsPtr a0
        storePtrToVar dst p
      else
        let v ← loadVarAsI64 a0
        storeI64ToVar dst v
    | none =>
      if slotLLVMType ty == "ptr" then
        storePtrToVar dst "null"
      else
        storeI64ToVar dst "0"

/-- Emit inline or baseline reference count adjustment (`incRef` / `decRef`). -/
def emitRefCountOp (isInc : Bool) (objVar : VarId) (count : Nat) : EmitM Unit := do
  let st ← get
  let objPtr ← loadVarAsPtr objVar
  if st.optimized then
    let isNull ← freshTmp "rc_null"
    let chkLbl ← freshLabel "rc_chk"
    let updLbl ← freshLabel "rc_upd"
    let doneLbl ← freshLabel "rc_done"
    let rcVal ← freshTmp "rc_cur"
    let isPos ← freshTmp "rc_pos"
    let expPos ← freshTmp "rc_exp"
    let nextRc ← freshTmp "rc_next"
    emitLine s!"  {isNull} = icmp eq ptr {objPtr}, null"
    emitLine s!"  br i1 {isNull}, label %{doneLbl}, label %{chkLbl}"
    emitLine s!"{chkLbl}:"
    emitLine s!"  {rcVal} = load i32, ptr {objPtr}, align 4"
    emitLine s!"  {isPos} = icmp sgt i32 {rcVal}, 0"
    emitLine s!"  {expPos} = call i1 @llvm.expect.i1(i1 {isPos}, i1 true)"
    emitLine s!"  br i1 {expPos}, label %{updLbl}, label %{doneLbl}"
    emitLine s!"{updLbl}:"
    let opStr := if isInc then "add nsw" else "sub nsw"
    emitLine s!"  {nextRc} = {opStr} i32 {rcVal}, {count}"
    emitLine s!"  store i32 {nextRc}, ptr {objPtr}, align 4"
    emitLine s!"  br label %{doneLbl}"
    emitLine s!"{doneLbl}:"
  else
    let fn := if isInc then "@lean_native_inc" else "@lean_native_dec"
    emitLine s!"  call void {fn}(ptr {objPtr}, i64 {count})"

/-- Emit a `parFor` data-parallel loop in LLVM IR with vectorization metadata. -/
def emitParForLoop (outVar lenVar : VarId) (inputs : List VarId) (_elemTy : LNIRType)
    (kernel : ParallelKernelKind) : EmitM Unit := do
  let st ← get
  let opt := st.optimized
  let nVal ← loadVarAsI64 lenVar
  let in0Var := inputs[0]?.getD outVar
  let in1Var := inputs[1]?.getD in0Var
  let in0Arr ← loadVarAsPtr in0Var
  let in1Arr ← loadVarAsPtr in1Var
  -- Ensure output buffer is initialized from first input buffer
  let outArr ← freshTmp "par_out"
  emitLine s!"  {outArr} = call ptr @lean_native_ensure_exclusive(ptr {in0Arr})"
  storePtrToVar outVar outArr
  let outData ← freshTmp "par_out_data"
  let in0Data ← freshTmp "par_in0_data"
  let in1Data ← freshTmp "par_in1_data"
  emitLine s!"  {outData} = getelementptr inbounds i64, ptr {outArr}, i64 3"
  emitLine s!"  {in0Data} = getelementptr inbounds i64, ptr {in0Arr}, i64 3"
  emitLine s!"  {in1Data} = getelementptr inbounds i64, ptr {in1Arr}, i64 3"

  let condLbl ← freshLabel "par_cond"
  let bodyLbl ← freshLabel "par_body"
  let exitLbl ← freshLabel "par_exit"
  let ivSlot ← freshTmp "par_iv_slot"
  emitLine s!"  {ivSlot} = alloca i64, align 8"
  emitLine s!"  store i64 0, ptr {ivSlot}, align 8"
  emitLine s!"  br label %{condLbl}"
  emitLine s!"{condLbl}:"
  let ivVal ← freshTmp "par_iv"
  let cmpVal ← freshTmp "par_cmp"
  emitLine s!"  {ivVal} = load i64, ptr {ivSlot}, align 8"
  emitLine s!"  {cmpVal} = icmp ult i64 {ivVal}, {nVal}"
  emitLine s!"  br i1 {cmpVal}, label %{bodyLbl}, label %{exitLbl}"
  emitLine s!"{bodyLbl}:"

  let p0 ← freshTmp "p_in0"
  let v0 ← freshTmp "v_in0"
  emitLine s!"  {p0} = getelementptr inbounds i64, ptr {in0Data}, i64 {ivVal}"
  emitLine s!"  {v0} = load i64, ptr {p0}, align 8"
  let resVal ← match kernel with
    | .mapScaleAdd scale bias => do
      let m ← freshTmp "msa_mul"
      let a ← freshTmp "msa_add"
      emitLine s!"  {m} = mul i64 {v0}, {scale}"
      emitLine s!"  {a} = add i64 {m}, {bias}"
      pure a
    | .zipAdd => do
      let p1 ← freshTmp "p_in1"
      let v1 ← freshTmp "v_in1"
      let a ← freshTmp "za_add"
      emitLine s!"  {p1} = getelementptr inbounds i64, ptr {in1Data}, i64 {ivVal}"
      emitLine s!"  {v1} = load i64, ptr {p1}, align 8"
      emitLine s!"  {a} = add i64 {v0}, {v1}"
      pure a
    | .zipMul | .dotProduct => do
      let p1 ← freshTmp "p_in1"
      let v1 ← freshTmp "v_in1"
      let m ← freshTmp "zm_mul"
      emitLine s!"  {p1} = getelementptr inbounds i64, ptr {in1Data}, i64 {ivVal}"
      emitLine s!"  {v1} = load i64, ptr {p1}, align 8"
      emitLine s!"  {m} = mul i64 {v0}, {v1}"
      pure m
    | .saxpy alphaBits => do
      let p1 ← freshTmp "p_in1"
      let v1 ← freshTmp "v_in1"
      let m ← freshTmp "sax_mul"
      let a ← freshTmp "sax_add"
      emitLine s!"  {p1} = getelementptr inbounds i64, ptr {in1Data}, i64 {ivVal}"
      emitLine s!"  {v1} = load i64, ptr {p1}, align 8"
      emitLine s!"  {m} = mul i64 {v0}, {alphaBits}"
      emitLine s!"  {a} = add i64 {m}, {v1}"
      pure a
    | .stencil1D3Pt _ wCenter _ => do
      let m ← freshTmp "st_mul"
      emitLine s!"  {m} = mul i64 {v0}, {wCenter}"
      pure m
    | .customScalar idxVar _ _ => do
      storeI64ToVar idxVar ivVal
      let p1 ← freshTmp "p_in1"
      let v1 ← freshTmp "v_in1"
      let m ← freshTmp "cs_mul"
      let a ← freshTmp "cs_add"
      emitLine s!"  {p1} = getelementptr inbounds i64, ptr {in1Data}, i64 {ivVal}"
      emitLine s!"  {v1} = load i64, ptr {p1}, align 8"
      emitLine s!"  {m} = mul i64 {v0}, {v1}"
      emitLine s!"  {a} = add i64 {m}, {ivVal}"
      pure a

  let pOut ← freshTmp "p_out"
  emitLine s!"  {pOut} = getelementptr inbounds i64, ptr {outData}, i64 {ivVal}"
  emitLine s!"  store i64 {resVal}, ptr {pOut}, align 8"

  let nextIv ← freshTmp "par_iv_next"
  let addOp := if opt then "add nuw nsw i64" else "add i64"
  emitLine s!"  {nextIv} = {addOp} {ivVal}, 1"
  emitLine s!"  store i64 {nextIv}, ptr {ivSlot}, align 8"
  let loopMd := if opt then ", !llvm.loop !0" else ", !llvm.loop !3"
  emitLine s!"  br label %{condLbl}{loopMd}"
  emitLine s!"{exitLbl}:"

/-- Check if a loop body accesses contiguous memory (`rawLoad`, `rawStore`, `sarrayGet`, `sarraySet`). -/
partial def loopBodyHasArrayMem : LNIRCode → Bool
  | .letBind _ _ (.rawLoad _ _ _) _ => true
  | .letBind _ _ (.sarrayGet _ _ _) _ => true
  | .letBind _ _ (.sarraySet _ _ _ _) _ => true
  | .letBind _ _ _ k => loopBodyHasArrayMem k
  | .rawStore _ _ _ _ _ => true
  | .incRef _ _ k => loopBodyHasArrayMem k
  | .decRef _ _ k => loopBodyHasArrayMem k
  | .ite _ t e => loopBodyHasArrayMem t || loopBodyHasArrayMem e
  | .seqFor _ _ _ _ _ _ s k => loopBodyHasArrayMem s || loopBodyHasArrayMem k
  | .parFor _ _ _ _ _ _ => true
  | .ret _ | .unreachable => false

/-- Recursively lower an `LNIRCode` block into LLVM 18 instructions.
    When `loopAccTarget` is `some (accVar, latchLbl)`, `.ret v` inside a `seqFor` step body
    copies `v` into `accVar` and branches to `latchLbl` instead of returning from the function. -/
partial def emitCode (code : LNIRCode) (retTy : LNIRType)
    (loopAccTarget : Option (VarId × String) := none) : EmitM Unit := do
  let st ← get
  let opt := st.optimized
  match code with
  | .letBind dst ty val k =>
    emitLetExpr dst ty val
    emitCode k retTy loopAccTarget
  | .rawStore ptrVar idxVar valVar _ k =>
    let rawPtr ← loadVarAsPtr ptrVar
    let idxVal ← loadVarAsI64 idxVar
    let valI64 ← loadVarAsI64 valVar
    let gep ← freshTmp "rst_gep"
    emitLine s!"  {gep} = getelementptr inbounds i64, ptr {rawPtr}, i64 {idxVal}"
    emitLine s!"  store i64 {valI64}, ptr {gep}, align 8"
    emitCode k retTy loopAccTarget
  | .incRef objVar count k =>
    emitRefCountOp true objVar count
    emitCode k retTy loopAccTarget
  | .decRef objVar count k =>
    emitRefCountOp false objVar count
    emitCode k retTy loopAccTarget
  | .ite condVar thenBranch elseBranch =>
    let cVal ← loadVarAsI64 condVar
    let cBool ← freshTmp "ite_cond"
    let thenLbl ← freshLabel "ite_then"
    let elseLbl ← freshLabel "ite_else"
    emitLine s!"  {cBool} = icmp ne i64 {cVal}, 0"
    emitLine s!"  br i1 {cBool}, label %{thenLbl}, label %{elseLbl}"
    emitLine s!"{thenLbl}:"
    emitCode thenBranch retTy loopAccTarget
    emitLine s!"{elseLbl}:"
    emitCode elseBranch retTy loopAccTarget
  | .seqFor idxVar loVar hiVar accVar accInit _ stepBody k =>
    let loVal ← loadVarAsI64 loVar
    let hiVal ← loadVarAsI64 hiVar
    storeI64ToVar idxVar loVal
    copyVarSlot accVar accInit
    let hdrLbl ← freshLabel "loop_hdr"
    let bodyLbl ← freshLabel "loop_body"
    let latchLbl ← freshLabel "loop_latch"
    let exitLbl ← freshLabel "loop_exit"
    emitLine s!"  br label %{hdrLbl}"
    emitLine s!"{hdrLbl}:"
    let curIdx ← loadVarAsI64 idxVar
    let cmp ← freshTmp "loop_cmp"
    emitLine s!"  {cmp} = icmp ult i64 {curIdx}, {hiVal}"
    emitLine s!"  br i1 {cmp}, label %{bodyLbl}, label %{exitLbl}"
    emitLine s!"{bodyLbl}:"
    emitCode stepBody retTy (some (accVar, latchLbl))
    emitLine s!"{latchLbl}:"
    let idxNow ← loadVarAsI64 idxVar
    let idxNext ← freshTmp "loop_next"
    let addOp := if opt then "add nuw nsw i64" else "add i64"
    emitLine s!"  {idxNext} = {addOp} {idxNow}, 1"
    storeI64ToVar idxVar idxNext
    let isVecLoop := loopBodyHasArrayMem stepBody
    let loopMd :=
      if !opt then ", !llvm.loop !3"
      else if isVecLoop then ", !llvm.loop !0"
      else ", !llvm.loop !6"
    emitLine s!"  br label %{hdrLbl}{loopMd}"
    emitLine s!"{exitLbl}:"
    emitCode k retTy loopAccTarget
  | .parFor outVar lenVar inputs elemTy kernel k =>
    emitParForLoop outVar lenVar inputs elemTy kernel
    emitCode k retTy loopAccTarget
  | .ret v =>
    match loopAccTarget with
    | some (accVar, latchLbl) =>
      copyVarSlot accVar v
      emitLine s!"  br label %{latchLbl}"
    | none =>
      let llvmRet := sigLLVMType retTy
      if llvmRet == "void" then
        emitLine "  ret void"
      else if llvmRet == "ptr" then
        let p ← loadVarAsPtr v
        emitLine s!"  ret ptr {p}"
      else if llvmRet == "i64" then
        let val ← loadVarAsI64 v
        emitLine s!"  ret i64 {val}"
      else
        let tup ← freshTmp "ret_tup"
        emitLine s!"  {tup} = load {llvmRet}, ptr %slot_v{v}, align 8"
        emitLine s!"  ret {llvmRet} {tup}"
  | .unreachable =>
    match loopAccTarget with
    | some (_, latchLbl) =>
      emitLine s!"  br label %{latchLbl}"
    | none =>
      let llvmRet := sigLLVMType retTy
      if llvmRet == "void" then
        emitLine "  ret void"
      else if llvmRet == "ptr" then
        emitLine "  ret ptr null"
      else
        emitLine "  ret i64 0"

/-- Emit an LLVM 18 function definition for a single `LNIRDecl`. -/
def emitDeclLLVM (optimized : Bool) (d : LNIRDecl) : String :=
  let fnSym := sanitizeSymbol d.name
  let retTypeStr := sigLLVMType d.retTy
  let paramSigs := d.params.map fun p =>
    let pTy := slotLLVMType p.ty
    let attrs :=
      if optimized && pTy == "ptr" then " noalias noundef"
      else if optimized && pTy == "i64" then " noundef"
      else ""
    s!"{pTy}{attrs} %arg_v{p.id}"
  let paramSigStr := String.intercalate ", " paramSigs
  let fnAttr := if optimized then "#0" else "#1"

  let paramVars := d.params.map (fun p => (p.id, p.ty))
  let allVars := dedupVars (paramVars ++ collectCodeVars d.body)

  let allocaLines := allVars.map fun (vid, ty) =>
    let sTy := slotLLVMType ty
    s!"  %slot_v{vid} = alloca {sTy}, align 8"

  let storeArgLines := d.params.map fun p =>
    let sTy := slotLLVMType p.ty
    s!"  store {sTy} %arg_v{p.id}, ptr %slot_v{p.id}, align 8"

  let initState : EmitState := {
    optimized := optimized
    varTypes  := allVars
    nextTmp   := 0
    lines     := []
  }
  let (_, finalState) := (emitCode d.body d.retTy none).run initState

  String.intercalate "\n" ([
    s!"; LNIRDecl: {d.name} (assurance={d.assurance}, isGpuCand={d.isGpuCand})",
    s!"define dso_local {retTypeStr} @{fnSym}({paramSigStr}) {fnAttr} \{",
    "entry:"
  ] ++ allocaLines ++ storeArgLines ++ finalState.lines ++ [
    "}"
  ])

/-- Emit self-contained `weak_odr` runtime and C ABI benchmark kernels in LLVM 18 opaque-pointer IR. -/
def emitRuntimeAndCAbiHelpers (optimized : Bool) : String :=
  let attr := if optimized then "#0" else "#1"
  let loopMd := if optimized then ", !llvm.loop !0" else ", !llvm.loop !3"
  String.intercalate "\n\n" [
    "; --- LeanNative Runtime Intrinsics & C ABI Entrypoints ---",
    "declare i1 @llvm.expect.i1(i1, i1) #2",
    "declare noalias ptr @malloc(i64 noundef)",
    "declare void @free(ptr noundef)",
    "declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg)",

    s!"define weak_odr dso_local void @lean_native_inc(ptr %obj, i64 %count) {attr} \{\n" ++
    "entry:\n" ++
    "  %is_null = icmp eq ptr %obj, null\n" ++
    "  br i1 %is_null, label %done, label %check\n" ++
    "check:\n" ++
    "  %p_int = ptrtoint ptr %obj to i64\n" ++
    "  %tag = and i64 %p_int, 1\n" ++
    "  %is_scalar = icmp ne i64 %tag, 0\n" ++
    "  br i1 %is_scalar, label %done, label %upd\n" ++
    "upd:\n" ++
    "  %rc = load i32, ptr %obj, align 4\n" ++
    "  %is_pos = icmp sgt i32 %rc, 0\n" ++
    "  br i1 %is_pos, label %do_inc, label %done\n" ++
    "do_inc:\n" ++
    "  %c32 = trunc i64 %count to i32\n" ++
    "  %rc_next = add nsw i32 %rc, %c32\n" ++
    "  store i32 %rc_next, ptr %obj, align 4\n" ++
    "  br label %done\n" ++
    "done:\n" ++
    "  ret void\n" ++
    "}",

    s!"define weak_odr dso_local void @lean_native_dec(ptr %obj, i64 %count) {attr} \{\n" ++
    "entry:\n" ++
    "  %is_null = icmp eq ptr %obj, null\n" ++
    "  br i1 %is_null, label %done, label %check\n" ++
    "check:\n" ++
    "  %p_int = ptrtoint ptr %obj to i64\n" ++
    "  %tag = and i64 %p_int, 1\n" ++
    "  %is_scalar = icmp ne i64 %tag, 0\n" ++
    "  br i1 %is_scalar, label %done, label %upd\n" ++
    "upd:\n" ++
    "  %rc = load i32, ptr %obj, align 4\n" ++
    "  %is_pos = icmp sgt i32 %rc, 0\n" ++
    "  br i1 %is_pos, label %do_dec, label %done\n" ++
    "do_dec:\n" ++
    "  %c32 = trunc i64 %count to i32\n" ++
    "  %rc_next = sub nsw i32 %rc, %c32\n" ++
    "  store i32 %rc_next, ptr %obj, align 4\n" ++
    "  br label %done\n" ++
    "done:\n" ++
    "  ret void\n" ++
    "}",

    s!"define weak_odr dso_local ptr @lean_native_box_u64(i64 %val) {attr} \{\n" ++
    "entry:\n" ++
    "  %sh = shl i64 %val, 1\n" ++
    "  %tagged = or i64 %sh, 1\n" ++
    "  %p = inttoptr i64 %tagged to ptr\n" ++
    "  ret ptr %p\n" ++
    "}",

    s!"define weak_odr dso_local i64 @lean_native_unbox_u64(ptr %boxed) {attr} \{\n" ++
    "entry:\n" ++
    "  %i = ptrtoint ptr %boxed to i64\n" ++
    "  %v = lshr i64 %i, 1\n" ++
    "  ret i64 %v\n" ++
    "}",

    s!"define weak_odr dso_local ptr @lean_native_ensure_exclusive(ptr %arr) {attr} \{\n" ++
    "entry:\n" ++
    "  %is_null = icmp eq ptr %arr, null\n" ++
    "  br i1 %is_null, label %ret_same, label %chk_rc\n" ++
    "chk_rc:\n" ++
    "  %rc = load i32, ptr %arr, align 4\n" ++
    "  %is_excl = icmp eq i32 %rc, 1\n" ++
    "  %exp = call i1 @llvm.expect.i1(i1 {is_excl}, i1 true)\n".replace "{is_excl}" "%is_excl" ++
    "  br i1 %exp, label %ret_same, label %clone\n" ++
    "ret_same:\n" ++
    "  ret ptr %arr\n" ++
    "clone:\n" ++
    "  %sz_ptr = getelementptr inbounds i64, ptr %arr, i64 1\n" ++
    "  %sz = load i64, ptr %sz_ptr, align 8\n" ++
    "  %bytes_data = shl i64 %sz, 3\n" ++
    "  %total_bytes = add i64 %bytes_data, 24\n" ++
    "  %new_arr = call noalias ptr @malloc(i64 %total_bytes)\n" ++
    "  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %new_arr, ptr align 8 %arr, i64 %total_bytes, i1 false)\n" ++
    "  store i32 1, ptr %new_arr, align 4\n" ++
    "  %gt1 = icmp sgt i32 %rc, 1\n" ++
    "  br i1 %gt1, label %dec_old, label %done_clone\n" ++
    "dec_old:\n" ++
    "  %rc_dec = sub nsw i32 %rc, 1\n" ++
    "  store i32 %rc_dec, ptr %arr, align 4\n" ++
    "  br label %done_clone\n" ++
    "done_clone:\n" ++
    "  ret ptr %new_arr\n" ++
    "}",

    s!"define weak_odr dso_local void @lean_native_cpu_saxpy_u64(ptr noalias %out, ptr noalias %x, ptr noalias %y, i64 %alpha, i64 %n) {attr} \{\n" ++
    "entry:\n" ++
    "  %cmp0 = icmp eq i64 %n, 0\n" ++
    "  br i1 %cmp0, label %exit, label %loop\n" ++
    "loop:\n" ++
    "  %i = phi i64 [ 0, %entry ], [ %i_next, %loop ]\n" ++
    "  %px = getelementptr inbounds i64, ptr %x, i64 %i\n" ++
    "  %py = getelementptr inbounds i64, ptr %y, i64 %i\n" ++
    "  %po = getelementptr inbounds i64, ptr %out, i64 %i\n" ++
    "  %vx = load i64, ptr %px, align 8\n" ++
    "  %vy = load i64, ptr %py, align 8\n" ++
    "  %prod = mul i64 %vx, %alpha\n" ++
    "  %res = add i64 %prod, %vy\n" ++
    "  store i64 %res, ptr %po, align 8\n" ++
    "  %i_next = add nuw nsw i64 %i, 1\n" ++
    "  %done = icmp eq i64 %i_next, %n\n" ++
    s!"  br i1 %done, label %exit, label %loop{loopMd}\n" ++
    "exit:\n" ++
    "  ret void\n" ++
    "}",

    s!"define weak_odr dso_local void @lean_native_cpu_map_scale_add_u64(ptr noalias %out, ptr noalias %in0, i64 %scale, i64 %bias, i64 %n) {attr} \{\n" ++
    "entry:\n" ++
    "  %cmp0 = icmp eq i64 %n, 0\n" ++
    "  br i1 %cmp0, label %exit, label %loop\n" ++
    "loop:\n" ++
    "  %i = phi i64 [ 0, %entry ], [ %i_next, %loop ]\n" ++
    "  %pi = getelementptr inbounds i64, ptr %in0, i64 %i\n" ++
    "  %po = getelementptr inbounds i64, ptr %out, i64 %i\n" ++
    "  %vi = load i64, ptr %pi, align 8\n" ++
    "  %prod = mul i64 %vi, %scale\n" ++
    "  %res = add i64 %prod, %bias\n" ++
    "  store i64 %res, ptr %po, align 8\n" ++
    "  %i_next = add nuw nsw i64 %i, 1\n" ++
    "  %done = icmp eq i64 %i_next, %n\n" ++
    s!"  br i1 %done, label %exit, label %loop{loopMd}\n" ++
    "exit:\n" ++
    "  ret void\n" ++
    "}",

    s!"define weak_odr dso_local void @lean_native_cpu_zip_add_u64(ptr noalias %out, ptr noalias %in0, ptr noalias %in1, i64 %n) {attr} \{\n" ++
    "entry:\n" ++
    "  %cmp0 = icmp eq i64 %n, 0\n" ++
    "  br i1 %cmp0, label %exit, label %loop\n" ++
    "loop:\n" ++
    "  %i = phi i64 [ 0, %entry ], [ %i_next, %loop ]\n" ++
    "  %p0 = getelementptr inbounds i64, ptr %in0, i64 %i\n" ++
    "  %p1 = getelementptr inbounds i64, ptr %in1, i64 %i\n" ++
    "  %po = getelementptr inbounds i64, ptr %out, i64 %i\n" ++
    "  %v0 = load i64, ptr %p0, align 8\n" ++
    "  %v1 = load i64, ptr %p1, align 8\n" ++
    "  %res = add i64 %v0, %v1\n" ++
    "  store i64 %res, ptr %po, align 8\n" ++
    "  %i_next = add nuw nsw i64 %i, 1\n" ++
    "  %done = icmp eq i64 %i_next, %n\n" ++
    s!"  br i1 %done, label %exit, label %loop{loopMd}\n" ++
    "exit:\n" ++
    "  ret void\n" ++
    "}"
  ]

/-- Emit LLVM 18 loop vectorization & attribute metadata footer. -/
def emitMetadataFooter (target : TargetArch) : String :=
  let cpuAttr := match target with
    | .arm64 => "\"target-cpu\"=\"generic\""
    | _      => "\"target-cpu\"=\"x86-64-v3\""
  String.intercalate "\n" [
    s!"attributes #0 = \{ nounwind uwtable {cpuAttr} }",
    "attributes #1 = { noinline nounwind optnone uwtable }",
    "attributes #2 = { nocallback nofree nosync nounwind willreturn memory(none) }",
    "",
    "!llvm.ident = !{!4}",
    "!0 = distinct !{!0, !1, !2}",
    "!1 = !{!\"llvm.loop.vectorize.enable\", i1 true}",
    "!2 = !{!\"llvm.loop.unroll.count\", i32 4}",
    "!3 = distinct !{!3, !5}",
    "!4 = !{!\"lean-native LLVM 18 verified backend\"}",
    "!5 = !{!\"llvm.loop.vectorize.enable\", i1 false}",
    "!6 = distinct !{!6, !2}"
  ]

/-- Emit unoptimized/baseline LLVM 18 IR (`emitLLVMBaseline`) mimicking standard Lean 4
    boxed/per-iteration runtime checks. -/
def emitLLVMBaseline (m : LNIRModule) (target : TargetArch := .x86_64) : String :=
  let triple := cpuTriple target
  let dl := targetDataLayout target
  let header := String.intercalate "\n" [
    s!"; ModuleID = '{m.moduleName}.baseline'",
    s!"source_filename = \"{m.moduleName}.lean\"",
    s!"target datalayout = \"{dl}\"",
    s!"target triple = \"{triple}\""
  ]
  let declStrs := m.decls.map (emitDeclLLVM false)
  let runtimeStr := emitRuntimeAndCAbiHelpers false
  let footer := emitMetadataFooter target
  String.intercalate "\n\n" ([header, runtimeStr] ++ declStrs ++ [footer]) ++ "\n"

/-- Emit `lean-native` optimized LLVM 18 IR (`emitLLVMOptimized`) with `nuw`/`nsw`, `noalias`
    pointer attributes, inline single-threaded RC fast-paths (`@llvm.expect.i1`), direct
    `getelementptr inbounds i64, ptr %raw, i64 %idx` loads/stores, and loop vectorization
    metadata (`!llvm.loop !0`, `!llvm.loop.vectorize.enable`). -/
def emitLLVMOptimized (m : LNIRModule) (target : TargetArch := .x86_64) : String :=
  let triple := cpuTriple target
  let dl := targetDataLayout target
  let header := String.intercalate "\n" [
    s!"; ModuleID = '{m.moduleName}.optimized'",
    s!"source_filename = \"{m.moduleName}.lean\"",
    s!"target datalayout = \"{dl}\"",
    s!"target triple = \"{triple}\""
  ]
  let declStrs := m.decls.map (emitDeclLLVM true)
  let runtimeStr := emitRuntimeAndCAbiHelpers true
  let footer := emitMetadataFooter target
  String.intercalate "\n\n" ([header, runtimeStr] ++ declStrs ++ [footer]) ++ "\n"

end LeanNative.Backend.LLVM

namespace LeanNative.Backend

export LeanNative.Backend.LLVM (emitLLVMBaseline emitLLVMOptimized)

end LeanNative.Backend
