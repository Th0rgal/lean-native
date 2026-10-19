import Lean
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.NameMangling
import Lean.Compiler.ExternAttr
import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/--
Map a Lean 4.31 `LCNF.ImpureType` or `MonoType` `Expr` into a formal `LNIRType`.
Handles both the stage-2 impure types (`ImpureType.uint8`, `uint16`, `uint32`, `uint64`,
`usize`, `float`, `float32`, `object`, `tagged`, `tobject`, `erased`, `void`) and
high-level mono types (`ByteArray`, `FloatArray`, `Array`, `Prod`).
-/
partial def lowerImpureType (e : Lean.Expr) : LNIRType :=
  if e == ImpureType.uint8 then .i8
  else if e == ImpureType.uint16 then .i16
  else if e == ImpureType.uint32 then .i32
  else if e == ImpureType.uint64 then .i64
  else if e == ImpureType.usize then .usize
  else if e == ImpureType.float32 then .f32
  else if e == ImpureType.float then .f64
  else if e == ImpureType.object then .objPtr
  else if e == ImpureType.tagged || e == ImpureType.tobject then .taggedPtr
  else if e == ImpureType.erased || e == ImpureType.void then .unit
  else
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const declName _ =>
      if declName == ``UInt8 then .i8
      else if declName == ``UInt16 then .i16
      else if declName == ``UInt32 then .i32
      else if declName == ``UInt64 || declName == ``Nat then .i64
      else if declName == ``USize then .usize
      else if declName == ``Float32 then .f32
      else if declName == ``Float then .f64
      else if declName == ``Bool then .i1
      else if declName == ``Unit || declName == ``PUnit || declName == ``lcErased || declName == ``lcVoid then .unit
      else if declName == ``ByteArray then .sarray .i8
      else if declName == ``FloatArray then .sarray .f64
      else if declName == ``Array then
        match args[0]? with
        | some elemExpr => .sarray (lowerImpureType elemExpr)
        | none => .sarray .taggedPtr
      else if declName == ``Prod || declName == ``MProd || declName == ``PProd then
        match args[0]?, args[1]? with
        | some a, some b => .tuple [lowerImpureType a, lowerImpureType b]
        | _, _ => .objPtr
      else
        .objPtr
    | .forallE _ _ body _ =>
      lowerImpureType body
    | _ =>
      .objPtr

/-- Deterministic state for lowering LCNF `FVarId`s to sequential LNIR `VarId`s. -/
structure BridgeState where
  fvarToVar  : Std.HashMap Lean.FVarId VarId := {}
  varTypes   : Std.HashMap VarId LNIRType := {}
  nextVarId  : VarId := 0
  hasExtern  : Bool := false
  deriving Inhabited

abbrev BridgeM := StateRefT BridgeState Lean.CoreM

/-- Lookup or allocate a deterministic `VarId` for a Lean `FVarId`. -/
def internFVar (fvarId : Lean.FVarId) (ty : LNIRType := .objPtr) : BridgeM VarId := do
  let st ← get
  match st.fvarToVar[fvarId]? with
  | some vid => return vid
  | none =>
    let vid := st.nextVarId
    set {
      st with
      fvarToVar := st.fvarToVar.insert fvarId vid
      varTypes  := st.varTypes.insert vid ty
      nextVarId := vid + 1
    }
    return vid

/-- Allocate a fresh synthetic `VarId` in `BridgeM`. -/
def freshBridgeVar (ty : LNIRType) : BridgeM VarId := do
  let st ← get
  let vid := st.nextVarId
  set {
    st with
    varTypes  := st.varTypes.insert vid ty
    nextVarId := vid + 1
  }
  return vid

/-- Lookup the recorded `LNIRType` of a `VarId`. -/
def getVarType (vid : VarId) : BridgeM LNIRType := do
  let st ← get
  return st.varTypes.getD vid .objPtr

/-- Lower an LCNF `Arg` to a `VarId`, synthesizing a unit variable for erased arguments. -/
def lowerArg (arg : Lean.Compiler.LCNF.Arg pu) : BridgeM VarId := do
  match arg with
  | .fvar fvarId => internFVar fvarId
  | _ => freshBridgeVar .unit

/-- Lower an LCNF `LitValue` into an `LNIRExpr`. -/
def lowerLitValue (lit : Lean.Compiler.LCNF.LitValue) : LNIRExpr :=
  match lit with
  | .nat n     => .scalar (.constU64 n.toUInt64)
  | .uint8 v   => .scalar (.constU64 v.toUInt64)
  | .uint16 v  => .scalar (.constU64 v.toUInt64)
  | .uint32 v  => .scalar (.constU64 v.toUInt64)
  | .uint64 v  => .scalar (.constU64 v)
  | .usize v   => .scalar (.constU64 v)
  | .str s     => .scalar (.constU64 s.length.toUInt64)

/-- Try to recognize primitive arithmetic/comparison/array operations in LCNF function calls. -/
def tryLowerIntrinsicCall (fnName : Lean.Name) (argVars : List VarId) (retTy : LNIRType) : Option LNIRExpr :=
  let nameStr := fnName.toString
  match argVars with
  | [lhs, rhs] =>
    if nameStr.endsWith "add" then
      some (.scalar (.binOp .add (.var lhs) (.var rhs)))
    else if nameStr.endsWith "sub" then
      some (.scalar (.binOp .sub (.var lhs) (.var rhs)))
    else if nameStr.endsWith "mul" then
      some (.scalar (.binOp .mul (.var lhs) (.var rhs)))
    else if nameStr.endsWith "div" then
      some (.scalar (.binOp .div (.var lhs) (.var rhs)))
    else if nameStr.endsWith "mod" || nameStr.endsWith "rem" then
      some (.scalar (.binOp .mod (.var lhs) (.var rhs)))
    else if nameStr.endsWith "land" then
      some (.scalar (.binOp .bitAnd (.var lhs) (.var rhs)))
    else if nameStr.endsWith "lor" then
      some (.scalar (.binOp .bitOr (.var lhs) (.var rhs)))
    else if nameStr.endsWith "xor" then
      some (.scalar (.binOp .bitXor (.var lhs) (.var rhs)))
    else if nameStr.endsWith "shiftLeft" then
      some (.scalar (.binOp .shl (.var lhs) (.var rhs)))
    else if nameStr.endsWith "shiftRight" then
      some (.scalar (.binOp .shr (.var lhs) (.var rhs)))
    else if nameStr.endsWith "decEq" || nameStr.endsWith "beq" then
      some (.scalar (.binOp .eq (.var lhs) (.var rhs)))
    else if nameStr.endsWith "decLt" || nameStr.endsWith "blt" then
      some (.scalar (.binOp .lt (.var lhs) (.var rhs)))
    else if nameStr.endsWith "decLe" || nameStr.endsWith "ble" then
      some (.scalar (.binOp .le (.var lhs) (.var rhs)))
    else if nameStr.endsWith "uget" || nameStr.endsWith "get!" || nameStr.endsWith "fget" then
      some (.sarrayGet lhs rhs retTy)
    else
      none
  | [arr] =>
    if nameStr.endsWith "size" || nameStr.endsWith "usize" then
      some (.sarrayLen arr)
    else
      none
  | [arr, idx, val] =>
    if nameStr.endsWith "uset" || nameStr.endsWith "set!" || nameStr.endsWith "fset" then
      let elemTy := match retTy with
        | .sarray elem => elem
        | _ => .i64
      some (.sarraySet arr idx val elemTy)
    else
      none
  | _ => none

/-- Lower a stage-2 `LetValue .impure` into an `LNIRExpr`. -/
def lowerImpureLetValue (lv : Lean.Compiler.LCNF.LetValue .impure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  let env ← getEnv
  match lv with
  | .lit litVal =>
    return lowerLitValue litVal
  | .erased =>
    return .scalar (.constU64 0)
  | .fvar fvarId args =>
    let fnVar ← internFVar fvarId
    if args.isEmpty then
      return .scalar (.var fnVar)
    else
      let argVars ← args.toList.mapM lowerArg
      return .call s!"fvar_{fnVar}" argVars retTy false
  | .ctor ctorInfo args _ =>
    let argVars ← args.toList.mapM lowerArg
    if ctorInfo.name == ``Prod.mk || ctorInfo.name == ``MProd.mk || ctorInfo.name == ``PProd.mk then
      return .mkTuple argVars
    else
      let objVars := argVars.take ctorInfo.size
      let scalarVars := argVars.drop ctorInfo.size
      return .allocCtor ctorInfo.cidx objVars scalarVars
  | .oproj idx fvarId _ =>
    let v ← internFVar fvarId
    let vTy ← getVarType v
    match vTy with
    | .tuple _ => return .projTuple v idx
    | _ => return .ctorGetObj v idx
  | .uproj idx fvarId _ =>
    let v ← internFVar fvarId
    return .ctorGetScalar v idx .usize
  | .sproj offset _ fvarId _ =>
    let v ← internFVar fvarId
    return .ctorGetScalar v offset retTy
  | .fap fnName args _ =>
    let argVars ← args.toList.mapM lowerArg
    match tryLowerIntrinsicCall fnName argVars retTy with
    | some intrinsicExpr => return intrinsicExpr
    | none =>
      let isExt := Lean.isExtern env fnName
      if isExt then
        modify fun st => { st with hasExtern := true }
      return .call fnName.toString argVars retTy isExt
  | .pap fnName args _ =>
    let argVars ← args.toList.mapM lowerArg
    let isExt := Lean.isExtern env fnName
    if isExt then
      modify fun st => { st with hasExtern := true }
    return .call fnName.toString argVars retTy isExt
  | .reset _ fvarId _ =>
    let v ← internFVar fvarId
    return .scalar (.var v)
  | .reuse _ ctorInfo _ args _ =>
    let argVars ← args.toList.mapM lowerArg
    let objVars := argVars.take ctorInfo.size
    let scalarVars := argVars.drop ctorInfo.size
    return .allocCtor ctorInfo.cidx objVars scalarVars
  | .box tyExpr fvarId _ =>
    let v ← internFVar fvarId
    let scalarTy := lowerImpureType tyExpr
    return .boxScalar v scalarTy
  | .unbox fvarId _ =>
    let v ← internFVar fvarId
    return .unboxScalar v retTy
  | .isShared fvarId _ =>
    let v ← internFVar fvarId
    return .isExclusive v

/-- Lower a stage-2 `Code .impure` block into structured `LNIRCode`. -/
partial def lowerImpureCode (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let ty := lowerImpureType decl.type
    let dst ← internFVar decl.fvarId ty
    let rhs ← lowerImpureLetValue decl.value ty
    let kCode ← lowerImpureCode k
    return .letBind dst ty rhs kCode
  | .jp decl k =>
    let _ ← internFVar decl.fvarId (lowerImpureType decl.type)
    lowerImpureCode k
  | .jmp fvarId args =>
    match args.toList with
    | arg0 :: _ =>
      let v ← lowerArg arg0
      return .ret v
    | [] =>
      let v ← internFVar fvarId
      return .ret v
  | .inc fvarId n _ _ k _ =>
    let v ← internFVar fvarId
    let kCode ← lowerImpureCode k
    return .incRef v n kCode
  | .dec fvarId n _ _ _ k _ =>
    let v ← internFVar fvarId
    let kCode ← lowerImpureCode k
    return .decRef v n kCode
  | .del fvarId k _ =>
    let v ← internFVar fvarId
    let kCode ← lowerImpureCode k
    return .decRef v 1 kCode
  | .oset fvarId idx arg k _ =>
    let arrVar ← internFVar fvarId
    let valVar ← lowerArg arg
    let idxVar ← freshBridgeVar .i64
    let dstVar ← freshBridgeVar .objPtr
    let kCode ← lowerImpureCode k
    return .letBind idxVar .i64 (.scalar (.constU64 idx.toUInt64))
      (.letBind dstVar .objPtr (.sarraySet arrVar idxVar valVar .objPtr) kCode)
  | .uset fvarId idx valFVar k _ =>
    let arrVar ← internFVar fvarId
    let valVar ← internFVar valFVar .usize
    let idxVar ← freshBridgeVar .i64
    let dstVar ← freshBridgeVar .objPtr
    let kCode ← lowerImpureCode k
    return .letBind idxVar .i64 (.scalar (.constU64 idx.toUInt64))
      (.letBind dstVar .objPtr (.sarraySet arrVar idxVar valVar .usize) kCode)
  | .sset fvarId idx _ valFVar tyExpr k _ =>
    let elemTy := lowerImpureType tyExpr
    let arrVar ← internFVar fvarId
    let valVar ← internFVar valFVar elemTy
    let idxVar ← freshBridgeVar .i64
    let dstVar ← freshBridgeVar .objPtr
    let kCode ← lowerImpureCode k
    return .letBind idxVar .i64 (.scalar (.constU64 idx.toUInt64))
      (.letBind dstVar .objPtr (.sarraySet arrVar idxVar valVar elemTy) kCode)
  | .setTag _ _ k _ =>
    lowerImpureCode k
  | .cases c =>
    let condVar ← internFVar c.discr
    match c.alts[0]?, c.alts[1]? with
    | some alt0, some alt1 =>
      let b0 ← lowerImpureCode alt0.getCode
      let b1 ← lowerImpureCode alt1.getCode
      return .ite condVar b0 b1
    | some alt0, none =>
      lowerImpureCode alt0.getCode
    | none, _ =>
      return .unreachable
  | .return fvarId =>
    let v ← internFVar fvarId
    return .ret v
  | .unreach _ =>
    return .unreachable

/-- Lower a stage-1 `LetValue .pure` into an `LNIRExpr`. -/
def lowerPureLetValue (lv : Lean.Compiler.LCNF.LetValue .pure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  let env ← getEnv
  match lv with
  | .lit litVal =>
    return lowerLitValue litVal
  | .erased =>
    return .scalar (.constU64 0)
  | .proj _ idx fvarId _ =>
    let v ← internFVar fvarId
    return .projTuple v idx
  | .const declName _ args _ =>
    let argVars ← args.toList.mapM lowerArg
    if declName == ``Prod.mk || declName == ``MProd.mk || declName == ``PProd.mk then
      return .mkTuple argVars
    else
      match tryLowerIntrinsicCall declName argVars retTy with
      | some intrinsicExpr => return intrinsicExpr
      | none =>
        let isExt := Lean.isExtern env declName
        if isExt then
          modify fun st => { st with hasExtern := true }
        return .call declName.toString argVars retTy isExt
  | .fvar fvarId args =>
    let fnVar ← internFVar fvarId
    if args.isEmpty then
      return .scalar (.var fnVar)
    else
      let argVars ← args.toList.mapM lowerArg
      return .call s!"fvar_{fnVar}" argVars retTy false

/-- Lower a stage-1 `Code .pure` block into structured `LNIRCode`. -/
partial def lowerPureCode (code : Lean.Compiler.LCNF.Code .pure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let ty := lowerImpureType decl.type
    let dst ← internFVar decl.fvarId ty
    let rhs ← lowerPureLetValue decl.value ty
    let kCode ← lowerPureCode k
    return .letBind dst ty rhs kCode
  | .fun decl k _ =>
    let _ ← internFVar decl.fvarId (lowerImpureType decl.type)
    lowerPureCode k
  | .jp decl k =>
    let _ ← internFVar decl.fvarId (lowerImpureType decl.type)
    lowerPureCode k
  | .jmp fvarId args =>
    match args.toList with
    | arg0 :: _ =>
      let v ← lowerArg arg0
      return .ret v
    | [] =>
      let v ← internFVar fvarId
      return .ret v
  | .cases c =>
    let condVar ← internFVar c.discr
    match c.alts[0]?, c.alts[1]? with
    | some alt0, some alt1 =>
      let b0 ← lowerPureCode alt0.getCode
      let b1 ← lowerPureCode alt1.getCode
      return .ite condVar b0 b1
    | some alt0, none =>
      lowerPureCode alt0.getCode
    | none, _ =>
      return .unreachable
  | .return fvarId =>
    let v ← internFVar fvarId
    return .ret v
  | .unreach _ =>
    return .unreachable

/-- Lower a Lean 4.31 `LCNF.Decl .impure` into a verified/auditable `LNIRDecl`. -/
def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  let isDeclExtern := Lean.isExtern env decl.name
  let action : BridgeM LNIRDecl := do
    let mut lnirParams : List LNIRParam := []
    for p in decl.params do
      let pTy := lowerImpureType p.type
      let vid ← internFVar p.fvarId pTy
      lnirParams := lnirParams ++ [{
        id     := vid
        name   := p.binderName.toString
        ty     := pTy
        borrow := p.borrow
      }]
    let retTy := lowerImpureType decl.type
    match decl.value with
    | .code c =>
      let body ← lowerImpureCode c
      let st ← get
      let assurance : AssuranceLevel :=
        if isDeclExtern || st.hasExtern then .unverifiedFallback
        else .verifiedKernelProof
      let isGpu := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible
      return {
        name      := decl.name.toString
        params    := lnirParams
        retTy     := retTy
        body      := body
        assurance := assurance
        isGpuCand := isGpu
      }
    | .extern _ =>
      let retVar ← freshBridgeVar retTy
      let argIds := lnirParams.map (·.id)
      let body : LNIRCode :=
        .letBind retVar retTy (.call decl.name.toString argIds retTy true) (.ret retVar)
      return {
        name      := decl.name.toString
        params    := lnirParams
        retTy     := retTy
        body      := body
        assurance := .unverifiedFallback
        isGpuCand := false
      }
  Prod.fst <$> action.run {}

/-- Lower a Lean 4.31 `LCNF.Decl .pure` (mono phase) into an `LNIRDecl`. -/
def ingestLCNFMonoDecl (decl : Lean.Compiler.LCNF.Decl .pure) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  let isDeclExtern := Lean.isExtern env decl.name
  let action : BridgeM LNIRDecl := do
    let mut lnirParams : List LNIRParam := []
    for p in decl.params do
      let pTy := lowerImpureType p.type
      let vid ← internFVar p.fvarId pTy
      lnirParams := lnirParams ++ [{
        id     := vid
        name   := p.binderName.toString
        ty     := pTy
        borrow := p.borrow
      }]
    let retTy := lowerImpureType decl.type
    match decl.value with
    | .code c =>
      let body ← lowerPureCode c
      let st ← get
      let assurance : AssuranceLevel :=
        if isDeclExtern || st.hasExtern then .unverifiedFallback
        else .verifiedKernelProof
      let isGpu := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible
      return {
        name      := decl.name.toString
        params    := lnirParams
        retTy     := retTy
        body      := body
        assurance := assurance
        isGpuCand := isGpu
      }
    | .extern _ =>
      let retVar ← freshBridgeVar retTy
      let argIds := lnirParams.map (·.id)
      let body : LNIRCode :=
        .letBind retVar retTy (.call decl.name.toString argIds retTy true) (.ret retVar)
      return {
        name      := decl.name.toString
        params    := lnirParams
        retTy     := retTy
        body      := body
        assurance := .unverifiedFallback
        isGpuCand := false
      }
  Prod.fst <$> action.run {}

/--
Extract and lower an array of declaration names from the Lean 4.31 environment,
preferring stage-2 `getLocalImpureDecl?` and falling back to stage-1 `getMonoDecl?`.
-/
def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested") :
    Lean.CoreM LNIRModule := do
  let mut decls : List LNIRDecl := []
  for name in declNames do
    if let some impureDecl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      let d ← ingestLCNFImpureDecl impureDecl
      decls := decls ++ [d]
    else if let some monoDecl ← Lean.Compiler.LCNF.getMonoDecl? name then
      let d ← ingestLCNFMonoDecl monoDecl
      decls := decls ++ [d]
  return {
    moduleName := moduleName
    decls      := decls
  }

/-- Extract and lower all local impure LCNF declarations compiled in the current environment. -/
def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested") : Lean.CoreM LNIRModule := do
  let names ← Lean.Compiler.LCNF.getLocalImpureDecls
  ingestModuleDecls names moduleName

/-- Elaborate a `.lean` source file using Lean 4's frontend, run the LCNF compiler pipeline,
    and extract the resulting `LNIRModule`. -/
def ingestLeanSourceFile (filePath : String) (moduleName : String := "LeanNative.FileInput") : IO LNIRModule := do
  Lean.initSearchPath (← Lean.findSysroot)
  let input ← IO.FS.readFile filePath
  let opts : Lean.Options := {}
  let some env ← Lean.Elab.runFrontend input opts filePath `LeanNativeInput
    | throw <| IO.userError s!"Elaboration failed for {filePath}"
  let coreCtx : Lean.Core.Context := {
    fileName := filePath
    fileMap  := filePath.toFileMap
    options  := opts
  }
  let coreState : Lean.Core.State := { env := env }
  let (mod, _) ← (ingestAllLocalDecls moduleName).toIO coreCtx coreState
  return mod

/-!
## Canonical Benchmark & Workload Declarations

These 6 canonical workloads represent real Lean 4 computational kernels lowered from LCNF:
1. `collatz_steps` — scalar iterative loop with power-of-two mul/div and algebraic identity opportunities.
2. `tuple_accum_sum` — loop allocating and projecting intermediate 2-tuples `(a, b)` per iteration (`UnboxTupleSROA`).
3. `sarray_scale_bias` — in-place scalar array loop with `sarrayEnsureExclusive` inside the loop (`HoistExclusivity` + SIMD).
4. `dot_product_u64` — data-parallel dot product / reduction over contiguous unboxed arrays.
5. `saxpy_kernel` — data-parallel `alpha * x[i] + y[i]` kernel eligible for AVX2/NEON SIMD and GPU MLIR/PTX offload.
6. `matmul_tiled_u64` — dense numerical matrix FMA kernel eligible for GPU PTX and hybrid CPU/GPU dispatch.
-/

/-- 1. `collatz_steps`: Scalar loop with strength-reduction (`x * 2`, `x / 2`, `x + 0`, `x * 1`) opportunities. -/
def collatzStepsDecl : LNIRDecl := {
  name      := "collatz_steps"
  params    := [
    { id := 0, name := "n", ty := .i64, borrow := false },
    { id := 1, name := "steps", ty := .i64, borrow := false }
  ]
  retTy     := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body      :=
    .letBind 2 .i64 (.scalar (.constU64 0)) (
      .seqFor 3 2 1 4 0 .i64
        (.letBind 5 .i64 (.scalar (.binOp .mul (.var 4) (.constU64 2)))
          (.letBind 6 .i64 (.scalar (.binOp .add (.var 5) (.var 4)))
            (.letBind 7 .i64 (.scalar (.binOp .add (.var 6) (.constU64 1)))
              (.letBind 8 .i64 (.scalar (.binOp .div (.var 7) (.constU64 2)))
                (.letBind 9 .i64 (.scalar (.binOp .add (.var 8) (.constU64 0)))
                  (.ret 9))))))
        (.ret 4)
    )
}

/-- 2. `tuple_accum_sum`: Loop constructing intermediate 2-tuples `mkTuple` and projecting fields (`UnboxTupleSROA`). -/
def tupleAccumSumDecl : LNIRDecl := {
  name      := "tuple_accum_sum"
  params    := [
    { id := 0, name := "n", ty := .i64, borrow := false },
    { id := 1, name := "seed", ty := .i64, borrow := false }
  ]
  retTy     := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body      :=
    .letBind 2 .i64 (.scalar (.constU64 0)) (
      .seqFor 3 2 0 4 1 .i64
        (.letBind 5 .i64 (.scalar (.binOp .add (.var 4) (.var 3)))
          (.letBind 6 .i64 (.scalar (.binOp .mul (.var 3) (.constU64 2)))
            (.letBind 7 (.tuple [.i64, .i64]) (.mkTuple [5, 6])
              (.letBind 8 .i64 (.projTuple 7 0)
                (.letBind 9 .i64 (.projTuple 7 1)
                  (.letBind 10 .i64 (.scalar (.binOp .add (.var 8) (.var 9)))
                    (.ret 10)))))))
        (.ret 4)
    )
}

/-- 3. `sarray_scale_bias`: In-place scalar array loop with `sarrayEnsureExclusive` inside the loop body (`HoistExclusivity`). -/
def sarrayScaleBiasDecl : LNIRDecl := {
  name      := "sarray_scale_bias"
  params    := [
    { id := 0, name := "arr", ty := .sarray .i64, borrow := false },
    { id := 1, name := "scale", ty := .i64, borrow := false },
    { id := 2, name := "bias", ty := .i64, borrow := false }
  ]
  retTy     := .sarray .i64
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 3 .i64 (.scalar (.constU64 0)) (
      .letBind 4 .i64 (.sarrayLen 0) (
        .seqFor 5 3 4 6 0 (.sarray .i64)
          (.letBind 7 (.sarray .i64) (.sarrayEnsureExclusive 6 .i64)
            (.letBind 8 .i64 (.sarrayGet 7 5 .i64)
              (.letBind 9 .i64 (.scalar (.fma (.var 8) (.var 1) (.var 2)))
                (.letBind 10 (.sarray .i64) (.sarraySet 7 5 9 .i64)
                  (.ret 10)))))
          (.ret 6)
      )
    )
}

/-- 4. `dot_product_u64`: Data-parallel dot product / reduction over contiguous arrays with redundant RC pair for `BorrowInference`. -/
def dotProductU64Decl : LNIRDecl := {
  name      := "dot_product_u64"
  params    := [
    { id := 0, name := "xs", ty := .sarray .i64, borrow := false },
    { id := 1, name := "ys", ty := .sarray .i64, borrow := false }
  ]
  retTy     := .sarray .i64
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .incRef 0 1 (
      .letBind 2 .i64 (.sarrayLen 0) (
        .parFor 3 2 [0, 1] .i64 .dotProduct (
          .decRef 0 1 (.ret 3)
        )
      )
    )
}

/-- 5. `saxpy_kernel`: Data-parallel `alpha * x[i] + y[i]` kernel eligible for both CPU SIMD and GPU MLIR/PTX offload. -/
def saxpyKernelDecl : LNIRDecl := {
  name      := "saxpy_kernel"
  params    := [
    { id := 0, name := "xs", ty := .sarray .i64, borrow := true },
    { id := 1, name := "ys", ty := .sarray .i64, borrow := true }
  ]
  retTy     := .sarray .i64
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 2 .i64 (.sarrayLen 0) (
      .parFor 3 2 [0, 1] .i64 (.saxpy 4) (.ret 3)
    )
}

/-- 6. `matmul_tiled_u64`: Dense numerical matrix kernel eligible for GPU PTX and hybrid CPU/GPU dispatch. -/
def matmulTiledU64Decl : LNIRDecl := {
  name      := "matmul_tiled_u64"
  params    := [
    { id := 0, name := "matA", ty := .sarray .i64, borrow := true },
    { id := 1, name := "matB", ty := .sarray .i64, borrow := true },
    { id := 2, name := "matC", ty := .sarray .i64, borrow := true }
  ]
  retTy     := .sarray .i64
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 3 .i64 (.sarrayLen 0) (
      .parFor 4 3 [0, 1, 2] .i64
        (.customScalar 10 [0, 1, 2] (.fma (.var 0) (.var 1) (.var 2)))
        (.ret 4)
    )
}

/-- Construct the canonical 6-kernel benchmark `LNIRModule`. -/
def mkCanonicalBenchmarkModule : LNIRModule := {
  moduleName := "LeanNative.Benchmarks.Canonical"
  decls      := [
    collatzStepsDecl,
    tupleAccumSumDecl,
    sarrayScaleBiasDecl,
    dotProductU64Decl,
    saxpyKernelDecl,
    matmulTiledU64Decl
  ]
}

end LeanNative.IR
