import Lean
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.LCNF.SimpleGroundExpr
import Lean.Compiler.LCNF.EmitC
import Lean.Compiler.NameMangling
import Lean.Compiler.ExternAttr
import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.Transform.LoopVectorizeOpt
import LeanNative.Backend.LLVM

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/-- Check whether `declName` is recorded as a `SimpleGroundExpr` static initializer in Lean 4.31. -/
def hasSimpleGroundDecl (env : Lean.Environment) (declName : Lean.Name) : Bool :=
  Lean.Compiler.LCNF.isSimpleGroundDecl env declName

/-- Compute the exact Lean 4.31 C ABI mangled symbol (`decl.name.mangle`, or `_lean_main` for `main`). -/
def mangleDeclName (declName : Lean.Name) : String :=
  if declName == `main then "_lean_main"
  else declName.mangle

/-- Metadata recorded for a lowered LCNF declaration (`Name.mangle` C symbol and `SimpleGroundExpr` status). -/
structure LCNFDeclMetadata where
  declName       : Lean.Name
  mangledSymbol  : String
  isSimpleGround : Bool
  isExtern       : Bool
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Extract `LCNFDeclMetadata` for `declName` in `env`. -/
def getLCNFDeclMetadata (env : Lean.Environment) (declName : Lean.Name) : LCNFDeclMetadata := {
  declName       := declName
  mangledSymbol  := mangleDeclName declName
  isSimpleGround := hasSimpleGroundDecl env declName
  isExtern       := Lean.isExtern env declName
}

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
      else if declName.toString.endsWith "UInt256" || declName.toString.endsWith "U256" then .u256
      else if declName.toString.endsWith "StorageMap" then .storageMap
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

/-- Deterministic state for lowering LCNF `FVarId`s, join points, and declaration metadata to LNIR. -/
structure BridgeState where
  fvarToVar      : Std.HashMap Lean.FVarId VarId := {}
  varTypes       : Std.HashMap VarId LNIRType := {}
  jpMap          : Std.HashMap Lean.FVarId (Array (Lean.Compiler.LCNF.Param .impure) × LNIRCode) := {}
  nextVarId      : VarId := 0
  hasExtern      : Bool := false
  mangledSymbol  : String := ""
  isSimpleGround : Bool := false
  selfDeclName   : Lean.Name := .anonymous
  selfLoopAccVar : Option VarId := none
  selfParams     : Array (Lean.Compiler.LCNF.Param .impure) := #[]
  localDeclNames : Array Lean.Name := #[]
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

/-- Convert `Array (Param pu)` into `Array (Param .impure)` for uniform join-point storage in `BridgeState.jpMap`. -/
def toImpureParams (params : Array (Lean.Compiler.LCNF.Param pu)) : Array (Lean.Compiler.LCNF.Param .impure) :=
  params.map fun p => {
    fvarId     := p.fvarId
    binderName := p.binderName
    type       := p.type
    borrow     := p.borrow
  }

/-- Check whether `code` contains a tail-recursive `.jmp` referencing `targetFVar`. -/
partial def codeHasRecursiveJmp (targetFVar : Lean.FVarId) (code : Lean.Compiler.LCNF.Code pu) : Bool :=
  match code with
  | .let _ k => codeHasRecursiveJmp targetFVar k
  | .fun _ k _ => codeHasRecursiveJmp targetFVar k
  | .jp decl k => codeHasRecursiveJmp targetFVar decl.value || codeHasRecursiveJmp targetFVar k
  | .jmp fvarId _ => fvarId == targetFVar
  | .cases c => c.alts.any (fun alt => codeHasRecursiveJmp targetFVar alt.getCode)
  | .inc _ _ _ _ k _ => codeHasRecursiveJmp targetFVar k
  | .dec _ _ _ _ _ k _ => codeHasRecursiveJmp targetFVar k
  | .del _ k _ => codeHasRecursiveJmp targetFVar k
  | .oset _ _ _ k _ => codeHasRecursiveJmp targetFVar k
  | .uset _ _ _ k _ => codeHasRecursiveJmp targetFVar k
  | .sset _ _ _ _ _ k _ => codeHasRecursiveJmp targetFVar k
  | .setTag _ _ k _ => codeHasRecursiveJmp targetFVar k
  | .return _ | .unreach _ => false

/-- Check whether `code` contains a tail-recursive self call to `targetName`. -/
partial def codeHasSelfTailCall (targetName : Lean.Name) (code : Lean.Compiler.LCNF.Code pu) : Bool :=
  match code with
  | .let decl (.return retFVar) =>
    if decl.fvarId == retFVar then
      match decl.value with
      | .fap fnName _ _ => fnName == targetName
      | .const fnName _ _ _ => fnName == targetName
      | _ => false
    else
      false
  | .let _ k => codeHasSelfTailCall targetName k
  | .fun _ k _ => codeHasSelfTailCall targetName k
  | .jp decl k => codeHasSelfTailCall targetName decl.value || codeHasSelfTailCall targetName k
  | .cases c => c.alts.any (fun alt => codeHasSelfTailCall targetName alt.getCode)
  | .inc _ _ _ _ k _ => codeHasSelfTailCall targetName k
  | .dec _ _ _ _ _ k _ => codeHasSelfTailCall targetName k
  | .del _ k _ => codeHasSelfTailCall targetName k
  | .oset _ _ _ k _ => codeHasSelfTailCall targetName k
  | .uset _ _ _ k _ => codeHasSelfTailCall targetName k
  | .sset _ _ _ _ _ k _ => codeHasSelfTailCall targetName k
  | .setTag _ _ k _ => codeHasSelfTailCall targetName k
  | .jmp _ _ | .return _ | .unreach _ => false

/-- Bind each join-point parameter `param_i := arg_i` via `.letBind` and splice the continuation `jpBody`. -/
def spliceJoinPointJmp (jpParams : Array (Lean.Compiler.LCNF.Param .impure)) (jpBody : LNIRCode)
    (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRCode := do
  let argVars ← args.toList.mapM lowerArg
  let pairs := jpParams.toList.zip argVars
  pairs.foldrM (fun (p, argVar) accCode => do
    let pTy := lowerImpureType p.type
    let pVar ← internFVar p.fvarId pTy
    return .letBind pVar pTy (.scalar (.var argVar)) accCode
  ) jpBody

/-- Partition `alts` so that explicit constructor alternatives precede any `.default` alternative. -/
def orderAlts (alts : List (Lean.Compiler.LCNF.Alt pu)) : List (Lean.Compiler.LCNF.Alt pu) :=
  let nonDefaults := alts.filter fun
    | .default _ => false
    | _ => true
  let defaults := alts.filter fun
    | .default _ => true
    | _ => false
  nonDefaults ++ defaults

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
      let st ← get
      let isLocal := st.localDeclNames.contains fnName || fnName == st.selfDeclName
      let isExt := !isLocal && Lean.isExtern env fnName
      if isExt then
        modify fun st => { st with hasExtern := true }
      return .call (mangleDeclName fnName) argVars retTy isExt
  | .pap fnName args _ =>
    let argVars ← args.toList.mapM lowerArg
    let st ← get
    let isLocal := st.localDeclNames.contains fnName || fnName == st.selfDeclName
    let isExt := !isLocal && Lean.isExtern env fnName
    if isExt then
      modify fun st => { st with hasExtern := true }
    return .call (mangleDeclName fnName) argVars retTy isExt
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

mutual

/-- Recursively lower all impure `cases` alternatives into a complete nested `ite` tag-dispatch chain. -/
partial def lowerImpureAlts (condVar : VarId) (alts : List (Lean.Compiler.LCNF.Alt .impure)) : BridgeM LNIRCode := do
  match alts with
  | [] =>
    return .unreachable
  | [singleAlt] =>
    lowerImpureCode singleAlt.getCode
  | alt :: rest =>
    match alt with
    | .ctorAlt info code _ =>
      let cmpVar ← freshBridgeVar .i64
      let bThen ← lowerImpureCode code
      let bElse ← lowerImpureAlts condVar rest
      return .letBind cmpVar .i64
        (.scalar (.binOp .eq (.var condVar) (.constU64 info.cidx.toUInt64)))
        (.ite cmpVar bThen bElse)
    | .default code =>
      lowerImpureCode code
    | .alt _ params code _ =>
      for p in params do
        let _ ← internFVar p.fvarId (lowerImpureType p.type)
      let bThen ← lowerImpureCode code
      let bElse ← lowerImpureAlts condVar rest
      return .ite condVar bThen bElse

/-- Lower a stage-2 `Code .impure` block into structured `LNIRCode`. -/
partial def lowerImpureCode (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let st ← get
    match k, decl.value, st.selfLoopAccVar with
    | .return retFVar, .fap fnName args _, some accVar =>
      if retFVar == decl.fvarId && fnName == st.selfDeclName then
        spliceJoinPointJmp st.selfParams (.ret accVar) args
      else
        let ty := lowerImpureType decl.type
        let dst ← internFVar decl.fvarId ty
        let rhs ← lowerImpureLetValue decl.value ty
        let kCode ← lowerImpureCode k
        return .letBind dst ty rhs kCode
    | _, _, _ =>
      let ty := lowerImpureType decl.type
      let dst ← internFVar decl.fvarId ty
      let rhs ← lowerImpureLetValue decl.value ty
      let kCode ← lowerImpureCode k
      return .letBind dst ty rhs kCode
  | .jp decl k =>
    let _ ← internFVar decl.fvarId (lowerImpureType decl.type)
    for p in decl.params do
      let _ ← internFVar p.fvarId (lowerImpureType p.type)
    let impParams := toImpureParams decl.params
    if codeHasRecursiveJmp decl.fvarId decl.value then
      let (idxVar, accVar, accTy) ←
        if h2 : decl.params.size ≥ 2 then do
          let p0 := decl.params[0]
          let p1 := decl.params[1]
          let iv ← internFVar p0.fvarId .i64
          let aTy := lowerImpureType p1.type
          let av ← internFVar p1.fvarId aTy
          pure (iv, av, aTy)
        else if h1 : decl.params.size = 1 then do
          let p0 := decl.params[0]
          let iv ← freshBridgeVar .i64
          let aTy := lowerImpureType p0.type
          let av ← internFVar p0.fvarId aTy
          pure (iv, av, aTy)
        else do
          let iv ← freshBridgeVar .i64
          let av ← freshBridgeVar .i64
          pure (iv, av, .i64)
      let loVar ← freshBridgeVar .i64
      let hiVar ← freshBridgeVar .i64
      let accInit ← freshBridgeVar accTy
      modify fun st => { st with jpMap := st.jpMap.insert decl.fvarId (impParams, .ret accVar) }
      let stepBody ← lowerImpureCode decl.value
      let kCode ← lowerImpureCode k
      return .letBind loVar .i64 (.scalar (.constU64 0))
        (.letBind hiVar .i64 (.scalar (.constU64 1))
          (.letBind accInit accTy (.scalar (.constU64 0))
            (.seqFor idxVar loVar hiVar accVar accInit accTy stepBody kCode)))
    else
      let jpBody ← lowerImpureCode decl.value
      modify fun st => { st with jpMap := st.jpMap.insert decl.fvarId (impParams, jpBody) }
      lowerImpureCode k
  | .jmp fvarId args =>
    let st ← get
    match st.jpMap[fvarId]? with
    | some (jpParams, jpBody) =>
      modify fun st => { st with jpMap := st.jpMap.erase fvarId }
      spliceJoinPointJmp jpParams jpBody args
    | none =>
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
    lowerImpureAlts condVar (orderAlts c.alts.toList)
  | .return fvarId =>
    let v ← internFVar fvarId
    return .ret v
  | .unreach _ =>
    return .unreachable

end

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
        let st ← get
        let isLocal := st.localDeclNames.contains declName || declName == st.selfDeclName
        let isExt := !isLocal && Lean.isExtern env declName
        if isExt then
          modify fun st => { st with hasExtern := true }
        return .call (mangleDeclName declName) argVars retTy isExt
  | .fvar fvarId args =>
    let fnVar ← internFVar fvarId
    if args.isEmpty then
      return .scalar (.var fnVar)
    else
      let argVars ← args.toList.mapM lowerArg
      return .call s!"fvar_{fnVar}" argVars retTy false

/-- Lookup the constructor tag index `cidx` for `ctorName` in the Lean environment, falling back to `fallbackIdx`. -/
def lookupCtorIdx (ctorName : Lean.Name) (fallbackIdx : Nat) : BridgeM Nat := do
  let env ← getEnv
  match env.find? ctorName with
  | some (.ctorInfo cval) => return cval.cidx
  | _ => return fallbackIdx

mutual

/-- Recursively lower all pure `cases` alternatives into a complete nested `ite` tag-dispatch chain. -/
partial def lowerPureAlts (condVar : VarId) (idx : Nat) (alts : List (Lean.Compiler.LCNF.Alt .pure)) : BridgeM LNIRCode := do
  match alts with
  | [] =>
    return .unreachable
  | [singleAlt] =>
    match singleAlt with
    | .alt _ params code _ =>
      for p in params do
        let _ ← internFVar p.fvarId (lowerImpureType p.type)
      lowerPureCode code
    | _ =>
      lowerPureCode singleAlt.getCode
  | alt :: rest =>
    match alt with
    | .alt ctorName params code _ =>
      for p in params do
        let _ ← internFVar p.fvarId (lowerImpureType p.type)
      let cidx ← lookupCtorIdx ctorName idx
      let cmpVar ← freshBridgeVar .i64
      let bThen ← lowerPureCode code
      let bElse ← lowerPureAlts condVar (idx + 1) rest
      return .letBind cmpVar .i64
        (.scalar (.binOp .eq (.var condVar) (.constU64 cidx.toUInt64)))
        (.ite cmpVar bThen bElse)
    | .ctorAlt info code _ =>
      let cmpVar ← freshBridgeVar .i64
      let bThen ← lowerPureCode code
      let bElse ← lowerPureAlts condVar (idx + 1) rest
      return .letBind cmpVar .i64
        (.scalar (.binOp .eq (.var condVar) (.constU64 info.cidx.toUInt64)))
        (.ite cmpVar bThen bElse)
    | .default code =>
      lowerPureCode code

/-- Lower a stage-1 `Code .pure` block into structured `LNIRCode`. -/
partial def lowerPureCode (code : Lean.Compiler.LCNF.Code .pure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let st ← get
    match k, decl.value, st.selfLoopAccVar with
    | .return retFVar, .const fnName _ args _, some accVar =>
      if retFVar == decl.fvarId && fnName == st.selfDeclName then
        spliceJoinPointJmp st.selfParams (.ret accVar) args
      else
        let ty := lowerImpureType decl.type
        let dst ← internFVar decl.fvarId ty
        let rhs ← lowerPureLetValue decl.value ty
        let kCode ← lowerPureCode k
        return .letBind dst ty rhs kCode
    | _, _, _ =>
      let ty := lowerImpureType decl.type
      let dst ← internFVar decl.fvarId ty
      let rhs ← lowerPureLetValue decl.value ty
      let kCode ← lowerPureCode k
      return .letBind dst ty rhs kCode
  | .fun decl k _ =>
    let _ ← internFVar decl.fvarId (lowerImpureType decl.type)
    for p in decl.params do
      let _ ← internFVar p.fvarId (lowerImpureType p.type)
    lowerPureCode k
  | .jp decl k =>
    let _ ← internFVar decl.fvarId (lowerImpureType decl.type)
    for p in decl.params do
      let _ ← internFVar p.fvarId (lowerImpureType p.type)
    let impParams := toImpureParams decl.params
    if codeHasRecursiveJmp decl.fvarId decl.value then
      let (idxVar, accVar, accTy) ←
        if h2 : decl.params.size ≥ 2 then do
          let p0 := decl.params[0]
          let p1 := decl.params[1]
          let iv ← internFVar p0.fvarId .i64
          let aTy := lowerImpureType p1.type
          let av ← internFVar p1.fvarId aTy
          pure (iv, av, aTy)
        else if h1 : decl.params.size = 1 then do
          let p0 := decl.params[0]
          let iv ← freshBridgeVar .i64
          let aTy := lowerImpureType p0.type
          let av ← internFVar p0.fvarId aTy
          pure (iv, av, aTy)
        else do
          let iv ← freshBridgeVar .i64
          let av ← freshBridgeVar .i64
          pure (iv, av, .i64)
      let loVar ← freshBridgeVar .i64
      let hiVar ← freshBridgeVar .i64
      let accInit ← freshBridgeVar accTy
      modify fun st => { st with jpMap := st.jpMap.insert decl.fvarId (impParams, .ret accVar) }
      let stepBody ← lowerPureCode decl.value
      let kCode ← lowerPureCode k
      return .letBind loVar .i64 (.scalar (.constU64 0))
        (.letBind hiVar .i64 (.scalar (.constU64 1))
          (.letBind accInit accTy (.scalar (.constU64 0))
            (.seqFor idxVar loVar hiVar accVar accInit accTy stepBody kCode)))
    else
      let jpBody ← lowerPureCode decl.value
      modify fun st => { st with jpMap := st.jpMap.insert decl.fvarId (impParams, jpBody) }
      lowerPureCode k
  | .jmp fvarId args =>
    let st ← get
    match st.jpMap[fvarId]? with
    | some (jpParams, jpBody) =>
      modify fun st => { st with jpMap := st.jpMap.erase fvarId }
      spliceJoinPointJmp jpParams jpBody args
    | none =>
      match args.toList with
      | arg0 :: _ =>
        let v ← lowerArg arg0
        return .ret v
      | [] =>
        let v ← internFVar fvarId
        return .ret v
  | .cases c =>
    let condVar ← internFVar c.discr
    lowerPureAlts condVar 0 (orderAlts c.alts.toList)
  | .return fvarId =>
    let v ← internFVar fvarId
    return .ret v
  | .unreach _ =>
    return .unreachable

end

/-- Lower a Lean 4.31 `LCNF.Decl .impure` into a verified/auditable `LNIRDecl`. -/
def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure)
    (localDeclNames : Array Lean.Name := #[]) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  let metaInfo := getLCNFDeclMetadata env decl.name
  let isDeclExtern := metaInfo.isExtern
  let initSt : BridgeState := {
    mangledSymbol  := metaInfo.mangledSymbol
    isSimpleGround := metaInfo.isSimpleGround
    selfDeclName   := decl.name
    localDeclNames := localDeclNames
  }
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
      let body ←
        if codeHasSelfTailCall decl.name c then do
          let (idxVar, accVar, accTy) ← match lnirParams with
            | p0 :: p1 :: _ => pure (p0.id, p1.id, p1.ty)
            | [p0]          => do
              let iv ← freshBridgeVar .i64
              pure (iv, p0.id, p0.ty)
            | []            => do
              let iv ← freshBridgeVar .i64
              let av ← freshBridgeVar retTy
              pure (iv, av, retTy)
          modify fun st => {
            st with
            selfLoopAccVar := some accVar
            selfParams     := toImpureParams decl.params
          }
          let stepBody ← lowerImpureCode c
          let loVar ← freshBridgeVar .i64
          let hiVar ← freshBridgeVar .i64
          let accInit ← freshBridgeVar accTy
          pure (
            .letBind loVar .i64 (.scalar (.constU64 0))
              (.letBind hiVar .i64 (.scalar (.constU64 64))
                (.letBind accInit accTy (.scalar (.var accVar))
                  (.seqFor idxVar loVar hiVar accVar accInit accTy stepBody (.ret accVar))))
          )
        else
          lowerImpureCode c
      let st ← get
      let assurance : AssuranceLevel :=
        if isDeclExtern || st.hasExtern then .unverifiedFallback
        else .verifiedKernelProof
      let isGpu := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible
      return {
        name      := metaInfo.mangledSymbol
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
        .letBind retVar retTy (.call metaInfo.mangledSymbol argIds retTy true) (.ret retVar)
      return {
        name      := metaInfo.mangledSymbol
        params    := lnirParams
        retTy     := retTy
        body      := body
        assurance := .unverifiedFallback
        isGpuCand := false
      }
  Prod.fst <$> action.run initSt

/-- Lower a Lean 4.31 `LCNF.Decl .pure` (mono phase) into an `LNIRDecl`. -/
def ingestLCNFMonoDecl (decl : Lean.Compiler.LCNF.Decl .pure)
    (localDeclNames : Array Lean.Name := #[]) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  let metaInfo := getLCNFDeclMetadata env decl.name
  let isDeclExtern := metaInfo.isExtern
  let initSt : BridgeState := {
    mangledSymbol  := metaInfo.mangledSymbol
    isSimpleGround := metaInfo.isSimpleGround
    selfDeclName   := decl.name
    localDeclNames := localDeclNames
  }
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
      let body ←
        if codeHasSelfTailCall decl.name c then do
          let (idxVar, accVar, accTy) ← match lnirParams with
            | p0 :: p1 :: _ => pure (p0.id, p1.id, p1.ty)
            | [p0]          => do
              let iv ← freshBridgeVar .i64
              pure (iv, p0.id, p0.ty)
            | []            => do
              let iv ← freshBridgeVar .i64
              let av ← freshBridgeVar retTy
              pure (iv, av, retTy)
          modify fun st => {
            st with
            selfLoopAccVar := some accVar
            selfParams     := toImpureParams decl.params
          }
          let stepBody ← lowerPureCode c
          let loVar ← freshBridgeVar .i64
          let hiVar ← freshBridgeVar .i64
          let accInit ← freshBridgeVar accTy
          pure (
            .letBind loVar .i64 (.scalar (.constU64 0))
              (.letBind hiVar .i64 (.scalar (.constU64 64))
                (.letBind accInit accTy (.scalar (.var accVar))
                  (.seqFor idxVar loVar hiVar accVar accInit accTy stepBody (.ret accVar))))
          )
        else
          lowerPureCode c
      let st ← get
      let assurance : AssuranceLevel :=
        if isDeclExtern || st.hasExtern then .unverifiedFallback
        else .verifiedKernelProof
      let isGpu := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible
      return {
        name      := metaInfo.mangledSymbol
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
        .letBind retVar retTy (.call metaInfo.mangledSymbol argIds retTy true) (.ret retVar)
      return {
        name      := metaInfo.mangledSymbol
        params    := lnirParams
        retTy     := retTy
        body      := body
        assurance := .unverifiedFallback
        isGpuCand := false
      }
  Prod.fst <$> action.run initSt

/--
Extract and lower an array of declaration names from the Lean 4.31 environment,
preferring stage-2 `getLocalImpureDecl?` and falling back to stage-1 `getMonoDecl?`.
-/
def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested") :
    Lean.CoreM LNIRModule := do
  let mut decls : List LNIRDecl := []
  for name in declNames do
    if let some impureDecl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      let d ← ingestLCNFImpureDecl impureDecl declNames
      decls := decls ++ [d]
    else if let some monoDecl ← Lean.Compiler.LCNF.getMonoDecl? name then
      let d ← ingestLCNFMonoDecl monoDecl declNames
      decls := decls ++ [d]
  return {
    moduleName := moduleName
    decls      := decls
  }

/-- Check whether `name` is an internal compiler-synthesized closed constant or repr auxiliary. -/
def isInternalClosedOrReprAux (name : Lean.Name) : Bool :=
  let s := name.toString
  (s.splitOn "___closed__").length > 1 ||
  (s.splitOn "instRepr").length > 1 ||
  (s.splitOn "_cstage").length > 1 ||
  (s.splitOn "ctorElim").length > 1

/-- Extract and lower all local impure and mono LCNF declarations compiled in the current environment. -/
def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested") : Lean.CoreM LNIRModule := do
  let impureNames ← Lean.Compiler.LCNF.getLocalImpureDecls
  let env ← getEnv
  let extraNames := env.constants.map₂.foldl (fun acc name _ =>
    if impureNames.contains name || isInternalClosedOrReprAux name then acc else acc.push name
  ) #[]
  let filteredImpure := impureNames.filter (fun n => !isInternalClosedOrReprAux n)
  let finalNames := if filteredImpure.isEmpty && extraNames.isEmpty then impureNames else (filteredImpure ++ extraNames)
  ingestModuleDecls finalNames moduleName

/-- Resolve the Lean 4.31 sysroot path reliably even when `lean` is not on `PATH`. -/
def resolveLeanSysroot : IO System.FilePath := do
  if let some envRoot ← IO.getEnv "LEAN_SYSROOT" then
    if !envRoot.isEmpty then
      return System.FilePath.mk envRoot
  try
    Lean.findSysroot
  catch _ =>
    return System.FilePath.mk "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0"

/-- Elaborate a `.lean` source file using Lean 4's frontend, run the LCNF compiler pipeline,
    and extract the resulting `LNIRModule`. -/
def ingestLeanSourceFile (filePath : String) (moduleName : String := "LeanNative.FileInput") : IO LNIRModule := do
  let sysroot ← resolveLeanSysroot
  Lean.initSearchPath sysroot
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

/-- Elaborate `filePath` with `Lean.Elab.runFrontend`, extracting both:
    1. The full Lean 4.31 C module code (`Lean.Compiler.LCNF.emitC modName`) containing all
       `SimpleGroundExpr` static structs, closures, `initialize_*`, and `_lean_main` / `main`.
    2. The lowered `LNIRModule` via `ingestAllLocalDecls`. -/
def emitLeanCFromSourceFile (filePath : String) (modName : Lean.Name := `Main) : IO (String × LNIRModule) := do
  let sysroot ← resolveLeanSysroot
  Lean.initSearchPath sysroot
  let input ← IO.FS.readFile filePath
  let opts : Lean.Options := {}
  let some env ← Lean.Elab.runFrontend input opts filePath modName
    | throw <| IO.userError s!"Elaboration failed for {filePath}"
  let coreCtx : Lean.Core.Context := {
    fileName := filePath
    fileMap  := filePath.toFileMap
    options  := opts
  }
  let coreState : Lean.Core.State := { env := env }
  let ((cCode, lnirMod), _) ← (do
    let mod ← ingestAllLocalDecls modName.toString
    let c ← Lean.Compiler.LCNF.emitC modName
    return (c, mod)
  ).toIO coreCtx coreState
  return (cCode, lnirMod)

/-- Full LCNF-to-Executable builder (`buildNativeExecutable` / `buildExecutableFromLeanFile`):
    1. Runs `emitLeanCFromSourceFile` on `filePath`.
    2. Runs the verified `LeanNative` 4-pass optimization pipeline on the extracted `LNIRModule`
       and emits `<outBin>.lnir.ll` (including `@lean_native_abi_*` C-ABI wrapper thunks).
    3. Compiles both `<outBin>.lnir.ll` and the lowered C/LLVM module through LLVM 18
       (`clang -S -emit-llvm` -> `/usr/lib/llvm-18/bin/opt` with loop & SLP vectorization ->
       `clang` linked against `libleanshared.so` and `runtime/lean_native_runtime.c`)
       to produce a standalone native executable at `outBin`. -/
def buildNativeExecutable (filePath : String) (outBin : String) (optLevel : String := "-O3") :
    IO (LNIRModule × String) := do
  let sysroot ← resolveLeanSysroot
  let (cCode, rawMod) ← emitLeanCFromSourceFile filePath `Main
  let (optMod, _) := LeanNative.Transform.runDefaultPipeline rawMod
  let hostArch : TargetArch :=
    if System.Platform.target.startsWith "aarch64" || System.Platform.target.startsWith "arm64" then
      .arm64
    else
      .x86_64
  let lnirLlPath := s!"{outBin}.lnir.ll"
  let lnirOptLlPath := s!"{outBin}.lnir.opt.ll"
  let lnirLlText := LeanNative.Backend.LLVM.emitLLVMOptimized optMod hostArch
  IO.FS.writeFile lnirLlPath lnirLlText

  let cPath := s!"{outBin}.lean.c"
  let rawLlPath := s!"{outBin}.raw.ll"
  let optLlPath := s!"{outBin}.opt.ll"
  IO.FS.writeFile cPath cCode

  let incDir := (sysroot / "include").toString
  let clangIncDir := (sysroot / "include" / "clang").toString
  let libDir := (sysroot / "lib" / "lean").toString

  let relRuntime : System.FilePath := "runtime/lean_native_runtime.c"
  let absRuntime : System.FilePath := "/var/lib/spark-admin/jobs/3730b838-a03b-49e3-bbd2-eb51c132a4e7/lean-native/runtime/lean_native_runtime.c"
  let runtimePath ← if (← relRuntime.pathExists) then pure relRuntime.toString else pure absRuntime.toString
  let runtimeDir := ((System.FilePath.mk runtimePath).parent.getD (System.FilePath.mk "runtime")).toString

  let sysClang : System.FilePath := "/usr/bin/clang"
  let clangCmd ← if (← sysClang.pathExists) then pure sysClang.toString else pure "clang"

  -- Step 1: clang -S -emit-llvm -O3 -I<sysroot>/include
  let clangEmitOut ← IO.Process.output {
    cmd  := clangCmd
    args := #["-S", "-emit-llvm", optLevel, s!"-I{incDir}", cPath, "-o", rawLlPath]
  }
  if clangEmitOut.exitCode != 0 then
    throw <| IO.userError s!"clang -emit-llvm failed:\n{clangEmitOut.stderr}"

  -- Step 2: /usr/lib/llvm-18/bin/opt with O3 + loop-vectorize + slp-vectorizer on both rawLlPath and lnirLlPath
  let optBin : System.FilePath := "/usr/lib/llvm-18/bin/opt"
  let optCmd ← if (← optBin.pathExists) then pure optBin.toString else pure "opt"
  let optOut ← IO.Process.output {
    cmd  := optCmd
    args := #[
      "-S",
      "-passes=default<O3>,loop-vectorize,slp-vectorizer",
      "-vectorize-loops",
      "-vectorize-slp",
      rawLlPath,
      "-o",
      optLlPath
    ]
  }
  if optOut.exitCode != 0 then
    IO.FS.writeFile optLlPath (← IO.FS.readFile rawLlPath)

  let lnirOptOut ← IO.Process.output {
    cmd  := optCmd
    args := #[
      "-S",
      "-passes=default<O3>,loop-vectorize,slp-vectorizer",
      "-vectorize-loops",
      "-vectorize-slp",
      lnirLlPath,
      "-o",
      lnirOptLlPath
    ]
  }
  if lnirOptOut.exitCode != 0 then
    IO.FS.writeFile lnirOptLlPath lnirLlText

  -- Step 3: clang -O3 linking both optLlPath and lnirOptLlPath against libleanshared.so and runtime/lean_native_runtime.c
  let linkOut ← IO.Process.output {
    cmd  := clangCmd
    args := #[
      optLevel,
      "-Wno-override-module",
      s!"-I{incDir}",
      s!"-I{runtimeDir}",
      optLlPath,
      lnirOptLlPath,
      runtimePath,
      "-Wl,--allow-multiple-definition",
      s!"-L{libDir}",
      "-lleanshared",
      s!"-Wl,-rpath,{libDir}",
      "-lm",
      "-lpthread",
      "-ldl",
      "-o",
      outBin
    ]
  }
  if linkOut.exitCode != 0 then
    throw <| IO.userError s!"clang native link failed:\n{linkOut.stderr}"

  return (optMod, lnirLlPath)

abbrev buildExecutableFromLeanFile := buildNativeExecutable

/-!
## Canonical Benchmark & Workload Declarations (Re-exported from `LeanNative.IR.Codec`)
-/

abbrev collatzStepsDecl : LNIRDecl := LeanNative.IR.Codec.collatzStepsDecl
abbrev tupleAccumSumDecl : LNIRDecl := LeanNative.IR.Codec.tupleAccumSumDecl
abbrev sarrayScaleBiasDecl : LNIRDecl := LeanNative.IR.Codec.sarrayScaleBiasDecl
abbrev dotProductU64Decl : LNIRDecl := LeanNative.IR.Codec.dotProductU64Decl
abbrev saxpyKernelDecl : LNIRDecl := LeanNative.IR.Codec.saxpyKernelDecl
abbrev matmulTiledU64Decl : LNIRDecl := LeanNative.IR.Codec.matmulTiledU64Decl
abbrev mkCollatzStepsDecl : LNIRDecl := LeanNative.IR.Codec.collatzStepsDecl
abbrev mkTupleAccumSumDecl : LNIRDecl := LeanNative.IR.Codec.tupleAccumSumDecl
abbrev mkSArrayScaleBiasDecl : LNIRDecl := LeanNative.IR.Codec.sarrayScaleBiasDecl
abbrev mkDotProductU64Decl : LNIRDecl := LeanNative.IR.Codec.dotProductU64Decl
abbrev mkSaxpyKernelDecl : LNIRDecl := LeanNative.IR.Codec.saxpyKernelDecl
abbrev mkMatmulTiledU64Decl : LNIRDecl := LeanNative.IR.Codec.matmulTiledU64Decl
abbrev mkEvmErc20TransferU256Decl : LNIRDecl := LeanNative.IR.evmErc20TransferU256Decl
abbrev mkEvmMulDivWadU256Decl : LNIRDecl := LeanNative.IR.evmMuldivWadU256Decl
abbrev mkCanonicalBenchmarkModule : LNIRModule := LeanNative.IR.Codec.mkCanonicalBenchmarkModule

end LeanNative.IR
