import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value

namespace LeanNative.Semantics

open LeanNative.IR

/-- Total, deterministic evaluation of binary scalar operators on `Val`. -/
def evalBinOp (op : BinOp) (v1 v2 : Val) : Except UBError Val :=
  match op, v1, v2 with
  | .add, .u64 a, .u64 b => .ok (.u64 (a + b))
  | .add, v, .u64 0 => .ok v
  | .add, .u64 0, v => .ok v
  | .sub, .u64 a, .u64 b => .ok (.u64 (a - b))
  | .sub, v, .u64 0 => .ok v
  | .mul, .u64 a, .u64 b => .ok (.u64 (a * b))
  | .mul, v, .u64 1 => .ok v
  | .mul, .u64 1, v => .ok v
  | .div, .u64 a, .u64 b =>
    if b == 0 then .error .divisionByZero else .ok (.u64 (a / b))
  | .div, v, .u64 1 => .ok v
  | .mod, .u64 a, .u64 b =>
    if b == 0 then .error .divisionByZero else .ok (.u64 (a % b))
  | .bitAnd, .u64 a, .u64 b => .ok (.u64 (a &&& b))
  | .bitAnd, v1, v2 =>
    if v1 == v2 then .ok v1 else .error (.typeError "bitAnd requires u64")
  | .bitOr, .u64 a, .u64 b => .ok (.u64 (a ||| b))
  | .bitOr, v, .u64 0 => .ok v
  | .bitOr, .u64 0, v => .ok v
  | .bitOr, v1, v2 =>
    if v1 == v2 then .ok v1 else .error (.typeError "bitOr requires u64")
  | .bitXor, .u64 a, .u64 b => .ok (.u64 (a ^^^ b))
  | .bitXor, v, .u64 0 => .ok v
  | .bitXor, .u64 0, v => .ok v
  | .shl, .u64 a, .u64 b => .ok (.u64 (a <<< b))
  | .shl, v, .u64 0 => .ok v
  | .shr, .u64 a, .u64 b => .ok (.u64 (a >>> b))
  | .shr, v, .u64 0 => .ok v
  | .eq, .u64 a, .u64 b => .ok (.bool (a == b))
  | .eq, .bool a, .bool b => .ok (.bool (a == b))
  | .lt, .u64 a, .u64 b => .ok (.bool (decide (a < b)))
  | .le, .u64 a, .u64 b => .ok (.bool (decide (a ≤ b)))
  | _, _, _ => .error (.typeError "evalBinOp: invalid operand types")

/-- Total, deterministic evaluation of unary scalar operators on `Val`. -/
def evalUnaryOp (op : UnaryOp) (v : Val) : Except UBError Val :=
  match op, v with
  | .not, .bool b => .ok (.bool (!b))
  | .not, .u64 n  => .ok (.u64 (~~~n))
  | .neg, .u64 n  => .ok (.u64 (0 - n))
  | _, _ => .error (.typeError "evalUnaryOp: invalid operand type")

/-- Total denotational evaluator for pure scalar SSA expressions (`ScalarExpr`). -/
def evalScalarExpr (env : VarEnv) : ScalarExpr → Except UBError Val
  | .constU64 val => .ok (.u64 val)
  | .constBool val => .ok (.bool val)
  | .var id =>
    match env id with
    | some v => .ok v
    | none => .error (.unboundVar id)
  | .binOp op lhs rhs =>
    match evalScalarExpr env lhs, evalScalarExpr env rhs with
    | .ok v1, .ok v2 => evalBinOp op v1 v2
    | .error err, _ => .error err
    | .ok _, .error err => .error err
  | .unaryOp op arg =>
    match evalScalarExpr env arg with
    | .ok v => evalUnaryOp op v
    | .error err => .error err
  | .select cond thenVal elseVal =>
    match evalScalarExpr env cond with
    | .ok (.bool true) => evalScalarExpr env thenVal
    | .ok (.bool false) => evalScalarExpr env elseVal
    | .ok (.u64 n) =>
      if n != 0 then evalScalarExpr env thenVal else evalScalarExpr env elseVal
    | .ok _ => .error (.typeError "select condition must be bool or u64")
    | .error err => .error err
  | .fma a b c =>
    match evalScalarExpr env a, evalScalarExpr env b with
    | .ok va, .ok vb =>
      match evalBinOp .mul va vb, evalScalarExpr env c with
      | .ok vab, .ok vc => evalBinOp .add vab vc
      | .error err, _ => .error err
      | .ok _, .error err => .error err
    | .error err, _ => .error err
    | .ok _, .error err => .error err

/-- Look up a list of SSA variables in `VarEnv`. -/
def evalVarList (env : VarEnv) : List VarId → Except UBError (List Val)
  | [] => .ok []
  | x :: xs =>
    match env x, evalVarList env xs with
    | some v, .ok vs => .ok (v :: vs)
    | none, _ => .error (.unboundVar x)
    | some _, .error err => .error err

/-- Total evaluator for right-hand side LNIR expressions (`LNIRExpr`). -/
def evalExpr (env : VarEnv) (st : HeapState) (e : LNIRExpr) : Except UBError (Val × HeapState) :=
  match e with
  | .scalar se =>
    match evalScalarExpr env se with
    | .ok v => .ok (v, st)
    | .error err => .error err
  | .mkTuple fields =>
    match evalVarList env fields with
    | .ok vals => .ok (.tuple vals, st)
    | .error err => .error err
  | .projTuple tupleVar idx =>
    match env tupleVar with
    | some (.tuple vals) =>
      match vals[idx]? with
      | some v => .ok (v, st)
      | none => .error (.outOfBounds idx vals.length)
    | some _ => .error (.typeError "projTuple expects tuple value")
    | none => .error (.unboundVar tupleVar)
  | .allocCtor tag objFields scalarFields =>
    match evalVarList env (objFields ++ scalarFields) with
    | .ok vals => .ok (.tuple (.u64 tag.toUInt64 :: vals), st)
    | .error err => .error err
  | .ctorGetObj ctorVar idx =>
    match env ctorVar with
    | some (.tuple (_tag :: vals)) =>
      match vals[idx]? with
      | some v => .ok (v, st)
      | none => .error (.outOfBounds idx vals.length)
    | some (.tuple []) => .error (.outOfBounds idx 0)
    | some _ => .error (.typeError "ctorGetObj expects constructor tuple")
    | none => .error (.unboundVar ctorVar)
  | .ctorGetScalar ctorVar idx _ty =>
    match env ctorVar with
    | some (.tuple (_tag :: vals)) =>
      match vals[idx]? with
      | some v => .ok (v, st)
      | none => .error (.outOfBounds idx vals.length)
    | some (.tuple []) => .error (.outOfBounds idx 0)
    | some _ => .error (.typeError "ctorGetScalar expects constructor tuple")
    | none => .error (.unboundVar ctorVar)
  | .isExclusive objVar =>
    match env objVar with
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf => .ok (.bool buf.exclusive, st)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some _ => .ok (.bool true, st)
    | none => .error (.unboundVar objVar)
  | .sarrayLen arrVar =>
    match env arrVar with
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf => .ok (.u64 buf.data.size.toUInt64, st)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some _ => .error (.typeError "sarrayLen expects sarrayId")
    | none => .error (.unboundVar arrVar)
  | .sarrayDataPtr arrVar _elemTy =>
    match env arrVar with
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf =>
        if buf.exclusive then .ok (.rawPtrId bufId, st)
        else .error (.nonExclusiveWrite bufId)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some (.rawPtrId bufId) => .ok (.rawPtrId bufId, st)
    | some _ => .error (.typeError "sarrayDataPtr expects sarrayId")
    | none => .error (.unboundVar arrVar)
  | .sarrayEnsureExclusive arrVar _elemTy =>
    match env arrVar with
    | some (.sarrayId bufId) =>
      match st.ensureExclusive bufId with
      | .ok st' => .ok (.sarrayId bufId, st')
      | .error err => .error err
    | some _ => .error (.typeError "sarrayEnsureExclusive expects sarrayId")
    | none => .error (.unboundVar arrVar)
  | .sarrayGet arrVar idxVar _elemTy =>
    match env arrVar, env idxVar with
    | some (.sarrayId bufId), some (.u64 idx) =>
      match st.readElem bufId idx.toNat with
      | .ok v => .ok (.u64 v, st)
      | .error err => .error err
    | none, _ => .error (.unboundVar arrVar)
    | _, none => .error (.unboundVar idxVar)
    | _, _ => .error (.typeError "sarrayGet expects sarrayId and u64 index")
  | .sarraySet arrVar idxVar valVar _elemTy =>
    match env arrVar, env idxVar, env valVar with
    | some (.sarrayId bufId), some (.u64 idx), some (.u64 val) =>
      match st.ensureExclusive bufId with
      | .ok st1 =>
        match st1.writeElemExclusive bufId idx.toNat val with
        | .ok st2 => .ok (.sarrayId bufId, st2)
        | .error err => .error err
      | .error err => .error err
    | none, _, _ => .error (.unboundVar arrVar)
    | _, none, _ => .error (.unboundVar idxVar)
    | _, _, none => .error (.unboundVar valVar)
    | _, _, _ => .error (.typeError "sarraySet expects sarrayId, u64 index, and u64 value")
  | .rawLoad ptrVar idxVar _elemTy =>
    match env ptrVar, env idxVar with
    | some (.rawPtrId bufId), some (.u64 idx) =>
      match st.readElem bufId idx.toNat with
      | .ok v => .ok (.u64 v, st)
      | .error err => .error err
    | some (.sarrayId bufId), some (.u64 idx) =>
      match st.readElem bufId idx.toNat with
      | .ok v => .ok (.u64 v, st)
      | .error err => .error err
    | none, _ => .error (.unboundVar ptrVar)
    | _, none => .error (.unboundVar idxVar)
    | _, _ => .error (.typeError "rawLoad expects rawPtrId/sarrayId and u64 index")
  | .boxScalar valVar _ty =>
    match env valVar with
    | some v => .ok (v, st)
    | none => .error (.unboundVar valVar)
  | .unboxScalar boxVar _ty =>
    match env boxVar with
    | some v => .ok (v, st)
    | none => .error (.unboundVar boxVar)
  | .call _fnName args _retTy _isExtern =>
    match evalVarList env args with
    | .ok _ => .ok (.unit, st)
    | .error err => .error err

/-- Bounded sequential loop evaluation helper for `seqFor`. -/
def evalSeqLoop (count : Nat) (curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env : VarEnv) (st : HeapState)
    (evalStep : VarEnv → HeapState → Except UBError (Val × HeapState)) :
    Except UBError (Val × HeapState) :=
  match count with
  | 0 => .ok (accVal, st)
  | count' + 1 =>
    let stepEnv := (env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal
    match evalStep stepEnv st with
    | .ok (nextAcc, st') =>
      evalSeqLoop count' (curIdx + 1) idxVar accVar nextAcc env st' evalStep
    | .error err => .error err

/-- Total, fuel-bounded operational evaluator for structured `LNIRCode`. -/
def evalCode : Nat → VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)
  | 0, _, st, _ => .ok (.unit, st)
  | fuel + 1, env, st, code =>
    match code with
    | .letBind dst _ty val k =>
      match evalExpr env st val with
      | .ok (v, st') => evalCode fuel (env.bind dst v) st' k
      | .error err => .error err
    | .rawStore ptrVar idxVar valVar _elemTy k =>
      match env ptrVar, env idxVar, env valVar with
      | some (.rawPtrId bufId), some (.u64 idx), some (.u64 val) =>
        match st.writeElemExclusive bufId idx.toNat val with
        | .ok st' => evalCode fuel env st' k
        | .error err => .error err
      | some (.sarrayId bufId), some (.u64 idx), some (.u64 val) =>
        match st.writeElemExclusive bufId idx.toNat val with
        | .ok st' => evalCode fuel env st' k
        | .error err => .error err
      | none, _, _ => .error (.unboundVar ptrVar)
      | _, none, _ => .error (.unboundVar idxVar)
      | _, _, none => .error (.unboundVar valVar)
      | _, _, _ => .error (.typeError "rawStore requires rawPtrId/sarrayId and u64 index/value")
    | .incRef _objVar _count k =>
      evalCode fuel env st k
    | .decRef _objVar _count k =>
      evalCode fuel env st k
    | .ite condVar thenBranch elseBranch =>
      match env condVar with
      | some (.bool true) => evalCode fuel env st thenBranch
      | some (.bool false) => evalCode fuel env st elseBranch
      | some (.u64 n) =>
        if n != 0 then evalCode fuel env st thenBranch
        else evalCode fuel env st elseBranch
      | some _ => .error (.typeError "ite condition must be bool or u64")
      | none => .error (.unboundVar condVar)
    | .seqFor idxVar loVar hiVar accVar accInit _accTy stepBody k =>
      match env loVar, env hiVar, env accInit with
      | some (.u64 lo), some (.u64 hi), some initVal =>
        let count := hi.toNat - lo.toNat
        match evalSeqLoop count lo.toNat idxVar accVar initVal env st
            (fun stepEnv stepSt => evalCode fuel stepEnv stepSt stepBody) with
        | .ok (finalAcc, st') => evalCode fuel (env.bind accVar finalAcc) st' k
        | .error err => .error err
      | none, _, _ => .error (.unboundVar loVar)
      | _, none, _ => .error (.unboundVar hiVar)
      | _, _, none => .error (.unboundVar accInit)
      | _, _, _ => .error (.typeError "seqFor bounds must be u64")
    | .parFor outVar _lenVar _inputs _elemTy _kernel k =>
      evalCode fuel (env.bind outVar (.sarrayId 0)) st k
    | .ret v =>
      match env v with
      | some val => .ok (val, st)
      | none => .error (.unboundVar v)
    | .unreachable =>
      .error (.typeError "reached unreachable code")

end LeanNative.Semantics
