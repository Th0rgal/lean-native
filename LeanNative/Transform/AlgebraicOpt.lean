import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Transform.Pass

namespace LeanNative.Transform

open LeanNative.IR

/-- Single-step algebraic and strength-reduction peephole rewrite on `ScalarExpr`.
    Backed by `LeanNative.Proofs.PeepholeProofs.rewriteScalarPeephole_sound`. -/
def rewriteScalarPeepholeStep (e : ScalarExpr) : ScalarExpr :=
  match e with
  -- Constant folding for binary operations on UInt64
  | .binOp .add (.constU64 a) (.constU64 b) => .constU64 (a + b)
  | .binOp .sub (.constU64 a) (.constU64 b) => .constU64 (a - b)
  | .binOp .mul (.constU64 a) (.constU64 b) => .constU64 (a * b)
  | .binOp .div (.constU64 a) (.constU64 b) =>
    if b == 0 then e else .constU64 (a / b)
  | .binOp .mod (.constU64 a) (.constU64 b) =>
    if b == 0 then e else .constU64 (a % b)
  | .binOp .bitAnd (.constU64 a) (.constU64 b) => .constU64 (a &&& b)
  | .binOp .bitOr (.constU64 a) (.constU64 b) => .constU64 (a ||| b)
  | .binOp .bitXor (.constU64 a) (.constU64 b) => .constU64 (a ^^^ b)
  | .binOp .shl (.constU64 a) (.constU64 b) => .constU64 (a <<< (b &&& 63))
  | .binOp .shr (.constU64 a) (.constU64 b) => .constU64 (a >>> (b &&& 63))
  | .binOp .eq (.constU64 a) (.constU64 b) => .constBool (a == b)
  | .binOp .lt (.constU64 a) (.constU64 b) => .constBool (a < b)
  | .binOp .le (.constU64 a) (.constU64 b) => .constBool (a ≤ b)
  | .binOp .eq (.constBool a) (.constBool b) => .constBool (a == b)

  -- Additive identities: x + 0 -> x, 0 + x -> x, x - 0 -> x, x - x -> 0
  | .binOp .add x (.constU64 0) => x
  | .binOp .add (.constU64 0) x => x
  | .binOp .sub x (.constU64 0) => x
  | .binOp .sub x y =>
    if x == y then .constU64 0 else e

  -- Multiplicative identities & annihilation: x * 1 -> x, 1 * x -> x, x * 0 -> 0, 0 * x -> 0
  | .binOp .mul x (.constU64 1) => x
  | .binOp .mul (.constU64 1) x => x
  | .binOp .mul _ (.constU64 0) => .constU64 0
  | .binOp .mul (.constU64 0) _ => .constU64 0

  -- Strength reduction for multiplication by powers of 2: * 2 -> <<< 1, * 4 -> <<< 2, * 8 -> <<< 3
  | .binOp .mul x (.constU64 2) => .binOp .shl x (.constU64 1)
  | .binOp .mul (.constU64 2) x => .binOp .shl x (.constU64 1)
  | .binOp .mul x (.constU64 4) => .binOp .shl x (.constU64 2)
  | .binOp .mul (.constU64 4) x => .binOp .shl x (.constU64 2)
  | .binOp .mul x (.constU64 8) => .binOp .shl x (.constU64 3)
  | .binOp .mul (.constU64 8) x => .binOp .shl x (.constU64 3)

  -- Strength reduction for unsigned division by powers of 2: / 1 -> x, / 2 -> >>> 1, / 4 -> >>> 2, / 8 -> >>> 3
  | .binOp .div x (.constU64 1) => x
  | .binOp .div x (.constU64 2) => .binOp .shr x (.constU64 1)
  | .binOp .div x (.constU64 4) => .binOp .shr x (.constU64 2)
  | .binOp .div x (.constU64 8) => .binOp .shr x (.constU64 3)

  -- Strength reduction for unsigned modulo by powers of 2: % 1 -> 0, % 2 -> &&& 1, % 4 -> &&& 3, % 8 -> &&& 7
  | .binOp .mod _ (.constU64 1) => .constU64 0
  | .binOp .mod x (.constU64 2) => .binOp .bitAnd x (.constU64 1)
  | .binOp .mod x (.constU64 4) => .binOp .bitAnd x (.constU64 3)
  | .binOp .mod x (.constU64 8) => .binOp .bitAnd x (.constU64 7)

  -- Bitwise identities and idempotence
  | .binOp .bitXor x (.constU64 0) => x
  | .binOp .bitXor (.constU64 0) x => x
  | .binOp .bitXor x y =>
    if x == y then .constU64 0 else e
  | .binOp .bitOr x (.constU64 0) => x
  | .binOp .bitOr (.constU64 0) x => x
  | .binOp .bitOr x y =>
    if x == y then x else e
  | .binOp .bitAnd _ (.constU64 0) => .constU64 0
  | .binOp .bitAnd (.constU64 0) _ => .constU64 0
  | .binOp .bitAnd x y =>
    if x == y then x else e

  -- Shift identities
  | .binOp .shl x (.constU64 0) => x
  | .binOp .shr x (.constU64 0) => x

  -- Reflexive comparisons
  | .binOp .eq x y =>
    if x == y then .constBool true else e
  | .binOp .lt x y =>
    if x == y then .constBool false else e
  | .binOp .le x y =>
    if x == y then .constBool true else e

  -- Unary operations
  | .unaryOp .not (.constBool b) => .constBool (!b)
  | .unaryOp .not (.unaryOp .not x) => x
  | .unaryOp .neg (.constU64 a) => .constU64 (0 - a)
  | .unaryOp .neg (.unaryOp .neg x) => x

  -- Select / branch folding
  | .select (.constBool true) t _ => t
  | .select (.constBool false) _ f => f
  | .select (.constU64 c) t f =>
    if c != 0 then t else f
  | .select _ t f =>
    if t == f then t else e

  -- FMA folding
  | .fma (.constU64 a) (.constU64 b) (.constU64 c) => .constU64 (a * b + c)
  | .fma x (.constU64 1) c => rewriteScalarPeepholeStep (.binOp .add x c)
  | .fma (.constU64 1) x c => rewriteScalarPeepholeStep (.binOp .add x c)
  | .fma _ (.constU64 0) c => c
  | .fma (.constU64 0) _ c => c
  | .fma a b (.constU64 0) => rewriteScalarPeepholeStep (.binOp .mul a b)

  | _ => e

/-- Recursive bottom-up peephole optimizer on `ScalarExpr`. -/
def rewriteScalarPeephole : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var id
  | .binOp op lhs rhs =>
    let lhs' := rewriteScalarPeephole lhs
    let rhs' := rewriteScalarPeephole rhs
    rewriteScalarPeepholeStep (.binOp op lhs' rhs')
  | .unaryOp op arg =>
    let arg' := rewriteScalarPeephole arg
    rewriteScalarPeepholeStep (.unaryOp op arg')
  | .select c t f =>
    let c' := rewriteScalarPeephole c
    let t' := rewriteScalarPeephole t
    let f' := rewriteScalarPeephole f
    rewriteScalarPeepholeStep (.select c' t' f')
  | .fma a b c =>
    let a' := rewriteScalarPeephole a
    let b' := rewriteScalarPeephole b
    let c' := rewriteScalarPeephole c
    rewriteScalarPeepholeStep (.fma a' b' c')

/-- Substitute known scalar constants from an SSA environment before peephole rewriting. -/
def substConstScalar (env : List (VarId × ScalarExpr)) : ScalarExpr → ScalarExpr
  | .var id =>
    match env.lookup id with
    | some c => c
    | none => .var id
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .binOp op l r => .binOp op (substConstScalar env l) (substConstScalar env r)
  | .unaryOp op a => .unaryOp op (substConstScalar env a)
  | .select c t f => .select (substConstScalar env c) (substConstScalar env t) (substConstScalar env f)
  | .fma a b c => .fma (substConstScalar env a) (substConstScalar env b) (substConstScalar env c)

def isScalarConst : ScalarExpr → Bool
  | .constU64 _ | .constBool _ => true
  | _ => false

/-- Optimize a `ParallelKernelKind` when it embeds a `customScalar` expression. -/
def optimizeKernelAlgebraic (env : List (VarId × ScalarExpr)) (k : ParallelKernelKind) : ParallelKernelKind :=
  match k with
  | .customScalar idxVar inVars body =>
    let env' := env.filter (fun (id, _) => id != idxVar && !(inVars.contains id))
    .customScalar idxVar inVars (rewriteScalarPeephole (substConstScalar env' body))
  | other => other

/-- Recursively apply algebraic strength reduction, identity folding, constant propagation,
    and constant branch (`ite`) elimination across `LNIRCode`. -/
def optimizeCodeAlgebraic (env : List (VarId × ScalarExpr)) (code : LNIRCode) : LNIRCode :=
  match code with
  | .letBind dst ty (.scalar e) k =>
    let e' := rewriteScalarPeephole (substConstScalar env e)
    let env' :=
      if isScalarConst e' then
        (dst, e') :: env.filter (fun (id, _) => id != dst)
      else
        env.filter (fun (id, _) => id != dst)
    .letBind dst ty (.scalar e') (optimizeCodeAlgebraic env' k)
  | .letBind dst ty val k =>
    let env' := env.filter (fun (id, _) => id != dst)
    .letBind dst ty val (optimizeCodeAlgebraic env' k)
  | .rawStore ptrVar idxVar valVar elemTy k =>
    .rawStore ptrVar idxVar valVar elemTy (optimizeCodeAlgebraic env k)
  | .incRef objVar count k =>
    .incRef objVar count (optimizeCodeAlgebraic env k)
  | .decRef objVar count k =>
    .decRef objVar count (optimizeCodeAlgebraic env k)
  | .ite condVar thenBranch elseBranch =>
    match env.lookup condVar with
    | some (.constBool true) => optimizeCodeAlgebraic env thenBranch
    | some (.constBool false) => optimizeCodeAlgebraic env elseBranch
    | some (.constU64 v) =>
      if v != 0 then optimizeCodeAlgebraic env thenBranch
      else optimizeCodeAlgebraic env elseBranch
    | _ =>
      .ite condVar (optimizeCodeAlgebraic env thenBranch) (optimizeCodeAlgebraic env elseBranch)
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    let stepEnv := env.filter (fun (id, _) => id != idxVar && id != accVar)
    let stepBody' := optimizeCodeAlgebraic stepEnv stepBody
    let kEnv := env.filter (fun (id, _) => id != accVar)
    .seqFor idxVar loVar hiVar accVar accInit accTy stepBody' (optimizeCodeAlgebraic kEnv k)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    let kernel' := optimizeKernelAlgebraic env kernel
    let kEnv := env.filter (fun (id, _) => id != outVar)
    .parFor outVar lenVar inputs elemTy kernel' (optimizeCodeAlgebraic kEnv k)
  | .ret v => .ret v
  | .unreachable => .unreachable

/-- Run algebraic optimization on an `LNIRDecl`. -/
def algebraicOptDecl (d : LNIRDecl) : LNIRDecl :=
  { d with body := optimizeCodeAlgebraic [] d.body }

/-- Verified Algebraic Optimization & Strength Reduction Pass (`AlgebraicOpt`). -/
def algebraicOptPass : TransformPass :=
  TransformPass.ofCodeTransform
    "AlgebraicOpt"
    .verifiedKernelProof
    "LeanNative.Proofs.PeepholeProofs.rewriteScalarPeephole_sound"
    "Strength reduction (*2^k -> <<<k, /2^k -> >>>k, %2^k -> &&&(2^k-1)), identity folding, and constant branch elimination"
    (fun d => (optimizeCodeAlgebraic [] d.body, none))

end LeanNative.Transform
