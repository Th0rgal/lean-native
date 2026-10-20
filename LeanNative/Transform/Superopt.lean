import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.SymbolicTV

namespace LeanNative.Transform

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Proofs

/-!
# Cost-Guided Enumerative Superoptimizer (`LeanNative.Transform.Superopt`)

Provides a self-contained (zero `import Lean`) cost-guided enumerative superoptimizer
for LNIR scalar expressions and modules across CPU and GPU targets:
- Hardware-specific instruction latency cost model (`SuperoptTarget`: `x86_64`, `arm64`, `cuda_ptx`, `apple_metal`)
- Bottom-up + template-guided candidate synthesis (`synthesizeCandidates`) combining:
  1. Kernel-verified `LeanNative.Proofs.rewriteScalarPeephole`
  2. Symbolic canonical normalizer (`symExprToScalarExpr?`)
  3. Enumerative algebraic, bitwise, shift-composition, FMA-contraction, and distributive factoring templates
- Two-stage formal soundness filter for every synthesized candidate:
  1. `fastCheckScalarEquiv`: 16-state concrete equivalence filter (boundary values + SplitMix64) via `evalScalarExpr`
  2. `symCheckScalarEquiv`: SymbolicTV canonical equivalence verifier (`normSymExpr`)
-/

/-- Target architecture for cost-guided superoptimization. -/
inductive SuperoptTarget where
  | x86_64
  | arm64
  | cuda_ptx
  | apple_metal
  deriving Repr, DecidableEq, Inhabited, BEq

namespace SuperoptTarget

def toString : SuperoptTarget → String
  | .x86_64      => "x86_64"
  | .arm64       => "arm64"
  | .cuda_ptx    => "cuda_ptx"
  | .apple_metal => "apple_metal"

instance : ToString SuperoptTarget := ⟨toString⟩

def isGpu : SuperoptTarget → Bool
  | .cuda_ptx | .apple_metal => true
  | .x86_64 | .arm64 => false

end SuperoptTarget

/-- Declarative, community-contributable hardware latency & tuning profile (`profiles/*.json`).
    Note (Law 1 / Law 5): A `HardwareCostProfile` only affects cost-guided candidate ranking;
    every synthesized rewrite still passes `fastCheckScalarEquiv` + `symCheckScalarEquiv`. -/
structure HardwareCostProfile where
  profileId            : String := "x86_64_default"
  target               : SuperoptTarget := .x86_64
  llvmTargetCpu        : String := "x86-64-v3"
  smArch               : String := "sm_90"
  addSubCost           : Nat := 1
  bitwiseCost          : Nat := 1
  shiftCost            : Nat := 1
  cmpCost              : Nat := 1
  mulCost              : Nat := 4
  divModCost           : Nat := 24
  fmaCost              : Nat := 3
  selectCost           : Nat := 2
  clz256Cost           : Nat := 2
  addSubChecked256Cost : Nat := 3
  mulChecked256Cost    : Nat := 4
  minGpuElements       : Nat := 65536
  gpuBlockThreads      : Nat := 256
  matmulTileDim        : Nat := 16
  deriving Repr, DecidableEq, Inhabited, BEq

namespace HardwareCostProfile

/-- Built-in default hardware cost profile for a `SuperoptTarget`. -/
def forTarget (t : SuperoptTarget) : HardwareCostProfile :=
  match t with
  | .x86_64 => {
      profileId := "x86_64_skylake_avx2"
      target := .x86_64
      llvmTargetCpu := "x86-64-v3"
      mulCost := 4
      divModCost := 24
      fmaCost := 3
      mulChecked256Cost := 4
    }
  | .arm64 => {
      profileId := "arm64_grace_neoverse_v2"
      target := .arm64
      llvmTargetCpu := "neoverse-v2"
      mulCost := 3
      divModCost := 20
      fmaCost := 2
      mulChecked256Cost := 4
    }
  | .cuda_ptx => {
      profileId := "cuda_blackwell_gb10_sm121"
      target := .cuda_ptx
      llvmTargetCpu := "neoverse-v2"
      smArch := "sm_90"
      mulCost := 5
      divModCost := 36
      fmaCost := 2
      mulChecked256Cost := 5
      minGpuElements := 65536
      gpuBlockThreads := 256
      matmulTileDim := 16
    }
  | .apple_metal => {
      profileId := "apple_silicon_m3_metal"
      target := .apple_metal
      llvmTargetCpu := "apple-m3"
      mulCost := 5
      divModCost := 36
      fmaCost := 2
      mulChecked256Cost := 5
      minGpuElements := 32768
      gpuBlockThreads := 256
      matmulTileDim := 16
    }

private def extractJsonStringField (raw : String) (key : String) : Option String :=
  let pat := "\"" ++ key ++ "\""
  match raw.splitOn pat with
  | _ :: afterKey :: _ =>
    match afterKey.splitOn ":" with
    | _ :: afterColon :: _ =>
      let trimmed := afterColon.trimAscii.toString
      match trimmed.splitOn "\"" with
      | _ :: val :: _ => some val
      | _ => none
    | _ => none
  | _ => none

private def extractJsonNatField (raw : String) (key : String) : Option Nat :=
  let pat := "\"" ++ key ++ "\""
  match raw.splitOn pat with
  | _ :: afterKey :: _ =>
    match afterKey.splitOn ":" with
    | _ :: afterColon :: _ =>
      let trimmed := afterColon.trimAscii.toString
      let digits := trimmed.toList.takeWhile (fun c => c.isDigit)
      if digits.isEmpty then none else (String.ofList digits).toNat?
    | _ => none
  | _ => none

/-- Parse a `HardwareCostProfile` from a `profiles/*.json` file. -/
def fromJson? (raw : String) : Option HardwareCostProfile := do
  let tgtStr := (extractJsonStringField raw "target").getD "x86_64"
  let target : SuperoptTarget :=
    if tgtStr == "arm64" || tgtStr == "aarch64" then .arm64
    else if tgtStr == "cuda_ptx" || tgtStr == "cuda" || tgtStr == "ptx" then .cuda_ptx
    else if tgtStr == "apple_metal" || tgtStr == "metal" then .apple_metal
    else .x86_64
  let base := forTarget target
  let pid := (extractJsonStringField raw "profile_id").orElse (fun _ => extractJsonStringField raw "profileId") |>.getD base.profileId
  let llvmCpu := (extractJsonStringField raw "llvm_target_cpu").getD base.llvmTargetCpu
  let sm := (extractJsonStringField raw "sm_arch").getD base.smArch
  return {
    profileId            := pid
    target               := target
    llvmTargetCpu        := llvmCpu
    smArch               := sm
    addSubCost           := (extractJsonNatField raw "add_sub_cost").getD base.addSubCost
    bitwiseCost          := (extractJsonNatField raw "bitwise_cost").getD base.bitwiseCost
    shiftCost            := (extractJsonNatField raw "shift_cost").getD base.shiftCost
    cmpCost              := (extractJsonNatField raw "cmp_cost").getD base.cmpCost
    mulCost              := (extractJsonNatField raw "mul_cost").getD base.mulCost
    divModCost           := (extractJsonNatField raw "div_mod_cost").getD base.divModCost
    fmaCost              := (extractJsonNatField raw "fma_cost").getD base.fmaCost
    selectCost           := (extractJsonNatField raw "select_cost").getD base.selectCost
    clz256Cost           := (extractJsonNatField raw "clz256_cost").getD base.clz256Cost
    addSubChecked256Cost := (extractJsonNatField raw "add_sub_checked256_cost").getD base.addSubChecked256Cost
    mulChecked256Cost    := (extractJsonNatField raw "mul_checked256_cost").getD base.mulChecked256Cost
    minGpuElements       := (extractJsonNatField raw "min_gpu_elements").getD base.minGpuElements
    gpuBlockThreads      := (extractJsonNatField raw "gpu_block_threads").getD base.gpuBlockThreads
    matmulTileDim        := (extractJsonNatField raw "matmul_tile_dim").getD base.matmulTileDim
  }

end HardwareCostProfile

/-- Profile-guided binary operator latency cost. -/
def binOpCostWithProfile (p : HardwareCostProfile) (op : BinOp) : Nat :=
  match op with
  | .div | .mod => p.divModCost
  | .mul => p.mulCost
  | .mulChecked256 => p.mulChecked256Cost
  | .addChecked256 | .subChecked256 => p.addSubChecked256Cost
  | .add | .sub => p.addSubCost
  | .bitAnd | .bitOr | .bitXor => p.bitwiseCost
  | .shl | .shr | .sar => p.shiftCost
  | .eq | .lt | .le => p.cmpCost

/-- Profile-guided unary operator latency cost. -/
def unaryOpCostWithProfile (p : HardwareCostProfile) (op : UnaryOp) : Nat :=
  match op with
  | .not | .neg => p.bitwiseCost
  | .clz256 => p.clz256Cost

/-- Profile-guided total latency cost of a `ScalarExpr`. -/
def scalarExprCostWithProfile (p : HardwareCostProfile) : ScalarExpr → Nat
  | .constU64 _ | .constBool _ | .var _ => 0
  | .binOp op lhs rhs =>
    let dupPenalty := if op == .add && lhs == rhs then 1 else 0
    binOpCostWithProfile p op + dupPenalty + scalarExprCostWithProfile p lhs + scalarExprCostWithProfile p rhs
  | .unaryOp op arg =>
    unaryOpCostWithProfile p op + scalarExprCostWithProfile p arg
  | .select c t e =>
    p.selectCost + scalarExprCostWithProfile p c + scalarExprCostWithProfile p t + scalarExprCostWithProfile p e
  | .fma a b c =>
    p.fmaCost + scalarExprCostWithProfile p a + scalarExprCostWithProfile p b + scalarExprCostWithProfile p c

/-- Hardware-specific instruction cost model for a binary scalar operator. -/
def binOpCost (target : SuperoptTarget) (op : BinOp) : Nat :=
  match op with
  | .div | .mod =>
    if target.isGpu then 36 else 24
  | .mul | .mulChecked256 =>
    if target.isGpu then 5 else 4
  | .addChecked256 | .subChecked256 => 3
  | .add | .sub | .bitAnd | .bitOr | .bitXor | .shl | .shr | .sar | .eq | .lt | .le => 1

/-- Hardware-specific instruction cost model for a unary scalar operator. -/
def unaryOpCost (_target : SuperoptTarget) (op : UnaryOp) : Nat :=
  match op with
  | .not | .neg => 1
  | .clz256 => 2

/-- Hardware-specific total latency cost of a `ScalarExpr` on `target`.
    - `.div`/`.mod` cost 24 on CPU (`x86_64`/`arm64`) and 36 on GPU (`cuda_ptx`/`apple_metal`)
    - `.mul` costs 4 on CPU and 5 on GPU
    - `.fma` costs 2 on `arm64`/`cuda_ptx`/`apple_metal` and 3 on `x86_64`
    - shifts/bitwise/add/sub cost 1
    - constants and variables cost 0 -/
def scalarExprCost (target : SuperoptTarget) : ScalarExpr → Nat
  | .constU64 _ | .constBool _ | .var _ => 0
  | .binOp op lhs rhs =>
    let dupPenalty := if op == .add && lhs == rhs then 1 else 0
    binOpCost target op + dupPenalty + scalarExprCost target lhs + scalarExprCost target rhs
  | .unaryOp op arg =>
    unaryOpCost target op + scalarExprCost target arg
  | .select c t e =>
    2 + scalarExprCost target c + scalarExprCost target t + scalarExprCost target e
  | .fma a b c =>
    let fmaOpCost := match target with
      | .x86_64 => 3
      | .arm64 | .cuda_ptx | .apple_metal => 2
    fmaOpCost + scalarExprCost target a + scalarExprCost target b + scalarExprCost target c

/-- Convert a normalized `SymExpr` back into a `ScalarExpr` when it belongs to the pure scalar fragment. -/
def symExprToScalarExpr? : SymExpr → Option ScalarExpr
  | .constU64 v => some (.constU64 v)
  | .constBool b => some (.constBool b)
  | .symVar id => some (.var id)
  | .binOp op l r => do
    let l' ← symExprToScalarExpr? l
    let r' ← symExprToScalarExpr? r
    some (.binOp op l' r')
  | .unaryOp op a => do
    let a' ← symExprToScalarExpr? a
    some (.unaryOp op a')
  | .ite c t e => do
    let c' ← symExprToScalarExpr? c
    let t' ← symExprToScalarExpr? t
    let e' ← symExprToScalarExpr? e
    some (.select c' t' e')
  | .tuple _ | .bufElem _ _ | .unit => none

/-- Check if any 64-bit constant `d` is an exact power of two (`d != 0 && (d &&& (d - 1)) == 0`)
    and return its base-2 shift exponent `k ∈ [0, 63]`. -/
def powerOfTwoShift? (d : UInt64) : Option UInt64 :=
  if d == 0 || (d &&& (d - 1)) != 0 then none
  else
    (List.range 64).findSome? (fun k =>
      let ku := k.toUInt64
      if (1 : UInt64) <<< ku == d then some ku else none)

/-- Deduplicate a list of `ScalarExpr` candidates while preserving order. -/
def dedupScalarExprs (es : List ScalarExpr) : List ScalarExpr :=
  es.foldl (fun acc e => if acc.contains e then acc else acc ++ [e]) []

/-- Declarative synthesis rule for the enumerative superoptimizer. -/
structure SynthRule where
  name  : String
  apply : ScalarExpr → List ScalarExpr

/-- Declarative table of algebraic, bitwise, shift-composition, FMA, and distributive synthesis rules. -/
def superoptSynthRules : List SynthRule :=
  [ { name := "const_fold_binop"
      apply := fun
        | .binOp op (.constU64 a) (.constU64 b) => [LeanNative.Proofs.rewriteConstFoldBinOp op a b]
        | _ => [] }
  , { name := "add_self_and_quad_shift"
      apply := fun
        | .binOp .add x y =>
          let same := if x == y then [ScalarExpr.binOp .shl x (.constU64 1)] else []
          let quad :=
            match x, y with
            | .binOp .mul x1 (.constU64 2), .binOp .mul x2 (.constU64 2)
            | .binOp .shl x1 (.constU64 1), .binOp .shl x2 (.constU64 1) =>
              if x1 == x2 then [ScalarExpr.binOp .shl x1 (.constU64 2)] else []
            | _, _ => []
          same ++ quad
        | _ => [] }
  , { name := "fma_contraction"
      apply := fun
        | .binOp .add x y =>
          (match x with | .binOp .mul a b => [ScalarExpr.fma a b y] | _ => []) ++
          (match y with | .binOp .mul a b => [ScalarExpr.fma a b x] | _ => [])
        | _ => [] }
  , { name := "distributive_factoring"
      apply := fun
        | .binOp .add (.binOp .mul x1 (.constU64 a)) (.binOp .mul x2 (.constU64 b)) =>
          if x1 == x2 then
            let mulCand := ScalarExpr.binOp .mul x1 (.constU64 (a + b))
            [mulCand, LeanNative.Proofs.rewriteScalarPeephole mulCand]
          else []
        | .binOp .add (.binOp .mul x1 a) (.binOp .mul x2 b) =>
          if x1 == x2 then
            let mulCand := ScalarExpr.binOp .mul x1 (.binOp .add a b)
            [mulCand, LeanNative.Proofs.rewriteScalarPeephole mulCand]
          else []
        | _ => [] }
  , { name := "assoc_add_const"
      apply := fun
        | .binOp .add (.binOp .add inner (.constU64 c1)) (.constU64 c2)
        | .binOp .add (.constU64 c1) (.binOp .add inner (.constU64 c2)) =>
          let cSum := c1 + c2
          if cSum == 0 then [inner] else [ScalarExpr.binOp .add inner (.constU64 cSum)]
        | _ => [] }
  , { name := "shift_composition"
      apply := fun
        | .binOp .shl (.binOp .shl x (.constU64 k1)) (.constU64 k2) =>
          if k1 < 64 && k2 < 64 && (k1 + k2) < 64 then
            if k1 + k2 == 0 then [x] else [ScalarExpr.binOp .shl x (.constU64 (k1 + k2))]
          else []
        | .binOp .shr (.binOp .shr x (.constU64 k1)) (.constU64 k2) =>
          if k1 < 64 && k2 < 64 && (k1 + k2) < 64 then
            if k1 + k2 == 0 then [x] else [ScalarExpr.binOp .shr x (.constU64 (k1 + k2))]
          else []
        | _ => [] }
  , { name := "bitwise_mask_coalesce"
      apply := fun
        | .binOp .bitAnd (.binOp .bitAnd x (.constU64 m1)) (.constU64 m2) =>
          let m := m1 &&& m2
          if m == 0 then [.constU64 0] else [ScalarExpr.binOp .bitAnd x (.constU64 m)]
        | .binOp .bitOr (.binOp .bitOr x (.constU64 m1)) (.constU64 m2) =>
          let m := m1 ||| m2
          if m == 0 then [x] else [ScalarExpr.binOp .bitOr x (.constU64 m)]
        | .binOp .bitXor (.binOp .bitXor x (.constU64 m1)) (.constU64 m2) =>
          let m := m1 ^^^ m2
          if m == 0 then [x] else [ScalarExpr.binOp .bitXor x (.constU64 m)]
        | _ => [] }
  , { name := "pow2_strength_reduction"
      apply := fun
        | .binOp .div (.binOp .div x (.constU64 d1)) (.constU64 d2) =>
          match powerOfTwoShift? d1, powerOfTwoShift? d2 with
          | some k1, some k2 =>
            if (k1 + k2) < 64 then
              if k1 + k2 == 0 then [x] else [ScalarExpr.binOp .shr x (.constU64 (k1 + k2))]
            else []
          | _, _ => []
        | .binOp .div x (.constU64 d) =>
          match powerOfTwoShift? d with
          | some 0 => [x]
          | some k => [ScalarExpr.binOp .shr x (.constU64 k)]
          | none => []
        | .binOp .mod x (.constU64 d) =>
          match powerOfTwoShift? d with
          | some 0 => [.constU64 0]
          | some _ => [ScalarExpr.binOp .bitAnd x (.constU64 (d - 1))]
          | none => []
        | .binOp .mul x (.constU64 d) | .binOp .mul (.constU64 d) x =>
          match powerOfTwoShift? d with
          | some 0 => [x]
          | some k => [ScalarExpr.binOp .shl x (.constU64 k)]
          | none => []
        | _ => [] }
  ]

/-- Apply all declarative `superoptSynthRules` to a top-level `ScalarExpr`. -/
def synthesizeTopLevelTemplates (e : ScalarExpr) : List ScalarExpr :=
  superoptSynthRules.foldl (fun acc rule => acc ++ rule.apply e) []

/-- Collect all variable IDs referenced in a `ScalarExpr`. -/
def collectScalarVars : ScalarExpr → List VarId
  | .constU64 _ | .constBool _ => []
  | .var id => [id]
  | .binOp _ l r =>
    let vl := collectScalarVars l
    let vr := collectScalarVars r
    vl ++ vr.filter (fun x => !vl.contains x)
  | .unaryOp _ a => collectScalarVars a
  | .select c t e =>
    let vc := collectScalarVars c
    let vt := collectScalarVars t
    let ve := collectScalarVars e
    let vct := vc ++ vt.filter (fun x => !vc.contains x)
    vct ++ ve.filter (fun x => !vct.contains x)
  | .fma a b c =>
    let va := collectScalarVars a
    let vb := collectScalarVars b
    let vc := collectScalarVars c
    let vab := va ++ vb.filter (fun x => !va.contains x)
    vab ++ vc.filter (fun x => !vab.contains x)

/-- Extended algebraic normalizer on `SymExpr` that also canonicalizes associative constants,
    distributive constant factoring, `(x + x) -> x <<< 1`, and shift/mask composition so
    `symCheckScalarEquiv` can formally validate superoptimizer synthesis templates. -/
def normSymSuperoptStep (s : SymExpr) : SymExpr :=
  let s0 := normSymExpr s
  match s0 with
  -- (x + x) -> x <<< 1
  | .binOp .add x y =>
    if x == y then
      normSymExpr (.binOp .shl x (.constU64 1))
    else
      match x, y with
      -- (x <<< 1) + (x <<< 1) -> x <<< 2
      | .binOp .shl x1 (.constU64 1), .binOp .shl x2 (.constU64 1) =>
        if x1 == x2 then normSymExpr (.binOp .shl x1 (.constU64 2)) else s0
      -- Distributive factoring: (x * a) + (x * b) or shifted equivalents
      | .binOp .mul x1 (.constU64 a), .binOp .mul x2 (.constU64 b) =>
        if x1 == x2 then normSymExpr (.binOp .mul x1 (.constU64 (a + b))) else s0
      | .binOp .shl x1 (.constU64 k1), .binOp .mul x2 (.constU64 b) =>
        if x1 == x2 && k1 < 64 then
          normSymExpr (.binOp .mul x1 (.constU64 ((1 <<< k1) + b)))
        else s0
      | .binOp .mul x1 (.constU64 a), .binOp .shl x2 (.constU64 k2) =>
        if x1 == x2 && k2 < 64 then
          normSymExpr (.binOp .mul x1 (.constU64 (a + (1 <<< k2))))
        else s0
      | .binOp .shl x1 (.constU64 k1), .binOp .shl x2 (.constU64 k2) =>
        if x1 == x2 && k1 < 64 && k2 < 64 then
          normSymExpr (.binOp .mul x1 (.constU64 ((1 <<< k1) + (1 <<< k2))))
        else s0
      -- Associative addition: (x + c1) + c2 -> x + (c1 + c2)
      | .binOp .add inner (.constU64 c1), .constU64 c2 =>
        normSymExpr (.binOp .add inner (.constU64 (c1 + c2)))
      | _, _ => s0
  -- Shift composition: (x <<< k1) <<< k2 -> x <<< (k1 + k2)
  | .binOp .shl (.binOp .shl x (.constU64 k1)) (.constU64 k2) =>
    if k1 < 64 && k2 < 64 && (k1 + k2) < 64 then
      normSymExpr (.binOp .shl x (.constU64 (k1 + k2)))
    else s0
  | .binOp .shr (.binOp .shr x (.constU64 k1)) (.constU64 k2) =>
    if k1 < 64 && k2 < 64 && (k1 + k2) < 64 then
      normSymExpr (.binOp .shr x (.constU64 (k1 + k2)))
    else s0
  -- Bitwise mask composition
  | .binOp .bitAnd (.binOp .bitAnd x (.constU64 m1)) (.constU64 m2) =>
    normSymExpr (.binOp .bitAnd x (.constU64 (m1 &&& m2)))
  | .binOp .bitOr (.binOp .bitOr x (.constU64 m1)) (.constU64 m2) =>
    normSymExpr (.binOp .bitOr x (.constU64 (m1 ||| m2)))
  | .binOp .bitXor (.binOp .bitXor x (.constU64 m1)) (.constU64 m2) =>
    normSymExpr (.binOp .bitXor x (.constU64 (m1 ^^^ m2)))
  -- Division/modulo by power of two
  | .binOp .div (.binOp .div x (.constU64 d1)) (.constU64 d2) =>
    match powerOfTwoShift? d1, powerOfTwoShift? d2 with
    | some k1, some k2 =>
      if (k1 + k2) < 64 then normSymExpr (.binOp .shr x (.constU64 (k1 + k2))) else s0
    | _, _ => s0
  | .binOp .div x (.constU64 d) =>
    match powerOfTwoShift? d with
    | some k => normSymExpr (.binOp .shr x (.constU64 k))
    | none => s0
  | .binOp .mod x (.constU64 d) =>
    match powerOfTwoShift? d with
    | some 0 => .constU64 0
    | some _ => normSymExpr (.binOp .bitAnd x (.constU64 (d - 1)))
    | none => s0
  | .binOp .mul x (.constU64 d) =>
    match powerOfTwoShift? d with
    | some k => normSymExpr (.binOp .shl x (.constU64 k))
    | none => s0
  | _ => s0

/-- Recursive bottom-up superoptimizer canonicalizer on `SymExpr`. -/
def normSymSuperopt : SymExpr → SymExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .symVar id => .symVar id
  | .binOp op l r => normSymSuperoptStep (.binOp op (normSymSuperopt l) (normSymSuperopt r))
  | .unaryOp op a => normSymSuperoptStep (.unaryOp op (normSymSuperopt a))
  | .ite c t e => normSymSuperoptStep (.ite (normSymSuperopt c) (normSymSuperopt t) (normSymSuperopt e))
  | other => normSymExpr other

/-- Stage 1 Soundness Filter: FastCheck 16-state concrete equivalence filter.
    Tests boundary values (`0, 1, 2, 7, 42, 255, 0xffffffff, 0xffffffffffffffff`) and
    SplitMix64 states via `evalScalarExpr`. -/
def fastCheckScalarEquiv (e cand : ScalarExpr) : Bool :=
  let vars := collectScalarVars e ++ (collectScalarVars cand).filter (fun x => !(collectScalarVars e).contains x)
  let boundaryVals : List UInt64 :=
    [0, 1, 2, 7, 42, 255, 0xffffffff, 0xffffffffffffffff]
  (List.range 16).all (fun sampleIdx =>
    let env : VarEnv := vars.foldl (fun (accEnv, vIdx) varId =>
      let val : UInt64 :=
        if sampleIdx < 8 then
          let bIdx := (sampleIdx + vIdx * 3) % boundaryVals.length
          boundaryVals[bIdx]?.getD 0
        else
          let seed : UInt64 := (sampleIdx.toUInt64 + 1) * 0x9e3779b97f4a7c15 + vIdx.toUInt64 * 0xbf58476d1ce4e5b9
          let (r, _) := splitMix64Next seed
          r
      (accEnv.bind varId (.u64 val), vIdx + 1)
    ) (VarEnv.empty, 0) |>.1
    match evalScalarExpr env e, evalScalarExpr env cand with
    | .ok v1, .ok v2 => v1 == v2
    | .error _, .error _ => true
    | _, _ => false
  )

/-- Stage 2 Soundness Verifier: SymbolicTV formal equivalence check.
    Verifies symbolic canonical normal form equivalence plus UB/poison preservation. -/
def symCheckScalarEquiv (e cand : ScalarExpr) : Bool :=
  let se := symEvalScalar default e
  let sc := symEvalScalar default cand
  let ubOk := !se.noUB || sc.noUB
  let poisonOk := !se.nonPoison || sc.nonPoison
  let strictNormEq := normSymExpr se.expr == normSymExpr sc.expr
  let extNormEq := normSymSuperopt se.expr == normSymSuperopt sc.expr
  ubOk && poisonOk && (strictNormEq || extNormEq)

/-- Synthesize candidate expressions for `e` on `target`:
    1. Kernel-verified `LeanNative.Proofs.rewriteScalarPeephole e`
    2. Symbolic canonical normalizer `symExprToScalarExpr? (normSymExpr (symEvalScalar default e).expr)`
    3. Enumerative algebraic & bitwise synthesis templates over `e` and its optimized subexpressions. -/
partial def synthesizeCandidates (target : SuperoptTarget) (e : ScalarExpr) : List ScalarExpr :=
  -- First recursively optimize children so multi-level templates trigger
  let eRec : ScalarExpr :=
    match e with
    | .binOp op l r =>
      let lBest := match (synthesizeCandidates target l).head? with | some c => c | none => l
      let rBest := match (synthesizeCandidates target r).head? with | some c => c | none => r
      .binOp op lBest rBest
    | .unaryOp op a =>
      let aBest := match (synthesizeCandidates target a).head? with | some c => c | none => a
      .unaryOp op aBest
    | .select c t f =>
      let cBest := match (synthesizeCandidates target c).head? with | some x => x | none => c
      let tBest := match (synthesizeCandidates target t).head? with | some x => x | none => t
      let fBest := match (synthesizeCandidates target f).head? with | some x => x | none => f
      .select cBest tBest fBest
    | .fma a b c =>
      let aBest := match (synthesizeCandidates target a).head? with | some x => x | none => a
      let bBest := match (synthesizeCandidates target b).head? with | some x => x | none => b
      let cBest := match (synthesizeCandidates target c).head? with | some x => x | none => c
      .fma aBest bBest cBest
    | other => other
  let peepCand1 := LeanNative.Proofs.rewriteScalarPeephole e
  let peepCand2 := LeanNative.Proofs.rewriteScalarPeephole eRec
  let symCand1 :=
    match symExprToScalarExpr? (normSymExpr (symEvalScalar default e).expr) with
    | some sc => [sc]
    | none => []
  let symCand2 :=
    match symExprToScalarExpr? (normSymSuperopt (symEvalScalar default e).expr) with
    | some sc => [sc]
    | none => []
  let tmplCands1 := synthesizeTopLevelTemplates e
  let tmplCands2 := synthesizeTopLevelTemplates eRec
  let tmplCands3 := tmplCands1.flatMap synthesizeTopLevelTemplates ++ tmplCands2.flatMap synthesizeTopLevelTemplates
  let rawCands :=
    [eRec, peepCand1, peepCand2] ++ symCand1 ++ symCand2 ++ tmplCands1 ++ tmplCands2 ++ tmplCands3
  let uniqueCands := dedupScalarExprs rawCands
  -- Filter by two-stage soundness (FastCheck + SymbolicTV) and sort by target cost
  let validCands := uniqueCands.filter (fun cand =>
    fastCheckScalarEquiv e cand && symCheckScalarEquiv e cand)
  -- Pick the lowest-cost verified candidate first
  let best := validCands.foldl (fun bestOpt cand =>
    match bestOpt with
    | none => some cand
    | some curBest =>
      if scalarExprCost target cand < scalarExprCost target curBest then
        some cand
      else
        some curBest
  ) none
  match best with
  | some b => b :: (validCands.filter (fun c => c != b))
  | none => [e]

/-- Record of a single verified superoptimizer rewrite inside an `LNIRDecl`. -/
structure SuperoptRewriteRecord where
  declName            : String
  target              : String
  originalExpr        : String
  synthesizedExpr     : String
  costBefore          : Nat
  costAfter           : Nat
  fastCheckPassed     : Bool
  symbolicTVPassed    : Bool
  kernelProofVerified : Bool := false
  theoremRef          : String := "LeanNative.Proofs.SymbolicTV"
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Module-level superoptimization report. -/
structure SuperoptReport where
  moduleName       : String
  schemaVersion    : String := "lean-native-superopt-v1"
  target           : String
  totalDecls       : Nat
  rewritesApplied  : Nat
  totalCostBefore  : Nat
  totalCostAfter   : Nat
  records          : List SuperoptRewriteRecord
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Superoptimize a single `ScalarExpr` for `target`, selecting the lowest-cost verified
    candidate strictly cheaper than `scalarExprCost target e`. -/
def superoptScalarExpr (target : SuperoptTarget) (declName : String) (e : ScalarExpr) :
    ScalarExpr × Option SuperoptRewriteRecord :=
  let origCost := scalarExprCost target e
  let cands := synthesizeCandidates target e
  let bestCand :=
    cands.foldl (fun acc cand =>
      let cCost := scalarExprCost target cand
      let fcOk := fastCheckScalarEquiv e cand
      let tvOk := symCheckScalarEquiv e cand
      if fcOk && tvOk && cCost < scalarExprCost target acc then
        cand
      else
        acc
    ) e
  let afterCost := scalarExprCost target bestCand
  if bestCand != e && afterCost < origCost then
    let isKernelVerified :=
      bestCand == LeanNative.Proofs.rewriteScalarVerified e ||
      bestCand == LeanNative.Proofs.rewriteScalarPeephole e
    let thmRef :=
      if isKernelVerified then "LeanNative.Proofs.rewriteScalarVerified_sound"
      else "LeanNative.Proofs.SymbolicTV"
    let recEntry : SuperoptRewriteRecord := {
      declName := declName
      target := target.toString
      originalExpr := reprStr e
      synthesizedExpr := reprStr bestCand
      costBefore := origCost
      costAfter := afterCost
      fastCheckPassed := fastCheckScalarEquiv e bestCand
      symbolicTVPassed := symCheckScalarEquiv e bestCand
      kernelProofVerified := isKernelVerified
      theoremRef := thmRef
    }
    (bestCand, some recEntry)
  else
    (e, none)

/-- Superoptimize all scalar expressions in an `LNIRCode` block. -/
def superoptCode (target : SuperoptTarget) (declName : String) :
    LNIRCode → LNIRCode × List SuperoptRewriteRecord
  | .letBind dst ty (.scalar se) k =>
    let (se', recOpt) := superoptScalarExpr target declName se
    let (k', kRecs) := superoptCode target declName k
    let recs := match recOpt with | some r => r :: kRecs | none => kRecs
    (.letBind dst ty (.scalar se') k', recs)
  | .letBind dst ty val k =>
    let (k', kRecs) := superoptCode target declName k
    (.letBind dst ty val k', kRecs)
  | .rawStore pv iv vv ety k =>
    let (k', kRecs) := superoptCode target declName k
    (.rawStore pv iv vv ety k', kRecs)
  | .incRef ov c k =>
    let (k', kRecs) := superoptCode target declName k
    (.incRef ov c k', kRecs)
  | .decRef ov c k =>
    let (k', kRecs) := superoptCode target declName k
    (.decRef ov c k', kRecs)
  | .ite cv t e =>
    let (t', tRecs) := superoptCode target declName t
    let (e', eRecs) := superoptCode target declName e
    (.ite cv t' e', tRecs ++ eRecs)
  | .seqFor iv lv hv av ai aty step k =>
    let (step', sRecs) := superoptCode target declName step
    let (k', kRecs) := superoptCode target declName k
    (.seqFor iv lv hv av ai aty step' k', sRecs ++ kRecs)
  | .parFor ov lv ins ety (.customScalar idxVar inVars body) k =>
    let (body', recOpt) := superoptScalarExpr target declName body
    let (k', kRecs) := superoptCode target declName k
    let recs := match recOpt with | some r => r :: kRecs | none => kRecs
    (.parFor ov lv ins ety (.customScalar idxVar inVars body') k', recs)
  | .parFor ov lv ins ety kern k =>
    let (k', kRecs) := superoptCode target declName k
    (.parFor ov lv ins ety kern k', kRecs)
  | .ret v => (.ret v, [])
  | .unreachable => (.unreachable, [])

/-- Compute total scalar expression latency cost across an `LNIRCode` block. -/
def codeScalarCost (target : SuperoptTarget) : LNIRCode → Nat
  | .letBind _ _ (.scalar se) k => scalarExprCost target se + codeScalarCost target k
  | .letBind _ _ _ k => codeScalarCost target k
  | .rawStore _ _ _ _ k => codeScalarCost target k
  | .incRef _ _ k => codeScalarCost target k
  | .decRef _ _ k => codeScalarCost target k
  | .ite _ t e => 4 + codeScalarCost target t + codeScalarCost target e
  | .seqFor _ _ _ _ _ _ step k => codeScalarCost target step + codeScalarCost target k
  | .parFor _ _ _ _ (.customScalar _ _ body) k => scalarExprCost target body + codeScalarCost target k
  | .parFor _ _ _ _ _ k => codeScalarCost target k
  | .ret _ | .unreachable => 0

/-- Superoptimize an `LNIRDecl` for `target`. -/
def superoptDecl (target : SuperoptTarget) (d : LNIRDecl) :
    LNIRDecl × List SuperoptRewriteRecord :=
  let (body', recs) := superoptCode target d.name d.body
  let assurance' :=
    if recs.isEmpty then d.assurance
    else if recs.all (fun r => r.kernelProofVerified) then
      AssuranceLevel.combine d.assurance .verifiedKernelProof
    else
      AssuranceLevel.combine d.assurance .translationValidated
  ({ d with body := body', assurance := assurance' }, recs)

/-- Superoptimize all declarations in an `LNIRModule` for `target` and return the
    optimized module along with a structured `SuperoptReport`. -/
def superoptModule (target : SuperoptTarget) (m : LNIRModule) : LNIRModule × SuperoptReport :=
  let costBefore := m.decls.foldl (fun acc d => acc + codeScalarCost target d.body) 0
  let (decls', allRecs) := m.decls.foldl (fun (dAcc, rAcc) d =>
    let (d', recs) := superoptDecl target d
    (dAcc ++ [d'], rAcc ++ recs)
  ) ([], [])
  let m' : LNIRModule := { m with decls := decls' }
  let costAfter := m'.decls.foldl (fun acc d => acc + codeScalarCost target d.body) 0
  let report : SuperoptReport := {
    moduleName := m.moduleName
    schemaVersion := "lean-native-superopt-v1"
    target := target.toString
    totalDecls := m.decls.length
    rewritesApplied := allRecs.length
    totalCostBefore := costBefore
    totalCostAfter := costAfter
    records := allRecs
  }
  (m', report)

/-- Superoptimize a single `ScalarExpr` using a custom `HardwareCostProfile` (`profiles/*.json`),
    enforcing the exact same `fastCheckScalarEquiv` + `symCheckScalarEquiv` formal soundness gate. -/
def superoptScalarExprWithProfile (p : HardwareCostProfile) (declName : String) (e : ScalarExpr) :
    ScalarExpr × Option SuperoptRewriteRecord :=
  let origCost := scalarExprCostWithProfile p e
  let cands := synthesizeCandidates p.target e
  let bestCand :=
    cands.foldl (fun acc cand =>
      let cCost := scalarExprCostWithProfile p cand
      let fcOk := fastCheckScalarEquiv e cand
      let tvOk := symCheckScalarEquiv e cand
      if fcOk && tvOk && cCost < scalarExprCostWithProfile p acc then
        cand
      else
        acc
    ) e
  let afterCost := scalarExprCostWithProfile p bestCand
  if bestCand != e && afterCost < origCost then
    let isKernelVerified :=
      bestCand == LeanNative.Proofs.rewriteScalarVerified e ||
      bestCand == LeanNative.Proofs.rewriteScalarPeephole e
    let thmRef :=
      if isKernelVerified then "LeanNative.Proofs.rewriteScalarVerified_sound"
      else "LeanNative.Proofs.SymbolicTV"
    let recEntry : SuperoptRewriteRecord := {
      declName := declName
      target := s!"{p.target.toString}:{p.profileId}"
      originalExpr := reprStr e
      synthesizedExpr := reprStr bestCand
      costBefore := origCost
      costAfter := afterCost
      fastCheckPassed := fastCheckScalarEquiv e bestCand
      symbolicTVPassed := symCheckScalarEquiv e bestCand
      kernelProofVerified := isKernelVerified
      theoremRef := thmRef
    }
    (bestCand, some recEntry)
  else
    (e, none)

/-- Superoptimize all declarations in an `LNIRModule` using a `HardwareCostProfile` (`profiles/*.json`). -/
def superoptModuleWithProfile (p : HardwareCostProfile) (m : LNIRModule) : LNIRModule × SuperoptReport :=
  let rec goCode (declName : String) : LNIRCode → LNIRCode × List SuperoptRewriteRecord
    | .letBind dst ty (.scalar se) k =>
      let (se', recOpt) := superoptScalarExprWithProfile p declName se
      let (k', kRecs) := goCode declName k
      let recs := match recOpt with | some r => r :: kRecs | none => kRecs
      (.letBind dst ty (.scalar se') k', recs)
    | .letBind dst ty val k =>
      let (k', kRecs) := goCode declName k
      (.letBind dst ty val k', kRecs)
    | .rawStore pv iv vv ety k =>
      let (k', kRecs) := goCode declName k
      (.rawStore pv iv vv ety k', kRecs)
    | .incRef ov c k =>
      let (k', kRecs) := goCode declName k
      (.incRef ov c k', kRecs)
    | .decRef ov c k =>
      let (k', kRecs) := goCode declName k
      (.decRef ov c k', kRecs)
    | .ite cv t e =>
      let (t', tRecs) := goCode declName t
      let (e', eRecs) := goCode declName e
      (.ite cv t' e', tRecs ++ eRecs)
    | .seqFor iv lv hv av ai aty step k =>
      let (step', sRecs) := goCode declName step
      let (k', kRecs) := goCode declName k
      (.seqFor iv lv hv av ai aty step' k', sRecs ++ kRecs)
    | .parFor ov lv ins ety (.customScalar idxVar inVars body) k =>
      let (body', recOpt) := superoptScalarExprWithProfile p declName body
      let (k', kRecs) := goCode declName k
      let recs := match recOpt with | some r => r :: kRecs | none => kRecs
      (.parFor ov lv ins ety (.customScalar idxVar inVars body') k', recs)
    | .parFor ov lv ins ety kern k =>
      let (k', kRecs) := goCode declName k
      (.parFor ov lv ins ety kern k', kRecs)
    | .ret v => (.ret v, [])
    | .unreachable => (.unreachable, [])
  let rec codeCostProf : LNIRCode → Nat
    | .letBind _ _ (.scalar se) k => scalarExprCostWithProfile p se + codeCostProf k
    | .letBind _ _ _ k => codeCostProf k
    | .rawStore _ _ _ _ k => codeCostProf k
    | .incRef _ _ k => codeCostProf k
    | .decRef _ _ k => codeCostProf k
    | .ite _ t e => 4 + codeCostProf t + codeCostProf e
    | .seqFor _ _ _ _ _ _ step k => codeCostProf step + codeCostProf k
    | .parFor _ _ _ _ (.customScalar _ _ body) k => scalarExprCostWithProfile p body + codeCostProf k
    | .parFor _ _ _ _ _ k => codeCostProf k
    | .ret _ | .unreachable => 0
  let cBefore := m.decls.foldl (fun acc d => acc + codeCostProf d.body) 0
  let (decls', allRecs) := m.decls.foldl (fun (dAcc, rAcc) d =>
    let (body', recs) := goCode d.name d.body
    let assurance' :=
      if recs.isEmpty then d.assurance
      else if recs.all (fun r => r.kernelProofVerified) then
        AssuranceLevel.combine d.assurance .verifiedKernelProof
      else
        AssuranceLevel.combine d.assurance .translationValidated
    (dAcc ++ [{ d with body := body', assurance := assurance' }], rAcc ++ recs)
  ) ([], [])
  let m' : LNIRModule := { m with decls := decls' }
  let cAfter := m'.decls.foldl (fun acc d => acc + codeCostProf d.body) 0
  (m', {
    moduleName := m.moduleName
    schemaVersion := "lean-native-superopt-v1"
    target := s!"{p.target.toString}:{p.profileId}"
    totalDecls := m.decls.length
    rewritesApplied := allRecs.length
    totalCostBefore := cBefore
    totalCostAfter := cAfter
    records := allRecs
  })

private abbrev escapeJsonSO := LeanNative.IR.jsonEscape

def SuperoptRewriteRecord.toJson (r : SuperoptRewriteRecord) : String :=
  "{" ++
  s!"\"declName\":\"{escapeJsonSO r.declName}\"," ++
  s!"\"target\":\"{escapeJsonSO r.target}\"," ++
  s!"\"originalExpr\":\"{escapeJsonSO r.originalExpr}\"," ++
  s!"\"synthesizedExpr\":\"{escapeJsonSO r.synthesizedExpr}\"," ++
  s!"\"costBefore\":{r.costBefore}," ++
  s!"\"costAfter\":{r.costAfter}," ++
  s!"\"fastCheckPassed\":{if r.fastCheckPassed then "true" else "false"}," ++
  s!"\"symbolicTVPassed\":{if r.symbolicTVPassed then "true" else "false"}," ++
  s!"\"kernelProofVerified\":{if r.kernelProofVerified then "true" else "false"}," ++
  s!"\"theoremRef\":\"{escapeJsonSO r.theoremRef}\"" ++
  "}"

def SuperoptReport.toJson (r : SuperoptReport) : String :=
  let recsJson := String.intercalate "," (r.records.map SuperoptRewriteRecord.toJson)
  "{" ++
  s!"\"schemaVersion\":\"{escapeJsonSO r.schemaVersion}\"," ++
  s!"\"moduleName\":\"{escapeJsonSO r.moduleName}\"," ++
  s!"\"target\":\"{escapeJsonSO r.target}\"," ++
  s!"\"totalDecls\":{r.totalDecls}," ++
  s!"\"rewritesApplied\":{r.rewritesApplied}," ++
  s!"\"totalCostBefore\":{r.totalCostBefore}," ++
  s!"\"totalCostAfter\":{r.totalCostAfter}," ++
  s!"\"records\":[{recsJson}]" ++
  "}"

def SuperoptReport.formatSummary (r : SuperoptReport) : String :=
  let header :=
    s!"=== LeanNative Cost-Guided Enumerative Superoptimizer Report ===\n" ++
    s!"Module          : {r.moduleName} ({r.schemaVersion})\n" ++
    s!"Target Arch     : {r.target}\n" ++
    s!"Rewrites Applied: {r.rewritesApplied} across {r.totalDecls} declarations\n" ++
    s!"Total Latency   : {r.totalCostBefore} -> {r.totalCostAfter} cycles\n"
  let lines := r.records.map (fun recEntry =>
    s!"  [{recEntry.declName}] cost {recEntry.costBefore} -> {recEntry.costAfter} " ++
    s!"(FastCheck={recEntry.fastCheckPassed}, SymbolicTV={recEntry.symbolicTVPassed}, KernelProof={recEntry.kernelProofVerified} [{recEntry.theoremRef}]): " ++
    s!"{recEntry.originalExpr} ==> {recEntry.synthesizedExpr}")
  header ++ String.intercalate "\n" lines

end LeanNative.Transform
