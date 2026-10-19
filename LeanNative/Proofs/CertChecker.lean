import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.LoopOptProofs

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-- Single transformation certificate recording input/output IR structural hashes,
    the referenced formal theorem or validation rule, and the assurance level. -/
structure OptimizationCert where
  passName   : String
  declName   : String
  inputHash  : String
  outputHash : String
  changed    : Bool := false
  assurance  : AssuranceLevel := .verifiedKernelProof
  theoremRef : String
  notes      : String := ""
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Per-declaration certificate chain summary produced by `verifyModuleCerts`. -/
structure DeclCertSummary where
  declName         : String
  initialHash      : String
  finalHash        : String
  overallAssurance : AssuranceLevel
  chainValid       : Bool
  theoremsValid    : Bool
  steps            : List OptimizationCert
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Module-level optimization certificate report and verification result. -/
structure ModuleCertReport where
  moduleName       : String
  schemaVersion    : String := "lean-native-cert-v1"
  certs            : List OptimizationCert
  declSummaries    : List DeclCertSummary := []
  overallAssurance : AssuranceLevel := .verifiedKernelProof
  verified         : Bool := true
  errors           : List String := []
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Registry of kernel-checked soundness theorems in `LeanNative.Proofs` and `LeanNative.Semantics`. -/
def verifiedTheoremRegistry : List String :=
  [ "LeanNative.Proofs.PeepholeProofs.rewriteScalarPeephole_sound"
  , "LeanNative.Proofs.PeepholeProofs.rewriteLNIRExpr_sound"
  , "LeanNative.Proofs.PeepholeProofs.evalExpr_optimizeExpr_eq"
  , "LeanNative.Proofs.rewriteScalarPeephole_sound"
  , "LeanNative.Proofs.rewriteLNIRExpr_sound"
  , "LeanNative.Proofs.evalExpr_optimizeExpr_eq"
  , "LeanNative.Proofs.LoopOptProofs.unboxTupleProj_sound"
  , "LeanNative.Proofs.LoopOptProofs.unboxTupleProj0_sound"
  , "LeanNative.Proofs.LoopOptProofs.unboxTupleProj1_sound"
  , "LeanNative.Proofs.LoopOptProofs.eval_unboxTupleSROA_refines"
  , "LeanNative.Proofs.LoopOptProofs.hoistExclusivity_sound"
  , "LeanNative.Proofs.LoopOptProofs.eval_hoistExclusivity_refines"
  , "LeanNative.Proofs.LoopOptProofs.unboxedLoopStep_sound"
  , "LeanNative.Proofs.LoopOptProofs.unboxedLoopAccumulator_sim"
  , "LeanNative.Proofs.unboxTupleProj_sound"
  , "LeanNative.Proofs.unboxTupleProj0_sound"
  , "LeanNative.Proofs.unboxTupleProj1_sound"
  , "LeanNative.Proofs.eval_unboxTupleSROA_refines"
  , "LeanNative.Proofs.hoistExclusivity_sound"
  , "LeanNative.Proofs.eval_hoistExclusivity_refines"
  , "LeanNative.Proofs.unboxedLoopStep_sound"
  , "LeanNative.Proofs.unboxedLoopAccumulator_sim"
  , "LeanNative.Semantics.ScalarExprEquiv.refl"
  , "LeanNative.Semantics.ExprRefines.refl"
  , "LeanNative.Semantics.CodeRefines.refl"
  ]

/-- Check whether `thmName` is a registered kernel-checked theorem in `LeanNative.Proofs`. -/
def isRegisteredTheorem (thmName : String) : Bool :=
  verifiedTheoremRegistry.contains thmName

/-- Verify a single `OptimizationCert` against its claimed `AssuranceLevel` and theorem reference. -/
def verifySingleCert (c : OptimizationCert) : Bool × List String :=
  let errs0 : List String :=
    if c.inputHash.isEmpty || c.outputHash.isEmpty then
      [s!"[{c.declName}:{c.passName}] empty structural hash"]
    else []
  let errs1 : List String :=
    if !c.changed && c.inputHash != c.outputHash then
      errs0 ++ [s!"[{c.declName}:{c.passName}] marked unchanged but inputHash ({c.inputHash}) != outputHash ({c.outputHash})"]
    else errs0
  let errs2 : List String :=
    match c.assurance with
    | .verifiedKernelProof =>
      if isRegisteredTheorem c.theoremRef then errs1
      else errs1 ++ [s!"[{c.declName}:{c.passName}] claims VerifiedKernelProof but theorem '{c.theoremRef}' is not in verifiedTheoremRegistry"]
    | .translationValidated =>
      if c.theoremRef.isEmpty then
        errs1 ++ [s!"[{c.declName}:{c.passName}] TranslationValidated certificate missing rule/obligation reference"]
      else errs1
    | .unverifiedFallback =>
      errs1
  (errs2.isEmpty, errs2)

/-- Verify hash-chain continuity (`prev.outputHash == next.inputHash`) for a single declaration's pass steps. -/
def verifyHashChain : List OptimizationCert → Bool × List String
  | [] => (true, [])
  | [_] => (true, [])
  | c1 :: c2 :: rest =>
    let (restOk, restErrs) := verifyHashChain (c2 :: rest)
    if c1.outputHash == c2.inputHash then
      (restOk, restErrs)
    else
      let err := s!"[{c1.declName}] hash chain broken between pass '{c1.passName}' (outputHash={c1.outputHash}) and '{c2.passName}' (inputHash={c2.inputHash})"
      (false, err :: restErrs)

/-- Deduplicate declaration names while preserving appearance order. -/
def uniqueDeclNames (certs : List OptimizationCert) : List String :=
  certs.foldl (fun acc c => if acc.contains c.declName then acc else acc ++ [c.declName]) []

/-- Summarize and verify all certificate steps for a single declaration `declName`. -/
def verifyDeclCerts (declName : String) (steps : List OptimizationCert) : DeclCertSummary × List String :=
  let initHash := match steps.head? with | some c => c.inputHash | none => ""
  let finHash  := match steps.getLast? with | some c => c.outputHash | none => ""
  let overallAssurance := steps.foldl (fun acc c => AssuranceLevel.combine acc c.assurance) .verifiedKernelProof
  let (chainOk, chainErrs) := verifyHashChain steps
  let stepResults := steps.map verifySingleCert
  let thmsOk := stepResults.all Prod.fst
  let stepErrs := stepResults.foldl (fun acc r => acc ++ r.snd) []
  let summary : DeclCertSummary := {
    declName := declName
    initialHash := initHash
    finalHash := finHash
    overallAssurance := overallAssurance
    chainValid := chainOk
    theoremsValid := thmsOk
    steps := steps
  }
  (summary, chainErrs ++ stepErrs)

/-- Independent certificate verifier for an entire `LNIRModule`'s optimization pipeline.
    Checks:
    1. Per-declaration hash-chain continuity (`inputHash -> outputHash`),
    2. Every `VerifiedKernelProof` step references a theorem in `verifiedTheoremRegistry`,
    3. Conservative assurance level aggregation across all passes. -/
def verifyModuleCerts (moduleName : String) (certs : List OptimizationCert) : ModuleCertReport :=
  let declNames := uniqueDeclNames certs
  let declChecks := declNames.map (fun dname =>
    let dsteps := certs.filter (fun c => c.declName == dname)
    verifyDeclCerts dname dsteps)
  let summaries := declChecks.map Prod.fst
  let allErrors := declChecks.foldl (fun acc r => acc ++ r.snd) []
  let overallAssurance := summaries.foldl (fun acc s => AssuranceLevel.combine acc s.overallAssurance) .verifiedKernelProof
  { moduleName := moduleName
    schemaVersion := "lean-native-cert-v1"
    certs := certs
    declSummaries := summaries
    overallAssurance := overallAssurance
    verified := allErrors.isEmpty
    errors := allErrors }

/-! ## JSON Serialization -/

private def escapeJsonString (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | other => acc.push other
  ) ""

def OptimizationCert.toJson (c : OptimizationCert) : String :=
  "{" ++
  s!"\"passName\":\"{escapeJsonString c.passName}\"," ++
  s!"\"declName\":\"{escapeJsonString c.declName}\"," ++
  s!"\"inputHash\":\"{escapeJsonString c.inputHash}\"," ++
  s!"\"outputHash\":\"{escapeJsonString c.outputHash}\"," ++
  s!"\"changed\":{if c.changed then "true" else "false"}," ++
  s!"\"assurance\":\"{c.assurance.toString}\"," ++
  s!"\"theoremRef\":\"{escapeJsonString c.theoremRef}\"," ++
  s!"\"notes\":\"{escapeJsonString c.notes}\"" ++
  "}"

def DeclCertSummary.toJson (s : DeclCertSummary) : String :=
  let stepsJson := String.intercalate "," (s.steps.map OptimizationCert.toJson)
  "{" ++
  s!"\"declName\":\"{escapeJsonString s.declName}\"," ++
  s!"\"initialHash\":\"{escapeJsonString s.initialHash}\"," ++
  s!"\"finalHash\":\"{escapeJsonString s.finalHash}\"," ++
  s!"\"overallAssurance\":\"{s.overallAssurance.toString}\"," ++
  s!"\"chainValid\":{if s.chainValid then "true" else "false"}," ++
  s!"\"theoremsValid\":{if s.theoremsValid then "true" else "false"}," ++
  s!"\"steps\":[{stepsJson}]" ++
  "}"

def ModuleCertReport.toJson (r : ModuleCertReport) : String :=
  let certsJson := String.intercalate "," (r.certs.map OptimizationCert.toJson)
  let summariesJson := String.intercalate "," (r.declSummaries.map DeclCertSummary.toJson)
  let errsJson := String.intercalate "," (r.errors.map (fun e => s!"\"{escapeJsonString e}\""))
  "{" ++
  s!"\"schemaVersion\":\"{escapeJsonString r.schemaVersion}\"," ++
  s!"\"moduleName\":\"{escapeJsonString r.moduleName}\"," ++
  s!"\"verified\":{if r.verified then "true" else "false"}," ++
  s!"\"overallAssurance\":\"{r.overallAssurance.toString}\"," ++
  s!"\"declSummaries\":[{summariesJson}]," ++
  s!"\"certs\":[{certsJson}]," ++
  s!"\"errors\":[{errsJson}]" ++
  "}"

end LeanNative.Proofs
