import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.LoopOptProofs
import LeanNative.Proofs.SymbolicTV

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
  let proofs := [
    "rewriteBinOpStep_sound", "rewriteSelectStep_sound", "rewriteScalarPeepholeStep_sound",
    "rewriteScalarPeephole_sound", "rewriteLNIRExpr_sound", "evalExpr_optimizeExpr_eq",
    "evalCode_rewriteCodePeephole_eq", "rewriteCodePeephole_refines", "evalBinOp_u256_and_self",
    "evalBinOp_u256_or_self", "evalBinOp_u256_xor_zero", "evalBinOp_u256_or_zero",
    "storageStore_load_same_sound", "storageStore_load_ne_sound", "evalBinOp_const_fold_sound",
    "rewriteConstFoldStep_sound", "rewriteScalarVerified_sound", "uint64_mul_sixteen",
    "uint64_mul_thirtytwo", "uint64_two_mul", "uint64_four_mul", "uint64_eight_mul",
    "uint64_div_two", "uint64_div_four", "uint64_div_eight", "uint64_add_self_shl_one",
    "uint64_add_assoc_const", "uint64_and_mask_coalesce", "uint64_or_mask_coalesce",
    "uint64_xor_mask_coalesce", "uint64_mul_add_distrib_const", "evalScalarExpr_add_self_u64",
    "evalScalarExpr_add_assoc_const_u64", "evalScalarExpr_and_mask_coalesce_u64",
    "evalScalarExpr_or_mask_coalesce_u64", "evalScalarExpr_xor_mask_coalesce_u64",
    "evalScalarExpr_mul_add_distrib_const_u64", "uint64_shr_shl_mask_collapse",
    "evalScalarExpr_shr_shl_mask_collapse_u64", "evalScalarExpr_fma_fusion_u64",
    "uint64_rotl_comm_or", "unboxTupleProj_sound", "unboxTupleProj0_sound",
    "unboxTupleProj1_sound", "eval_unboxTupleSROA_refines", "unboxTupleLetChain_refines",
    "unboxTupleLetChain1_refines", "unboxTupleDeadElim_refines", "hoistExclusivity_sound",
    "eval_hoistExclusivity_refines", "hoistExclusivityPreheader_refines",
    "unboxedLoopStep_sound", "unboxedLoopAccumulator_sim", "normSymExpr_constU64",
    "normSymExpr_constBool", "normSymExpr_const_sound", "checkSingleSample_of_codeRefines",
    "checkConcreteSamples_of_codeRefines", "sound_of_checkSingleSample_eq_true",
    "symbolicTV_refl_sound"
  ]
  let sem := [
    "ScalarExprEquiv.refl", "ScalarExprEquiv.symm", "ScalarExprEquiv.trans",
    "ExprRefines.refl", "ExprRefines.trans", "ExprRefines.of_scalar_equiv",
    "ExprEquiv.refl", "ExprEquiv.symm", "ExprEquiv.trans", "ExprEquiv.toRefines",
    "CodeRefines.refl", "CodeRefines.trans", "CodeRefines.letBind_congr",
    "CodeRefines.rawStore_congr", "CodeRefines.incRef_congr", "CodeRefines.decRef_congr",
    "CodeRefines.ite_congr", "CodeRefines.parFor_congr",
    "StorageMapBuffer.lookupSlot_writeSlot_same", "StorageMapBuffer.lookupSlot_writeSlot_ne",
    "HeapState.storageLoad_after_storageStore_same", "HeapState.storageLoad_after_storageStore_ne"
  ]
  let spec := [
    "untrusted_opt_plugin_tv_gate_sound", "untrusted_opt_plugin_code_refines",
    "untrusted_opt_plugin_timeout_fallback", "untrusted_opt_plugin_reject_fallback",
    "opt_pipeline_two_step_refines", "opt_pipeline_chain_refines",
    "fastcheck_rejects_vacuous_precondition", "fastcheck_non_vacuous_tightness_law",
    "c_abi_box_zero_eq_one", "c_abi_unbox_box_zero", "c_abi_unbox_box_one",
    "pr_spec_pinning_blocks_spec_tampering", "pr_spec_pinning_blocks_test_tampering",
    "pr_spec_pinning_blocks_forbidden_axioms", "pr_spec_pinning_gate_sound",
    "meta_verified_contract_compose_sound", "meta_validator_rejects_semantic_mutants",
    "meta_limb256_mul_lo_homomorphism", "meta_unbox_tuple_full_elim_sound",
    "meta_double_shift_mask_and_fma_sound", "small_trip_prefers_cpu_simd",
    "matrix_contraction_prefers_tpu_mxu", "federated_node_effective_cost_monotone_in_queue",
    "composeAffineBudget_eval", "affine_step_budget_monotone",
    "bootstrap_shift_step_budget_sound", "empirical_high_water_refutes_loose_bound",
    "evalLoopStepBudget_monotone", "riscv_div_by_zero_spec", "zisk_csr_atomic_step_budget",
    "evalPassChainBudget_cons", "sptLookup_insert_same", "pass_chain_two_passes_eval",
    "spt_rom_fetch_deterministic"
  ]
  let gov := [
    "bayesian_effective_effort_pos", "bayesian_falsified_branch_score_zero",
    "bayesian_zero_impact_score_zero", "bayesian_effective_effort_monotone_in_tail",
    "bayesian_score_monotone_in_prob", "bayesian_posterior_bounded",
    "governor_accept_blocks_spec_tampering", "governor_accept_blocks_sorry_axioms",
    "governor_accept_blocks_vacuous_spec", "governor_accept_gate_sound",
    "governor_race_winner_cancels_siblings", "governor_budget_exceeded_never_continues",
    "governor_survival_stagnation_never_continues",
    "governor_continue_implies_within_budget_and_no_winner",
    "pruneArm_falsified_true", "decideWorkerActionC_sibling_won"
  ]
  let ir := ["bitAnd_self", "bitOr_self", "bitXor_zero", "zero_bitXor", "bitOr_zero", "zero_bitOr"]
  let fc := ["certifyCounterexample_no_false_positive", "substScalarExpr_nil",
    "substSingleConstraint_sound", "propagatePrecondition_letBind_sound"]
  (proofs.map ("LeanNative.Proofs." ++ ·)) ++
  (proofs.map ("LeanNative.Proofs.PeepholeProofs." ++ ·)) ++
  (proofs.map ("LeanNative.Proofs.LoopOptProofs." ++ ·)) ++
  (proofs.map ("LeanNative.Proofs.SymbolicTV." ++ ·)) ++
  (sem.map ("LeanNative.Semantics." ++ ·)) ++
  (spec.map ("LeanNative.Spec." ++ ·)) ++
  (gov.map ("LeanNative.ResearchGovernor." ++ ·)) ++
  (ir.map ("LeanNative.IR.UInt256." ++ ·)) ++
  (fc.map ("LeanNative.Backend.FastCheck." ++ ·))

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

private abbrev escapeJsonString := LeanNative.IR.jsonEscape

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
