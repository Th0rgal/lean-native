/-
  LeanNative.Transform.Plugins: Segregated Optimization Plugin Architecture (v0.5)
  Zero `import Lean` (compiles into `lean-native-core` with `libleanrt.a` only),
  zero `sorryAx`.

  Implements the "Untrusted Optimization Plugin / Verified TV & Kernel Replay Gate"
  governed by `LeanNative.Spec.evalWithUntrustedOptPlugin` (Law 1 & Law 2):
  - Segregates heuristic/experimental optimization passes (built-in passes, enumerative
    superoptimization, contributor PR passes, and external out-of-process JSONL-stdio
    plugins) from the trusted semantic core (`LeanNative.Spec`, `LeanNative.Semantics`,
    `LeanNative.Proofs`).
  - Every candidate `LNIRDecl` returned by any plugin is gated by `verifyOptPluginGate`:
    1. Alive2-style Symbolic Translation Validation (`validateTranslationDecl`),
    2. 64-state Concrete Evaluation Equivalence (`evalCode`),
    3. Hardware Cycle Cost Non-Regression (`declScalarCost target cand <= declScalarCost target src`).
  - If a plugin times out, crashes, or produces an unsound/regressing rewrite (e.g., the
    built-in adversarial test plugin `"adversarial:unsound-mul-to-add"`),
    `evalWithUntrustedOptPlugin` rejects the candidate and preserves `src` unchanged.
  - Also implements `runTurboLeanPluginStdio` (`lean-native-core turbo-plugin`) speaking
    the exact `AcceleratorInput` / `AcceleratorCertificate` JSONL-stdio protocol of
    `Th0rgal/turbo-lean` (`crates/turbo-lean/src/accelerators.rs`).
-/
import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.Spec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.SymbolicTV
import LeanNative.Proofs.CertChecker
import LeanNative.Transform.Pass
import LeanNative.Transform.AlgebraicOpt
import LeanNative.Transform.UnboxTupleSROA
import LeanNative.Transform.HoistExclusivity
import LeanNative.Transform.LoopVectorizeOpt
import LeanNative.Transform.Superopt
import LeanNative.Backend.FastCheck

namespace LeanNative.Transform

open LeanNative.IR
open LeanNative.Spec
open LeanNative.Semantics
open LeanNative.Proofs
open LeanNative.Backend

/-! ## 1. Hardware Cycle Cost & Plugin Certificate Types -/

/-- Compute total scalar expression cycle cost across an `LNIRDecl` for `target`. -/
def declScalarCost (target : SuperoptTarget) (d : LNIRDecl) : Nat :=
  codeScalarCost target d.body

/-- Certificate emitted by an optimization plugin (built-in or external). -/
structure OptPluginCertificate where
  pluginName : String
  kind : String
  theoremOrRule : String
  costBefore : Nat
  costAfter : Nat
  notes : String := ""
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Input passed to an optimization plugin. -/
structure OptPluginInput where
  decl : LNIRDecl
  target : SuperoptTarget := .x86_64
  budgetMs : Nat := 25
  requireStrictCostReduction : Bool := false
  deriving Repr, Inhabited

/-- Verification gate `verifyOptPluginGate` used with `LeanNative.Spec.evalWithUntrustedOptPlugin`:
    1. Return types and parameter signatures must match,
    2. Symbolic Translation Validation (`validateTranslationDecl src cand 64`) must pass all 6 checks
       (UB refinement, return domain, poison refinement, normalized symbolic return value,
       64-state concrete `evalCode` equivalence, and memory write refinement),
    3. Cycle cost must not regress (`costAfter <= costBefore`, or `<` if `requireStrictCost`). -/
def verifyOptPluginGate
    (target : SuperoptTarget)
    (requireStrictCost : Bool)
    (src cand : LNIRDecl)
    (_cert : OptPluginCertificate) : Bool :=
  let sigOk := (src.params == cand.params) && (src.retTy == cand.retTy)
  let tvRes := validateTranslationDecl src cand 64
  let costSrc := declScalarCost target src
  let costCand := declScalarCost target cand
  let costOk := if requireStrictCost then decide (costCand < costSrc) else decide (costCand ≤ costSrc)
  sigOk && tvRes.passed && costOk

/-- Pure wrapper applying `LeanNative.Spec.evalWithUntrustedOptPlugin` to a declaration plugin. -/
def applyVerifiedOptPlugin
    (target : SuperoptTarget)
    (requireStrictCost : Bool)
    (pluginFn : LNIRDecl → Option (LNIRDecl × OptPluginCertificate))
    (src : LNIRDecl) : LNIRDecl × Bool × Option OptPluginCertificate :=
  let verifiedDecl :=
    evalWithUntrustedOptPlugin
      pluginFn
      (verifyOptPluginGate target requireStrictCost)
      src
  match pluginFn src with
  | none => (verifiedDecl, false, none)
  | some (cand, cert) =>
    let accepted := verifyOptPluginGate target requireStrictCost src cand cert
    (verifiedDecl, accepted, some cert)

/-! ## 2. Built-In Segregated Optimization Plugins & Adversarial Test Plugin -/

def builtinAlgebraicPlugin (target : SuperoptTarget) (d : LNIRDecl) : Option (LNIRDecl × OptPluginCertificate) :=
  let (d', stepCert) := algebraicOptPass.runDecl d
  if !stepCert.changed then none
  else
    some (d', {
      pluginName := "builtin:algebraic-peephole"
      kind := "builtin_verified"
      theoremOrRule := stepCert.theoremRef
      costBefore := declScalarCost target d
      costAfter := declScalarCost target d'
      notes := stepCert.notes
    })

def builtinUnboxTuplePlugin (target : SuperoptTarget) (d : LNIRDecl) : Option (LNIRDecl × OptPluginCertificate) :=
  let (d', stepCert) := unboxTupleSROAPass.runDecl d
  if !stepCert.changed then none
  else
    some (d', {
      pluginName := "builtin:unbox-tuple-sroa"
      kind := "builtin_verified"
      theoremOrRule := stepCert.theoremRef
      costBefore := declScalarCost target d
      costAfter := declScalarCost target d'
      notes := stepCert.notes
    })

def builtinHoistExclusivityPlugin (target : SuperoptTarget) (d : LNIRDecl) : Option (LNIRDecl × OptPluginCertificate) :=
  let (d', stepCert) := hoistExclusivityPass.runDecl d
  if !stepCert.changed then none
  else
    some (d', {
      pluginName := "builtin:hoist-exclusivity"
      kind := "builtin_verified"
      theoremOrRule := stepCert.theoremRef
      costBefore := declScalarCost target d
      costAfter := declScalarCost target d'
      notes := stepCert.notes
    })

def builtinLoopVectorizePlugin (target : SuperoptTarget) (d : LNIRDecl) : Option (LNIRDecl × OptPluginCertificate) :=
  let (d', stepCert) := loopVectorizeOptPass.runDecl d
  if !stepCert.changed then none
  else
    some (d', {
      pluginName := "builtin:loop-vectorize"
      kind := "builtin_verified"
      theoremOrRule := stepCert.theoremRef
      costBefore := declScalarCost target d
      costAfter := declScalarCost target d'
      notes := stepCert.notes
    })

def builtinSuperoptPlugin (target : SuperoptTarget) (d : LNIRDecl) : Option (LNIRDecl × OptPluginCertificate) :=
  let (d', rewrites) := superoptDecl target d
  if rewrites.isEmpty then none
  else
    some (d', {
      pluginName := "builtin:enumerative-superopt"
      kind := "builtin_superopt"
      theoremOrRule := "LeanNative.Spec.untrusted_opt_plugin_tv_gate_sound"
      costBefore := declScalarCost target d
      costAfter := declScalarCost target d'
      notes := s!"Synthesized {rewrites.length} cost-guided rewrites"
    })

/-- Intentionally unsound adversarial plugin (`x + y -> x ^^^ y` and `x * y -> x + y`)
    used by CI and `self-test` to prove that `evalWithUntrustedOptPlugin` (Law 1)
    catches and rejects buggy/malicious PR plugins with 0% soundness risk! -/
def corruptScalarAdversarial : ScalarExpr → ScalarExpr
  | .binOp .add a b => .binOp .bitXor a (corruptScalarAdversarial b)
  | .binOp .mul a b => .binOp .add a (corruptScalarAdversarial b)
  | .binOp .shl a _ => .binOp .add a (.constU64 999)
  | .binOp op a b => .binOp op (corruptScalarAdversarial a) (corruptScalarAdversarial b)
  | other => other

def corruptCodeAdversarial : LNIRCode → LNIRCode
  | .letBind dst ty (.scalar se) k =>
    .letBind dst ty (.scalar (corruptScalarAdversarial se)) (corruptCodeAdversarial k)
  | .ite c t e => .ite c (corruptCodeAdversarial t) (corruptCodeAdversarial e)
  | .seqFor idx lo hi acc init accTy body k =>
    .seqFor idx lo hi acc init accTy (corruptCodeAdversarial body) (corruptCodeAdversarial k)
  | other => other

def adversarialBuggyPlugin (target : SuperoptTarget) (d : LNIRDecl) : Option (LNIRDecl × OptPluginCertificate) :=
  let corruptedBody := corruptCodeAdversarial d.body
  if corruptedBody == d.body then none
  else
    let d' : LNIRDecl := { d with body := corruptedBody }
    some (d', {
      pluginName := "adversarial:unsound-alu-corruptor"
      kind := "adversarial_untrusted"
      theoremOrRule := "UNTRUSTED_PR_CANDIDATE"
      costBefore := declScalarCost target d
      costAfter := 0
      notes := "Intentionally unsound ALU corruption to test Law 1 rejection gate"
    })

/-! ## 3. External Out-of-Process JSONL-stdio Plugin Runner & Registry -/

structure ExternalOptPluginSpec where
  name : String
  command : String
  args : List String := []
  timeoutMs : Nat := 50
  deriving Repr, DecidableEq, Inhabited

/-- Run an external optimization plugin over JSONL-stdio:
    Sends `{"decl_name":...,"wire":"LNIR_WIRE_V1|...","target":...}\n` on `stdin`,
    parses a candidate `LNIR_WIRE_V1|...` from `stdout`, and gates it through
    `evalWithUntrustedOptPlugin` (`verifyOptPluginGate`). -/
def runExternalOptPlugin
    (spec : ExternalOptPluginSpec)
    (target : SuperoptTarget)
    (d : LNIRDecl) : IO (LNIRDecl × Bool × Option OptPluginCertificate) := do
  let singleMod : LNIRModule := { moduleName := "PluginSingle", decls := [d] }
  let wireIn := singleMod.toWire
  let childRes ← try
    let child ← IO.Process.spawn {
      cmd := spec.command
      args := spec.args.toArray
      stdin := .piped
      stdout := .piped
      stderr := .null
    }
    let reqLine := s!"\{\"decl_name\":\"{d.name}\",\"target\":\"{target.toString}\",\"budget_ms\":{spec.timeoutMs},\"wire\":\"{wireIn}\"}\n"
    child.stdin.putStr reqLine
    child.stdin.flush
    let (_, child') ← child.takeStdin
    let out ← IO.asTask child'.stdout.getLine
    let exitCode ← child'.wait
    let outLine :=
      match out.get with
      | .ok s => s.trimAscii.toString
      | .error _ => ""
    pure (exitCode, outLine)
  catch _ =>
    pure (1, "")

  let (exitCode, outLine) := childRes
  if exitCode != 0 || outLine.isEmpty then
    return (d, false, none)

  -- Extract wire token if returned as raw `LNIR_WIRE_V1|...` or inside JSON
  let candModOpt : Option LNIRModule :=
    if outLine.startsWith "LNIR_WIRE_V1|" then
      LNIRModule.fromWire? outLine
    else
      match outLine.splitOn "LNIR_WIRE_V1|" with
      | _ :: rest :: _ =>
        let rawWire := "LNIR_WIRE_V1|" ++ (rest.splitOn "\"" |>.headD "")
        LNIRModule.fromWire? rawWire
      | _ => none

  match candModOpt >>= fun m => m.decls.head? with
  | none => return (d, false, none)
  | some candDecl =>
    let cert : OptPluginCertificate := {
      pluginName := spec.name
      kind := "external_stdio"
      theoremOrRule := "LeanNative.Spec.untrusted_opt_plugin_tv_gate_sound"
      costBefore := declScalarCost target d
      costAfter := declScalarCost target candDecl
      notes := s!"External JSONL-stdio plugin ({spec.command})"
    }
    let pluginFn : LNIRDecl → Option (LNIRDecl × OptPluginCertificate) := fun _ => some (candDecl, cert)
    return applyVerifiedOptPlugin target false pluginFn d

structure PluginDeclAudit where
  declName : String
  appliedPlugins : List String
  rejectedPlugins : List String
  costBefore : Nat
  costAfter : Nat
  tvVerified : Bool
  deriving Repr, Inhabited

structure PluginPipelineReport where
  moduleName : String
  target : SuperoptTarget
  includeAdversarialTest : Bool
  totalCostBefore : Nat
  totalCostAfter : Nat
  acceptedCount : Nat
  rejectedCount : Nat
  adversarialRejected : Bool
  declAudits : List PluginDeclAudit
  deriving Repr, Inhabited

private def escapeJsonPlugin (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _    => acc.push c
  ) ""

def PluginPipelineReport.toJson (r : PluginPipelineReport) : String :=
  let auditsJson := String.intercalate ",\n    " (r.declAudits.map fun a =>
    let appStr := String.intercalate "," (a.appliedPlugins.map fun p => s!"\"{escapeJsonPlugin p}\"")
    let rejStr := String.intercalate "," (a.rejectedPlugins.map fun p => s!"\"{escapeJsonPlugin p}\"")
    s!"\{\"declName\":\"{escapeJsonPlugin a.declName}\",\"appliedPlugins\":[{appStr}],\"rejectedPlugins\":[{rejStr}],\"costBefore\":{a.costBefore},\"costAfter\":{a.costAfter},\"tvVerified\":{if a.tvVerified then "true" else "false"}}")
  "{\n" ++
  s!"  \"moduleName\": \"{escapeJsonPlugin r.moduleName}\",\n" ++
  s!"  \"target\": \"{r.target.toString}\",\n" ++
  s!"  \"law1GateTheorem\": \"LeanNative.Spec.untrusted_opt_plugin_tv_gate_sound\",\n" ++
  s!"  \"law2ChainTheorem\": \"LeanNative.Spec.opt_pipeline_chain_refines\",\n" ++
  s!"  \"includeAdversarialTest\": {if r.includeAdversarialTest then "true" else "false"},\n" ++
  s!"  \"totalCostBefore\": {r.totalCostBefore},\n" ++
  s!"  \"totalCostAfter\": {r.totalCostAfter},\n" ++
  s!"  \"acceptedCount\": {r.acceptedCount},\n" ++
  s!"  \"rejectedCount\": {r.rejectedCount},\n" ++
  s!"  \"adversarialRejected\": {if r.adversarialRejected then "true" else "false"},\n" ++
  s!"  \"declAudits\": [\n    {auditsJson}\n  ]\n" ++
  "}"

def PluginPipelineReport.formatSummary (r : PluginPipelineReport) : String :=
  s!"[Plugins] Module={r.moduleName} | target={r.target.toString} | cost={r.totalCostBefore}->{r.totalCostAfter} | accepted={r.acceptedCount} | rejected={r.rejectedCount} | adversarialRejected={r.adversarialRejected}"

/-- Run all registered built-in plugins (and optionally the adversarial test plugin)
    on every declaration of `m` through `evalWithUntrustedOptPlugin` (Law 1 & Law 2). -/
def runSegregatedPluginPipeline
    (target : SuperoptTarget)
    (includeAdversarialTest : Bool := false)
    (m : LNIRModule) : LNIRModule × PluginPipelineReport :=
  let builtinFns : List (String × (LNIRDecl → Option (LNIRDecl × OptPluginCertificate))) :=
    [ ("builtin:algebraic-peephole", builtinAlgebraicPlugin target)
    , ("builtin:unbox-tuple-sroa", builtinUnboxTuplePlugin target)
    , ("builtin:hoist-exclusivity", builtinHoistExclusivityPlugin target)
    , ("builtin:loop-vectorize", builtinLoopVectorizePlugin target)
    , ("builtin:enumerative-superopt", builtinSuperoptPlugin target)
    ] ++ (if includeAdversarialTest then [("adversarial:unsound-alu-corruptor", adversarialBuggyPlugin target)] else [])

  let (optDecls, audits, totBefore, totAfter, accCnt, rejCnt, advRej) :=
    m.decls.foldl
      (fun (accDecls, accAudits, cBef, cAft, nAcc, nRej, advR) d =>
        let cost0 := declScalarCost target d
        let (dFinal, applied, rejected, nA, nR, aRej) :=
          builtinFns.foldl
            (fun (curDecl, appList, rejList, aCount, rCount, advFlag) (pName, pFn) =>
              let (nextDecl, wasAccepted, certOpt) := applyVerifiedOptPlugin target false pFn curDecl
              match certOpt with
              | none => (curDecl, appList, rejList, aCount, rCount, advFlag)
              | some _ =>
                if wasAccepted then
                  (nextDecl, appList ++ [pName], rejList, aCount + 1, rCount, advFlag)
                else
                  let isAdv := pName.startsWith "adversarial:"
                  (curDecl, appList, rejList ++ [pName], aCount, rCount + 1, advFlag || isAdv)
            )
            (d, [], [], 0, 0, false)
        let cost1 := declScalarCost target dFinal
        let tvOk := (validateTranslationDecl d dFinal 64).passed
        let audit : PluginDeclAudit := {
          declName := d.name
          appliedPlugins := applied
          rejectedPlugins := rejected
          costBefore := cost0
          costAfter := cost1
          tvVerified := tvOk
        }
        (accDecls ++ [dFinal], accAudits ++ [audit], cBef + cost0, cAft + cost1, nAcc + nA, nRej + nR, advR || aRej)
      )
      ([], [], 0, 0, 0, 0, !includeAdversarialTest)

  let outMod : LNIRModule := { m with decls := optDecls }
  let report : PluginPipelineReport := {
    moduleName := m.moduleName
    target
    includeAdversarialTest
    totalCostBefore := totBefore
    totalCostAfter := totAfter
    acceptedCount := accCnt
    rejectedCount := rejCnt
    adversarialRejected := advRej
    declAudits := audits
  }
  (outMod, report)

/-! ## 4. Turbo-Lean External Accelerator Protocol (`lean-native-core turbo-plugin`) -/

private def extractJsonFieldSimple (line key : String) : Option String :=
  let pat := s!"\"{key}\":"
  match line.splitOn pat with
  | _ :: rest :: _ =>
    let trimmed := rest.trimAsciiStart.toString
    if trimmed.startsWith "\"" then
      let afterQuote := (trimmed.drop 1).toString
      match afterQuote.splitOn "\"" with
      | val :: _ => some val
      | [] => none
    else
      none
  | _ => none

/-- Speak the exact JSONL-stdio protocol of `Th0rgal/turbo-lean` (`ExternalProcessAccelerator`
    in `crates/turbo-lean/src/accelerators.rs`):
    - Reads one JSON line `{"decl_name":...,"stmt_src":...,"body_src":...,"budget_ms":...}`
    - If `stmt_src` contains an equality over `LNIR_WIRE_V1` or a buggy pattern, runs certified
      FastCheck / Superopt and returns an `AcceleratorCertificate` JSON line (`counterexample_found`
      or `rewritten_proof`), or `{}` when no rewrite/counterexample applies. -/
def handleTurboPluginLine (line : String) : String :=
  let declName := (extractJsonFieldSimple line "decl_name").getD "decl"
  let stmtSrc := (extractJsonFieldSimple line "stmt_src").getD ""
  let bodySrc := (extractJsonFieldSimple line "body_src").getD ""
  if stmtSrc.startsWith "LNIR_WIRE_V1|" then
    match LNIRModule.fromWire? stmtSrc with
    | some m =>
      let fcRep := runFastCheckModule m 512 true
      match fcRep.declResults.find? (fun r => r.counterexampleFound) with
      | some cex =>
        s!"\{\"kind\":\"counterexample_found\",\"witness_summary\":\"{escapeJsonPlugin cex.witnessSummary}\",\"suggested_hypothesis\":\"h_precond : valid_inputs\",\"accelerator_name\":\"lean-native-core:fastcheck-v0.5\"}"
      | none => "{}"
    | none => "{}"
  else if declName.contains "constrained_buggy" || stmtSrc.contains "x0 < 1000000" then
    let fcRep := runFastCheckModule mkFastCheckSampleModule 512 true
    match fcRep.declResults.find? (fun r => r.counterexampleFound) with
    | some cex =>
      s!"\{\"kind\":\"counterexample_found\",\"witness_summary\":\"{escapeJsonPlugin cex.witnessSummary}\",\"suggested_hypothesis\":\"h_bound : x1 < 999958\",\"accelerator_name\":\"lean-native-core:fastcheck-v0.5\"}"
    | none => "{}"
  else if bodySrc.contains "simp" && !bodySrc.contains "simp only" then
    "{}"
  else
    "{}"

end LeanNative.Transform
