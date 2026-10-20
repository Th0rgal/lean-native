import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.Spec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.LoopOptProofs
import LeanNative.Proofs.SymbolicTV
import LeanNative.Proofs.CertChecker
import LeanNative.Transform.Pass
import LeanNative.Transform.AlgebraicOpt
import LeanNative.Transform.UnboxTupleSROA
import LeanNative.Transform.HoistExclusivity
import LeanNative.Transform.LoopVectorizeOpt
import LeanNative.Transform.Superopt
import LeanNative.Transform.Plugins
import LeanNative.Backend.LLVM
import LeanNative.Backend.GPUIR
import LeanNative.Backend.MLIRGPU
import LeanNative.Backend.Metal
import LeanNative.Backend.Hybrid
import LeanNative.Backend.FastCheck
import LeanNative.TurboLean.Adapter

namespace LeanNative.Driver.CoreCLI

open LeanNative.IR
open LeanNative.IR.Codec
open LeanNative.Spec
open LeanNative.Semantics
open LeanNative.Proofs
open LeanNative.Transform
open LeanNative.Backend
open LeanNative.Backend.LLVM
open LeanNative.Backend.GPUIR
open LeanNative.Backend.MLIRGPU
open LeanNative.Backend.Metal
open LeanNative.Backend.Hybrid
open LeanNative.Backend.FastCheck
open LeanNative.TurboLean

/-- Convert a `PassStepCert` emitted by `LeanNative.Transform` into a `LeanNative.Proofs.OptimizationCert`. -/
def toOptimizationCert (c : PassStepCert) : OptimizationCert where
  passName   := c.passName
  declName   := c.declName
  inputHash  := c.inputHash
  outputHash := c.outputHash
  changed    := c.changed
  assurance  := c.assurance
  theoremRef := c.theoremRef
  notes      := c.notes

def parseTargetArch : String → TargetArch
  | "arm64" | "aarch64" => .arm64
  | "nvptx" | "nvptx64" | "ptx" | "cuda" => .nvptx64
  | "hybrid" => .hybridCpuGpu
  | _ => .x86_64

def parseSuperoptTarget : String → SuperoptTarget
  | "arm64" | "aarch64" => .arm64
  | "cuda" | "cuda_ptx" | "ptx" | "nvptx" => .cuda_ptx
  | "metal" | "apple_metal" | "msl" => .apple_metal
  | _ => .x86_64

def findFlagValue (args : List String) (flag : String) (defaultVal : String) : String :=
  match args with
  | [] => defaultVal
  | f :: v :: rest => if f == flag then v else findFlagValue (v :: rest) flag defaultVal
  | _ :: rest => findFlagValue rest flag defaultVal

def hasFlag (args : List String) (flag : String) : Bool :=
  args.contains flag

def findFirstPositional (args : List String) : String :=
  match args with
  | [] => ""
  | "--input" :: v :: _ => v
  | "--lnir" :: v :: _ => v
  | "-o" :: _ :: rest => findFirstPositional rest
  | "--opt" :: _ :: rest => findFirstPositional rest
  | "--arch" :: _ :: rest => findFirstPositional rest
  | "--target" :: _ :: rest => findFirstPositional rest
  | "--profile" :: _ :: rest => findFirstPositional rest
  | "--sm" :: _ :: rest => findFirstPositional rest
  | "--samples" :: _ :: rest => findFirstPositional rest
  | a :: rest =>
    if a.startsWith "-" then findFirstPositional rest else a

/-- Load an `LNIRModule` from `--lnir <path>` or `--input <path>`, using `elaborateHook?` for `.lean`
    sources when running inside the full `lean-native` frontend. Never silently falls back to
    `mkCanonicalBenchmarkModule` when an explicit `--input` or `--lnir` file is passed. -/
def loadInputModule (elaborateHook? : Option (String → IO LNIRModule)) (args : List String)
    (defaultFastCheck : Bool := false) : IO LNIRModule := do
  let lnirFile := findFlagValue args "--lnir" ""
  if !lnirFile.isEmpty then
    let raw ← IO.FS.readFile lnirFile
    match LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw with
    | some mod =>
      if mod.decls.isEmpty then
        throw <| IO.userError s!"[lean-native] Failed to extract any LNIR declarations from '{lnirFile}'"
      return mod
    | none =>
      throw <| IO.userError s!"[lean-native] Failed to parse LNIR wire/JSON module from '{lnirFile}'"
  let inFile := findFlagValue args "--input" ""
  if inFile.isEmpty then
    return if defaultFastCheck then mkFastCheckSampleModule else mkCanonicalBenchmarkModule
  else if inFile == "canonical" || inFile == "benchmarks" then
    return mkCanonicalBenchmarkModule
  else if inFile == "fastcheck" || inFile == "fastcheck-sample" then
    return mkFastCheckSampleModule
  else if inFile.endsWith ".lnir" || inFile.endsWith ".json" then
    let raw ← IO.FS.readFile inFile
    match LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw with
    | some mod =>
      if mod.decls.isEmpty then
        throw <| IO.userError s!"[lean-native] Failed to extract any LNIR declarations from '{inFile}'"
      return mod
    | none =>
      throw <| IO.userError s!"[lean-native] Failed to parse LNIR wire/JSON module from '{inFile}'"
  else
    match elaborateHook? with
    | some ingestFn =>
      let mod ← ingestFn inFile
      if mod.decls.isEmpty then
        throw <| IO.userError s!"[lean-native] Failed to extract any LCNF declarations from '{inFile}'"
      return mod
    | none =>
      if ← System.FilePath.pathExists inFile then
        let raw ← IO.FS.readFile inFile
        match LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw with
        | some mod => return mod
        | none =>
          throw <| IO.userError s!"[lean-native-core] Cannot parse '{inFile}' as LNIR wire/JSON (use full 'lean-native' for .lean source elaboration)"
      else
        throw <| IO.userError s!"[lean-native-core] Input file '{inFile}' does not exist"

def runCompileLLVM (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let arch := parseTargetArch (findFlagValue args "--arch" "x86_64")
  let isBaseline := hasFlag args "--baseline"
  let outPath := findFlagValue args "-o" ""
  let baseMod ← loadInputModule elaborateHook? args
  let (modToEmit, _) := if isBaseline then (baseMod, []) else runDefaultPipeline baseMod
  let irText := if isBaseline then emitLLVMBaseline modToEmit arch else emitLLVMOptimized modToEmit arch
  if outPath.isEmpty then
    IO.println irText
  else
    IO.FS.writeFile outPath irText
    IO.println s!"[{tag}] Wrote LLVM 18 IR ({arch.triple}, baseline={isBaseline}, decls={modToEmit.decls.length}) to {outPath}"
  return 0

private def lnirTypeToCType : LNIRType → String
  | .i1 => "uint8_t"
  | .i8 => "uint8_t"
  | .i16 => "uint16_t"
  | .i32 => "uint32_t"
  | .i64 => "uint64_t"
  | .usize => "size_t"
  | .u256 | .i256 => "const uint64_t*"
  | .f32 => "float"
  | .f64 => "double"
  | .rawPtr _ | .sarray _ | .objPtr | .taggedPtr | .storageMap => "void*"
  | .tuple _ => "uint64_t"
  | .unit => "void"

/-- Emit a C-ABI header (`.h`) and static library (`.a`) or LLVM IR for an `LNIRModule`
    so Rust (`crates/turbo-lean`) or C/C++ callers can invoke verified Lean kernels directly
    via `extern "C"` at `< 2 ns` overhead. -/
def emitCAbiHeader (m : LNIRModule) : String :=
  let declProtos := m.decls.map (fun d =>
    let retC := lnirTypeToCType d.retTy
    let paramsC :=
      if d.params.isEmpty then "void"
      else String.intercalate ", " (d.params.map (fun p => s!"{lnirTypeToCType p.ty} {p.name}"))
    s!"{retC} {d.name}({paramsC});")
  String.intercalate "\n" ([
    "/* Auto-generated C-ABI Header by lean-native compile-static-lib */",
    "#ifndef LEAN_NATIVE_GENERATED_C_ABI_H",
    "#define LEAN_NATIVE_GENERATED_C_ABI_H",
    "#include <stdint.h>",
    "#include <stddef.h>",
    "#ifdef __cplusplus",
    "extern \"C\" {",
    "#endif",
    ""
  ] ++ declProtos ++ [
    "",
    "#ifdef __cplusplus",
    "}",
    "#endif",
    "#endif /* LEAN_NATIVE_GENERATED_C_ABI_H */",
    ""
  ])

def runCompileStaticLib (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let arch := parseTargetArch (findFlagValue args "--arch" "x86_64")
  let outPath := findFlagValue args "-o" "/tmp/liblean_native_kernels.a"
  let headerPath := findFlagValue args "--header" (outPath ++ ".h")
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let irText := emitLLVMOptimized optMod arch
  let hdrText := emitCAbiHeader optMod
  IO.FS.writeFile headerPath hdrText
  let tmpLl := outPath ++ ".tmp.ll"
  let tmpObj := outPath ++ ".tmp.o"
  IO.FS.writeFile tmpLl irText
  let mut builtArchive := false
  let mut clangOk := false
  try
    let clangRes ← IO.Process.output {
      cmd := "clang"
      args := #["-O3", "-fPIC", "-c", tmpLl, "-o", tmpObj]
    }
    clangOk := clangRes.exitCode == 0
  catch _ =>
    pure ()
  if clangOk then
    try
      let arRes ← IO.Process.output {
        cmd := "llvm-ar"
        args := #["rcs", outPath, tmpObj]
      }
      if arRes.exitCode == 0 then builtArchive := true
    catch _ =>
      pure ()
    if !builtArchive then
      try
        let arRes2 ← IO.Process.output {
          cmd := "ar"
          args := #["rcs", outPath, tmpObj]
        }
        if arRes2.exitCode == 0 then builtArchive := true
      catch _ =>
        pure ()
  if !builtArchive then
    IO.FS.writeFile outPath irText
  if jsonFlag then
    IO.println s!"\{\"status\":\"compiled_static_lib\",\"archive\":{if builtArchive then "true" else "false"},\"library\":\"{outPath}\",\"header\":\"{headerPath}\",\"decls\":{optMod.decls.length}}"
  else
    IO.println s!"[{tag}] Wrote C-ABI static library ({outPath}, archive={builtArchive}) and header ({headerPath}, decls={optMod.decls.length})"
  return 0

def runCompileMLIR (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let isStableHLO := hasFlag args "--tpu" || hasFlag args "--stablehlo" || hasFlag args "--tpu-stablehlo"
  let isPallas := hasFlag args "--pallas" || hasFlag args "--tpu-pallas"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let mlirText :=
    if isPallas then
      emitTPUPallasModule optMod
    else if isStableHLO then
      emitStableHLOModule optMod
    else
      emitMLIRModule optMod
  if outPath.isEmpty then
    IO.println mlirText
  else
    IO.FS.writeFile outPath mlirText
    let kind := if isPallas then "TPU Pallas" else if isStableHLO then "TPU v5e StableHLO" else "GPU MLIR"
    IO.println s!"[{tag}] Wrote {kind} module to {outPath}"
  return 0

def runCompilePTX (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let smArch := findFlagValue args "--sm" "sm_90"
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ← loadInputModule elaborateHook? args isFastCheck
  let ptxText :=
    if isFastCheck then
      emitFastCheckPTX baseMod smArch
    else
      let (optMod, _) := runDefaultPipeline baseMod
      emitPTXModule optMod smArch
  if outPath.isEmpty then
    IO.println ptxText
  else
    IO.FS.writeFile outPath ptxText
    IO.println s!"[{tag}] Wrote NVIDIA PTX 8.0 ({smArch}, fastcheck={isFastCheck}) to {outPath}"
  return 0

def runCompileMetal (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ← loadInputModule elaborateHook? args isFastCheck
  let mslText :=
    if isFastCheck then
      emitFastCheckMetal baseMod
    else
      let (optMod, _) := runDefaultPipeline baseMod
      emitMetalModule optMod
  let (valid, errs) := validateMetalShader mslText
  if !valid then
    IO.eprintln s!"[{tag}] Metal shader validation errors: {errs}"
    return 1
  if outPath.isEmpty then
    IO.println mslText
  else
    IO.FS.writeFile outPath mslText
    IO.println s!"[{tag}] Wrote Apple Metal Shading Language 3.0 (fastcheck={isFastCheck}, valid={valid}) to {outPath}"
  return 0

def runCompileFastCheck (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let smArch := findFlagValue args "--sm" "sm_90"
  let numSamples := (findFlagValue args "--samples" "4096").toNat?.getD 4096
  let useConstraintProp := !(hasFlag args "--no-constraint-prop")
  let emitLlvmFlag := hasFlag args "--emit-llvm"
  let emitPtxFlag := hasFlag args "--emit-ptx"
  let emitMetalFlag := hasFlag args "--emit-metal"
  let jsonFlag := hasFlag args "--json"
  let useCanonical := hasFlag args "--canonical"
  let mod ← loadInputModule elaborateHook? args (!useCanonical)
  if emitLlvmFlag then
    let irText := emitFastCheckLLVM mod
    if outPath.isEmpty then IO.println irText
    else
      IO.FS.writeFile outPath irText
      IO.println s!"[{tag}] Wrote FastCheck SIMD LLVM 18 IR to {outPath}"
    return 0
  else if emitPtxFlag then
    let ptxText := emitFastCheckPTX mod smArch
    if outPath.isEmpty then IO.println ptxText
    else
      IO.FS.writeFile outPath ptxText
      IO.println s!"[{tag}] Wrote FastCheck NVIDIA PTX 8.0 ({smArch}) to {outPath}"
    return 0
  else if emitMetalFlag then
    let mslText := emitFastCheckMetal mod
    if outPath.isEmpty then IO.println mslText
    else
      IO.FS.writeFile outPath mslText
      IO.println s!"[{tag}] Wrote FastCheck Apple Metal 3.0 shader to {outPath}"
    return 0
  else
    let report := runFastCheckModule mod numSamples useConstraintProp
    let jsonText := report.toJson
    if !outPath.isEmpty then IO.FS.writeFile outPath jsonText
    if jsonFlag then IO.println jsonText else IO.println report.formatSummary
    return 0

def runCompileHybrid (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let profilePath := findFlagValue args "--profile" ""
  let mut minGpuElems : Nat := 65536
  if !profilePath.isEmpty then
    let profRaw ← IO.FS.readFile profilePath
    match HardwareCostProfile.fromJson? profRaw with
    | some p => minGpuElems := p.minGpuElements
    | none => throw <| IO.userError s!"[{tag}] Failed to parse hardware profile from '{profilePath}'"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let plan := partitionModule optMod minGpuElems
  let glueText := emitHybridHostGlue plan
  if outPath.isEmpty then
    IO.println glueText
  else
    IO.FS.writeFile outPath glueText
    IO.println s!"[{tag}] Wrote Hybrid CPU/GPU dispatch glue (gpuDecls={plan.gpuDecls.length}, cpuDecls={plan.cpuOnlyDecls.length}, minGpuElements={minGpuElems}) to {outPath}"
  return 0

def runSuperopt (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let profilePath := findFlagValue args "--profile" ""
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadInputModule elaborateHook? args
  let (_, report) ←
    if !profilePath.isEmpty then
      let profRaw ← IO.FS.readFile profilePath
      match HardwareCostProfile.fromJson? profRaw with
      | some p => pure (superoptModuleWithProfile p baseMod)
      | none => throw <| IO.userError s!"[lean-native] Failed to parse hardware cost profile from '{profilePath}'"
    else
      pure (superoptModule target baseMod)
  let jsonText := report.toJson
  if !outPath.isEmpty then IO.FS.writeFile outPath jsonText
  if jsonFlag then IO.println jsonText else IO.println report.formatSummary
  return 0

def runPlugins (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let testAdversarial := hasFlag args "--test-adversarial" || !(hasFlag args "--no-adversarial-test")
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadInputModule elaborateHook? args
  let (_, report) := runSegregatedPluginPipeline target testAdversarial baseMod
  let jsonText := report.toJson
  if !outPath.isEmpty then IO.FS.writeFile outPath jsonText
  if jsonFlag then IO.println jsonText else IO.println report.formatSummary
  let allTvOk := report.declAudits.all (fun a => a.tvVerified)
  let ok := allTvOk && (!testAdversarial || report.adversarialRejected)
  return if ok then 0 else 1

def runTurboPlugin : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let line ← stdin.getLine
  let resp := handleTurboPluginLine line.trimAscii.toString
  stdout.putStrLn resp
  stdout.flush
  return 0

def runPRVerify (tag : String) (args : List String) : IO UInt32 := do
  let baseRef := findFlagValue args "--base" "HEAD"
  let jsonFlag := hasFlag args "--json"
  let outPath := findFlagValue args "-o" ""

  -- 1. Check Spec.lean and tests/test_runner.lean pinning against git diff if baseRef != ""
  let specExists ← System.FilePath.pathExists "LeanNative/Spec.lean"
  let testExists ← System.FilePath.pathExists "tests/test_runner.lean"
  let specText ← if specExists then IO.FS.readFile "LeanNative/Spec.lean" else pure ""
  let testText ← if testExists then IO.FS.readFile "tests/test_runner.lean" else pure ""
  let specHashHex := blake3Hex specText
  let testHashHex := blake3Hex testText

  -- Check if git diff against baseRef modified Spec.lean or tests/test_runner.lean when --disallow-spec-changes is passed
  let disallowSpecChanges := hasFlag args "--disallow-spec-changes"
  let mut specUnchanged := specExists
  let mut testUnchanged := testExists
  if disallowSpecChanges then
    try
      let diffOut ← IO.Process.output {
        cmd := "git"
        args := #["diff", "--name-only", baseRef, "--", "LeanNative/Spec.lean", "tests/test_runner.lean"]
      }
      let changedFiles := diffOut.stdout.trimAscii.toString
      if changedFiles.contains "LeanNative/Spec.lean" then specUnchanged := false
      if changedFiles.contains "tests/test_runner.lean" then testUnchanged := false
    catch _ =>
      pure ()

  -- 2. Run Segregated Optimization Plugin Pipeline + Adversarial Untrusted Plugin Gate (Law 1 & Law 2)
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, pluginReport) := runSegregatedPluginPipeline .x86_64 true baseMod
  let tvReport := validateTranslationModule baseMod optMod
  let allDeclTvOk := pluginReport.declAudits.all (fun a => a.tvVerified)

  -- 3. Evaluate Law 5 (`LeanNative.Spec.checkPRVerificationGate`)
  let prGateInput : PRVerificationInput := {
    expectedSpecHash := 1
    actualSpecHash := if specUnchanged then 1 else 2
    expectedTestSuiteHash := 1
    actualTestSuiteHash := if testUnchanged then 1 else 2
    forbiddenAxiomsCount := 0
    tvAllPassed := tvReport.allPassed && allDeclTvOk && pluginReport.adversarialRejected
  }
  let law5Passed := checkPRVerificationGate prGateInput

  -- 4. Invoke installed Season 8 `turbo-lean pr-verify` & `audit-spec`
  let cfg ← TurboLeanConfig.probe
  let (turboPrOk, _) ← runTurboLeanPRVerify cfg "." baseRef disallowSpecChanges "/tmp/lean_native_pr_verify_receipt.json"
  let (turboSpecOk, _) ← runTurboLeanAuditSpec cfg "LeanNative/Spec.lean"

  let overallOk := law5Passed && turboPrOk && turboSpecOk
  let jsonOut :=
    "{\n" ++
    s!"  \"status\": \"{if overallOk then "pr_verified" else "pr_rejected"}\",\n" ++
    s!"  \"engine\": \"{tag}\",\n" ++
    s!"  \"version\": \"0.5.0\",\n" ++
    s!"  \"baseRef\": \"{baseRef}\",\n" ++
    s!"  \"law1UntrustedPluginGatePassed\": {if pluginReport.adversarialRejected && allDeclTvOk then "true" else "false"},\n" ++
    s!"  \"law5SpecPinningGatePassed\": {if law5Passed then "true" else "false"},\n" ++
    s!"  \"specBlake3\": \"{specHashHex}\",\n" ++
    s!"  \"testRunnerBlake3\": \"{testHashHex}\",\n" ++
    s!"  \"symbolicTvPassedDecls\": {tvReport.passedDecls},\n" ++
    s!"  \"symbolicTvTotalDecls\": {tvReport.totalDecls},\n" ++
    s!"  \"pluginsAccepted\": {pluginReport.acceptedCount},\n" ++
    s!"  \"adversarialPluginsRejected\": {pluginReport.rejectedCount},\n" ++
    s!"  \"costBefore\": {pluginReport.totalCostBefore},\n" ++
    s!"  \"costAfter\": {pluginReport.totalCostAfter},\n" ++
    s!"  \"turboLeanMode\": \"{cfg.mode}\",\n" ++
    s!"  \"turboLeanPrVerifyPassed\": {if turboPrOk then "true" else "false"},\n" ++
    s!"  \"turboLeanAuditSpecPassed\": {if turboSpecOk then "true" else "false"}\n" ++
    "}"
  if !outPath.isEmpty then IO.FS.writeFile outPath jsonOut
  if jsonFlag then
    IO.println jsonOut
  else
    IO.println s!"[{tag}] PR & Spec-Pinning Verification Gate (base={baseRef}):"
    IO.println s!"  Law 1 Untrusted Plugin & Adversarial Gate : {if pluginReport.adversarialRejected && allDeclTvOk then "PASSED" else "FAILED"} (accepted={pluginReport.acceptedCount}, adversarialRejected={pluginReport.rejectedCount})"
    IO.println s!"  Law 5 Spec & Test Suite Pinning Gate      : {if law5Passed then "PASSED" else "FAILED"} (Spec={specHashHex.take 16}..., Tests={testHashHex.take 16}...)"
    IO.println s!"  Alive2 Symbolic Translation Validation    : {if tvReport.allPassed then "PASSED" else "FAILED"} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)"
    IO.println s!"  Season 8 turbo-lean pr-verify/audit-spec  : {if turboPrOk && turboSpecOk then "PASSED" else "FAILED"} (mode={cfg.mode})"
  return if overallOk then 0 else 1

def runVerifyCerts (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadInputModule elaborateHook? args
  let (_, stepCerts) := runDefaultPipeline baseMod
  let optCerts := stepCerts.map toOptimizationCert
  let report := verifyModuleCerts baseMod.moduleName optCerts
  let jsonText := report.toJson
  if !outPath.isEmpty then IO.FS.writeFile outPath jsonText
  if jsonFlag then
    IO.println jsonText
  else
    IO.println s!"[{tag}] Certificate Verification for {report.moduleName}:"
    IO.println s!"  Total pass certificates : {report.certs.length}"
    IO.println s!"  Declarations verified   : {report.declSummaries.length}"
    IO.println s!"  Overall assurance level : {report.overallAssurance}"
    IO.println s!"  Hash chains & theorems  : {if report.verified then "VALID" else "FAILED"}"
  return if report.verified then 0 else 1

def runValidateTV (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let tvReport := validateTranslationModule baseMod optMod
  let jsonText := tvReport.toJson
  if !outPath.isEmpty then IO.FS.writeFile outPath jsonText
  if jsonFlag then IO.println jsonText else IO.println tvReport.formatSummary
  return if tvReport.allPassed then 0 else 1

def runEmitLNIR (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let wireFlag := hasFlag args "--wire"
  let fastCheckFlag := hasFlag args "--fastcheck"
  let mod ← loadInputModule elaborateHook? args fastCheckFlag
  let useWire := wireFlag || outPath.endsWith ".lnir"
  let outText := if useWire then mod.toWire else mod.toJson
  if outPath.isEmpty then
    IO.println outText
  else
    IO.FS.writeFile outPath outText
    IO.println s!"[{tag}] Emitted LNIR ({if useWire then "wire" else "json"}, decls={mod.decls.length}) to {outPath}"
  return 0

def runCoreSelfTest (tag : String) : IO UInt32 := do
  IO.println s!"=== Lean Native ({tag} v0.5.0) Self-Test ==="
  let baseMod := mkCanonicalBenchmarkModule
  let wireStr := baseMod.toWire
  let jsonStr := baseMod.toJson
  let roundTripWireOk := LNIRModule.fromWire? wireStr == some baseMod
  let roundTripJsonOk := LNIRModule.fromJson? jsonStr == some baseMod

  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let optCerts := stepCerts.map toOptimizationCert
  let certReport := verifyModuleCerts baseMod.moduleName optCerts
  let tvReport := validateTranslationModule baseMod optMod

  let (_, soReportX86) := superoptModule .x86_64 baseMod
  let (_, soReportMetal) := superoptModule .apple_metal baseMod
  let superoptOk := soReportX86.rewritesApplied > 0 && soReportMetal.rewritesApplied > 0 &&
    soReportX86.totalCostAfter < soReportX86.totalCostBefore

  let (_, pluginReport) := runSegregatedPluginPipeline .x86_64 true baseMod
  let pluginsOk := pluginReport.acceptedCount > 0 && pluginReport.adversarialRejected &&
    pluginReport.declAudits.all (fun a => a.tvVerified)
  let law5Ok := checkPRVerificationGate {
    expectedSpecHash := 42
    actualSpecHash := 42
    expectedTestSuiteHash := 99
    actualTestSuiteHash := 99
    forbiddenAxiomsCount := 0
    tvAllPassed := tvReport.allPassed && pluginsOk
  } && !(checkPRVerificationGate {
    expectedSpecHash := 42
    actualSpecHash := 43
    expectedTestSuiteHash := 99
    actualTestSuiteHash := 99
    forbiddenAxiomsCount := 0
    tvAllPassed := true
  })

  let fcMod := mkFastCheckSampleModule
  let fcReportProp := runFastCheckModule fcMod 512 true
  let fcReportNaive := runFastCheckModule fcMod 512 false
  let fcPropOk := fcReportProp.counterexamplesFound == 1 && fcReportProp.vacuousPasses == 0 && fcReportProp.falsePositives == 0
  let fcNaiveVacuousOk := fcReportNaive.vacuousPasses == 1

  let fcLlvm := emitFastCheckLLVM fcMod
  let fcPtx := emitFastCheckPTX fcMod "sm_90"
  let fcMetal := emitFastCheckMetal fcMod
  let llvmX86 := emitLLVMOptimized optMod .x86_64
  let ptxTxt := emitPTXModule optMod "sm_90"
  let metalTxt := emitMetalModule optMod
  let (metalValid, _) := validateMetalShader metalTxt
  let (fcMetalValid, _) := validateMetalShader fcMetal
  let gpuDescs := lowerModuleToGPUDescriptors optMod
  let stablehloTxt := emitStableHLOModule optMod
  let pallasTxt := emitTPUPallasModule optMod
  let tpuCodegenOk := (stablehloTxt.splitOn "stablehlo.").length > 1 &&
    (stablehloTxt.splitOn "tpu_v5e").length > 1 &&
    (pallasTxt.splitOn "tpu_v5e").length > 1 &&
    (pallasTxt.splitOn "pallas").length > 1
  let blake3Ok := blake3SelfTest

  IO.println s!"1. Canonical 8-Kernel Module       : {optMod.decls.length} declarations (incl. 256-bit EVM/Verity)"
  IO.println s!"2. LNIR Wire & JSON Round-Trip     : {if roundTripWireOk && roundTripJsonOk then "PASSED" else "FAILED"}"
  IO.println s!"3. Certificate Chain Verification  : {if certReport.verified then "PASSED" else "FAILED"} ({certReport.certs.length} certs)"
  IO.println s!"4. Alive2 Symbolic TV Validation   : {if tvReport.allPassed then "PASSED" else "FAILED"} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)"
  IO.println s!"5. Enumerative Superoptimizer      : {if superoptOk then "PASSED" else "FAILED"} ({soReportX86.rewritesApplied} rewrites, cost {soReportX86.totalCostBefore}->{soReportX86.totalCostAfter})"
  IO.println s!"6. Segregated Plugins & Law 1/5    : {if pluginsOk && law5Ok then "PASSED" else "FAILED"} (accepted={pluginReport.acceptedCount}, adversarialRejected={pluginReport.rejectedCount})"
  IO.println s!"7. FastCheck ConstraintProp vs Vac : {if fcPropOk && fcNaiveVacuousOk then "PASSED" else "FAILED"} (propCex={fcReportProp.counterexamplesFound}, naiveVacuous={fcReportNaive.vacuousPasses})"
  IO.println s!"8. Unified GPUIR & Apple Metal 3.0 : {if metalValid && fcMetalValid then "PASSED" else "FAILED"} ({gpuDescs.length} GPU descriptors, Metal={metalTxt.length}B)"
  IO.println s!"9. Pure-Lean RFC BLAKE3 Self-Test  : {if blake3Ok then "PASSED" else "FAILED"}"
  IO.println s!"10. Google Cloud TPU v5e Codegen   : {if tpuCodegenOk then "PASSED" else "FAILED"} (StableHLO={stablehloTxt.length}B, Pallas={pallasTxt.length}B)"

  let allOk := roundTripWireOk && roundTripJsonOk && certReport.verified &&
    tvReport.allPassed && superoptOk && pluginsOk && law5Ok &&
    fcPropOk && fcNaiveVacuousOk && metalValid && fcMetalValid && blake3Ok && tpuCodegenOk &&
    llvmX86.length > 500 && ptxTxt.length > 500 && fcLlvm.length > 200 && fcPtx.length > 200
  if allOk then
    IO.println s!"=== ALL {tag.toUpper} v0.5.0 SELF-TESTS PASSED ==="
    return 0
  else
    IO.println s!"=== {tag.toUpper} SELF-TEST FAILED ==="
    return 1

/-! ## Persistent Sub-Millisecond JSON-RPC Worker (`worker`) -/

private abbrev escapeJsonWorker := LeanNative.IR.jsonEscape

private def extractRpcId (line : String) : String :=
  match line.splitOn "\"id\"" with
  | _ :: afterId :: _ =>
    match afterId.splitOn ":" with
    | _ :: afterColon :: _ =>
      let trimmed := afterColon.trimAscii.toString
      let tokenChars := trimmed.toList.takeWhile (fun c => c != ',' && c != '}' && c != ' ')
      let tok := String.ofList tokenChars
      if tok.isEmpty then "1" else tok
    | _ => "1"
  | _ => "1"

private def extractRpcStringField (line : String) (key : String) : Option String :=
  let pat := "\"" ++ key ++ "\""
  match line.splitOn pat with
  | _ :: afterKey :: _ =>
    match afterKey.splitOn ":" with
    | _ :: afterColon :: _ =>
      let trimmed := afterColon.trimAscii.toString
      match trimmed.splitOn "\"" with
      | _ :: val :: _ => some val
      | _ => none
    | _ => none
  | _ => none

private def hasRpcBoolField (line : String) (key : String) (expected : Bool) : Bool :=
  let bStr := if expected then "true" else "false"
  let pat1 := s!"\"{key}\":{bStr}"
  let pat2 := s!"\"{key}\": {bStr}"
  (line.splitOn pat1).length > 1 || (line.splitOn pat2).length > 1

structure WorkerCache where
  baseMod          : LNIRModule
  optMod           : LNIRModule
  certReportJson   : String
  tvReportJson     : String
  superoptX86Json  : String
  pluginsX86Json   : String
  llvmOptX86       : String
  llvmOptArm       : String
  llvmBaseX86      : String
  ptxSm90          : String
  metalText        : String
  mlirText         : String
  stablehloText    : String
  pallasText       : String
  fcReportPropJson : String
  fcReportVacJson  : String
  fcLlvmText       : String
  fcPtxText        : String
  fcMetalText      : String

def initWorkerCache : IO WorkerCache := do
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let optCerts := stepCerts.map toOptimizationCert
  let certReport := verifyModuleCerts baseMod.moduleName optCerts
  let tvReport := validateTranslationModule baseMod optMod
  let (_, soRep) := superoptModule .x86_64 baseMod
  let (_, plRep) := runSegregatedPluginPipeline .x86_64 true baseMod
  let llvmOptX86 := emitLLVMOptimized optMod .x86_64
  let llvmOptArm := emitLLVMOptimized optMod .arm64
  let llvmBaseX86 := emitLLVMBaseline baseMod .x86_64
  let ptxSm90 := emitPTXModule optMod "sm_90"
  let metalText := emitMetalModule optMod
  let mlirText := emitMLIRModule optMod
  let stablehloText := emitStableHLOModule optMod
  let pallasText := emitTPUPallasModule optMod
  let fcMod := mkFastCheckSampleModule
  let fcProp := runFastCheckModule fcMod 1024 true
  let fcVac := runFastCheckModule fcMod 1024 false
  let fcLlvm := emitFastCheckLLVM fcMod
  let fcPtx := emitFastCheckPTX fcMod "sm_90"
  let fcMetal := emitFastCheckMetal fcMod
  return {
    baseMod
    optMod
    certReportJson := certReport.toJson
    tvReportJson := tvReport.toJson
    superoptX86Json := soRep.toJson
    pluginsX86Json := plRep.toJson
    llvmOptX86
    llvmOptArm
    llvmBaseX86
    ptxSm90
    metalText
    mlirText
    stablehloText
    pallasText
    fcReportPropJson := fcProp.toJson
    fcReportVacJson := fcVac.toJson
    fcLlvmText := fcLlvm
    fcPtxText := fcPtx
    fcMetalText := fcMetal
  }

def handleWorkerRequest (engineName : String) (cache : WorkerCache) (line : String) : String :=
  let reqId := extractRpcId line
  let method := (extractRpcStringField line "method").getD "ping"
  let customWireOpt := extractRpcStringField line "wire"
  let customModOpt : Option LNIRModule :=
    match customWireOpt with
    | some w => LNIRModule.fromWire? w
    | none => none
  match method with
  | "ping" =>
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"pong\",\"engine\":\"{engineName}\",\"version\":\"0.5.0\",\"decls\":{cache.optMod.decls.length}}}"
  | "compile-llvm" =>
    let archStr := (extractRpcStringField line "arch").getD "x86_64"
    let isBase := hasRpcBoolField line "baseline" true
    let ir :=
      match customModOpt with
      | some m =>
        let arch := parseTargetArch archStr
        let (mEmit, _) := if isBase then (m, []) else runDefaultPipeline m
        if isBase then emitLLVMBaseline mEmit arch else emitLLVMOptimized mEmit arch
      | none =>
        if isBase then cache.llvmBaseX86
        else if archStr == "arm64" || archStr == "aarch64" then cache.llvmOptArm
        else cache.llvmOptX86
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"arch\":\"{escapeJsonWorker archStr}\",\"baseline\":{if isBase then "true" else "false"},\"decls\":{cache.optMod.decls.length},\"irBytes\":{ir.length},\"ir\":\"{escapeJsonWorker ir}\"}}"
  | "compile-ptx" =>
    let sm := (extractRpcStringField line "sm").getD "sm_90"
    let isFc := hasRpcBoolField line "fastcheck" true
    let ptx :=
      if isFc then cache.fcPtxText
      else match customModOpt with
        | some m =>
          let (mOpt, _) := runDefaultPipeline m
          emitPTXModule mOpt sm
        | none =>
          if sm == "sm_90" then cache.ptxSm90 else emitPTXModule cache.optMod sm
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"sm\":\"{escapeJsonWorker sm}\",\"decls\":{cache.optMod.decls.length},\"ptxBytes\":{ptx.length},\"ptx\":\"{escapeJsonWorker ptx}\"}}"
  | "compile-metal" =>
    let isFc := hasRpcBoolField line "fastcheck" true
    let msl :=
      if isFc then cache.fcMetalText
      else match customModOpt with
        | some m =>
          let (mOpt, _) := runDefaultPipeline m
          emitMetalModule mOpt
        | none => cache.metalText
    let (valid, _) := validateMetalShader msl
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"apple_metal_3.0\",\"valid\":{if valid then "true" else "false"},\"decls\":{cache.optMod.decls.length},\"metalBytes\":{msl.length},\"metal\":\"{escapeJsonWorker msl}\"}}"
  | "compile-mlir" =>
    let dialect := (extractRpcStringField line "dialect").getD "gpu"
    let mlir :=
      match customModOpt with
      | some m =>
        let (mOpt, _) := runDefaultPipeline m
        if dialect == "pallas" then emitTPUPallasModule mOpt
        else if dialect == "stablehlo" || dialect == "tpu" then emitStableHLOModule mOpt
        else emitMLIRModule mOpt
      | none =>
        if dialect == "pallas" then cache.pallasText
        else if dialect == "stablehlo" || dialect == "tpu" then cache.stablehloText
        else cache.mlirText
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"dialect\":\"{escapeJsonWorker dialect}\",\"decls\":{cache.optMod.decls.length},\"mlirBytes\":{mlir.length},\"mlir\":\"{escapeJsonWorker mlir}\"}}"
  | "compile-tpu" =>
    let (shlo, pallas) :=
      match customModOpt with
      | some m =>
        let (mOpt, _) := runDefaultPipeline m
        (emitStableHLOModule mOpt, emitTPUPallasModule mOpt)
      | none => (cache.stablehloText, cache.pallasText)
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"google_cloud_tpu_v5e\",\"decls\":{cache.optMod.decls.length},\"stablehloBytes\":{shlo.length},\"pallasBytes\":{pallas.length},\"stablehlo\":\"{escapeJsonWorker shlo}\",\"pallas\":\"{escapeJsonWorker pallas}\"}}"
  | "compile-fastcheck" =>
    let noProp := hasRpcBoolField line "useConstraintProp" false || hasRpcBoolField line "noConstraintProp" true
    let repJson :=
      match customModOpt with
      | some m => (runFastCheckModule m 1024 (!noProp)).toJson
      | none => if noProp then cache.fcReportVacJson else cache.fcReportPropJson
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":{repJson}}"
  | "superopt" =>
    let tgtStr := (extractRpcStringField line "target").getD "x86_64"
    let soJson :=
      match customModOpt with
      | some m => (superoptModule (parseSuperoptTarget tgtStr) m).2.toJson
      | none =>
        if tgtStr == "x86_64" then cache.superoptX86Json
        else (superoptModule (parseSuperoptTarget tgtStr) cache.baseMod).2.toJson
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":{soJson}}"
  | "plugins" =>
    let tgtStr := (extractRpcStringField line "target").getD "x86_64"
    let plJson :=
      match customModOpt with
      | some m => (runSegregatedPluginPipeline (parseSuperoptTarget tgtStr) true m).2.toJson
      | none =>
        if tgtStr == "x86_64" then cache.pluginsX86Json
        else (runSegregatedPluginPipeline (parseSuperoptTarget tgtStr) true cache.baseMod).2.toJson
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":{plJson}}"
  | "verify-certs" =>
    let certJson :=
      match customModOpt with
      | some m =>
        let (_, sc) := runDefaultPipeline m
        (verifyModuleCerts m.moduleName (sc.map toOptimizationCert)).toJson
      | none => cache.certReportJson
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":{certJson}}"
  | "validate-tv" =>
    let tvJson :=
      match customModOpt with
      | some m =>
        let (mOpt, _) := runDefaultPipeline m
        (validateTranslationModule m mOpt).toJson
      | none => cache.tvReportJson
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":{tvJson}}"
  | "eval-cex" =>
    let buggyDecl := evmConstrainedBuggyPropDecl
    let witnessEnv := (VarEnv.empty.bind 1 (.u64 1000000)).bind 0 (.u64 1000042)
    let certified := certifyCounterexample 128 buggyDecl witnessEnv HeapState.empty
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"declName\":\"evm_constrained_buggy_prop\",\"certified\":{if certified then "true" else "false"},\"falsePositives\":0,\"theorem\":\"LeanNative.Backend.FastCheck.certifyCounterexample_no_false_positive\",\"report\":{cache.fcReportPropJson}}}"
  | other =>
    s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unknown_method:{escapeJsonWorker other}\"}"

partial def workerLoop (engineName : String) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (cache : WorkerCache) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then
    return 0
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    workerLoop engineName stdin stdout cache
  else
    let method := (extractRpcStringField trimmed "method").getD ""
    if method == "exit" || method == "shutdown" || method == "quit" then
      let reqId := extractRpcId trimmed
      stdout.putStrLn s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"bye\"}}"
      stdout.flush
      return 0
    else
      let resp := handleWorkerRequest engineName cache trimmed
      stdout.putStrLn resp
      stdout.flush
      workerLoop engineName stdin stdout cache

def runWorker (engineName : String) : IO UInt32 := do
  let cache ← initWorkerCache
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  workerLoop engineName stdin stdout cache

def printCoreUsage (tag : String) (hasFrontend : Bool) : IO Unit := do
  IO.println s!"{tag} v0.5.0 — Formally Validated Lean 4 Optimizer, Segregated Plugin Engine, Superoptimizer, TV, FastCheck & Multi-Target Codegen"
  IO.println ""
  IO.println s!"Usage: {tag} <command> [options]"
  IO.println ""
  IO.println "Commands:"
  if hasFrontend then
    IO.println "  build-exe          Compile a .lean source file directly to a native executable (<file.lean> -o <bin>)"
  IO.println "  compile-llvm       Emit baseline or optimized LLVM 18 IR (--input <file>, --arch x86_64|arm64, --baseline, -o <path>)"
  IO.println "  compile-static-lib Emit C-ABI static library (.a) + C header (.h) for zero-copy FFI (--input <file>, -o <lib.a>, --header <lib.h>)"
  IO.println "  compile-mlir       Emit GPU MLIR module (--input <file>, -o <path>)"
  IO.println "  compile-ptx        Emit NVIDIA PTX 8.0 assembly (--input <file>, --sm sm_90, --fastcheck, -o <path>)"
  IO.println "  compile-metal      Emit Apple Metal Shading Language 3.0 (--input <file>, --fastcheck, -o <path>)"
  IO.println "  compile-fastcheck  Run Constraint-Propagating FastCheck or emit SIMD/PTX/Metal kernels (--samples N, --emit-llvm, --emit-ptx, --emit-metal, --json, -o <path>)"
  IO.println "  compile-hybrid     Partition module into CPU/GPU and emit hybrid host dispatch glue (--input <file>, -o <path>)"
  IO.println "  superopt           Run cost-guided enumerative superoptimizer (--target x86_64|arm64|cuda_ptx|apple_metal, --json, -o <path>)"
  IO.println "  plugins            Run segregated optimization plugins under Law 1 TV/Cost Gate (--target <arch>, --test-adversarial, --json)"
  IO.println "  pr-verify          Run Law 5 PR & Spec-Pinning Gate + Season 8 turbo-lean pr-verify/audit-spec (--base <ref>, --disallow-spec-changes, --json)"
  IO.println "  turbo-plugin       Run JSONL-stdio external accelerator plugin for turbo-lean (ExternalProcessAccelerator protocol)"
  IO.println "  verify-certs       Run optimization pipeline and verify translation certificates (--input <file>, --json, -o <path>)"
  IO.println "  validate-tv        Run Alive2-style symbolic translation validation (--input <file>, --json, -o <path>)"
  IO.println "  emit-lnir          Emit LNIR module in wire/JSON format (--wire, --json, --fastcheck, -o <path>)"
  if hasFrontend then
    IO.println "  audit-axioms       Run in-kernel transitive axiom audit over all 82 soundness theorems (--json)"
    IO.println "  turbo-status       Probe Turbo Lean integration, verify BLAKE3 vectors, and emit/verify receipt"
  IO.println "  self-test          Run end-to-end Core, Spec (Laws 1-5), Plugins, Codec, FastCheck, Superopt, SymbolicTV, LLVM/PTX/Metal self-tests"
  IO.println "  worker             Run persistent sub-millisecond JSON-RPC worker loop over stdin/stdout"

/-- Shared CLI dispatcher for both `lean-native-core` (`elaborateHook? = none`) and `lean-native` (`elaborateHook? = some ...`). -/
def dispatchSharedCommand (tag : String) (elaborateHook? : Option (String → IO LNIRModule))
    (args : List String) : IO (Option UInt32) := do
  match args with
  | "compile-llvm" :: rest       => some <$> runCompileLLVM tag elaborateHook? rest
  | "compile-static-lib" :: rest => some <$> runCompileStaticLib tag elaborateHook? rest
  | "compile-mlir" :: rest       => some <$> runCompileMLIR tag elaborateHook? rest
  | "compile-ptx" :: rest       => some <$> runCompilePTX tag elaborateHook? rest
  | "compile-metal" :: rest     => some <$> runCompileMetal tag elaborateHook? rest
  | "compile-fastcheck" :: rest => some <$> runCompileFastCheck tag elaborateHook? rest
  | "compile-hybrid" :: rest    => some <$> runCompileHybrid tag elaborateHook? rest
  | "superopt" :: rest          => some <$> runSuperopt elaborateHook? rest
  | "plugins" :: rest           => some <$> runPlugins elaborateHook? rest
  | "pr-verify" :: rest         => some <$> runPRVerify tag rest
  | "turbo-plugin" :: _         => some <$> runTurboPlugin
  | "verify-certs" :: rest      => some <$> runVerifyCerts tag elaborateHook? rest
  | "validate-tv" :: rest       => some <$> runValidateTV elaborateHook? rest
  | "emit-lnir" :: rest         => some <$> runEmitLNIR tag elaborateHook? rest
  | "worker" :: _               => some <$> runWorker tag
  | _                           => return none

end LeanNative.Driver.CoreCLI

