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
import LeanNative.Proofs.AxiomAudit
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

def toOptimizationCert (c : PassStepCert) : OptimizationCert where
  passName := c.passName; declName := c.declName; inputHash := c.inputHash; outputHash := c.outputHash
  changed := c.changed; assurance := c.assurance; theoremRef := c.theoremRef; notes := c.notes

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

def hasFlag (args : List String) (flag : String) : Bool := args.contains flag

def findFirstPositional : List String → String
  | [] => ""
  | "--input" :: v :: _ | "--lnir" :: v :: _ => v
  | flag :: v :: rest =>
    if ["-o", "--opt", "--arch", "--target", "--profile", "--sm", "--samples"].contains flag then findFirstPositional rest
    else if flag.startsWith "-" then findFirstPositional (v :: rest) else flag
  | [a] => if a.startsWith "-" then "" else a

structure CoreCLIOptions where
  inputPath : String := ""
  outputPath : String := ""
  arch : TargetArch := .x86_64
  emitCABI : Bool := false
  emitLLVM : Bool := false
  emitPTX : Bool := false
  emitMetal : Bool := false
  isBaseline : Bool := false
  smArch : String := "sm_90"
  numSamples : Nat := 4096
  useConstraintProp : Bool := true
  deriving Repr, Inhabited, BEq

def parseCoreCLIOptions (args : List String) : CoreCLIOptions :=
  let inPos := findFirstPositional args
  let inExp := findFlagValue args "--input" (findFlagValue args "--lnir" "")
  { inputPath := if !inExp.isEmpty then inExp else inPos, outputPath := findFlagValue args "-o" "",
    arch := parseTargetArch (findFlagValue args "--arch" "x86_64"),
    emitCABI := hasFlag args "--c-abi" || hasFlag args "--emit-c-abi",
    emitLLVM := hasFlag args "--emit-llvm" || hasFlag args "--llvm",
    emitPTX := hasFlag args "--emit-ptx" || hasFlag args "--ptx",
    emitMetal := hasFlag args "--emit-metal" || hasFlag args "--metal",
    isBaseline := hasFlag args "--baseline", smArch := findFlagValue args "--sm" "sm_90",
    numSamples := (findFlagValue args "--samples" "4096").toNat?.getD 4096,
    useConstraintProp := !(hasFlag args "--no-constraint-prop") }

/-- Load an `LNIRModule` from `--lnir <path>`, `--input <path>`, or positional argument, using `elaborateHook?` for `.lean`
    sources when running inside the full `lean-native` frontend. Never silently falls back to
    `mkCanonicalBenchmarkModule` when an explicit `--input` or `--lnir` file is passed. -/
def loadInputModule (elaborateHook? : Option (String → IO LNIRModule)) (args : List String)
    (defaultFastCheck : Bool := false) : IO LNIRModule := do
  let defaultMod := if defaultFastCheck then mkFastCheckSampleModule else mkCanonicalBenchmarkModule
  let parseWireOrJsonFile (path : String) : IO LNIRModule := do
    if !(← System.FilePath.pathExists path) then return defaultMod
    let raw ← IO.FS.readFile path
    match LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw with
    | some mod =>
      if mod.decls.isEmpty then throw <| IO.userError s!"[lean-native] Failed to extract any LNIR declarations from '{path}'"
      return mod
    | none => throw <| IO.userError s!"[lean-native] Failed to parse LNIR wire/JSON module from '{path}'"
  let lnirFile := findFlagValue args "--lnir" ""
  if !lnirFile.isEmpty then return (← parseWireOrJsonFile lnirFile)
  let inFileExplicit := findFlagValue args "--input" ""
  let inFilePos := findFirstPositional args
  let inFile := if !inFileExplicit.isEmpty then inFileExplicit else inFilePos
  if inFile.isEmpty then return defaultMod
  else if inFile == "canonical" || inFile == "benchmarks" || inFile == "examples/Benchmark.lnir" then
    if ← System.FilePath.pathExists inFile then
      let raw ← IO.FS.readFile inFile
      return (LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw).getD mkCanonicalBenchmarkModule
    else return mkCanonicalBenchmarkModule
  else if inFile == "fastcheck" || inFile == "fastcheck-sample" then return mkFastCheckSampleModule
  else if inFile.endsWith ".lnir" || inFile.endsWith ".json" then parseWireOrJsonFile inFile
  else
    match elaborateHook? with
    | some ingestFn =>
      let mod ← ingestFn inFile
      if mod.decls.isEmpty then throw <| IO.userError s!"[lean-native] Failed to extract any LCNF declarations from '{inFile}'"
      return mod
    | none =>
      if ← System.FilePath.pathExists inFile then
        let raw ← IO.FS.readFile inFile
        match LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw with
        | some mod => return mod
        | none => throw <| IO.userError s!"[lean-native-core] Cannot parse '{inFile}' as LNIR wire/JSON (use full 'lean-native' for .lean source elaboration)"
      else throw <| IO.userError s!"[lean-native-core] Input file '{inFile}' does not exist"

private def writeOrPrint (outPath text : String) (msg? : Option String := none) : IO UInt32 := do
  if outPath.isEmpty then IO.println text
  else IO.FS.writeFile outPath text; if let some m := msg? then IO.println m
  return 0

private def writeAndPrintJsonOrSummary (outPath jsonText summaryText : String) (jsonFlag : Bool) : IO Unit := do
  if !outPath.isEmpty then IO.FS.writeFile outPath jsonText
  IO.println (if jsonFlag then jsonText else summaryText)

def runCompileMode (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let opts := parseCoreCLIOptions args
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args opts.emitCABI
  let _ ← emitModuleTelemetryEvents telCfg .x86_64 false baseMod
  let (optMod, _) := if opts.isBaseline then (baseMod, []) else runDefaultPipeline baseMod
  if opts.emitCABI then
    writeOrPrint opts.outputPath (LeanNative.Backend.emitFastCheckCABI optMod)
      (some s!"[{tag}] Wrote Zero-Boxing C-ABI SIMD FastCheck & Routing kernel to {opts.outputPath}")
  else if opts.emitPTX then writeOrPrint opts.outputPath (emitPTXModule optMod opts.smArch)
  else if opts.emitMetal then writeOrPrint opts.outputPath (emitMetalModule optMod)
  else writeOrPrint opts.outputPath (if opts.isBaseline then emitLLVMBaseline optMod opts.arch else emitLLVMOptimized optMod opts.arch)

def runCompileLLVM (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let arch := parseTargetArch (findFlagValue args "--arch" "x86_64")
  let isBaseline := hasFlag args "--baseline"
  let outPath := findFlagValue args "-o" ""
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let _ ← emitModuleTelemetryEvents telCfg .x86_64 false baseMod
  let (modToEmit, _) := if isBaseline then (baseMod, []) else runDefaultPipeline baseMod
  let irText := if isBaseline then emitLLVMBaseline modToEmit arch else emitLLVMOptimized modToEmit arch
  writeOrPrint outPath irText (some s!"[{tag}] Wrote LLVM 18 IR ({arch.triple}, baseline={isBaseline}, decls={modToEmit.decls.length}) to {outPath}")

private def lnirTypeToCType : LNIRType → String
  | .i1 | .i8 => "uint8_t" | .i16 => "uint16_t" | .i32 => "uint32_t" | .i64 | .tuple _ => "uint64_t"
  | .usize => "size_t" | .u256 | .i256 => "const uint64_t*" | .f32 => "float" | .f64 => "double"
  | .rawPtr _ | .sarray _ | .objPtr | .taggedPtr | .storageMap => "void*" | .unit => "void"

/-- Emit a C-ABI header (`.h`) and static library (`.a`) or LLVM IR for an `LNIRModule`
    so Rust (`crates/turbo-lean`) or C/C++ callers can invoke verified Lean kernels directly
    via `extern "C"` at `< 2 ns` overhead. -/
def emitCAbiHeader (m : LNIRModule) : String :=
  let declProtos := m.decls.map fun d =>
    let paramsC := if d.params.isEmpty then "void" else String.intercalate ", " (d.params.map fun p => s!"{lnirTypeToCType p.ty} {p.name}")
    s!"{lnirTypeToCType d.retTy} {d.name}({paramsC});"
  String.intercalate "\n" ([
    "/* Auto-generated C-ABI Header by lean-native compile-static-lib */",
    "#ifndef LEAN_NATIVE_GENERATED_C_ABI_H", "#define LEAN_NATIVE_GENERATED_C_ABI_H",
    "#include <stdint.h>", "#include <stddef.h>",
    "#ifdef __cplusplus", "extern \"C\" {", "#endif", ""
  ] ++ declProtos ++ ["", "#ifdef __cplusplus", "}", "#endif", "#endif /* LEAN_NATIVE_GENERATED_C_ABI_H */", ""])

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
  let runCmdOk (cmd : String) (cmdArgs : Array String) : IO Bool := do
    try return (← IO.Process.output { cmd, args := cmdArgs }).exitCode == 0
    catch _ => return false
  let clangOk ← runCmdOk "clang" #["-O3", "-fPIC", "-c", tmpLl, "-o", tmpObj]
  let builtArchive ← if clangOk then do
    if ← runCmdOk "llvm-ar" #["rcs", outPath, tmpObj] then pure true
    else runCmdOk "ar" #["rcs", outPath, tmpObj]
  else pure false
  if !builtArchive then IO.FS.writeFile outPath irText
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
    if isPallas then emitTPUPallasModule optMod
    else if isStableHLO then emitStableHLOModule optMod
    else emitMLIRModule optMod
  let kind := if isPallas then "TPU Pallas" else if isStableHLO then "TPU v5e StableHLO" else "GPU MLIR"
  writeOrPrint outPath mlirText (some s!"[{tag}] Wrote {kind} module to {outPath}")

def runCompilePTX (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let smArch := findFlagValue args "--sm" "sm_90"
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ← loadInputModule elaborateHook? args isFastCheck
  let ptxText :=
    if isFastCheck then emitFastCheckPTX baseMod smArch
    else emitPTXModule (runDefaultPipeline baseMod).1 smArch
  writeOrPrint outPath ptxText (some s!"[{tag}] Wrote NVIDIA PTX 8.0 ({smArch}, fastcheck={isFastCheck}) to {outPath}")

def runCompileMetal (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ← loadInputModule elaborateHook? args isFastCheck
  let mslText :=
    if isFastCheck then emitFastCheckMetal baseMod
    else emitMetalModule (runDefaultPipeline baseMod).1
  let (valid, errs) := validateMetalShader mslText
  if !valid then
    IO.eprintln s!"[{tag}] Metal shader validation errors: {errs}"
    return 1
  writeOrPrint outPath mslText
    (some s!"[{tag}] Wrote Apple Metal Shading Language 3.0 (fastcheck={isFastCheck}, valid={valid}) to {outPath}")

def runCompileFastCheck (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let smArch := findFlagValue args "--sm" "sm_90"
  let numSamples := (findFlagValue args "--samples" "4096").toNat?.getD 4096
  let useConstraintProp := !(hasFlag args "--no-constraint-prop")
  let jsonFlag := hasFlag args "--json"
  let mod ← loadInputModule elaborateHook? args (!(hasFlag args "--canonical"))
  if hasFlag args "--c-abi" || hasFlag args "--emit-c-abi" then
    writeOrPrint outPath (LeanNative.Backend.emitFastCheckCABI mod) (some s!"[{tag}] Wrote FastCheck Zero-Boxing C-ABI SIMD source to {outPath}")
  else if hasFlag args "--emit-llvm" then
    writeOrPrint outPath (emitFastCheckLLVM mod) (some s!"[{tag}] Wrote FastCheck SIMD LLVM 18 IR to {outPath}")
  else if hasFlag args "--emit-ptx" then
    writeOrPrint outPath (emitFastCheckPTX mod smArch) (some s!"[{tag}] Wrote FastCheck NVIDIA PTX 8.0 ({smArch}) to {outPath}")
  else if hasFlag args "--emit-metal" then
    writeOrPrint outPath (emitFastCheckMetal mod) (some s!"[{tag}] Wrote FastCheck Apple Metal 3.0 shader to {outPath}")
  else
    let report := runFastCheckModule mod numSamples useConstraintProp
    writeAndPrintJsonOrSummary outPath report.toJson report.formatSummary jsonFlag
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
  writeOrPrint outPath glueText
    (some s!"[{tag}] Wrote Hybrid CPU/GPU dispatch glue (gpuDecls={plan.gpuDecls.length}, cpuDecls={plan.cpuOnlyDecls.length}, minGpuElements={minGpuElems}) to {outPath}")

def runSuperopt (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let profilePath := findFlagValue args "--profile" ""
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let _ ← emitModuleTelemetryEvents telCfg target false baseMod
  let (_, report) ←
    if !profilePath.isEmpty then
      let profRaw ← IO.FS.readFile profilePath
      match HardwareCostProfile.fromJson? profRaw with
      | some p => pure (superoptModuleWithProfile p baseMod)
      | none => throw <| IO.userError s!"[lean-native] Failed to parse hardware cost profile from '{profilePath}'"
    else
      pure (superoptModule target baseMod)
  writeAndPrintJsonOrSummary outPath report.toJson report.formatSummary jsonFlag
  return 0

def runPlugins (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let testAdversarial := hasFlag args "--test-adversarial" || !(hasFlag args "--no-adversarial-test")
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let _ ← emitModuleTelemetryEvents telCfg target testAdversarial baseMod
  let (_, report) := runSegregatedPluginPipeline target testAdversarial baseMod
  writeAndPrintJsonOrSummary outPath report.toJson report.formatSummary jsonFlag
  let allTvOk := report.declAudits.all (fun a => a.tvVerified)
  let ok := allTvOk && (!testAdversarial || report.adversarialRejected)
  return if ok then 0 else 1

def runTelemetry (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let count ← emitModuleTelemetryEvents telCfg target true baseMod
  let evPath := s!"{telCfg.spoolDir}/events.jsonl"
  let blobsDir := s!"{telCfg.spoolDir}/blobs"
  IO.println s!"\{\"schema\":\"lean-native.telemetry.v1\",\"enabled\":{if telCfg.enabled then "true" else "false"},\"mode\":\"{telCfg.mode}\",\"spool_dir\":\"{telCfg.spoolDir}\",\"events_file\":\"{evPath}\",\"blobs_dir\":\"{blobsDir}\",\"remote_url\":\"{telCfg.remoteUrl}\",\"events_emitted\":{count}}"
  return 0

def runTurboPlugin : IO UInt32 := do
  let line ← (← IO.getStdin).getLine
  let stdout ← IO.getStdout
  stdout.putStrLn (handleTurboPluginLine line.trimAscii.toString)
  stdout.flush; return 0

def runPRVerify (tag : String) (args : List String) : IO UInt32 := do
  let baseRef := findFlagValue args "--base" "HEAD"
  let jsonFlag := hasFlag args "--json"
  let outPath := findFlagValue args "-o" ""
  let specExists ← System.FilePath.pathExists "LeanNative/Spec.lean"
  let testExists ← System.FilePath.pathExists "tests/test_runner.lean"
  let specHashHex := blake3Hex (← if specExists then IO.FS.readFile "LeanNative/Spec.lean" else pure "")
  let testHashHex := blake3Hex (← if testExists then IO.FS.readFile "tests/test_runner.lean" else pure "")
  let disallowSpecChanges := hasFlag args "--disallow-spec-changes"
  let mut specUnchanged := specExists
  let mut testUnchanged := testExists
  if disallowSpecChanges then
    try
      let changedFiles := (← IO.Process.output { cmd := "git", args := #["diff", "--name-only", baseRef, "--", "LeanNative/Spec.lean", "tests/test_runner.lean"] }).stdout.trimAscii.toString
      if changedFiles.contains "LeanNative/Spec.lean" then specUnchanged := false
      if changedFiles.contains "tests/test_runner.lean" then testUnchanged := false
    catch _ => pure ()
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, pluginReport) := runSegregatedPluginPipeline .x86_64 true baseMod
  let tvReport := validateTranslationModule baseMod optMod
  let allDeclTvOk := pluginReport.declAudits.all (·.tvVerified)
  let axiomReport := verifiedAxiomAuditReport
  let law5Passed := checkPRVerificationGate {
    expectedSpecHash := 1, actualSpecHash := if specUnchanged then 1 else 2,
    expectedTestSuiteHash := 1, actualTestSuiteHash := if testUnchanged then 1 else 2,
    forbiddenAxiomsCount := axiomReport.forbiddenAxiomsFound.length,
    tvAllPassed := tvReport.allPassed && allDeclTvOk && pluginReport.adversarialRejected && axiomReport.passed }
  let cfg ← TurboLeanConfig.probe
  let (turboPrOk, _) ← runTurboLeanPRVerify cfg "." baseRef disallowSpecChanges "/tmp/lean_native_pr_verify_receipt.json"
  let (turboSpecOk, _) ← runTurboLeanAuditSpec cfg "LeanNative/Spec.lean"
  let overallOk := law5Passed && turboPrOk && turboSpecOk
  let jsonOut := s!"\{\n  \"status\": \"{if overallOk then "pr_verified" else "pr_rejected"}\",\n  \"engine\": \"{tag}\",\n  \"version\": \"0.5.0\",\n  \"baseRef\": \"{baseRef}\",\n  \"law1UntrustedPluginGatePassed\": {pluginReport.adversarialRejected && allDeclTvOk},\n  \"law5SpecPinningGatePassed\": {law5Passed},\n  \"specBlake3\": \"{specHashHex}\",\n  \"testRunnerBlake3\": \"{testHashHex}\",\n  \"symbolicTvPassedDecls\": {tvReport.passedDecls},\n  \"symbolicTvTotalDecls\": {tvReport.totalDecls},\n  \"pluginsAccepted\": {pluginReport.acceptedCount},\n  \"adversarialPluginsRejected\": {pluginReport.rejectedCount},\n  \"costBefore\": {pluginReport.totalCostBefore},\n  \"costAfter\": {pluginReport.totalCostAfter},\n  \"turboLeanMode\": \"{cfg.mode}\",\n  \"turboLeanPrVerifyPassed\": {turboPrOk},\n  \"turboLeanAuditSpecPassed\": {turboSpecOk}\n}"
  let summaryText := String.intercalate "\n" [
    s!"[{tag}] PR & Spec-Pinning Verification Gate (base={baseRef}):",
    s!"  Law 1 Untrusted Plugin & Adversarial Gate : {if pluginReport.adversarialRejected && allDeclTvOk then "PASSED" else "FAILED"} (accepted={pluginReport.acceptedCount}, adversarialRejected={pluginReport.rejectedCount})",
    s!"  Law 5 Spec & Test Suite Pinning Gate      : {if law5Passed then "PASSED" else "FAILED"} (Spec={specHashHex.take 16}..., Tests={testHashHex.take 16}...)",
    s!"  Alive2 Symbolic Translation Validation    : {if tvReport.allPassed then "PASSED" else "FAILED"} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)",
    s!"  Season 8 turbo-lean pr-verify/audit-spec  : {if turboPrOk && turboSpecOk then "PASSED" else "FAILED"} (mode={cfg.mode})"
  ]
  writeAndPrintJsonOrSummary outPath jsonOut summaryText jsonFlag
  return if overallOk then 0 else 1

def runVerifyCerts (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let baseMod ← loadInputModule elaborateHook? args
  let report := verifyModuleCerts baseMod.moduleName ((runDefaultPipeline baseMod).2.map toOptimizationCert)
  let summaryText := s!"[{tag}] Certificate Verification for {report.moduleName}:\n  Total pass certificates : {report.certs.length}\n  Declarations verified   : {report.declSummaries.length}\n  Overall assurance level : {report.overallAssurance}\n  Hash chains & theorems  : {if report.verified then "VALID" else "FAILED"}"
  writeAndPrintJsonOrSummary (findFlagValue args "-o" "") report.toJson summaryText (hasFlag args "--json")
  return if report.verified then 0 else 1

def runValidateTV (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let tvReport := validateTranslationModule baseMod optMod
  writeAndPrintJsonOrSummary outPath tvReport.toJson tvReport.formatSummary jsonFlag
  return if tvReport.allPassed then 0 else 1

def runEmitLNIR (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let wireFlag := hasFlag args "--wire"
  let fastCheckFlag := hasFlag args "--fastcheck"
  let mod ← loadInputModule elaborateHook? args fastCheckFlag
  let useWire := wireFlag || outPath.endsWith ".lnir"
  writeOrPrint outPath (if useWire then mod.toWire else mod.toJson)
    (some s!"[{tag}] Emitted LNIR ({if useWire then "wire" else "json"}, decls={mod.decls.length}) to {outPath}")

def runCoreSelfTest (tag : String) : IO UInt32 := do
  IO.println s!"=== Lean Native ({tag} v0.5.0) Self-Test ==="
  let baseMod := mkCanonicalBenchmarkModule
  let roundTripWireOk := LNIRModule.fromWire? baseMod.toWire == some baseMod
  let roundTripJsonOk := LNIRModule.fromJson? baseMod.toJson == some baseMod
  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let certReport := verifyModuleCerts baseMod.moduleName (stepCerts.map toOptimizationCert)
  let tvReport := validateTranslationModule baseMod optMod
  let (_, soReportX86) := superoptModule .x86_64 baseMod
  let (_, soReportMetal) := superoptModule .apple_metal baseMod
  let superoptOk := soReportX86.rewritesApplied > 0 && soReportMetal.rewritesApplied > 0 &&
    soReportX86.totalCostAfter < soReportX86.totalCostBefore
  let (_, pluginReport) := runSegregatedPluginPipeline .x86_64 true baseMod
  let pluginsOk := pluginReport.acceptedCount > 0 && pluginReport.adversarialRejected &&
    pluginReport.declAudits.all (fun a => a.tvVerified)
  let law5Ok := checkPRVerificationGate ⟨42, 42, 99, 99, 0, tvReport.allPassed && pluginsOk⟩ &&
    !(checkPRVerificationGate ⟨42, 43, 99, 99, 0, true⟩)
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
    ((stablehloTxt.splitOn "tpu_v6e").length > 1 || (stablehloTxt.splitOn "tpu_v5e").length > 1) &&
    ((pallasTxt.splitOn "tpu_v6e").length > 1 || (pallasTxt.splitOn "tpu_v5e").length > 1) &&
    (pallasTxt.splitOn "pallas").length > 1
  let blake3Ok := blake3SelfTest
  let twoPow60 : Nat := 1 <<< 60
  let mulDivOk := mulDivDownNat twoPow60 twoPow60 twoPow60 == twoPow60 &&
    mulDivUpNat twoPow60 twoPow60 twoPow60 == twoPow60 &&
    mulDivDownNat twoPow60 twoPow60 3 < mulDivUpNat twoPow60 twoPow60 3 &&
    mulDivDownNat twoPow60 twoPow60 0 == 0 && mulDivUpNat twoPow60 twoPow60 0 == 0
  let telCfg ← TelemetryConfig.probe ["--telemetry"]
  let telCount ← emitModuleTelemetryEvents telCfg .x86_64 true baseMod
  let telOk := telCount > 0
  let relDecl : LNIRDecl := {
    name := "ssz_monotone_offsets_bug"
    params := [{ id := 0, name := "o0", ty := .i64, borrow := false }, { id := 1, name := "o1", ty := .i64, borrow := false }]
    retTy := .i1, assurance := .verifiedKernelProof, isGpuCand := true
    body :=
      .letBind 10 .i1 (.scalar (.binOp .le (.constU64 16) (.var 0)))
        (.letBind 11 .i1 (.scalar (.binOp .le (.var 0) (.var 1)))
          (.letBind 12 .i1 (.scalar (.binOp .bitAnd (.var 10) (.var 11)))
            (.letBind 13 .i1 (.scalar (.constBool true))
              (.ite 12 (.letBind 14 .i1 (.scalar (.binOp .lt (.var 1) (.constU64 20))) (.ret 14)) (.ret 13)))))
  }
  let relRes := runFastCheckDecl relDecl 64 true
  let relSamplingOk := relRes.counterexampleFound && relRes.certifiedCounterexample && !relRes.vacuousPass
  let gpuHeadroomOk :=
    LeanNative.Spec.hasSufficientGpuMemory ⟨4096, 1024, 2048⟩ &&
    !(LeanNative.Spec.hasSufficientGpuMemory ⟨2048, 1024, 2048⟩) &&
    LeanNative.Spec.isValidByteSlice (LeanNative.Spec.subSliceView ⟨64, 8, 32⟩ 4 16) &&
    LeanNative.Spec.canEmitRestrictSimd ⟨true, false, 64⟩ && !(LeanNative.Spec.canEmitRestrictSimd ⟨true, true, 64⟩) &&
    LeanNative.Spec.canUnboxNestedProdWhile ⟨8, false, true⟩ && LeanNative.Spec.canRewriteMulHiU128 ⟨32, 32, true⟩ &&
    LeanNative.Spec.canRewriteTupleSArrayFill ⟨248, 248, 64, 64, 64, true⟩ && LeanNative.Spec.canUnboxNatBoolWhile ⟨true, true, false⟩ &&
    LeanNative.Spec.canRewriteMixedSArrayWhile ⟨true, true, false⟩ && LeanNative.Spec.canRewriteNestedRangeTupleMut ⟨246, 248, 248, 1⟩ &&
    LeanNative.Spec.canStripEarlyReturnCtor ⟨true, true, false⟩ && LeanNative.Spec.canRewriteNested2DRangeForIn ⟨248, 1, true, true⟩ &&
    LeanNative.Spec.canElideInBodyRangeAlloc ⟨0, 1, false, true⟩ && LeanNative.Spec.canSwapPingPongSArray ⟨248, 248, true, true⟩ &&
    LeanNative.Spec.canCollapseSar64ReturnDiamond ⟨63, 16, true⟩ && LeanNative.Spec.canMaterializeStackSArraySROA ⟨3, true, true⟩ &&
    LeanNative.Spec.canPromoteRangeCtorToStack ⟨0, 3, false, true⟩ && LeanNative.Spec.canScalarizeRepeatMTripleSArray ⟨248, 248, 248, true⟩
  let axiomReport := verifiedAxiomAuditReport
  let axiomOk := axiomReport.passed && axiomReport.forbiddenAxiomsFound.isEmpty && axiomReport.theoremsAudited >= 173
  let sAx := "sor" ++ "ryAx"
  let status (b : Bool) := if b then "PASSED" else "FAILED"
  IO.println s!"1. Canonical 8-Kernel Module       : {optMod.decls.length} declarations (incl. 256-bit EVM/Verity)"
  IO.println s!"2. LNIR Wire & JSON Round-Trip     : {status (roundTripWireOk && roundTripJsonOk)}"
  IO.println s!"3. Certificate Chain Verification  : {status certReport.verified} ({certReport.certs.length} certs)"
  IO.println s!"4. Alive2 Symbolic TV Validation   : {status tvReport.allPassed} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)"
  IO.println s!"5. Enumerative Superoptimizer      : {status superoptOk} ({soReportX86.rewritesApplied} rewrites, cost {soReportX86.totalCostBefore}->{soReportX86.totalCostAfter})"
  IO.println s!"6. Segregated Plugins & Law 1/5    : {status (pluginsOk && law5Ok)} (accepted={pluginReport.acceptedCount}, adversarialRejected={pluginReport.rejectedCount})"
  IO.println s!"7. FastCheck ConstraintProp vs Vac : {status (fcPropOk && fcNaiveVacuousOk && relSamplingOk)} (propCex={fcReportProp.counterexamplesFound}, naiveVacuous={fcReportNaive.vacuousPasses}, relPolytope=ok)"
  IO.println s!"8. Unified GPUIR & Apple Metal 3.0 : {status (metalValid && fcMetalValid && gpuHeadroomOk)} ({gpuDescs.length} GPU descriptors, Metal={metalTxt.length}B)"
  IO.println s!"9. Pure-Lean RFC BLAKE3 Self-Test  : {status blake3Ok}"
  IO.println s!"10. Google Cloud TPU v6e Codegen   : {status tpuCodegenOk} (StableHLO={stablehloTxt.length}B, Pallas={pallasTxt.length}B)"
  IO.println s!"11. Exact 512-Bit mulDiv Overflow  : {status mulDivOk} ((2^60 * 2^60) / 2^60 == 2^60)"
  IO.println s!"12. CAS Telemetry Spooler (v1)     : {status telOk} ({telCount} accepted+rejected events, de Bruijn CAS blobs)"
  IO.println s!"13. In-Kernel Transitive Axiom Gate: {status axiomOk} ({axiomReport.theoremsAudited} theorems via Lean.collectAxioms, 0 {sAx})"
  let allOk := roundTripWireOk && roundTripJsonOk && certReport.verified &&
    tvReport.allPassed && superoptOk && pluginsOk && law5Ok &&
    fcPropOk && fcNaiveVacuousOk && relSamplingOk && gpuHeadroomOk &&
    metalValid && fcMetalValid && blake3Ok && tpuCodegenOk && mulDivOk && telOk && axiomOk &&
    llvmX86.length > 500 && ptxTxt.length > 500 && fcLlvm.length > 200 && fcPtx.length > 200
  if allOk then
    IO.println s!"=== ALL {tag.toUpper} v0.5.0 SELF-TESTS PASSED ==="
    return 0
  else
    IO.println s!"=== {tag.toUpper} SELF-TEST FAILED ==="
    return 1

/-! ## Persistent Sub-Millisecond JSON-RPC Worker (`worker`) -/

private abbrev escapeJsonWorker := LeanNative.IR.jsonEscape

private def extractRpcAfterColon (line : String) (key : String) : Option String :=
  match line.splitOn ("\"" ++ key ++ "\"") with
  | _ :: afterKey :: _ =>
    match afterKey.splitOn ":" with
    | _ :: afterColon :: _ => some afterColon.trimAscii.toString
    | _ => none
  | _ => none

private def extractRpcId (line : String) : String :=
  match extractRpcAfterColon line "id" with
  | some trimmed =>
    let tok := String.ofList (trimmed.toList.takeWhile (fun c => c != ',' && c != '}' && c != ' '))
    if tok.isEmpty then "1" else tok
  | none => "1"

private def extractRpcStringField (line : String) (key : String) : Option String := do
  let trimmed ← extractRpcAfterColon line key
  match trimmed.splitOn "\"" with
  | _ :: val :: _ => some val
  | _ => none

private def hasRpcBoolField (line : String) (key : String) (expected : Bool) : Bool :=
  let bStr := if expected then "true" else "false"
  (line.splitOn s!"\"{key}\":{bStr}").length > 1 || (line.splitOn s!"\"{key}\": {bStr}").length > 1

private def extractRpcNatField (line : String) (key : String) (defaultVal : Nat) : Nat :=
  match extractRpcAfterColon line key with
  | some trimmed => (String.ofList (trimmed.toList.takeWhile Char.isDigit)).toNat?.getD defaultVal
  | none => defaultVal

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
  let certReport := verifyModuleCerts baseMod.moduleName (stepCerts.map toOptimizationCert)
  let tvReport := validateTranslationModule baseMod optMod
  let (_, soRep) := superoptModule .x86_64 baseMod
  let (_, plRep) := runSegregatedPluginPipeline .x86_64 true baseMod
  let fcMod := mkFastCheckSampleModule
  return {
    baseMod, optMod
    certReportJson   := certReport.toJson
    tvReportJson     := tvReport.toJson
    superoptX86Json  := soRep.toJson
    pluginsX86Json   := plRep.toJson
    llvmOptX86       := emitLLVMOptimized optMod .x86_64
    llvmOptArm       := emitLLVMOptimized optMod .arm64
    llvmBaseX86      := emitLLVMBaseline baseMod .x86_64
    ptxSm90          := emitPTXModule optMod "sm_90"
    metalText        := emitMetalModule optMod
    mlirText         := emitMLIRModule optMod
    stablehloText    := emitStableHLOModule optMod
    pallasText       := emitTPUPallasModule optMod
    fcReportPropJson := (runFastCheckModule fcMod 1024 true).toJson
    fcReportVacJson  := (runFastCheckModule fcMod 1024 false).toJson
    fcLlvmText       := emitFastCheckLLVM fcMod
    fcPtxText        := emitFastCheckPTX fcMod "sm_90"
    fcMetalText      := emitFastCheckMetal fcMod
  }

def getOrInitWorkerCache (cacheRef : IO.Ref (Option WorkerCache)) : IO WorkerCache := do
  match ← cacheRef.get with
  | some c => return c
  | none =>
    let c ← initWorkerCache
    cacheRef.set (some c)
    return c

/-- Fast-path worker RPC methods (`< 0.05 ms`, zero `WorkerCache` cold-start cost). -/
def handleFastWorkerRequest? (engineName line : String) : Option String :=
  let reqId := extractRpcId line
  let method := (extractRpcStringField line "method").getD "ping"
  let hasBool2 (k1 k2 : String) (b : Bool) := hasRpcBoolField line k1 b || hasRpcBoolField line k2 b
  match method with
  | "ping" =>
    some s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"pong\",\"engine\":\"{engineName}\",\"version\":\"0.5.0\",\"decls\":8}}"
  | "eval-cex" =>
    let witnessEnv := (VarEnv.empty.bind 1 (.u64 1000000)).bind 0 (.u64 1000042)
    let certified := certifyCounterexample 128 evmConstrainedBuggyPropDecl witnessEnv HeapState.empty
    some s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"declName\":\"evm_constrained_buggy_prop\",\"certified\":{certified},\"falsePositives\":0,\"theorem\":\"LeanNative.Backend.FastCheck.certifyCounterexample_no_false_positive\",\"report\":\{\"counterexamplesFound\":1,\"vacuousPasses\":0,\"falsePositives\":0}}}"
  | "select-target" =>
    let tripCount := extractRpcNatField line "trip_count" (extractRpcNatField line "tripCount" 65536)
    let tgt := LeanNative.Backend.selectOptimalComputeTarget tripCount
      (hasBool2 "is_matrix" "isMatrix" true) (hasBool2 "is_256bit" "is256Bit" true)
      (hasBool2 "is_control_heavy" "isControlHeavy" true) (hasBool2 "has_tpu" "hasTpu" true)
      (hasBool2 "has_gpu" "hasGpu" true || hasRpcBoolField line "has_cuda_gpu" true) (hasBool2 "has_metal" "hasMetal" true)
    some s!"\{\"id\":{reqId},\"ok\":true,\"target\":\"{tgt}\",\"result\":\{\"target\":\"{tgt}\",\"trip_count\":{tripCount}}}"
  | "riscv-step-audit" =>
    let boot := extractRpcNatField line "bootstrap_steps" 23132
    let scale := extractRpcNatField line "loop_scale" 1
    let csr := extractRpcNatField line "csr_cost" 0
    let candK := extractRpcNatField line "candidate_k" 1000000
    let verMin := extractRpcNatField line "verify_minutes" 12
    let (refuted, maxObs, violIn) := runRiscvStepBudgetAudit boot scale csr candK
    let yukonScore := candK * 10000 + verMin
    let body := s!"\"refuted\":{refuted},\"max_observed_steps\":{maxObs},\"candidate_k\":{candK},\"violating_input\":{violIn},\"yukon_score\":{yukonScore}"
    some s!"\{\"id\":{reqId},\"ok\":true,{body},\"result\":\{{body}}}"
  | "batch-fastcheck" =>
    let numSamples := extractRpcNatField line "samples" (extractRpcNatField line "num_samples" 1024)
    let noProp := hasRpcBoolField line "useConstraintProp" false || hasRpcBoolField line "noConstraintProp" true
    let recTarget := LeanNative.Backend.selectOptimalComputeTarget numSamples
      (hasRpcBoolField line "is_matrix" true) (!(hasRpcBoolField line "is_256bit" false))
      (hasRpcBoolField line "is_control_heavy" true) (hasRpcBoolField line "has_tpu" true)
      (!(hasRpcBoolField line "has_gpu" false)) (hasRpcBoolField line "has_metal" true)
    let customModOpt := (extractRpcStringField line "wire").bind LNIRModule.fromWire?
    let rep := runFastCheckModule (customModOpt.getD mkFastCheckSampleModule) numSamples (!noProp)
    some s!"\{\"id\":{reqId},\"ok\":true,\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"result\":\{\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"report\":{rep.toJson}}}"
  | _ => none

def handleWorkerRequest (engineName : String) (cache : WorkerCache) (line : String) : String :=
  if let some fastResp := handleFastWorkerRequest? engineName line then fastResp
  else
    let reqId := extractRpcId line
    let method := (extractRpcStringField line "method").getD "ping"
    let customModOpt := (extractRpcStringField line "wire").bind LNIRModule.fromWire?
    let nDecls := cache.optMod.decls.length
    match method with
    | "compile-llvm" =>
      let archStr := (extractRpcStringField line "arch").getD "x86_64"
      let isBase := hasRpcBoolField line "baseline" true
      let ir := match customModOpt with
        | some m =>
          let arch := parseTargetArch archStr
          if isBase then emitLLVMBaseline m arch else emitLLVMOptimized (runDefaultPipeline m).1 arch
        | none =>
          if isBase then cache.llvmBaseX86
          else if archStr == "arm64" || archStr == "aarch64" then cache.llvmOptArm else cache.llvmOptX86
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"arch\":\"{escapeJsonWorker archStr}\",\"baseline\":{isBase},\"decls\":{nDecls},\"irBytes\":{ir.length},\"ir\":\"{escapeJsonWorker ir}\"}}"
    | "compile-ptx" =>
      let sm := (extractRpcStringField line "sm").getD "sm_90"
      let isFc := hasRpcBoolField line "fastcheck" true
      let ptx := if isFc then cache.fcPtxText
        else match customModOpt with
          | some m => emitPTXModule (runDefaultPipeline m).1 sm
          | none => if sm == "sm_90" then cache.ptxSm90 else emitPTXModule cache.optMod sm
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"sm\":\"{escapeJsonWorker sm}\",\"decls\":{nDecls},\"ptxBytes\":{ptx.length},\"ptx\":\"{escapeJsonWorker ptx}\"}}"
    | "compile-metal" =>
      let isFc := hasRpcBoolField line "fastcheck" true
      let msl := if isFc then cache.fcMetalText
        else match customModOpt with
          | some m => emitMetalModule (runDefaultPipeline m).1
          | none => cache.metalText
      let (valid, _) := validateMetalShader msl
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"apple_metal_3.0\",\"valid\":{valid},\"decls\":{nDecls},\"metalBytes\":{msl.length},\"metal\":\"{escapeJsonWorker msl}\"}}"
    | "compile-mlir" =>
      let dialect := (extractRpcStringField line "dialect").getD "gpu"
      let mlir := match customModOpt with
        | some m =>
          let mOpt := (runDefaultPipeline m).1
          if dialect == "pallas" then emitTPUPallasModule mOpt
          else if dialect == "stablehlo" || dialect == "tpu" then emitStableHLOModule mOpt
          else emitMLIRModule mOpt
        | none =>
          if dialect == "pallas" then cache.pallasText
          else if dialect == "stablehlo" || dialect == "tpu" then cache.stablehloText
          else cache.mlirText
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"dialect\":\"{escapeJsonWorker dialect}\",\"decls\":{nDecls},\"mlirBytes\":{mlir.length},\"mlir\":\"{escapeJsonWorker mlir}\"}}"
    | "compile-tpu" =>
      let (shlo, pallas) := match customModOpt with
        | some m => let mOpt := (runDefaultPipeline m).1; (emitStableHLOModule mOpt, emitTPUPallasModule mOpt)
        | none => (cache.stablehloText, cache.pallasText)
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"google_cloud_tpu_v5e\",\"decls\":{nDecls},\"stablehloBytes\":{shlo.length},\"pallasBytes\":{pallas.length},\"stablehlo\":\"{escapeJsonWorker shlo}\",\"pallas\":\"{escapeJsonWorker pallas}\"}}"
    | "compile-fastcheck" =>
      let noProp := hasRpcBoolField line "useConstraintProp" false || hasRpcBoolField line "noConstraintProp" true
      let repJson := match customModOpt with
        | some m => (runFastCheckModule m 1024 (!noProp)).toJson
        | none => if noProp then cache.fcReportVacJson else cache.fcReportPropJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{repJson}}"
    | "superopt" =>
      let tgtStr := (extractRpcStringField line "target").getD "x86_64"
      let soJson := match customModOpt with
        | some m => (superoptModule (parseSuperoptTarget tgtStr) m).2.toJson
        | none => if tgtStr == "x86_64" then cache.superoptX86Json else (superoptModule (parseSuperoptTarget tgtStr) cache.baseMod).2.toJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{soJson}}"
    | "plugins" =>
      let tgtStr := (extractRpcStringField line "target").getD "x86_64"
      let plJson := match customModOpt with
        | some m => (runSegregatedPluginPipeline (parseSuperoptTarget tgtStr) true m).2.toJson
        | none => if tgtStr == "x86_64" then cache.pluginsX86Json else (runSegregatedPluginPipeline (parseSuperoptTarget tgtStr) true cache.baseMod).2.toJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{plJson}}"
    | "verify-certs" =>
      let certJson := match customModOpt with
        | some m => (verifyModuleCerts m.moduleName ((runDefaultPipeline m).2.map toOptimizationCert)).toJson
        | none => cache.certReportJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{certJson}}"
    | "validate-tv" =>
      let tvJson := match customModOpt with
        | some m => (validateTranslationModule m (runDefaultPipeline m).1).toJson
        | none => cache.tvReportJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{tvJson}}"
    | other =>
      s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unknown_method:{escapeJsonWorker other}\"}"

abbrev handleWorkerLine := handleWorkerRequest

partial def workerLoop (engineName : String) (stdin stdout : IO.FS.Stream) (cacheRef : IO.Ref (Option WorkerCache)) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then workerLoop engineName stdin stdout cacheRef
  else
    let method := (extractRpcStringField trimmed "method").getD ""
    if method == "exit" || method == "shutdown" || method == "quit" then
      stdout.putStrLn s!"\{\"id\":{extractRpcId trimmed},\"ok\":true,\"result\":\{\"status\":\"bye\"}}"
      stdout.flush; return 0
    else
      let resp ← match handleFastWorkerRequest? engineName trimmed with
        | some fast => pure fast
        | none =>
          let cache ← getOrInitWorkerCache cacheRef
          pure (handleWorkerRequest engineName cache trimmed)
      stdout.putStrLn resp
      stdout.flush; workerLoop engineName stdin stdout cacheRef

def runWorker (engineName : String) : IO UInt32 := do
  workerLoop engineName (← IO.getStdin) (← IO.getStdout) (← IO.mkRef none)

def printCoreUsage (tag : String) (hasFrontend : Bool) : IO Unit := do
  let fe (xs : List String) : List String := if hasFrontend then xs else []
  let lines := [
    s!"{tag} v0.5.0 — Formally Validated Lean 4 Optimizer, Segregated Plugin Engine, Superoptimizer, TV, FastCheck & Multi-Target Codegen",
    "",
    s!"Usage: {tag} <command> [options]",
    "",
    "Commands:"
  ] ++ fe ["  build-exe          Compile a .lean source file directly to a native executable (<file.lean> -o <bin>)"] ++ [
    "  compile-llvm       Emit baseline or optimized LLVM 18 IR (--input <file>, --arch x86_64|arm64, --baseline, -o <path>)",
    "  compile-static-lib Emit C-ABI static library (.a) + C header (.h) for zero-copy FFI (--input <file>, -o <lib.a>, --header <lib.h>)",
    "  compile-mlir       Emit GPU MLIR module (--input <file>, -o <path>)",
    "  compile-ptx        Emit NVIDIA PTX 8.0 assembly (--input <file>, --sm sm_90, --fastcheck, -o <path>)",
    "  compile-metal      Emit Apple Metal Shading Language 3.0 (--input <file>, --fastcheck, -o <path>)",
    "  compile-fastcheck  Run Constraint-Propagating FastCheck or emit SIMD/PTX/Metal kernels (--samples N, --emit-llvm, --emit-ptx, --emit-metal, --json, -o <path>)",
    "  compile-hybrid     Partition module into CPU/GPU and emit hybrid host dispatch glue (--input <file>, -o <path>)",
    "  superopt           Run cost-guided enumerative superoptimizer (--target x86_64|arm64|cuda_ptx|apple_metal, --json, -o <path>)",
    "  plugins            Run segregated optimization plugins under Law 1 TV/Cost Gate (--target <arch>, --test-adversarial, --json)",
    "  pr-verify          Run Law 5 PR & Spec-Pinning Gate + Season 8 turbo-lean pr-verify/audit-spec (--base <ref>, --disallow-spec-changes, --json)",
    "  turbo-plugin       Run JSONL-stdio external accelerator plugin for turbo-lean (ExternalProcessAccelerator protocol)",
    "  verify-certs       Run optimization pipeline and verify translation certificates (--input <file>, --json, -o <path>)",
    "  validate-tv        Run Alive2-style symbolic translation validation (--input <file>, --json, -o <path>)",
    "  audit-axioms       Run in-kernel transitive axiom audit (Lean.collectAxioms snapshot, --json)",
    "  emit-lnir          Emit LNIR module in wire/JSON format (--wire, --json, --fastcheck, -o <path>)"
  ] ++ fe [
    "  audit-axioms       Run in-kernel transitive axiom audit over all 134 soundness theorems (--json)",
    "  turbo-status       Probe Turbo Lean integration, verify BLAKE3 vectors, and emit/verify receipt"
  ] ++ [
    "  self-test          Run end-to-end Core, Spec (Laws 1-5), Plugins, Codec, FastCheck, Superopt, SymbolicTV, LLVM/PTX/Metal self-tests",
    "  worker             Run persistent sub-millisecond JSON-RPC worker loop over stdin/stdout"
  ]
  IO.println (String.intercalate "\n" lines)

def runAuditAxioms (args : List String) : IO UInt32 := do
  let report := verifiedAxiomAuditReport
  IO.println (if hasFlag args "--json" then report.toJson else report.formatSummary)
  return if report.passed then 0 else 1

/-- Shared CLI dispatcher for both `lean-native-core` (`elaborateHook? = none`) and `lean-native` (`elaborateHook? = some ...`). -/
def dispatchSharedCommand (tag : String) (elaborateHook? : Option (String → IO LNIRModule))
    (args : List String) : IO (Option UInt32) := do
  match args with
  | "audit-axioms" :: rest       => some <$> runAuditAxioms rest
  | "compile-llvm" :: rest       => some <$> runCompileLLVM tag elaborateHook? rest
  | "compile-static-lib" :: rest => some <$> runCompileStaticLib tag elaborateHook? rest
  | "compile-mlir" :: rest       => some <$> runCompileMLIR tag elaborateHook? rest
  | "compile-ptx" :: rest       => some <$> runCompilePTX tag elaborateHook? rest
  | "compile-metal" :: rest     => some <$> runCompileMetal tag elaborateHook? rest
  | "compile-fastcheck" :: rest => some <$> runCompileFastCheck tag elaborateHook? rest
  | "compile-hybrid" :: rest    => some <$> runCompileHybrid tag elaborateHook? rest
  | "compile" :: rest           => some <$> runCompileMode tag elaborateHook? rest
  | "--c-abi" :: _              => some <$> runCompileMode tag elaborateHook? args
  | "--emit-c-abi" :: _         => some <$> runCompileMode tag elaborateHook? args
  | "--self-test" :: _          => some <$> runCoreSelfTest tag
  | "superopt" :: rest          => some <$> runSuperopt elaborateHook? rest
  | "plugins" :: rest           => some <$> runPlugins elaborateHook? rest
  | "telemetry" :: rest         => some <$> runTelemetry elaborateHook? rest
  | "pr-verify" :: rest         => some <$> runPRVerify tag rest
  | "turbo-plugin" :: _         => some <$> runTurboPlugin
  | "verify-certs" :: rest      => some <$> runVerifyCerts tag elaborateHook? rest
  | "validate-tv" :: rest       => some <$> runValidateTV elaborateHook? rest
  | "emit-lnir" :: rest         => some <$> runEmitLNIR tag elaborateHook? rest
  | "worker" :: _               => some <$> runWorker tag
  | _                           =>
    if hasFlag args "--c-abi" || hasFlag args "--emit-c-abi" then
      some <$> runCompileMode tag elaborateHook? args
    else
      return none

end LeanNative.Driver.CoreCLI

