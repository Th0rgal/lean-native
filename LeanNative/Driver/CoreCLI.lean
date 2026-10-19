import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
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

def runCompileMLIR (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let mlirText := emitMLIRModule optMod
  if outPath.isEmpty then
    IO.println mlirText
  else
    IO.FS.writeFile outPath mlirText
    IO.println s!"[{tag}] Wrote GPU MLIR module to {outPath}"
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
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let plan := partitionModule optMod 65536
  let glueText := emitHybridHostGlue plan
  if outPath.isEmpty then
    IO.println glueText
  else
    IO.FS.writeFile outPath glueText
    IO.println s!"[{tag}] Wrote Hybrid CPU/GPU dispatch glue (gpuDecls={plan.gpuDecls.length}, cpuDecls={plan.cpuOnlyDecls.length}) to {outPath}"
  return 0

def runSuperopt (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadInputModule elaborateHook? args
  let (_, report) := superoptModule target baseMod
  let jsonText := report.toJson
  if !outPath.isEmpty then IO.FS.writeFile outPath jsonText
  if jsonFlag then IO.println jsonText else IO.println report.formatSummary
  return 0

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
  IO.println s!"=== Lean Native ({tag} v0.4.0) Self-Test ==="
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
  let blake3Ok := blake3SelfTest

  IO.println s!"1. Canonical 8-Kernel Module       : {optMod.decls.length} declarations (incl. 256-bit EVM/Verity)"
  IO.println s!"2. LNIR Wire & JSON Round-Trip     : {if roundTripWireOk && roundTripJsonOk then "PASSED" else "FAILED"}"
  IO.println s!"3. Certificate Chain Verification  : {if certReport.verified then "PASSED" else "FAILED"} ({certReport.certs.length} certs)"
  IO.println s!"4. Alive2 Symbolic TV Validation   : {if tvReport.allPassed then "PASSED" else "FAILED"} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)"
  IO.println s!"5. Enumerative Superoptimizer      : {if superoptOk then "PASSED" else "FAILED"} ({soReportX86.rewritesApplied} rewrites, cost {soReportX86.totalCostBefore}->{soReportX86.totalCostAfter})"
  IO.println s!"6. FastCheck ConstraintProp vs Vac : {if fcPropOk && fcNaiveVacuousOk then "PASSED" else "FAILED"} (propCex={fcReportProp.counterexamplesFound}, naiveVacuous={fcReportNaive.vacuousPasses})"
  IO.println s!"7. Unified GPUIR & Apple Metal 3.0 : {if metalValid && fcMetalValid then "PASSED" else "FAILED"} ({gpuDescs.length} GPU descriptors, Metal={metalTxt.length}B)"
  IO.println s!"8. Pure-Lean RFC BLAKE3 Self-Test  : {if blake3Ok then "PASSED" else "FAILED"}"

  let allOk := roundTripWireOk && roundTripJsonOk && certReport.verified &&
    tvReport.allPassed && superoptOk && fcPropOk && fcNaiveVacuousOk &&
    metalValid && fcMetalValid && blake3Ok &&
    llvmX86.length > 500 && ptxTxt.length > 500 && fcLlvm.length > 200 && fcPtx.length > 200
  if allOk then
    IO.println s!"=== ALL {tag.toUpper} v0.4.0 SELF-TESTS PASSED ==="
    return 0
  else
    IO.println s!"=== {tag.toUpper} SELF-TEST FAILED ==="
    return 1

/-! ## Persistent Sub-Millisecond JSON-RPC Worker (`worker`) -/

private def escapeJsonWorker (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | other => acc.push other
  ) ""

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
  llvmOptX86       : String
  llvmOptArm       : String
  llvmBaseX86      : String
  ptxSm90          : String
  metalText        : String
  mlirText         : String
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
  let llvmOptX86 := emitLLVMOptimized optMod .x86_64
  let llvmOptArm := emitLLVMOptimized optMod .arm64
  let llvmBaseX86 := emitLLVMBaseline baseMod .x86_64
  let ptxSm90 := emitPTXModule optMod "sm_90"
  let metalText := emitMetalModule optMod
  let mlirText := emitMLIRModule optMod
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
    llvmOptX86
    llvmOptArm
    llvmBaseX86
    ptxSm90
    metalText
    mlirText
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
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"pong\",\"engine\":\"{engineName}\",\"version\":\"0.4.0\",\"decls\":{cache.optMod.decls.length}}}"
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
    let mlir :=
      match customModOpt with
      | some m =>
        let (mOpt, _) := runDefaultPipeline m
        emitMLIRModule mOpt
      | none => cache.mlirText
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"decls\":{cache.optMod.decls.length},\"mlirBytes\":{mlir.length},\"mlir\":\"{escapeJsonWorker mlir}\"}}"
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
  IO.println s!"{tag} v0.4.0 — Formally Validated Lean 4 Optimizer, Superoptimizer, TV, FastCheck & Multi-Target Codegen Engine"
  IO.println ""
  IO.println s!"Usage: {tag} <command> [options]"
  IO.println ""
  IO.println "Commands:"
  if hasFrontend then
    IO.println "  build-exe          Compile a .lean source file directly to a native executable (<file.lean> -o <bin>)"
  IO.println "  compile-llvm       Emit baseline or optimized LLVM 18 IR (--input <file>, --arch x86_64|arm64, --baseline, -o <path>)"
  IO.println "  compile-mlir       Emit GPU MLIR module (--input <file>, -o <path>)"
  IO.println "  compile-ptx        Emit NVIDIA PTX 8.0 assembly (--input <file>, --sm sm_90, --fastcheck, -o <path>)"
  IO.println "  compile-metal      Emit Apple Metal Shading Language 3.0 (--input <file>, --fastcheck, -o <path>)"
  IO.println "  compile-fastcheck  Run Constraint-Propagating FastCheck or emit SIMD/PTX/Metal kernels (--samples N, --emit-llvm, --emit-ptx, --emit-metal, --json, -o <path>)"
  IO.println "  compile-hybrid     Partition module into CPU/GPU and emit hybrid host dispatch glue (--input <file>, -o <path>)"
  IO.println "  superopt           Run cost-guided enumerative superoptimizer (--target x86_64|arm64|cuda_ptx|apple_metal, --json, -o <path>)"
  IO.println "  verify-certs       Run optimization pipeline and verify translation certificates (--input <file>, --json, -o <path>)"
  IO.println "  validate-tv        Run Alive2-style symbolic translation validation (--input <file>, --json, -o <path>)"
  IO.println "  emit-lnir          Emit LNIR module in wire/JSON format (--wire, --json, --fastcheck, -o <path>)"
  if hasFrontend then
    IO.println "  audit-axioms       Run in-kernel transitive axiom audit over all soundness theorems (--json)"
    IO.println "  turbo-status       Probe Turbo Lean integration, verify BLAKE3 vectors, and emit/verify receipt"
  IO.println "  self-test          Run end-to-end Core, Codec, FastCheck, Superopt, SymbolicTV, CertChecker, LLVM/PTX/Metal self-tests"
  IO.println "  worker             Run persistent sub-millisecond JSON-RPC worker loop over stdin/stdout"

/-- Shared CLI dispatcher for both `lean-native-core` (`elaborateHook? = none`) and `lean-native` (`elaborateHook? = some ...`). -/
def dispatchSharedCommand (tag : String) (elaborateHook? : Option (String → IO LNIRModule))
    (args : List String) : IO (Option UInt32) := do
  match args with
  | "compile-llvm" :: rest      => some <$> runCompileLLVM tag elaborateHook? rest
  | "compile-mlir" :: rest      => some <$> runCompileMLIR tag elaborateHook? rest
  | "compile-ptx" :: rest       => some <$> runCompilePTX tag elaborateHook? rest
  | "compile-metal" :: rest     => some <$> runCompileMetal tag elaborateHook? rest
  | "compile-fastcheck" :: rest => some <$> runCompileFastCheck tag elaborateHook? rest
  | "compile-hybrid" :: rest    => some <$> runCompileHybrid tag elaborateHook? rest
  | "superopt" :: rest          => some <$> runSuperopt elaborateHook? rest
  | "verify-certs" :: rest      => some <$> runVerifyCerts tag elaborateHook? rest
  | "validate-tv" :: rest       => some <$> runValidateTV elaborateHook? rest
  | "emit-lnir" :: rest         => some <$> runEmitLNIR tag elaborateHook? rest
  | "worker" :: _               => some <$> runWorker tag
  | _                           => return none

end LeanNative.Driver.CoreCLI
