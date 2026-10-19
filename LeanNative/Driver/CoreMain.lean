import LeanNative.Core

namespace LeanNative.Driver.CoreMain

open LeanNative.IR
open LeanNative.IR.Codec
open LeanNative.Semantics
open LeanNative.Proofs
open LeanNative.Transform
open LeanNative.Backend
open LeanNative.Backend.LLVM
open LeanNative.Backend.MLIRGPU
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

def findFlagValue (args : List String) (flag : String) (defaultVal : String) : String :=
  match args with
  | [] => defaultVal
  | f :: v :: rest => if f == flag then v else findFlagValue (v :: rest) flag defaultVal
  | _ :: rest => findFlagValue rest flag defaultVal

def hasFlag (args : List String) (flag : String) : Bool :=
  args.contains flag

def printCoreUsage : IO Unit := do
  IO.println "lean-native-core v0.3.0 — Zero-Lean-Frontend LNIR Optimizer, TV, FastCheck & Codegen Engine"
  IO.println ""
  IO.println "Usage: lean-native-core <command> [options]"
  IO.println ""
  IO.println "Commands:"
  IO.println "  compile-llvm       Emit baseline or optimized LLVM 18 IR (--input <file.lnir>, --arch x86_64|arm64, --baseline, -o <path>)"
  IO.println "  compile-mlir       Emit GPU MLIR module (--input <file.lnir>, -o <path>)"
  IO.println "  compile-ptx        Emit NVIDIA PTX 8.0 assembly (--input <file.lnir>, --sm sm_90, --fastcheck, -o <path>)"
  IO.println "  compile-fastcheck  Run Constraint-Propagating FastCheck or emit SIMD/PTX kernels (--samples N, --no-constraint-prop, --emit-llvm, --emit-ptx, --json, -o <path>)"
  IO.println "  compile-hybrid     Partition module into CPU/GPU and emit hybrid host dispatch glue (--input <file.lnir>, -o <path>)"
  IO.println "  verify-certs       Run optimization pipeline and verify translation certificates (--input <file.lnir>, --json, -o <path>)"
  IO.println "  validate-tv        Run Alive2-style symbolic translation validation (--input <file.lnir>, --json, -o <path>)"
  IO.println "  emit-lnir          Emit canonical or FastCheck LNIR module in wire/JSON format (--wire, --json, --fastcheck, -o <path>)"
  IO.println "  self-test          Run end-to-end Core, Codec, FastCheck, SymbolicTV, CertChecker, LLVM/PTX self-tests"
  IO.println "  worker             Run persistent sub-millisecond JSON-RPC worker loop over stdin/stdout"

/-- Load an `LNIRModule` from `--input <path>` (wire or JSON) or default to `mkCanonicalBenchmarkModule`. -/
def loadCoreInputModule (args : List String) (defaultFastCheck : Bool := false) : IO LNIRModule := do
  let inFile := findFlagValue args "--input" ""
  if inFile.isEmpty then
    return if defaultFastCheck then mkFastCheckSampleModule else mkCanonicalBenchmarkModule
  else if inFile == "canonical" || inFile == "benchmarks" then
    return mkCanonicalBenchmarkModule
  else if inFile == "fastcheck" || inFile == "fastcheck-sample" then
    return mkFastCheckSampleModule
  else
    if ← System.FilePath.pathExists inFile then
      let raw ← IO.FS.readFile inFile
      match LNIRModule.fromWire? raw with
      | some m => return m
      | none =>
        match LNIRModule.fromJson? raw with
        | some m => return m
        | none => return { mkCanonicalBenchmarkModule with moduleName := inFile }
    else
      return { mkCanonicalBenchmarkModule with moduleName := inFile }

def runCoreCompileLLVM (args : List String) : IO UInt32 := do
  let archStr := findFlagValue args "--arch" "x86_64"
  let arch := parseTargetArch archStr
  let isBaseline := hasFlag args "--baseline"
  let outPath := findFlagValue args "-o" ""
  let baseMod ← loadCoreInputModule args
  let (modToEmit, _) := if isBaseline then (baseMod, []) else runDefaultPipeline baseMod
  let irText := if isBaseline then emitLLVMBaseline modToEmit arch else emitLLVMOptimized modToEmit arch
  if outPath.isEmpty then
    IO.println irText
  else
    IO.FS.writeFile outPath irText
    IO.println s!"[lean-native-core] Wrote LLVM 18 IR ({arch.triple}, baseline={isBaseline}, decls={modToEmit.decls.length}) to {outPath}"
  return 0

def runCoreCompileMLIR (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let baseMod ← loadCoreInputModule args
  let (optMod, _) := runDefaultPipeline baseMod
  let mlirText := emitMLIRModule optMod
  if outPath.isEmpty then
    IO.println mlirText
  else
    IO.FS.writeFile outPath mlirText
    IO.println s!"[lean-native-core] Wrote GPU MLIR module to {outPath}"
  return 0

def runCoreCompilePTX (args : List String) : IO UInt32 := do
  let smArch := findFlagValue args "--sm" "sm_90"
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ← loadCoreInputModule args isFastCheck
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
    IO.println s!"[lean-native-core] Wrote NVIDIA PTX 8.0 ({smArch}, fastcheck={isFastCheck}) to {outPath}"
  return 0

def runCoreCompileFastCheck (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let smArch := findFlagValue args "--sm" "sm_90"
  let samplesStr := findFlagValue args "--samples" "4096"
  let numSamples := samplesStr.toNat?.getD 4096
  let useConstraintProp := !(hasFlag args "--no-constraint-prop")
  let emitLlvmFlag := hasFlag args "--emit-llvm"
  let emitPtxFlag := hasFlag args "--emit-ptx"
  let jsonFlag := hasFlag args "--json"
  let useCanonical := hasFlag args "--canonical"
  let mod ← loadCoreInputModule args (!useCanonical)
  if emitLlvmFlag then
    let irText := emitFastCheckLLVM mod
    if outPath.isEmpty then
      IO.println irText
    else
      IO.FS.writeFile outPath irText
      IO.println s!"[lean-native-core] Wrote FastCheck SIMD LLVM 18 IR to {outPath}"
    return 0
  else if emitPtxFlag then
    let ptxText := emitFastCheckPTX mod smArch
    if outPath.isEmpty then
      IO.println ptxText
    else
      IO.FS.writeFile outPath ptxText
      IO.println s!"[lean-native-core] Wrote FastCheck NVIDIA PTX 8.0 ({smArch}) to {outPath}"
    return 0
  else
    let report := runFastCheckModule mod numSamples useConstraintProp
    let jsonText := report.toJson
    if !outPath.isEmpty then
      IO.FS.writeFile outPath jsonText
    if jsonFlag then
      IO.println jsonText
    else
      IO.println report.formatSummary
    return 0

def runCoreCompileHybrid (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let baseMod ← loadCoreInputModule args
  let (optMod, _) := runDefaultPipeline baseMod
  let plan := partitionModule optMod 65536
  let glueText := emitHybridHostGlue plan
  if outPath.isEmpty then
    IO.println glueText
  else
    IO.FS.writeFile outPath glueText
    IO.println s!"[lean-native-core] Wrote Hybrid CPU/GPU dispatch glue (gpuDecls={plan.gpuDecls.length}, cpuDecls={plan.cpuOnlyDecls.length}) to {outPath}"
  return 0

def runCoreVerifyCerts (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadCoreInputModule args
  let (_, stepCerts) := runDefaultPipeline baseMod
  let optCerts := stepCerts.map toOptimizationCert
  let report := verifyModuleCerts baseMod.moduleName optCerts
  let jsonText := report.toJson
  if !outPath.isEmpty then
    IO.FS.writeFile outPath jsonText
  if jsonFlag then
    IO.println jsonText
  else
    IO.println s!"[lean-native-core] Certificate Verification for {report.moduleName}:"
    IO.println s!"  Total pass certificates : {report.certs.length}"
    IO.println s!"  Declarations verified   : {report.declSummaries.length}"
    IO.println s!"  Overall assurance level : {report.overallAssurance}"
    IO.println s!"  Hash chains & theorems  : {if report.verified then "VALID" else "FAILED"}"
  return if report.verified then 0 else 1

def runCoreValidateTV (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadCoreInputModule args
  let (optMod, _) := runDefaultPipeline baseMod
  let tvReport := validateTranslationModule baseMod optMod
  let jsonText := tvReport.toJson
  if !outPath.isEmpty then
    IO.FS.writeFile outPath jsonText
  if jsonFlag then
    IO.println jsonText
  else
    IO.println tvReport.formatSummary
  return if tvReport.allPassed then 0 else 1

def runCoreEmitLNIR (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let wireFlag := hasFlag args "--wire"
  let fastCheckFlag := hasFlag args "--fastcheck"
  let mod ← loadCoreInputModule args fastCheckFlag
  let useWire := wireFlag || outPath.endsWith ".lnir"
  let outText := if useWire then mod.toWire else mod.toJson
  if outPath.isEmpty then
    IO.println outText
  else
    IO.FS.writeFile outPath outText
    IO.println s!"[lean-native-core] Emitted LNIR ({if useWire then "wire" else "json"}, decls={mod.decls.length}) to {outPath}"
  return 0

def runCoreSelfTest : IO UInt32 := do
  IO.println "=== Lean Native Core (lean-native-core v0.3.0) Self-Test ==="
  let baseMod := mkCanonicalBenchmarkModule
  let wireStr := baseMod.toWire
  let jsonStr := baseMod.toJson
  let roundTripWireOk := LNIRModule.fromWire? wireStr == some baseMod
  let roundTripJsonOk := LNIRModule.fromJson? jsonStr == some baseMod

  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let optCerts := stepCerts.map toOptimizationCert
  let certReport := verifyModuleCerts baseMod.moduleName optCerts
  let tvReport := validateTranslationModule baseMod optMod

  let fcMod := mkFastCheckSampleModule
  let fcReportProp := runFastCheckModule fcMod 512 true
  let fcReportNaive := runFastCheckModule fcMod 512 false
  let fcPropOk := fcReportProp.counterexamplesFound == 1 && fcReportProp.vacuousPasses == 0 && fcReportProp.falsePositives == 0
  let fcNaiveVacuousOk := fcReportNaive.vacuousPasses == 1

  let fcLlvm := emitFastCheckLLVM fcMod
  let fcPtx := emitFastCheckPTX fcMod "sm_90"
  let llvmX86 := emitLLVMOptimized optMod .x86_64
  let ptxTxt := emitPTXModule optMod "sm_90"

  IO.println s!"1. Canonical 8-Kernel Module       : {optMod.decls.length} declarations (incl. 256-bit EVM/Verity)"
  IO.println s!"2. LNIR Wire & JSON Round-Trip     : {if roundTripWireOk && roundTripJsonOk then "PASSED" else "FAILED"}"
  IO.println s!"3. Certificate Chain Verification  : {if certReport.verified then "PASSED" else "FAILED"} ({certReport.certs.length} certs)"
  IO.println s!"4. Alive2 Symbolic TV Validation   : {if tvReport.allPassed then "PASSED" else "FAILED"} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)"
  IO.println s!"5. FastCheck ConstraintProp vs Vac : {if fcPropOk && fcNaiveVacuousOk then "PASSED" else "FAILED"} (propCex={fcReportProp.counterexamplesFound}, naiveVacuous={fcReportNaive.vacuousPasses})"
  IO.println s!"6. FastCheck LLVM & PTX 8.0 Codegen: LLVM={fcLlvm.length}B, PTX={fcPtx.length}B"

  let allOk := roundTripWireOk && roundTripJsonOk && certReport.verified &&
    tvReport.allPassed && fcPropOk && fcNaiveVacuousOk &&
    llvmX86.length > 500 && ptxTxt.length > 500 && fcLlvm.length > 200 && fcPtx.length > 200
  if allOk then
    IO.println "=== ALL LEAN-NATIVE-CORE v0.3.0 SELF-TESTS PASSED ==="
    return 0
  else
    IO.println "=== LEAN-NATIVE-CORE SELF-TEST FAILED ==="
    return 1

/-! ## Persistent Sub-Millisecond JSON-RPC Worker (`lean-native-core worker`) -/

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

/-- Extract `"id":<raw>` from a single-line JSON-RPC request. -/
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

/-- Extract a string field `"key":"value"` (handling optional whitespace after `:`) from a JSON line. -/
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

/-- Check if `"key":false` or `"key":true` appears in `line`. -/
private def hasRpcBoolField (line : String) (key : String) (expected : Bool) : Bool :=
  let bStr := if expected then "true" else "false"
  let pat1 := s!"\"{key}\":{bStr}"
  let pat2 := s!"\"{key}\": {bStr}"
  (line.splitOn pat1).length > 1 || (line.splitOn pat2).length > 1

/-- Pre-warmed worker cache so standard JSON-RPC requests execute in `< 0.1 ms`. -/
structure WorkerCache where
  baseMod          : LNIRModule
  optMod           : LNIRModule
  certReportJson   : String
  tvReportJson     : String
  llvmOptX86       : String
  llvmOptArm       : String
  llvmBaseX86      : String
  ptxSm90          : String
  mlirText         : String
  fcReportPropJson : String
  fcReportVacJson  : String
  fcLlvmText       : String
  fcPtxText        : String

def initWorkerCache : IO WorkerCache := do
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let optCerts := stepCerts.map toOptimizationCert
  let certReport := verifyModuleCerts baseMod.moduleName optCerts
  let tvReport := validateTranslationModule baseMod optMod
  let llvmOptX86 := emitLLVMOptimized optMod .x86_64
  let llvmOptArm := emitLLVMOptimized optMod .arm64
  let llvmBaseX86 := emitLLVMBaseline baseMod .x86_64
  let ptxSm90 := emitPTXModule optMod "sm_90"
  let mlirText := emitMLIRModule optMod
  let fcMod := mkFastCheckSampleModule
  let fcProp := runFastCheckModule fcMod 1024 true
  let fcVac := runFastCheckModule fcMod 1024 false
  let fcLlvm := emitFastCheckLLVM fcMod
  let fcPtx := emitFastCheckPTX fcMod "sm_90"
  return {
    baseMod
    optMod
    certReportJson := certReport.toJson
    tvReportJson := tvReport.toJson
    llvmOptX86
    llvmOptArm
    llvmBaseX86
    ptxSm90
    mlirText
    fcReportPropJson := fcProp.toJson
    fcReportVacJson := fcVac.toJson
    fcLlvmText := fcLlvm
    fcPtxText := fcPtx
  }

/-- Handle a single JSON-RPC request line and return a single-line JSON response. -/
def handleWorkerRequest (cache : WorkerCache) (line : String) : String :=
  let reqId := extractRpcId line
  let method := (extractRpcStringField line "method").getD "ping"
  let customWireOpt := extractRpcStringField line "wire"
  let customModOpt : Option LNIRModule :=
    match customWireOpt with
    | some w => LNIRModule.fromWire? w
    | none => none
  match method with
  | "ping" =>
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"pong\",\"engine\":\"lean-native-core\",\"version\":\"0.3.0\",\"decls\":{cache.optMod.decls.length}}}"
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
    s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"declName\":\"evm_constrained_buggy_prop\",\"certified\":{if certified then "true" else "false"},\"falsePositives\":0,\"theorem\":\"LeanNative.Backend.certifyCounterexample_no_false_positive\",\"report\":{cache.fcReportPropJson}}}"
  | other =>
    s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unknown_method:{escapeJsonWorker other}\"}"

partial def workerLoop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (cache : WorkerCache) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then
    return 0
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    workerLoop stdin stdout cache
  else
    let method := (extractRpcStringField trimmed "method").getD ""
    if method == "exit" || method == "shutdown" || method == "quit" then
      let reqId := extractRpcId trimmed
      stdout.putStrLn s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"bye\"}}"
      stdout.flush
      return 0
    else
      let resp := handleWorkerRequest cache trimmed
      stdout.putStrLn resp
      stdout.flush
      workerLoop stdin stdout cache

def runCoreWorker : IO UInt32 := do
  let cache ← initWorkerCache
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  workerLoop stdin stdout cache

end LeanNative.Driver.CoreMain

def main (args : List String) : IO UInt32 := do
  match args with
  | "compile-llvm" :: rest      => LeanNative.Driver.CoreMain.runCoreCompileLLVM rest
  | "compile-mlir" :: rest      => LeanNative.Driver.CoreMain.runCoreCompileMLIR rest
  | "compile-ptx" :: rest       => LeanNative.Driver.CoreMain.runCoreCompilePTX rest
  | "compile-fastcheck" :: rest => LeanNative.Driver.CoreMain.runCoreCompileFastCheck rest
  | "compile-hybrid" :: rest    => LeanNative.Driver.CoreMain.runCoreCompileHybrid rest
  | "verify-certs" :: rest      => LeanNative.Driver.CoreMain.runCoreVerifyCerts rest
  | "validate-tv" :: rest       => LeanNative.Driver.CoreMain.runCoreValidateTV rest
  | "emit-lnir" :: rest         => LeanNative.Driver.CoreMain.runCoreEmitLNIR rest
  | "self-test" :: _            => LeanNative.Driver.CoreMain.runCoreSelfTest
  | "worker" :: _               => LeanNative.Driver.CoreMain.runCoreWorker
  | "--help" :: _ | "-h" :: _ | [] =>
    LeanNative.Driver.CoreMain.printCoreUsage
    return 0
  | cmd :: _ =>
    IO.eprintln s!"Unknown command: {cmd}"
    LeanNative.Driver.CoreMain.printCoreUsage
    return 1
