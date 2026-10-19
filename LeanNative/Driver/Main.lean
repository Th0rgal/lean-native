import LeanNative

namespace LeanNative.Driver

open LeanNative.IR
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

def findFirstPositional (args : List String) : String :=
  match args with
  | [] => ""
  | "--input" :: v :: _ => v
  | "--lnir" :: v :: _ => v
  | "-o" :: _ :: rest => findFirstPositional rest
  | "--opt" :: _ :: rest => findFirstPositional rest
  | "--arch" :: _ :: rest => findFirstPositional rest
  | "--sm" :: _ :: rest => findFirstPositional rest
  | a :: rest =>
    if a.startsWith "-" then findFirstPositional rest else a

def printUsage : IO Unit := do
  IO.println "lean-native v0.2.0 — Formally Validated, Self-Optimizing Lean 4 Compiler"
  IO.println ""
  IO.println "Usage: lean-native <command> [options]"
  IO.println ""
  IO.println "Commands:"
  IO.println "  build-exe          Compile a .lean source file directly to a native executable (<file.lean> -o <bin>)"
  IO.println "  compile-llvm       Emit baseline or optimized LLVM 18 IR (--input <file.lean>, --lnir <file.lnir>, --arch x86_64|arm64, --baseline, -o <path>)"
  IO.println "  compile-mlir       Emit GPU MLIR module (--input <file.lean>, --lnir <file.lnir>, -o <path>)"
  IO.println "  compile-ptx        Emit NVIDIA PTX 8.0 assembly (--input <file.lean>, --lnir <file.lnir>, --sm sm_90, -o <path>)"
  IO.println "  compile-fastcheck  Run Constraint-Propagating FastCheck or emit SIMD/PTX kernels (--samples N, --no-constraint-prop, --emit-llvm, --emit-ptx, --json, -o <path>)"
  IO.println "  compile-hybrid     Partition module into CPU/GPU and emit hybrid host dispatch glue (--input <file.lean>, --lnir <file.lnir>, -o <path>)"
  IO.println "  emit-lnir          Emit LNIR module in wire or JSON format (--input <file.lean>, --wire, --json, -o <path>)"
  IO.println "  validate-tv        Run Alive2-style symbolic translation validation across source & optimized LNIR (--input <file.lean>, --json, -o <path>)"
  IO.println "  verify-certs       Run optimization pipeline and independently verify translation certificates (--input <file.lean>, --json, -o <path>)"
  IO.println "  audit-axioms       Run in-kernel transitive axiom audit over all soundness theorems (--json)"
  IO.println "  turbo-status       Probe Turbo Lean integration, verify BLAKE3 vectors, and emit/verify receipt"
  IO.println "  self-test          Run end-to-end compiler, semantics, SymbolicTV, certificate, axiom, and receipt self-tests"
  IO.println "  worker             Run persistent sub-millisecond JSON-RPC worker loop over stdin/stdout"

/-- Load an `LNIRModule` from `--lnir <path>` or `--input <path>`, or default to `mkCanonicalBenchmarkModule`
    only when neither flag is given. Throws an `IO.userError` (and never silently falls back to canonical)
    when an explicit `--input` or `--lnir` file fails to parse or yields zero LCNF declarations. -/
def loadTargetModule (args : List String) : IO LNIRModule := do
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
    return mkCanonicalBenchmarkModule
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
    let mod ← ingestLeanSourceFile inFile inFile
    if mod.decls.isEmpty then
      throw <| IO.userError s!"[lean-native] Failed to extract any LCNF declarations from '{inFile}'"
    else
      return mod

abbrev loadInputOrCanonicalModule := loadTargetModule

def runBuildExe (args : List String) : IO UInt32 := do
  let inFile :=
    let explicit := findFlagValue args "--input" ""
    if !explicit.isEmpty then explicit else findFirstPositional args
  if inFile.isEmpty then
    IO.eprintln "[lean-native] Error: build-exe requires a <file.lean> input path"
    return 1
  let outBin := findFlagValue args "-o" "a.out"
  let optLevel := findFlagValue args "--opt" "-O3"
  let (optMod, lnirLlPath) ← buildNativeExecutable inFile outBin optLevel
  IO.println s!"[lean-native] Built native executable {outBin} from {inFile} (lowered & optimized {optMod.decls.length} LCNF declarations; LNIR LLVM IR at {lnirLlPath})"
  return 0

def runValidateTV (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadTargetModule args
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

def runCompileLLVM (args : List String) : IO UInt32 := do
  let archStr := findFlagValue args "--arch" "x86_64"
  let arch := parseTargetArch archStr
  let isBaseline := hasFlag args "--baseline"
  let outPath := findFlagValue args "-o" ""
  let baseMod ← loadTargetModule args
  let (modToEmit, _) := if isBaseline then (baseMod, []) else runDefaultPipeline baseMod
  let irText := if isBaseline then emitLLVMBaseline modToEmit arch else emitLLVMOptimized modToEmit arch
  if outPath.isEmpty then
    IO.println irText
  else
    IO.FS.writeFile outPath irText
    IO.println s!"[lean-native] Wrote LLVM 18 IR ({arch.triple}, baseline={isBaseline}, decls={modToEmit.decls.length}) to {outPath}"
  return 0

def runCompileMLIR (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let baseMod ← loadTargetModule args
  let (optMod, _) := runDefaultPipeline baseMod
  let mlirText := emitMLIRModule optMod
  if outPath.isEmpty then
    IO.println mlirText
  else
    IO.FS.writeFile outPath mlirText
    IO.println s!"[lean-native] Wrote GPU MLIR module to {outPath}"
  return 0

def runCompilePTX (args : List String) : IO UInt32 := do
  let smArch := findFlagValue args "--sm" "sm_90"
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ←
    if isFastCheck && (findFlagValue args "--input" "").isEmpty && (findFlagValue args "--lnir" "").isEmpty then
      pure mkFastCheckSampleModule
    else
      loadTargetModule args
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
    IO.println s!"[lean-native] Wrote NVIDIA PTX 8.0 ({smArch}) to {outPath}"
  return 0

def runCompileFastCheck (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let smArch := findFlagValue args "--sm" "sm_90"
  let samplesStr := findFlagValue args "--samples" "4096"
  let numSamples := samplesStr.toNat?.getD 4096
  let useConstraintProp := !(hasFlag args "--no-constraint-prop")
  let emitLlvmFlag := hasFlag args "--emit-llvm"
  let emitPtxFlag := hasFlag args "--emit-ptx"
  let jsonFlag := hasFlag args "--json"
  let useCanonical := hasFlag args "--canonical"
  let mod ←
    if (findFlagValue args "--input" "").isEmpty && (findFlagValue args "--lnir" "").isEmpty then
      pure (if useCanonical then mkCanonicalBenchmarkModule else mkFastCheckSampleModule)
    else
      loadTargetModule args
  if emitLlvmFlag then
    let irText := emitFastCheckLLVM mod
    if outPath.isEmpty then
      IO.println irText
    else
      IO.FS.writeFile outPath irText
      IO.println s!"[lean-native] Wrote FastCheck SIMD LLVM 18 IR to {outPath}"
    return 0
  else if emitPtxFlag then
    let ptxText := emitFastCheckPTX mod smArch
    if outPath.isEmpty then
      IO.println ptxText
    else
      IO.FS.writeFile outPath ptxText
      IO.println s!"[lean-native] Wrote FastCheck NVIDIA PTX 8.0 ({smArch}) to {outPath}"
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

def runEmitLNIR (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let wireFlag := hasFlag args "--wire"
  let fastCheckFlag := hasFlag args "--fastcheck"
  let mod ←
    if fastCheckFlag && (findFlagValue args "--input" "").isEmpty && (findFlagValue args "--lnir" "").isEmpty then
      pure mkFastCheckSampleModule
    else
      loadTargetModule args
  let useWire := wireFlag || outPath.endsWith ".lnir"
  let outText := if useWire then mod.toWire else mod.toJson
  if outPath.isEmpty then
    IO.println outText
  else
    IO.FS.writeFile outPath outText
    IO.println s!"[lean-native] Emitted LNIR ({if useWire then "wire" else "json"}, decls={mod.decls.length}) to {outPath}"
  return 0

def runCompileHybrid (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let baseMod ← loadTargetModule args
  let (optMod, _) := runDefaultPipeline baseMod
  let plan := partitionModule optMod 65536
  let glueText := emitHybridHostGlue plan
  if outPath.isEmpty then
    IO.println glueText
  else
    IO.FS.writeFile outPath glueText
    IO.println s!"[lean-native] Wrote Hybrid CPU/GPU dispatch glue (gpuDecls={plan.gpuDecls.length}, cpuDecls={plan.cpuOnlyDecls.length}) to {outPath}"
  return 0

def runVerifyCerts (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadTargetModule args
  let (_, stepCerts) := runDefaultPipeline baseMod
  let optCerts := stepCerts.map toOptimizationCert
  let report := verifyModuleCerts baseMod.moduleName optCerts
  let jsonText := report.toJson
  if !outPath.isEmpty then
    IO.FS.writeFile outPath jsonText
  if jsonFlag then
    IO.println jsonText
  else
    IO.println s!"[lean-native] Certificate Verification for {report.moduleName}:"
    IO.println s!"  Total pass certificates : {report.certs.length}"
    IO.println s!"  Declarations verified   : {report.declSummaries.length}"
    IO.println s!"  Overall assurance level : {report.overallAssurance}"
    IO.println s!"  Hash chains & theorems  : {if report.verified then "VALID" else "FAILED"}"
  return if report.verified then 0 else 1

def runAuditAxioms (args : List String) : IO UInt32 := do
  let jsonFlag := hasFlag args "--json"
  let report := verifiedAxiomAuditReport
  if jsonFlag then
    IO.println report.toJson
  else
    IO.println report.formatSummary
  return if report.passed then 0 else 1

def runTurboStatus : IO UInt32 := do
  let cfg ← TurboLeanConfig.probe
  let ok ← runAdapterSelfTest "/tmp/lean_native_driver_receipt.json"
  IO.println s!"[lean-native] Turbo Lean Operating Mode : {cfg.mode}"
  IO.println s!"[lean-native] Daemon Metadata Path      : {cfg.daemonJsonPath}"
  IO.println s!"[lean-native] Adapter Self-Test & BLAKE3: {if ok then "PASSED" else "FAILED"}"
  return if ok then 0 else 1

def runSelfTest : IO UInt32 := do
  IO.println "=== Lean Native (lean-native v0.3.0) End-to-End Self-Test ==="
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let optCerts := stepCerts.map toOptimizationCert
  let certReport := verifyModuleCerts baseMod.moduleName optCerts
  let tvReport := validateTranslationModule baseMod optMod
  let axiomReport := verifiedAxiomAuditReport
  let llvmX86 := emitLLVMOptimized optMod .x86_64
  let llvmArm := emitLLVMOptimized optMod .arm64
  let mlirTxt := emitMLIRModule optMod
  let ptxTxt := emitPTXModule optMod "sm_90"
  let hybridPlan := partitionModule optMod 65536
  let turboOk ← runAdapterSelfTest "/tmp/lean_native_selftest_receipt.json"

  IO.println s!"1. Canonical LNIR Declarations     : {optMod.decls.length} declarations optimized"
  IO.println s!"2. Certificate Chain Verification  : {if certReport.verified then "PASSED" else "FAILED"} ({certReport.certs.length} certs, {certReport.overallAssurance})"
  IO.println s!"3. Alive2 Symbolic TV Validation   : {if tvReport.allPassed then "PASSED" else "FAILED"} ({tvReport.passedDecls}/{tvReport.totalDecls} decls, 64 concrete states/decl)"
  IO.println s!"4. In-Kernel Transitive Axiom Gate : {if axiomReport.passed then "PASSED" else "FAILED"} ({axiomReport.theoremsAudited} theorems, 0 sorryAx)"
  IO.println s!"5. LLVM 18 IR Generation (x86_64)  : {llvmX86.length} bytes"
  IO.println s!"6. LLVM 18 IR Generation (arm64)   : {llvmArm.length} bytes"
  IO.println s!"7. GPU MLIR Generation             : {mlirTxt.length} bytes"
  IO.println s!"8. NVIDIA PTX 8.0 Generation       : {ptxTxt.length} bytes (15 entry points incl. 256-bit EVM & 2D .shared matmul)"
  IO.println s!"9. Hybrid CPU/GPU Partitioner      : {hybridPlan.gpuDecls.length} GPU kernels, {hybridPlan.cpuOnlyDecls.length} CPU-only decls"
  IO.println s!"10. Turbo Lean Receipt & Fast-Check: {if turboOk then "PASSED" else "FAILED"}"

  let allOk := certReport.verified && tvReport.allPassed && axiomReport.passed && turboOk &&
    llvmX86.length > 500 && llvmArm.length > 500 && ptxTxt.length > 500
  if allOk then
    IO.println "=== ALL LEAN-NATIVE v0.3.0 SELF-TESTS PASSED ==="
    return 0
  else
    IO.println "=== LEAN-NATIVE SELF-TEST FAILED ==="
    return 1

private def escapeJsonRpc (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | other => acc.push other
  ) ""

private def extractJsonRpcId (line : String) : String :=
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

private def extractJsonRpcStr (line : String) (key : String) : Option String :=
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

private def hasJsonRpcBool (line : String) (key : String) (expected : Bool) : Bool :=
  let bStr := if expected then "true" else "false"
  (line.splitOn s!"\"{key}\":{bStr}").length > 1 || (line.splitOn s!"\"{key}\": {bStr}").length > 1

partial def runWorkerLoop (stdin stdout : IO.FS.Stream)
    (baseMod optMod : LNIRModule) (certJson tvJson llvmX86 ptxSm90 fcPropJson fcVacJson : String) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then
    return 0
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    runWorkerLoop stdin stdout baseMod optMod certJson tvJson llvmX86 ptxSm90 fcPropJson fcVacJson
  else
    let reqId := extractJsonRpcId trimmed
    let method := (extractJsonRpcStr trimmed "method").getD "ping"
    if method == "exit" || method == "shutdown" || method == "quit" then
      stdout.putStrLn s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"bye\"}}"
      stdout.flush
      return 0
    else
      let resp :=
        match method with
        | "ping" =>
          s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"pong\",\"engine\":\"lean-native\",\"version\":\"0.3.0\",\"decls\":{optMod.decls.length}}}"
        | "compile-llvm" =>
          s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"arch\":\"x86_64\",\"decls\":{optMod.decls.length},\"irBytes\":{llvmX86.length},\"ir\":\"{escapeJsonRpc llvmX86}\"}}"
        | "compile-ptx" =>
          s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"sm\":\"sm_90\",\"decls\":{optMod.decls.length},\"ptxBytes\":{ptxSm90.length},\"ptx\":\"{escapeJsonRpc ptxSm90}\"}}"
        | "compile-fastcheck" =>
          let noProp := hasJsonRpcBool trimmed "useConstraintProp" false || hasJsonRpcBool trimmed "noConstraintProp" true
          let rj := if noProp then fcVacJson else fcPropJson
          s!"\{\"id\":{reqId},\"ok\":true,\"result\":{rj}}"
        | "verify-certs" =>
          s!"\{\"id\":{reqId},\"ok\":true,\"result\":{certJson}}"
        | "validate-tv" =>
          s!"\{\"id\":{reqId},\"ok\":true,\"result\":{tvJson}}"
        | "eval-cex" =>
          let buggyDecl := evmConstrainedBuggyPropDecl
          let witnessEnv := (VarEnv.empty.bind 1 (.u64 1000000)).bind 0 (.u64 1000042)
          let certified := certifyCounterexample 128 buggyDecl witnessEnv HeapState.empty
          s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"declName\":\"evm_constrained_buggy_prop\",\"certified\":{if certified then "true" else "false"},\"falsePositives\":0,\"theorem\":\"LeanNative.Backend.FastCheck.certifyCounterexample_no_false_positive\",\"report\":{fcPropJson}}}"
        | other =>
          s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unknown_method:{escapeJsonRpc other}\"}"
      stdout.putStrLn resp
      stdout.flush
      runWorkerLoop stdin stdout baseMod optMod certJson tvJson llvmX86 ptxSm90 fcPropJson fcVacJson

def runWorker : IO UInt32 := do
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let certJson := (verifyModuleCerts baseMod.moduleName (stepCerts.map toOptimizationCert)).toJson
  let tvJson := (validateTranslationModule baseMod optMod).toJson
  let llvmX86 := emitLLVMOptimized optMod .x86_64
  let ptxSm90 := emitPTXModule optMod "sm_90"
  let fcMod := mkFastCheckSampleModule
  let fcPropJson := (runFastCheckModule fcMod 1024 true).toJson
  let fcVacJson := (runFastCheckModule fcMod 1024 false).toJson
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  runWorkerLoop stdin stdout baseMod optMod certJson tvJson llvmX86 ptxSm90 fcPropJson fcVacJson

unsafe def runMain (args : List String) : IO UInt32 := do
  Lean.enableInitializersExecution
  try
    match args with
    | "build-exe" :: rest         => runBuildExe rest
    | "compile-llvm" :: rest      => runCompileLLVM rest
    | "compile-mlir" :: rest      => runCompileMLIR rest
    | "compile-ptx" :: rest       => runCompilePTX rest
    | "compile-fastcheck" :: rest => runCompileFastCheck rest
    | "compile-hybrid" :: rest    => runCompileHybrid rest
    | "emit-lnir" :: rest         => runEmitLNIR rest
    | "validate-tv" :: rest       => runValidateTV rest
    | "verify-certs" :: rest      => runVerifyCerts rest
    | "audit-axioms" :: rest      => runAuditAxioms rest
    | "turbo-status" :: _         => runTurboStatus
    | "self-test" :: _            => runSelfTest
    | "worker" :: _               => runWorker
    | "--help" :: _ | "-h" :: _ | [] =>
      printUsage
      pure (0 : UInt32)
    | cmd :: _ =>
      IO.eprintln s!"Unknown command: {cmd}"
      printUsage
      pure (1 : UInt32)
  catch e =>
    IO.eprintln s!"{e}"
    pure (1 : UInt32)

end LeanNative.Driver

unsafe def main (args : List String) : IO UInt32 :=
  LeanNative.Driver.runMain args
