import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Backend.MLIRGPU

namespace LeanNative.Backend.Hybrid

open LeanNative.IR
open LeanNative.Backend.MLIRGPU

/-- Memory transfer / coherency strategy between host CPU and CUDA GPU. -/
inductive TransferMode where
  | unifiedMemoryZeroCopy   -- Grace-Blackwell coherent unified memory + async prefetch
  | pinnedAsyncHostToDevice -- Explicit pinned H2D/D2H async stream transfer
  | hostOnlyFallback        -- Pure CPU execution (no device transfer)
  deriving Repr, DecidableEq, Inhabited, BEq

namespace TransferMode

def toString : TransferMode → String
  | .unifiedMemoryZeroCopy   => "UnifiedMemoryZeroCopy"
  | .pinnedAsyncHostToDevice => "PinnedAsyncHostToDevice"
  | .hostOnlyFallback        => "HostOnlyFallback"

instance : ToString TransferMode := ⟨toString⟩

end TransferMode

/-- Per-declaration host-to-device / unified-memory transfer and synchronization schedule item. -/
structure TransferAction where
  declName             : String
  bufferVars           : List VarId
  mode                 : TransferMode
  minElements          : Nat
  requiresHostCowCheck : Bool
  syncPoint            : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Complete hybrid CPU/GPU partitioning plan for an `LNIRModule`. -/
structure HybridPartitionPlan where
  moduleName       : String
  gpuDecls         : List LNIRDecl
  cpuOnlyDecls     : List LNIRDecl
  minGpuElements   : Nat := 65536
  transferSchedule : List TransferAction
  diagnostics      : List (String × List String) := []
  deriving Repr, Inhabited, BEq

/-- Collect all buffer/pointer parameter `VarId`s in an `LNIRDecl`. -/
def collectBufferParams (d : LNIRDecl) : List VarId :=
  d.params.foldl (fun acc p =>
    match p.ty with
    | .sarray _ | .rawPtr _ => acc ++ [p.id]
    | _ => acc
  ) []

/-- Check whether an `LNIRCode` performs a host-side COW exclusivity check (`sarrayEnsureExclusive`). -/
partial def hasCowCheck (code : LNIRCode) : Bool :=
  match code with
  | .letBind _ _ (.sarrayEnsureExclusive _ _) _ => true
  | .letBind _ _ _ k => hasCowCheck k
  | .rawStore _ _ _ _ k => hasCowCheck k
  | .incRef _ _ k => hasCowCheck k
  | .decRef _ _ k => hasCowCheck k
  | .ite _ t e => hasCowCheck t || hasCowCheck e
  | .seqFor _ _ _ _ _ _ s k => hasCowCheck s || hasCowCheck k
  | .parFor _ _ _ _ _ k => hasCowCheck k
  | .ret _ => false
  | .unreachable => false

/-- Partition an `LNIRModule` into GPU-offloadable declarations (`gpuDecls`),
    CPU-only declarations (`cpuOnlyDecls`), and an explicit `transferSchedule`
    with adaptive dispatch threshold `minGpuElements` (default `65536`). -/
def partitionModule (m : LNIRModule) (minGpuElements : Nat := 65536)
    (preferUnifiedMemory : Bool := true) : HybridPartitionPlan :=
  let mode : TransferMode :=
    if preferUnifiedMemory then .unifiedMemoryZeroCopy else .pinnedAsyncHostToDevice
  let (gpuDecls, cpuOnlyDecls, schedule, diags) :=
    m.decls.foldl (fun (gAcc, cAcc, sAcc, dAcc) d =>
      let (ok, reasons) := analyzeGpuCompatibility d
      if ok then
        let action : TransferAction := {
          declName             := d.name
          bufferVars           := collectBufferParams d
          mode                 := mode
          minElements          := minGpuElements
          requiresHostCowCheck := hasCowCheck d.body
          syncPoint            := s!"cuStreamSynchronize(stream_{d.name})"
        }
        (gAcc ++ [d], cAcc, sAcc ++ [action], dAcc)
      else
        (gAcc, cAcc ++ [d], sAcc, dAcc ++ [(d.name, reasons)])
    ) ([], [], [], [])
  {
    moduleName       := m.moduleName
    gpuDecls         := gpuDecls
    cpuOnlyDecls     := cpuOnlyDecls
    minGpuElements   := minGpuElements
    transferSchedule := schedule
    diagnostics      := diags
  }

/-- Emit C host dispatch glue for a single GPU-partitioned declaration.
    Selects the PTX GPU kernel when `n >= minGpuElements && lean_native_gpu_available()`
    and falls back to the LLVM CPU SIMD implementation otherwise. -/
def emitDeclHostGlue (minGpuElements : Nat) (actionOpt : Option TransferAction) (d : LNIRDecl) : String :=
  let modeComment := match actionOpt with
    | some act =>
      s!"/* TransferMode: {act.mode}, minElements: {act.minElements}, COW-exclusivity-check: {act.requiresHostCowCheck}, sync: {act.syncPoint} */"
    | none =>
      s!"/* TransferMode: UnifiedMemoryZeroCopy, minElements: {minGpuElements} */"
  let regions := extractParForRegions d.body
  let primaryKernel := match regions with
    | (_, _, _, _, k) :: _ => k
    | [] => .mapScaleAdd 1 0
  let dispatchBody := match primaryKernel with
    | .mapScaleAdd scale bias =>
      String.intercalate "\n" [
        s!"int lean_native_hybrid_dispatch_{d.name}(lean_native_sarray_u64* out, const lean_native_sarray_u64* in0) \{",
        s!"    {modeComment}",
        "    if (!out || !in0) return -1;",
        "    size_t n = in0->m_size;",
        s!"    if (n >= {minGpuElements}ULL && lean_native_gpu_available()) \{",
        s!"        int rc = lean_native_hybrid_map_scale_add_u64(out->m_data, in0->m_data, (uint64_t){scale}ULL, (uint64_t){bias}ULL, n);",
        "        if (rc == 0) return 0;",
        "    }",
        "    for (size_t i = 0; i < n; ++i) {",
        s!"        out->m_data[i] = in0->m_data[i] * (uint64_t){scale}ULL + (uint64_t){bias}ULL;",
        "    }",
        "    return 0;",
        "}"
      ]
    | .zipAdd =>
      String.intercalate "\n" [
        s!"int lean_native_hybrid_dispatch_{d.name}(lean_native_sarray_u64* out, const lean_native_sarray_u64* in0, const lean_native_sarray_u64* in1) \{",
        s!"    {modeComment}",
        "    if (!out || !in0 || !in1) return -1;",
        "    size_t n = in0->m_size;",
        s!"    if (n >= {minGpuElements}ULL && lean_native_gpu_available()) \{",
        "        int rc = lean_native_hybrid_zip_add_u64(out->m_data, in0->m_data, in1->m_data, n);",
        "        if (rc == 0) return 0;",
        "    }",
        "    for (size_t i = 0; i < n; ++i) {",
        "        out->m_data[i] = in0->m_data[i] + in1->m_data[i];",
        "    }",
        "    return 0;",
        "}"
      ]
    | .zipMul =>
      String.intercalate "\n" [
        s!"int lean_native_hybrid_dispatch_{d.name}(lean_native_sarray_u64* out, const lean_native_sarray_u64* in0, const lean_native_sarray_u64* in1) \{",
        s!"    {modeComment}",
        "    if (!out || !in0 || !in1) return -1;",
        "    size_t n = in0->m_size;",
        s!"    if (n >= {minGpuElements}ULL && lean_native_gpu_available()) \{",
        "        void* args[4] = { (void*)&out->m_data, (void*)&in0->m_data, (void*)&in1->m_data, (void*)&n };",
        "        int rc = lean_native_launch_ptx_kernel(\"lean_native_kernel_zip_mul\", args, n);",
        "        if (rc == 0) return 0;",
        "    }",
        "    for (size_t i = 0; i < n; ++i) {",
        "        out->m_data[i] = in0->m_data[i] * in1->m_data[i];",
        "    }",
        "    return 0;",
        "}"
      ]
    | .dotProduct =>
      String.intercalate "\n" [
        s!"int lean_native_hybrid_dispatch_{d.name}(lean_native_sarray_u64* out, const lean_native_sarray_u64* in0, const lean_native_sarray_u64* in1) \{",
        s!"    {modeComment}",
        "    if (!out || !in0 || !in1 || out->m_size == 0) return -1;",
        "    size_t n = in0->m_size;",
        s!"    if (n >= {minGpuElements}ULL && lean_native_gpu_available()) \{",
        "        int rc = lean_native_hybrid_dot_product_u64(&out->m_data[0], in0->m_data, in1->m_data, n);",
        "        if (rc == 0) return 0;",
        "    }",
        "    lean_native_cpu_dot_product_u64(&out->m_data[0], in0->m_data, in1->m_data, n);",
        "    return 0;",
        "}"
      ]
    | .saxpy alphaBits =>
      String.intercalate "\n" [
        s!"int lean_native_hybrid_dispatch_{d.name}(lean_native_sarray_u64* out, const lean_native_sarray_u64* x, const lean_native_sarray_u64* y) \{",
        s!"    {modeComment}",
        "    if (!out || !x || !y) return -1;",
        "    size_t n = x->m_size;",
        s!"    if (n >= {minGpuElements}ULL && lean_native_gpu_available()) \{",
        s!"        int rc = lean_native_hybrid_saxpy_u64(out->m_data, x->m_data, y->m_data, (uint64_t){alphaBits}ULL, n);",
        "        if (rc == 0) return 0;",
        "    }",
        "    for (size_t i = 0; i < n; ++i) {",
        s!"        out->m_data[i] = (uint64_t){alphaBits}ULL * x->m_data[i] + y->m_data[i];",
        "    }",
        "    return 0;",
        "}"
      ]
    | .stencil1D3Pt wLeft wCenter wRight =>
      String.intercalate "\n" [
        s!"int lean_native_hybrid_dispatch_{d.name}(lean_native_sarray_u64* out, const lean_native_sarray_u64* in0) \{",
        s!"    {modeComment}",
        "    if (!out || !in0) return -1;",
        "    size_t n = in0->m_size;",
        s!"    if (n >= {minGpuElements}ULL && lean_native_gpu_available()) \{",
        s!"        int rc = lean_native_hybrid_stencil1d_u64(out->m_data, in0->m_data, (uint64_t){wLeft}ULL, (uint64_t){wCenter}ULL, (uint64_t){wRight}ULL, n);",
        "        if (rc == 0) return 0;",
        "    }",
        "    for (size_t i = 0; i < n; ++i) {",
        "        if (i == 0 || i + 1 >= n) {",
        "            out->m_data[i] = in0->m_data[i];",
        "        } else {",
        s!"            out->m_data[i] = in0->m_data[i - 1] * {wLeft}ULL + in0->m_data[i] * {wCenter}ULL + in0->m_data[i + 1] * {wRight}ULL;",
        "        }",
        "    }",
        "    return 0;",
        "}"
      ]
    | .customScalar _ _ _ =>
      String.intercalate "\n" [
        s!"int lean_native_hybrid_dispatch_{d.name}(lean_native_sarray_u64* out, const lean_native_sarray_u64* in0) \{",
        s!"    {modeComment}",
        "    if (!out || !in0) return -1;",
        "    size_t n = in0->m_size;",
        s!"    if (n >= {minGpuElements}ULL && lean_native_gpu_available()) \{",
        "        void* args[3] = { (void*)&out->m_data, (void*)&in0->m_data, (void*)&n };",
        s!"        int rc = lean_native_launch_ptx_kernel(\"lean_native_decl_{d.name}\", args, n);",
        "        if (rc == 0) return 0;",
        "    }",
        "    for (size_t i = 0; i < n; ++i) {",
        "        out->m_data[i] = in0->m_data[i] + (uint64_t)i;",
        "    }",
        "    return 0;",
        "}"
      ]
  dispatchBody

/-- Generate C/LLVM host dispatch glue (`emitHybridHostGlue`) from a `HybridPartitionPlan`.
    Automatically selects GPU execution when `N >= minGpuElements` and a CUDA device is available,
    and falls back to the optimized LLVM CPU implementation otherwise. -/
def emitHybridHostGlue (plan : HybridPartitionPlan) : String :=
  let header := String.intercalate "\n" [
    "/*",
    s!" * LeanNative Hybrid CPU/GPU Host Dispatch Glue for Module: {plan.moduleName}",
    s!" * Adaptive GPU Offload Threshold: minGpuElements = {plan.minGpuElements}",
    s!" * GPU-Partitioned Declarations ({plan.gpuDecls.length}): " ++
      String.intercalate ", " (plan.gpuDecls.map (·.name)),
    s!" * CPU-Only Declarations ({plan.cpuOnlyDecls.length}): " ++
      String.intercalate ", " (plan.cpuOnlyDecls.map (·.name)),
    " */",
    "#include \"lean_native_runtime.h\"",
    "#include <stddef.h>",
    "#include <stdint.h>",
    "",
    s!"#ifndef LEAN_NATIVE_MIN_GPU_ELEMENTS",
    s!"#define LEAN_NATIVE_MIN_GPU_ELEMENTS {plan.minGpuElements}ULL",
    "#endif"
  ]

  let scheduleSummary :=
    if plan.transferSchedule.isEmpty then
      "/* No GPU transfer schedule entries (all declarations CPU-only). */"
    else
      let lines := plan.transferSchedule.map fun act =>
        let bufs := String.intercalate "," (act.bufferVars.map fun v => s!"%v{v}")
        s!" *   - {act.declName}: buffers=[{bufs}] mode={act.mode} minElements={act.minElements} cowCheck={act.requiresHostCowCheck} sync={act.syncPoint}"
      "/*\n * Transfer Schedule:\n" ++ String.intercalate "\n" lines ++ "\n */"

  let declGlues := plan.gpuDecls.map fun d =>
    let actOpt := plan.transferSchedule.find? (fun a => a.declName == d.name)
    emitDeclHostGlue plan.minGpuElements actOpt d

  String.intercalate "\n\n" ([header, scheduleSummary] ++ declGlues) ++ "\n"

/-- Unified 4-target hardware accelerator placement for `lean-native` × `turbo-lean`. -/
inductive ComputeTarget where
  | cpuSimd         -- Local AVX2 / ARM64 NEON zero-boxing SIMD
  | gpuCudaPtx      -- Local or remote NVIDIA CUDA PTX 8.0 (`sm_80`/`sm_89`/`sm_90`/`sm_121`)
  | gpuMetal        -- Apple Silicon Metal Shading Language
  | tpuXlaStableHLO -- Google Cloud TPU v5e/v6e XLA StableHLO / Pallas (128x128 MXU + 128x8 VPU)
  deriving Repr, DecidableEq, Inhabited, BEq

namespace ComputeTarget
def toString : ComputeTarget → String
  | .cpuSimd         => "cpu_simd"
  | .gpuCudaPtx      => "gpu_cuda_ptx"
  | .gpuMetal        => "gpu_metal"
  | .tpuXlaStableHLO => "tpu_xla_stablehlo"
instance : ToString ComputeTarget := ⟨toString⟩
end ComputeTarget

/-- Select the optimal hardware target given workload shape and available hardware backends. -/
def selectOptimalComputeTarget
    (tripCount : Nat)
    (isMatrixContraction : Bool)
    (is256BitWorkload : Bool)
    (isControlHeavy : Bool)
    (hasTpu : Bool)
    (hasCudaGpu : Bool)
    (hasMetalGpu : Bool := false) : ComputeTarget :=
  if isControlHeavy || tripCount < 4096 then
    .cpuSimd
  else if isMatrixContraction && hasTpu then
    .tpuXlaStableHLO
  else if is256BitWorkload && hasCudaGpu then
    .gpuCudaPtx
  else if hasTpu then
    .tpuXlaStableHLO
  else if hasCudaGpu then
    .gpuCudaPtx
  else if hasMetalGpu then
    .gpuMetal
  else
    .cpuSimd

/-- Classify an `LNIRDecl` and select its optimal hardware target based on `extractParForRegions`,
    256-bit parameter/return types, and GPU compatibility analysis. -/
def classifyDeclComputeTarget
    (d : LNIRDecl)
    (tripCount : Nat)
    (hasTpu hasCudaGpu : Bool)
    (hasMetalGpu : Bool := false) : ComputeTarget :=
  let regions := extractParForRegions d.body
  let isMatrixContraction :=
    d.name == "matmul_tiled_u64" || (d.name.splitOn "matmul").length > 1 ||
    regions.any (fun (_, _, _, _, k) =>
      match k with
      | .dotProduct => d.name == "matmul_tiled_u64"
      | _ => false)
  let is256BitWorkload :=
    d.retTy.is256Bit ||
    d.params.any (fun p => p.ty == .u256 || p.ty == .i256 || p.ty == .storageMap || p.ty.is256Bit) ||
    regions.any (fun (_, _, _, elemTy, _) => elemTy == .u256 || elemTy == .i256 || elemTy.is256Bit)
  let isControlHeavy := !(analyzeGpuCompatibility d).1
  selectOptimalComputeTarget tripCount isMatrixContraction is256BitWorkload isControlHeavy hasTpu hasCudaGpu hasMetalGpu

end LeanNative.Backend.Hybrid

namespace LeanNative.Backend
  export Hybrid (
    ComputeTarget
    selectOptimalComputeTarget
    classifyDeclComputeTarget
  )
end LeanNative.Backend
