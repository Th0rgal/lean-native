import LeanNative.Backend.Hybrid
import LeanNative.Backend.Metal
import LeanNative.Backend.LLVM
import LeanNative.Proofs.SymbolicTV
open LeanNative.IR LeanNative.Backend.Hybrid LeanNative.Backend.LLVM LeanNative.Proofs
#guard slotLLVMType (.tuple [.i64, .i64]) == "{ i64, i64 }"
#guard slotTypeRegressionOk
#guard !SymExpr.isCommutative .eor3
#guard (symEvalScalar {} (.binOp .shl (.constU64 1) (.constU64 64))).nonPoison
#guard normSymBinOpStep .eor3 (.constU64 0) (.constU64 4294967296) == .constU64 1
#guard normSymBinOpStep .clmul64 (.constU64 3) (.constU64 3) == .constU64 5 && normSymBinOpStep .clmul64Hi (.constU64 ((1 : UInt64) <<< 63)) (.constU64 2) == .constU64 1
#guard normSymBinOpStep .gf2Affine (.constU64 1) (.constU64 1) == .constU64 1
def routingDecl (body : LNIRCode) : LNIRDecl := { name := "routing", params := [], retTy := .i64, body, isGpuCand := true }
def routingPlan (body : LNIRCode) : HybridPartitionPlan := partitionModule { moduleName := "Routing", decls := [routingDecl body] }
def routingRegion (ty : LNIRType) (kernel : ParallelKernelKind) (k : LNIRCode := .ret 0) : LNIRCode := .parFor 0 1 [2, 3] ty kernel k
#guard (routingPlan (routingRegion .i64 .zipMul)).gpuDecls.length == 1
#guard (routingPlan (routingRegion .i64 .zipMul)).cpuOnlyDecls.isEmpty
#guard (routingPlan (routingRegion .f64 .zipMul)).gpuDecls.isEmpty
#guard (routingPlan (.ret 0)).gpuDecls.isEmpty
#guard (routingPlan (routingRegion .i64 .zipMul (routingRegion .i64 .zipAdd))).gpuDecls.isEmpty
def customRoutingPlan := routingPlan (routingRegion .i64 (.customScalar 10 [11, 12] (.var 12)))
#guard customRoutingPlan.gpuDecls.isEmpty && customRoutingPlan.cpuOnlyDecls.length == 1 && customRoutingPlan.transferSchedule.isEmpty
#guard customRoutingPlan.diagnostics == [("routing", ["customScalar PTX lowering is unsupported"])]
#guard !(LeanNative.Backend.Metal.containsSubstr (emitHybridHostGlue customRoutingPlan) "lean_native_launch_ptx_kernel")
#guard !(LeanNative.Backend.Metal.containsSubstr LeanNative.Backend.Metal.emitMetalU256Library "pmull(")
#guard (LeanNative.Backend.Metal.emitMetalDeclKernel (routingDecl (routingRegion .i64 (.customScalar 10 [11, 12] (.var 12))))).isNone
#guard !(LeanNative.Backend.Metal.containsSubstr (LeanNative.Backend.Metal.emitMetalModule { moduleName := "Routing", decls := [routingDecl (.ret 0)] }) "lean_native_metal_decl_routing")

section Wave1SemanticsTests
open LeanNative.Semantics
instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

def testSt0 : HeapState :=
  { buffers := [{ id := 0, exclusive := true, data := #[10, 20, 30, 40] },
                { id := 1, exclusive := true, data := #[1, 2, 3, 4] }],
    nextId := 1 }
def testEnv0 : VarEnv :=
  (((VarEnv.empty.bind 0 (.sarrayId 0)).bind 1 (.sarrayId 1)).bind 2 (.u64 4)).bind 3 (.objPtr 1)

-- 1. Reference counting: 1 -> 2 -> 1, exclusivity sync, free at 0, double-free & resurrection traps, disjoint key space
#guard (testSt0.incRefBuf 1 0) == .ok testSt0
#guard (do let s1 ← testSt0.incRefBuf 1 1; s1.writeElemExclusive 1 0 99) == .error (.nonExclusiveWrite 1)
#guard (do let s1 ← testSt0.incRefBuf 1 1; s1.decRefBuf 1 1) == .ok testSt0
#guard (do let s1 ← testSt0.decRefBuf 1 1; pure (s1.findBuffer 1)) == .ok none
#guard (do let s1 ← testSt0.decRefBuf 1 1; s1.decRefBuf 1 1) == .error (.useAfterFree 1)
#guard (do let s1 ← testSt0.decRefBuf 1 1; s1.incRefBuf 1 1) == .error (.useAfterFree 1)
#guard (testSt0.decRefBuf 1 2) == .error (.useAfterFree 1)
#guard (testSt0.decRefBuf 99 1) == .error (.useAfterFree 99)
#guard (evalCode 64 testEnv0 testSt0 (.incRef 99 1 (.ret 2))) == .error (.unboundVar 99)
#guard (do let s1 ← testSt0.evalDecRef testEnv0 3 1; pure (s1.findBuffer 1).isSome) == .ok true
#guard (do let s1 ← testSt0.evalDecRef testEnv0 3 1; s1.evalDecRef testEnv0 3 1) == .error (.useAfterFree 1)

-- 2. All 7 parFor variants, fresh buffer allocation (preserving buffer 0), boundary stencil, empty len=0, OOB trap
#guard (do let (v, s) ← evalParFor 64 testEnv0 testSt0 2 [0] (.mapScaleAdd 2 5); s.readElem 2 1 >>= fun x => pure (v, x, (s.findBuffer 0).isSome)) == .ok (.sarrayId 2, 45, true)
#guard (do let (_, s) ← evalParFor 64 testEnv0 testSt0 2 [0, 1] .zipAdd; pure (s.findBuffer 2).get!.data) == .ok #[11, 22, 33, 44]
#guard (do let (_, s) ← evalParFor 64 testEnv0 testSt0 2 [0, 1] .zipMul; pure (s.findBuffer 2).get!.data) == .ok #[10, 40, 90, 160]
#guard (do let (_, s) ← evalParFor 64 testEnv0 testSt0 2 [0, 1] (.saxpy 3); pure (s.findBuffer 2).get!.data) == .ok #[31, 62, 93, 124]
#guard (do let (_, s) ← evalParFor 64 testEnv0 testSt0 2 [0, 1] .dotProduct; pure (s.findBuffer 2).get!.data) == .ok #[300]
#guard (do let (_, s) ← evalParFor 64 testEnv0 testSt0 2 [0] (.stencil1D3Pt 1 2 1); pure (s.findBuffer 2).get!.data) == .ok #[10, 80, 120, 40]
#guard (do let (_, s) ← evalParFor 64 testEnv0 testSt0 2 [0, 1] (.customScalar 10 [11, 12] (.binOp .add (.var 11) (.var 10))); pure (s.findBuffer 2).get!.data) == .ok #[10, 21, 32, 43]
#guard (do let (_, s) ← evalParFor 64 (testEnv0.bind 2 (.u64 0)) testSt0 2 [0] (.mapScaleAdd 2 5); pure (s.findBuffer 2).get!.data) == .ok #[]
#guard (evalParFor 64 (testEnv0.bind 2 (.u64 5)) testSt0 2 [0] (.mapScaleAdd 1 0)) == .error (.outOfBounds 4 4)

-- 3. .call intrinsics & unsupported/extern call error traps + rewriteCodePeephole equivalence
#guard (evalExpr testEnv0 testSt0 (.call "lean_native_box_u64" [2] .objPtr false)) == .ok (.u64 4, testSt0)
#guard (evalExpr testEnv0 testSt0 (.call "lean_native_unbox_u64" [2] .i64 false)) == .ok (.u64 4, testSt0)
#guard (evalExpr testEnv0 testSt0 (.call "lean_native_sarray_len" [0] .i64 false)) == .ok (.u64 4, testSt0)
#guard (evalExpr testEnv0 testSt0 (.call "lean_native_box_u64" [2] .objPtr true)) == .error (.unsupportedCall "lean_native_box_u64")
#guard (evalExpr testEnv0 testSt0 (.call "unknown_fn" [2] .i64 false)) == .error (.unsupportedCall "unknown_fn")
def testWave1Code : LNIRCode :=
  .incRef 0 1 (.letBind 4 .i64 (.call "lean_native_sarray_len" [0] .i64 false)
    (.parFor 5 4 [0, 1] .i64 .dotProduct (.decRef 0 1 (.ret 5))))
#guard evalCode 64 testEnv0 testSt0 (rewriteCodePeephole testWave1Code) == evalCode 64 testEnv0 testSt0 testWave1Code
end Wave1SemanticsTests
