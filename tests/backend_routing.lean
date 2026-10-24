import LeanNative.Backend.Hybrid
import LeanNative.Backend.Metal
import LeanNative.Backend.LLVM
import LeanNative.Proofs.SymbolicTV

open LeanNative.Backend.LLVM LeanNative.Proofs
#guard slotLLVMType (.tuple [.i64, .i64]) == "{ i64, i64 }"
#guard slotTypeRegressionOk
#guard !SymExpr.isCommutative .eor3
#guard (symEvalScalar {} (.binOp .shl (.constU64 1) (.constU64 64))).nonPoison
#guard normSymBinOpStep .eor3 (.constU64 0) (.constU64 4294967296) == .constU64 1
#guard normSymBinOpStep .clmul64 (.constU64 3) (.constU64 3) == .constU64 5
#guard normSymBinOpStep .gf2Affine (.constU64 1) (.constU64 1) == .constU64 1

open LeanNative.IR LeanNative.Backend.Hybrid

def routingDecl (body : LNIRCode) : LNIRDecl :=
  { name := "routing", params := [], retTy := .i64, body, isGpuCand := true }

def routingPlan (body : LNIRCode) : HybridPartitionPlan :=
  partitionModule { moduleName := "Routing", decls := [routingDecl body] }

def routingRegion (ty : LNIRType) (kernel : ParallelKernelKind) (k : LNIRCode := .ret 0) : LNIRCode :=
  .parFor 0 1 [2, 3] ty kernel k

#guard (routingPlan (routingRegion .i64 .zipMul)).gpuDecls.length == 1
#guard (routingPlan (routingRegion .i64 .zipMul)).cpuOnlyDecls.isEmpty
#guard (routingPlan (routingRegion .f64 .zipMul)).gpuDecls.isEmpty
#guard (routingPlan (.ret 0)).gpuDecls.isEmpty
#guard (routingPlan (routingRegion .i64 .zipMul (routingRegion .i64 .zipAdd))).gpuDecls.isEmpty

def customRoutingPlan := routingPlan (routingRegion .i64 (.customScalar 10 [11, 12] (.var 12)))
#guard customRoutingPlan.gpuDecls.isEmpty
#guard customRoutingPlan.cpuOnlyDecls.length == 1
#guard customRoutingPlan.transferSchedule.isEmpty
#guard customRoutingPlan.diagnostics == [("routing", ["customScalar PTX lowering is unsupported"])]
#guard !(LeanNative.Backend.Metal.containsSubstr (emitHybridHostGlue customRoutingPlan) "lean_native_launch_ptx_kernel")
#guard !(LeanNative.Backend.Metal.containsSubstr LeanNative.Backend.Metal.emitMetalU256Library "pmull(")
