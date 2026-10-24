import LeanNative.IR.Bridge
import LeanNative.Backend.LLVM

open Lean
open LeanNative.IR
open LeanNative.Backend.LLVM

namespace ValidLocal

def clmul64 (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _ : i < 64 then let iu := i.toUInt64; go (i + 1) (if ((b >>> iu) &&& 1) == 1 then acc ^^^ (a <<< iu) else acc) else acc
  go 0 0

end ValidLocal

namespace Local

def clmul64 (a b : UInt64) : UInt64 := a + b

namespace Alias

def clmul64 := LeanNative.IR.clmul64

end Alias

def gf2Affine (a b : Nat) : Nat := a + b

def eor3 (a b : UInt64) : UInt64 := a + b
end Local

def clmulTargetProbeModule : LNIRModule where
  moduleName := "clmul_target_probe"
  decls := [{
    name := "clmul_probe"
    params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
    retTy := .i64
    body := .letBind 2 .i64 (.scalar (.binOp .clmul64 (.var 0) (.var 1))) (.ret 2)
  }]

#guard ((emitLLVMOptimized clmulTargetProbeModule .x86_64).splitOn "call <2 x i64> @llvm.x86.pclmulqdq").length > 1
#guard ((emitLLVMOptimized clmulTargetProbeModule .arm64).splitOn "call <16 x i8> @llvm.aarch64.neon.pmull64").length > 1
#guard !(((emitLLVMOptimized clmulTargetProbeModule .arm64).splitOn "call <2 x i64> @llvm.x86.pclmulqdq").length > 1)

run_cmd
  let env ← getEnv
  let goodClmul := tryLowerIntrinsicCall env ``LeanNative.IR.clmul64 [0, 1] .i64 [.i64, .i64]
  let goodClmulHi := tryLowerIntrinsicCall env ``LeanNative.IR.clmul64Hi [0, 1] .i64 [.i64, .i64]
  let goodValidLocal := tryLowerIntrinsicCall env ``ValidLocal.clmul64 [0, 1] .i64 [.i64, .i64]
  let goodAffine := tryLowerIntrinsicCall env ``LeanNative.IR.gf2Affine [0, 1] .i64 [.i64, .i64]
  let goodEor3 := tryLowerIntrinsicCall env ``LeanNative.IR.eor3 [0, 1] .i64 [.i64, .i64]
  let localSuffix := tryLowerIntrinsicCall env ``Local.clmul64 [0, 1] .i64 [.i64, .i64]
  let aliasSuffix := tryLowerIntrinsicCall env ``Local.Alias.clmul64 [0, 1] .i64 [.i64, .i64]
  let wrongResult := tryLowerIntrinsicCall env ``LeanNative.IR.clmul64 [0, 1] .objPtr [.i64, .i64]
  let wrongArg := tryLowerIntrinsicCall env ``LeanNative.IR.clmul64 [0, 1] .i64 [.objPtr, .i64]
  if !goodClmul.isSome then throwError "canonical clmul64 was not recognized"
  if !goodClmulHi.isSome then throwError "canonical clmul64Hi was not recognized"
  if !goodValidLocal.isSome then throwError "AST-identical local clmul64 was not recognized"
  if !goodAffine.isSome then throwError "canonical gf2Affine was not recognized"
  if !goodEor3.isSome then throwError "canonical eor3 was not recognized"
  if localSuffix.isSome then throwError "local fake same-suffix declaration was recognized"
  if aliasSuffix.isSome then throwError "alias same-suffix declaration was recognized"
  if wrongResult.isSome then throwError "mismatched result type was recognized"
  if wrongArg.isSome then throwError "mismatched arg type was recognized"
  if (tryLowerIntrinsicCall env ``Local.gf2Affine [0, 1] .i64 [.i64, .i64]).isSome then
    throwError "mismatched signature was recognized"
  if (tryLowerIntrinsicCall env ``Local.eor3 [0, 1] .i64 [.i64, .i64]).isSome then
    throwError "unrelated eor3 body was recognized"
  if (tryLowerIntrinsicCall env ``LeanNative.IR.clmul64 [0] .i64 [.i64]).isSome then
    throwError "partial application was recognized"
  Elab.Command.liftCoreM do
    for name in [``trustedGfSimdIntrinsicOp, ``tryLowerGfSimdIntrinsic, ``tryLowerIntrinsicCall, ``lowerNamedCall] do
      if (← collectAxioms name).contains ``sorryAx then throwError "sorryAx in repair"
