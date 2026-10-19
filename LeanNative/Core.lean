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
import LeanNative.Backend.LLVM
import LeanNative.Backend.MLIRGPU
import LeanNative.Backend.Hybrid
import LeanNative.Backend.FastCheck
import LeanNative.TurboLean.Adapter

namespace LeanNative.Core

def coreVersion : String := "0.2.0"

end LeanNative.Core
