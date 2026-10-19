namespace LeanNative.IR

/-- Variable identifier in LNIR SSA/ANF form. -/
abbrev VarId := Nat

/-- Join point identifier in LNIR control flow. -/
abbrev JoinPointId := Nat

/-- Explicit formal assurance level attached to passes, certificates, and declarations. -/
inductive AssuranceLevel where
  | verifiedKernelProof   -- L3: Proved semantics-preserving in Lean 4 kernel (zero sorryAx)
  | translationValidated  -- L2: Validated by independent certificate checker / symbolic evaluator
  | unverifiedFallback    -- L1: Uses external C/Rust FFI, IO, or unverified runtime fallback
  deriving Repr, DecidableEq, Inhabited, BEq

namespace AssuranceLevel

def toString : AssuranceLevel → String
  | .verifiedKernelProof  => "VerifiedKernelProof"
  | .translationValidated => "TranslationValidated"
  | .unverifiedFallback   => "UnverifiedFallback"

instance : ToString AssuranceLevel := ⟨toString⟩

/-- Combine two assurance levels conservatively (minimum guarantee wins). -/
def combine : AssuranceLevel → AssuranceLevel → AssuranceLevel
  | .verifiedKernelProof, .verifiedKernelProof => .verifiedKernelProof
  | .unverifiedFallback, _ => .unverifiedFallback
  | _, .unverifiedFallback => .unverifiedFallback
  | _, _ => .translationValidated

end AssuranceLevel

/-- Target hardware architecture for code generation and cost modeling. -/
inductive TargetArch where
  | x86_64
  | arm64
  | nvptx64
  | hybridCpuGpu
  deriving Repr, DecidableEq, Inhabited, BEq

namespace TargetArch

def triple : TargetArch → String
  | .x86_64       => "x86_64-unknown-linux-gnu"
  | .arm64        => "aarch64-unknown-linux-gnu"
  | .nvptx64      => "nvptx64-nvidia-cuda"
  | .hybridCpuGpu => "hybrid-cpu-nvptx64"

end TargetArch

/-- Formally specified types in LNIR. -/
inductive LNIRType where
  | i1
  | i8
  | i16
  | i32
  | i64
  | usize
  | f32
  | f64
  | objPtr                          -- Heap lean_object*
  | taggedPtr                       -- Tagged scalar or lean_object* (tobject)
  | tuple (fields : List LNIRType)  -- Unboxed register-resident tuple/struct
  | sarray (elem : LNIRType)        -- Contiguous unboxed scalar array (ByteArray / FloatArray / UInt64 buffer)
  | rawPtr (elem : LNIRType)        -- Unboxed contiguous data pointer (m_data) after exclusivity check
  | unit
  deriving Repr, Inhabited, BEq

namespace LNIRType

partial def toLLVMType : LNIRType → String
  | .i1          => "i1"
  | .i8          => "i8"
  | .i16         => "i16"
  | .i32         => "i32"
  | .i64         => "i64"
  | .usize       => "i64"
  | .f32         => "float"
  | .f64         => "double"
  | .objPtr      => "ptr"
  | .taggedPtr   => "ptr"
  | .tuple fs    =>
    let inner := String.intercalate ", " (fs.map toLLVMType)
    "{ " ++ inner ++ " }"
  | .sarray _    => "ptr"
  | .rawPtr _    => "ptr"
  | .unit        => "void"

def isUnboxedScalar : LNIRType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize | .f32 | .f64 => true
  | _ => false

def isGpuCompatible : LNIRType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize | .f32 | .f64 => true
  | .sarray elem | .rawPtr elem => elem.isUnboxedScalar
  | _ => false

end LNIRType

end LeanNative.IR
