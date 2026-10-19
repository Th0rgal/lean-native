import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.IR

/-!
# Self-Contained LNIR Wire & JSON Codec + Canonical & FastCheck Modules (`LeanNative.IR.Codec`)

This module has **zero** `import Lean` dependencies so it can be linked into the ultra-lightweight
`lean-native-core` binary (~4-8 MB, `< 5 ms` cold start) without pulling in `libleanshared.so`
elaboration/meta state.

Provides:
1. Canonical 8-kernel benchmark suite (`Codec.mkCanonicalBenchmarkModule`), comprising the 6 core
   numerical/array kernels plus 2 256-bit EVM/Verity kernels (`evm_erc20_transfer_u256` and
   `evm_muldiv_wad_u256`).
2. Propositional FastCheck sample module (`mkFastCheckSampleModule`) with `evm_add_comm_prop`
   and `evm_constrained_buggy_prop` (demonstrating Vacuous Pass elimination via equality
   constraint propagation).
3. Lossless wire (`LNIRModule.toWire` / `LNIRModule.fromWire?`) and JSON (`LNIRModule.toJson` /
   `LNIRModule.fromJson?`) serialization and deserialization for `LNIRModule`.
-/

/-- 7. `evm_erc20_transfer_u256`: 256-bit EVM/Verity ERC-20 storage transfer kernel.
    Takes `(mapVar : .storageMap, senderSlot : .u256, receiverSlot : .u256, amount : .u256)`,
    loads `senderBal := storageLoad mapVar senderSlot`,
    computes `newSenderBal := binOp .subChecked256 senderBal amount`,
    stores `storageStore mapVar senderSlot newSenderBal`,
    loads `recvBal := storageLoad mapVar receiverSlot`,
    computes `newRecvBal := binOp .addChecked256 recvBal amount`,
    stores `storageStore mapVar receiverSlot newRecvBal`,
    and returns `newRecvBal`. -/
def evmErc20TransferU256Decl : LNIRDecl := {
  name      := "evm_erc20_transfer_u256"
  params    := [
    { id := 0, name := "mapVar", ty := .storageMap, borrow := false },
    { id := 1, name := "senderSlot", ty := .u256, borrow := false },
    { id := 2, name := "receiverSlot", ty := .u256, borrow := false },
    { id := 3, name := "amount", ty := .u256, borrow := false }
  ]
  retTy     := .u256
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 4 .u256 (.storageLoad 0 1) (
      .letBind 5 .u256 (.scalar (.binOp .subChecked256 (.var 4) (.var 3))) (
        .letBind 6 .storageMap (.storageStore 0 1 5) (
          .letBind 7 .u256 (.storageLoad 6 2) (
            .letBind 8 .u256 (.scalar (.binOp .addChecked256 (.var 7) (.var 3))) (
              .letBind 9 .storageMap (.storageStore 6 2 8) (
                .ret 8
              )
            )
          )
        )
      )
    )
}

/-- 8. `evm_muldiv_wad_u256`: 256-bit EVM/Verity full-precision WAD fixed-point kernel.
    Takes `(a : .u256, b : .u256, wad : .u256)`,
    computes `down := mulDivDown a b wad`,
    `up := mulDivUp a b wad`,
    `lz := unaryOp .clz256 down`,
    `diff := binOp .sub up down`,
    and returns `binOp .add down (binOp .add diff lz)`. -/
def evmMuldivWadU256Decl : LNIRDecl := {
  name      := "evm_muldiv_wad_u256"
  params    := [
    { id := 0, name := "a", ty := .u256, borrow := false },
    { id := 1, name := "b", ty := .u256, borrow := false },
    { id := 2, name := "wad", ty := .u256, borrow := false }
  ]
  retTy     := .u256
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 3 .u256 (.mulDivDown 0 1 2) (
      .letBind 4 .u256 (.mulDivUp 0 1 2) (
        .letBind 5 .u256 (.scalar (.unaryOp .clz256 (.var 3))) (
          .letBind 6 .u256 (.scalar (.binOp .sub (.var 4) (.var 3))) (
            .letBind 7 .u256 (.scalar (.binOp .add (.var 3) (.binOp .add (.var 6) (.var 5)))) (
              .ret 7
            )
          )
        )
      )
    )
}

/-- Valid propositional property for FastCheck: checks `a + b == b + a` on `.u256`. -/
def evmAddCommPropDecl : LNIRDecl := {
  name      := "evm_add_comm_prop"
  params    := [
    { id := 0, name := "a", ty := .u256, borrow := false },
    { id := 1, name := "b", ty := .u256, borrow := false }
  ]
  retTy     := .i1
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 2 .u256 (.scalar (.binOp .add (.var 0) (.var 1))) (
      .letBind 3 .u256 (.scalar (.binOp .add (.var 1) (.var 0))) (
        .letBind 4 .i1 (.scalar (.binOp .eq (.var 2) (.var 3))) (
          .ret 4
        )
      )
    )
}

/-- Buggy propositional property with an equality precondition `x0 == x1 + 42` in an `ite` guard
    and a conclusion `x0 < 1000000` that fails for large `x1`.
    Demonstrates that equality constraint propagation (`x0 := x1 + 42`) immediately finds a
    certified counterexample whereas naive rejection sampling without constraint propagation
    suffers a Vacuous Pass (`satisfiedPreconditionsCount == 0`). -/
def evmConstrainedBuggyPropDecl : LNIRDecl := {
  name      := "evm_constrained_buggy_prop"
  params    := [
    { id := 0, name := "x0", ty := .i64, borrow := false },
    { id := 1, name := "x1", ty := .i64, borrow := false }
  ]
  retTy     := .i1
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.binOp .add (.var 1) (.constU64 42)))) (
      .ite 2
        (.letBind 3 .i1 (.scalar (.binOp .lt (.var 0) (.constU64 1000000))) (.ret 3))
        (.letBind 4 .i1 (.scalar (.constBool true)) (.ret 4))
    )
}

/-- Propositional FastCheck sample module containing `evm_add_comm_prop` and `evm_constrained_buggy_prop`. -/
def mkFastCheckSampleModule : LNIRModule := {
  moduleName := "LeanNative.FastCheck.Sample"
  decls      := [
    evmAddCommPropDecl,
    evmConstrainedBuggyPropDecl
  ]
}

namespace Codec

/-- 1. `collatz_steps`: Scalar loop with strength-reduction (`x * 2`, `x / 2`, `x + 0`, `x * 1`) opportunities. -/
def collatzStepsDecl : LNIRDecl := {
  name      := "collatz_steps"
  params    := [
    { id := 0, name := "n", ty := .i64, borrow := false },
    { id := 1, name := "steps", ty := .i64, borrow := false }
  ]
  retTy     := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body      :=
    .letBind 2 .i64 (.scalar (.constU64 0)) (
      .seqFor 3 2 1 4 0 .i64
        (.letBind 5 .i64 (.scalar (.binOp .mul (.var 4) (.constU64 2)))
          (.letBind 6 .i64 (.scalar (.binOp .add (.var 5) (.var 4)))
            (.letBind 7 .i64 (.scalar (.binOp .add (.var 6) (.constU64 1)))
              (.letBind 8 .i64 (.scalar (.binOp .div (.var 7) (.constU64 2)))
                (.letBind 9 .i64 (.scalar (.binOp .add (.var 8) (.constU64 0)))
                  (.ret 9))))))
        (.ret 4)
    )
}

/-- 2. `tuple_accum_sum`: Loop constructing intermediate 2-tuples `mkTuple` and projecting fields (`UnboxTupleSROA`). -/
def tupleAccumSumDecl : LNIRDecl := {
  name      := "tuple_accum_sum"
  params    := [
    { id := 0, name := "n", ty := .i64, borrow := false },
    { id := 1, name := "seed", ty := .i64, borrow := false }
  ]
  retTy     := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body      :=
    .letBind 2 .i64 (.scalar (.constU64 0)) (
      .seqFor 3 2 0 4 1 .i64
        (.letBind 5 .i64 (.scalar (.binOp .add (.var 4) (.var 3)))
          (.letBind 6 .i64 (.scalar (.binOp .mul (.var 3) (.constU64 2)))
            (.letBind 7 (.tuple [.i64, .i64]) (.mkTuple [5, 6])
              (.letBind 8 .i64 (.projTuple 7 0)
                (.letBind 9 .i64 (.projTuple 7 1)
                  (.letBind 10 .i64 (.scalar (.binOp .add (.var 8) (.var 9)))
                    (.ret 10)))))))
        (.ret 4)
    )
}

/-- 3. `sarray_scale_bias`: In-place scalar array loop with `sarrayEnsureExclusive` inside the loop body (`HoistExclusivity`). -/
def sarrayScaleBiasDecl : LNIRDecl := {
  name      := "sarray_scale_bias"
  params    := [
    { id := 0, name := "arr", ty := .sarray .i64, borrow := false },
    { id := 1, name := "scale", ty := .i64, borrow := false },
    { id := 2, name := "bias", ty := .i64, borrow := false }
  ]
  retTy     := .sarray .i64
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 3 .i64 (.scalar (.constU64 0)) (
      .letBind 4 .i64 (.sarrayLen 0) (
        .seqFor 5 3 4 6 0 (.sarray .i64)
          (.letBind 7 (.sarray .i64) (.sarrayEnsureExclusive 6 .i64)
            (.letBind 8 .i64 (.sarrayGet 7 5 .i64)
              (.letBind 9 .i64 (.scalar (.fma (.var 8) (.var 1) (.var 2)))
                (.letBind 10 (.sarray .i64) (.sarraySet 7 5 9 .i64)
                  (.ret 10)))))
          (.ret 6)
      )
    )
}

/-- 4. `dot_product_u64`: Data-parallel dot product / reduction over contiguous arrays with redundant RC pair. -/
def dotProductU64Decl : LNIRDecl := {
  name      := "dot_product_u64"
  params    := [
    { id := 0, name := "xs", ty := .sarray .i64, borrow := false },
    { id := 1, name := "ys", ty := .sarray .i64, borrow := false }
  ]
  retTy     := .sarray .i64
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .incRef 0 1 (
      .letBind 2 .i64 (.sarrayLen 0) (
        .parFor 3 2 [0, 1] .i64 .dotProduct (
          .decRef 0 1 (.ret 3)
        )
      )
    )
}

/-- 5. `saxpy_kernel`: Data-parallel `alpha * x[i] + y[i]` kernel eligible for both CPU SIMD and GPU MLIR/PTX offload. -/
def saxpyKernelDecl : LNIRDecl := {
  name      := "saxpy_kernel"
  params    := [
    { id := 0, name := "xs", ty := .sarray .i64, borrow := true },
    { id := 1, name := "ys", ty := .sarray .i64, borrow := true }
  ]
  retTy     := .sarray .i64
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 2 .i64 (.sarrayLen 0) (
      .parFor 3 2 [0, 1] .i64 (.saxpy 4) (.ret 3)
    )
}

/-- 6. `matmul_tiled_u64`: Dense numerical matrix kernel eligible for GPU PTX and hybrid CPU/GPU dispatch. -/
def matmulTiledU64Decl : LNIRDecl := {
  name      := "matmul_tiled_u64"
  params    := [
    { id := 0, name := "matA", ty := .sarray .i64, borrow := true },
    { id := 1, name := "matB", ty := .sarray .i64, borrow := true },
    { id := 2, name := "matC", ty := .sarray .i64, borrow := true }
  ]
  retTy     := .sarray .i64
  assurance := .verifiedKernelProof
  isGpuCand := true
  body      :=
    .letBind 3 .i64 (.sarrayLen 0) (
      .parFor 4 3 [0, 1, 2] .i64
        (.customScalar 10 [0, 1, 2] (.fma (.var 0) (.var 1) (.var 2)))
        (.ret 4)
    )
}

/-- Construct the canonical 8-kernel benchmark `LNIRModule` (6 core + 2 EVM/Verity 256-bit kernels). -/
def mkCanonicalBenchmarkModule : LNIRModule := {
  moduleName := "LeanNative.Benchmarks.Canonical"
  decls      := [
    collatzStepsDecl,
    tupleAccumSumDecl,
    sarrayScaleBiasDecl,
    dotProductU64Decl,
    saxpyKernelDecl,
    matmulTiledU64Decl,
    evmErc20TransferU256Decl,
    evmMuldivWadU256Decl
  ]
}

end Codec

/-- Canonical 8-kernel benchmark module including the 6 core workloads and 2 EVM/Verity `u256` workloads. -/
def mkCanonicalBenchmarkModule8 : LNIRModule :=
  Codec.mkCanonicalBenchmarkModule

/-! ## Lossless Wire & JSON Serialization / Deserialization -/

private def hexEncodeString (s : String) : String :=
  let hexChars := "0123456789abcdef".toList
  let bytes := s.toUTF8
  let chars : List Char := bytes.foldl (fun acc b =>
    let hi := ((b >>> 4) &&& 0xf).toNat
    let lo := (b &&& 0xf).toNat
    let cHi := hexChars[hi]?.getD '0'
    let cLo := hexChars[lo]?.getD '0'
    acc ++ [cHi, cLo]
  ) []
  if chars.isEmpty then "_" else String.ofList chars

private def hexNibbleVal (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat).toUInt8
  else none

private def hexDecodeChars : List Char → List UInt8 → Option ByteArray
  | [], acc => some (ByteArray.mk acc.reverse.toArray)
  | [ _ ], _ => none
  | c1 :: c2 :: rest, acc =>
    match hexNibbleVal c1, hexNibbleVal c2 with
    | some hi, some lo =>
      let b : UInt8 := (hi <<< 4) ||| lo
      hexDecodeChars rest (b :: acc)
    | _, _ => none

private def hexDecodeString (s : String) : Option String :=
  if s == "_" then some ""
  else
    match hexDecodeChars s.toList [] with
    | some bytes => String.fromUTF8? bytes
    | none => none

private def encodeBool (b : Bool) : String :=
  if b then "1" else "0"

private def decodeBool (s : String) : Option Bool :=
  if s == "1" then some true
  else if s == "0" then some false
  else none

private def encodeNat (n : Nat) : String :=
  toString n

private def decodeNat (s : String) : Option Nat :=
  s.toNat?

private def encodeU64 (x : UInt64) : String :=
  toString x.toNat

private def decodeU64 (s : String) : Option UInt64 := do
  let n ← s.toNat?
  some (UInt64.ofNat n)

private def encodeU256Tokens (w : UInt256) : List String :=
  [encodeU64 w.lo0, encodeU64 w.lo1, encodeU64 w.hi0, encodeU64 w.hi1]

private def decodeU256Tokens : List String → Option (UInt256 × List String)
  | t0 :: t1 :: t2 :: t3 :: rest => do
    let l0 ← decodeU64 t0
    let l1 ← decodeU64 t1
    let h0 ← decodeU64 t2
    let h1 ← decodeU64 t3
    some (⟨l0, l1, h0, h1⟩, rest)
  | _ => none

private def encodeAssurance (a : AssuranceLevel) : String :=
  match a with
  | .verifiedKernelProof  => "A_L3"
  | .translationValidated => "A_L2"
  | .unverifiedFallback   => "A_L1"

private def decodeAssurance : String → Option AssuranceLevel
  | "A_L3" => some .verifiedKernelProof
  | "A_L2" => some .translationValidated
  | "A_L1" => some .unverifiedFallback
  | _      => none

mutual
  private def encodeTypeTokens : LNIRType → List String
    | .i1          => ["T_i1"]
    | .i8          => ["T_i8"]
    | .i16         => ["T_i16"]
    | .i32         => ["T_i32"]
    | .i64         => ["T_i64"]
    | .usize       => ["T_usize"]
    | .u256        => ["T_u256"]
    | .i256        => ["T_i256"]
    | .f32         => ["T_f32"]
    | .f64         => ["T_f64"]
    | .objPtr      => ["T_objPtr"]
    | .taggedPtr   => ["T_taggedPtr"]
    | .tuple fs    => "T_tuple" :: encodeNat fs.length :: encodeTypeListTokens fs
    | .sarray e    => "T_sarray" :: encodeTypeTokens e
    | .rawPtr e    => "T_rawPtr" :: encodeTypeTokens e
    | .storageMap  => ["T_storageMap"]
    | .unit        => ["T_unit"]

  private def encodeTypeListTokens : List LNIRType → List String
    | [] => []
    | t :: ts => encodeTypeTokens t ++ encodeTypeListTokens ts
end

mutual
  private def decodeTypeTokens (fuel : Nat) (toks : List String) : Option (LNIRType × List String) :=
    match fuel, toks with
    | 0, _ => none
    | _, [] => none
    | f + 1, tag :: rest =>
      match tag with
      | "T_i1"         => some (.i1, rest)
      | "T_i8"         => some (.i8, rest)
      | "T_i16"        => some (.i16, rest)
      | "T_i32"        => some (.i32, rest)
      | "T_i64"        => some (.i64, rest)
      | "T_usize"      => some (.usize, rest)
      | "T_u256"       => some (.u256, rest)
      | "T_i256"       => some (.i256, rest)
      | "T_f32"        => some (.f32, rest)
      | "T_f64"        => some (.f64, rest)
      | "T_objPtr"     => some (.objPtr, rest)
      | "T_taggedPtr"  => some (.taggedPtr, rest)
      | "T_storageMap" => some (.storageMap, rest)
      | "T_unit"       => some (.unit, rest)
      | "T_sarray"     => do
        let (elem, rest1) ← decodeTypeTokens f rest
        some (.sarray elem, rest1)
      | "T_rawPtr"     => do
        let (elem, rest1) ← decodeTypeTokens f rest
        some (.rawPtr elem, rest1)
      | "T_tuple"      =>
        match rest with
        | countTok :: rest1 => do
          let count ← decodeNat countTok
          let (fs, rest2) ← decodeTypeListTokens f count rest1
          some (.tuple fs, rest2)
        | [] => none
      | _ => none

  private def decodeTypeListTokens (fuel : Nat) (count : Nat) (toks : List String) :
      Option (List LNIRType × List String) :=
    match fuel, count with
    | _, 0 => some ([], toks)
    | 0, _ + 1 => none
    | f + 1, c + 1 => do
      let (t, rest1) ← decodeTypeTokens f toks
      let (ts, rest2) ← decodeTypeListTokens f c rest1
      some (t :: ts, rest2)
end

private def encodeBinOp : BinOp → String
  | .add           => "B_add"
  | .sub           => "B_sub"
  | .mul           => "B_mul"
  | .div           => "B_div"
  | .mod           => "B_mod"
  | .bitAnd        => "B_bitAnd"
  | .bitOr         => "B_bitOr"
  | .bitXor        => "B_bitXor"
  | .shl           => "B_shl"
  | .shr           => "B_shr"
  | .sar           => "B_sar"
  | .eq            => "B_eq"
  | .lt            => "B_lt"
  | .le            => "B_le"
  | .addChecked256 => "B_addChecked256"
  | .subChecked256 => "B_subChecked256"
  | .mulChecked256 => "B_mulChecked256"

private def decodeBinOp : String → Option BinOp
  | "B_add"           => some .add
  | "B_sub"           => some .sub
  | "B_mul"           => some .mul
  | "B_div"           => some .div
  | "B_mod"           => some .mod
  | "B_bitAnd"        => some .bitAnd
  | "B_bitOr"         => some .bitOr
  | "B_bitXor"        => some .bitXor
  | "B_shl"           => some .shl
  | "B_shr"           => some .shr
  | "B_sar"           => some .sar
  | "B_eq"            => some .eq
  | "B_lt"            => some .lt
  | "B_le"            => some .le
  | "B_addChecked256" => some .addChecked256
  | "B_subChecked256" => some .subChecked256
  | "B_mulChecked256" => some .mulChecked256
  | _                 => none

private def encodeUnaryOp : UnaryOp → String
  | .not    => "U_not"
  | .neg    => "U_neg"
  | .clz256 => "U_clz256"

private def decodeUnaryOp : String → Option UnaryOp
  | "U_not"    => some .not
  | "U_neg"    => some .neg
  | "U_clz256" => some .clz256
  | _          => none

private def encodeScalarTokens : ScalarExpr → List String
  | .constU64 v       => ["S_u64", encodeU64 v]
  | .constBool b      => ["S_bool", encodeBool b]
  | .var id           => ["S_var", encodeNat id]
  | .binOp op l r     => "S_bin" :: encodeBinOp op :: encodeScalarTokens l ++ encodeScalarTokens r
  | .unaryOp op a     => "S_un" :: encodeUnaryOp op :: encodeScalarTokens a
  | .select c t e     => "S_sel" :: encodeScalarTokens c ++ encodeScalarTokens t ++ encodeScalarTokens e
  | .fma a b c        => "S_fma" :: encodeScalarTokens a ++ encodeScalarTokens b ++ encodeScalarTokens c

private def decodeScalarTokens (fuel : Nat) (toks : List String) : Option (ScalarExpr × List String) :=
  match fuel, toks with
  | 0, _ => none
  | _, [] => none
  | f + 1, tag :: rest =>
    match tag with
    | "S_u64" =>
      match rest with
      | vTok :: rest1 => do
        let v ← decodeU64 vTok
        some (.constU64 v, rest1)
      | [] => none
    | "S_bool" =>
      match rest with
      | bTok :: rest1 => do
        let b ← decodeBool bTok
        some (.constBool b, rest1)
      | [] => none
    | "S_var" =>
      match rest with
      | idTok :: rest1 => do
        let id ← decodeNat idTok
        some (.var id, rest1)
      | [] => none
    | "S_bin" =>
      match rest with
      | opTok :: rest1 => do
        let op ← decodeBinOp opTok
        let (l, rest2) ← decodeScalarTokens f rest1
        let (r, rest3) ← decodeScalarTokens f rest2
        some (.binOp op l r, rest3)
      | [] => none
    | "S_un" =>
      match rest with
      | opTok :: rest1 => do
        let op ← decodeUnaryOp opTok
        let (a, rest2) ← decodeScalarTokens f rest1
        some (.unaryOp op a, rest2)
      | [] => none
    | "S_sel" => do
      let (c, rest1) ← decodeScalarTokens f rest
      let (t, rest2) ← decodeScalarTokens f rest1
      let (e, rest3) ← decodeScalarTokens f rest2
      some (.select c t e, rest3)
    | "S_fma" => do
      let (a, rest1) ← decodeScalarTokens f rest
      let (b, rest2) ← decodeScalarTokens f rest1
      let (c, rest3) ← decodeScalarTokens f rest2
      some (.fma a b c, rest3)
    | _ => none

private def encodeNatListTokens (xs : List Nat) : List String :=
  encodeNat xs.length :: xs.map encodeNat

private def decodeNatItems : Nat → List String → Option (List Nat × List String)
  | 0, toks => some ([], toks)
  | n + 1, t :: rest => do
    let x ← decodeNat t
    let (xs, rest') ← decodeNatItems n rest
    some (x :: xs, rest')
  | _ + 1, [] => none

private def decodeNatListTokens : List String → Option (List Nat × List String)
  | lenTok :: rest => do
    let len ← decodeNat lenTok
    decodeNatItems len rest
  | [] => none

private def encodeKernelTokens : ParallelKernelKind → List String
  | .mapScaleAdd s b => ["K_msa", encodeU64 s, encodeU64 b]
  | .zipAdd          => ["K_za"]
  | .zipMul          => ["K_zm"]
  | .saxpy a         => ["K_saxpy", encodeU64 a]
  | .dotProduct      => ["K_dot"]
  | .stencil1D3Pt l c r => ["K_st3", encodeU64 l, encodeU64 c, encodeU64 r]
  | .customScalar iv ins body =>
    "K_cust" :: encodeNat iv :: encodeNatListTokens ins ++ encodeScalarTokens body

private def decodeKernelTokens (fuel : Nat) (toks : List String) :
    Option (ParallelKernelKind × List String) :=
  match toks with
  | "K_msa" :: sTok :: bTok :: rest => do
    let s ← decodeU64 sTok
    let b ← decodeU64 bTok
    some (.mapScaleAdd s b, rest)
  | "K_za" :: rest => some (.zipAdd, rest)
  | "K_zm" :: rest => some (.zipMul, rest)
  | "K_saxpy" :: aTok :: rest => do
    let a ← decodeU64 aTok
    some (.saxpy a, rest)
  | "K_dot" :: rest => some (.dotProduct, rest)
  | "K_st3" :: lTok :: cTok :: rTok :: rest => do
    let l ← decodeU64 lTok
    let c ← decodeU64 cTok
    let r ← decodeU64 rTok
    some (.stencil1D3Pt l c r, rest)
  | "K_cust" :: ivTok :: rest => do
    let iv ← decodeNat ivTok
    let (ins, rest1) ← decodeNatListTokens rest
    let (body, rest2) ← decodeScalarTokens fuel rest1
    some (.customScalar iv ins body, rest2)
  | _ => none

private def encodeExprTokens : LNIRExpr → List String
  | .scalar se => "E_scalar" :: encodeScalarTokens se
  | .constU256 w => "E_u256" :: encodeU256Tokens w
  | .mulDivDown a b d => ["E_mdd", encodeNat a, encodeNat b, encodeNat d]
  | .mulDivUp a b d => ["E_mdu", encodeNat a, encodeNat b, encodeNat d]
  | .storageLoad m s => ["E_sload", encodeNat m, encodeNat s]
  | .storageStore m s v => ["E_sstore", encodeNat m, encodeNat s, encodeNat v]
  | .mkTuple fs => "E_mktup" :: encodeNatListTokens fs
  | .projTuple tv idx => ["E_projtup", encodeNat tv, encodeNat idx]
  | .allocCtor tag objs scals =>
    "E_ctor" :: encodeNat tag :: encodeNatListTokens objs ++ encodeNatListTokens scals
  | .ctorGetObj cv idx => ["E_cgeto", encodeNat cv, encodeNat idx]
  | .ctorGetScalar cv idx ty => "E_cgets" :: encodeNat cv :: encodeNat idx :: encodeTypeTokens ty
  | .isExclusive ov => ["E_isexcl", encodeNat ov]
  | .sarrayLen av => ["E_salen", encodeNat av]
  | .sarrayDataPtr av ty => "E_sadptr" :: encodeNat av :: encodeTypeTokens ty
  | .sarrayEnsureExclusive av ty => "E_saexcl" :: encodeNat av :: encodeTypeTokens ty
  | .sarrayGet av iv ty => "E_saget" :: encodeNat av :: encodeNat iv :: encodeTypeTokens ty
  | .sarraySet av iv vv ty => "E_saset" :: encodeNat av :: encodeNat iv :: encodeNat vv :: encodeTypeTokens ty
  | .rawLoad pv iv ty => "E_rload" :: encodeNat pv :: encodeNat iv :: encodeTypeTokens ty
  | .boxScalar vv ty => "E_box" :: encodeNat vv :: encodeTypeTokens ty
  | .unboxScalar bv ty => "E_unbox" :: encodeNat bv :: encodeTypeTokens ty
  | .call fn args rty isExt =>
    "E_call" :: hexEncodeString fn :: encodeBool isExt :: encodeNatListTokens args ++ encodeTypeTokens rty

private def decodeExprTokens (fuel : Nat) (toks : List String) : Option (LNIRExpr × List String) :=
  match toks with
  | "E_scalar" :: rest => do
    let (se, rest1) ← decodeScalarTokens fuel rest
    some (.scalar se, rest1)
  | "E_u256" :: rest => do
    let (w, rest1) ← decodeU256Tokens rest
    some (.constU256 w, rest1)
  | "E_mdd" :: aT :: bT :: dT :: rest => do
    let a ← decodeNat aT
    let b ← decodeNat bT
    let d ← decodeNat dT
    some (.mulDivDown a b d, rest)
  | "E_mdu" :: aT :: bT :: dT :: rest => do
    let a ← decodeNat aT
    let b ← decodeNat bT
    let d ← decodeNat dT
    some (.mulDivUp a b d, rest)
  | "E_sload" :: mT :: sT :: rest => do
    let m ← decodeNat mT
    let s ← decodeNat sT
    some (.storageLoad m s, rest)
  | "E_sstore" :: mT :: sT :: vT :: rest => do
    let m ← decodeNat mT
    let s ← decodeNat sT
    let v ← decodeNat vT
    some (.storageStore m s v, rest)
  | "E_mktup" :: rest => do
    let (fs, rest1) ← decodeNatListTokens rest
    some (.mkTuple fs, rest1)
  | "E_projtup" :: tvT :: idxT :: rest => do
    let tv ← decodeNat tvT
    let idx ← decodeNat idxT
    some (.projTuple tv idx, rest)
  | "E_ctor" :: tagT :: rest => do
    let tag ← decodeNat tagT
    let (objs, rest1) ← decodeNatListTokens rest
    let (scals, rest2) ← decodeNatListTokens rest1
    some (.allocCtor tag objs scals, rest2)
  | "E_cgeto" :: cvT :: idxT :: rest => do
    let cv ← decodeNat cvT
    let idx ← decodeNat idxT
    some (.ctorGetObj cv idx, rest)
  | "E_cgets" :: cvT :: idxT :: rest => do
    let cv ← decodeNat cvT
    let idx ← decodeNat idxT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some (.ctorGetScalar cv idx ty, rest1)
  | "E_isexcl" :: ovT :: rest => do
    let ov ← decodeNat ovT
    some (.isExclusive ov, rest)
  | "E_salen" :: avT :: rest => do
    let av ← decodeNat avT
    some (.sarrayLen av, rest)
  | "E_sadptr" :: avT :: rest => do
    let av ← decodeNat avT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some (.sarrayDataPtr av ty, rest1)
  | "E_saexcl" :: avT :: rest => do
    let av ← decodeNat avT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some (.sarrayEnsureExclusive av ty, rest1)
  | "E_saget" :: avT :: ivT :: rest => do
    let av ← decodeNat avT
    let iv ← decodeNat ivT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some (.sarrayGet av iv ty, rest1)
  | "E_saset" :: avT :: ivT :: vvT :: rest => do
    let av ← decodeNat avT
    let iv ← decodeNat ivT
    let vv ← decodeNat vvT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some (.sarraySet av iv vv ty, rest1)
  | "E_rload" :: pvT :: ivT :: rest => do
    let pv ← decodeNat pvT
    let iv ← decodeNat ivT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some (.rawLoad pv iv ty, rest1)
  | "E_box" :: vvT :: rest => do
    let vv ← decodeNat vvT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some (.boxScalar vv ty, rest1)
  | "E_unbox" :: bvT :: rest => do
    let bv ← decodeNat bvT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some (.unboxScalar bv ty, rest1)
  | "E_call" :: fnHex :: extT :: rest => do
    let fn ← hexDecodeString fnHex
    let isExt ← decodeBool extT
    let (args, rest1) ← decodeNatListTokens rest
    let (rty, rest2) ← decodeTypeTokens fuel rest1
    some (.call fn args rty isExt, rest2)
  | _ => none

private def encodeCodeTokens : LNIRCode → List String
  | .letBind dst ty val k =>
    "C_let" :: encodeNat dst :: encodeTypeTokens ty ++ encodeExprTokens val ++ encodeCodeTokens k
  | .rawStore pv iv vv ty k =>
    "C_rstore" :: encodeNat pv :: encodeNat iv :: encodeNat vv :: encodeTypeTokens ty ++ encodeCodeTokens k
  | .incRef ov cnt k =>
    "C_inc" :: encodeNat ov :: encodeNat cnt :: encodeCodeTokens k
  | .decRef ov cnt k =>
    "C_dec" :: encodeNat ov :: encodeNat cnt :: encodeCodeTokens k
  | .ite cv t e =>
    "C_ite" :: encodeNat cv :: encodeCodeTokens t ++ encodeCodeTokens e
  | .seqFor iv lv hv av ai aty step k =>
    "C_seq" :: encodeNat iv :: encodeNat lv :: encodeNat hv :: encodeNat av :: encodeNat ai ::
      encodeTypeTokens aty ++ encodeCodeTokens step ++ encodeCodeTokens k
  | .parFor ov lv ins ety kern k =>
    "C_par" :: encodeNat ov :: encodeNat lv ::
      encodeNatListTokens ins ++ encodeTypeTokens ety ++ encodeKernelTokens kern ++ encodeCodeTokens k
  | .ret v => ["C_ret", encodeNat v]
  | .unreachable => ["C_unreach"]

private def decodeCodeTokens (fuel : Nat) (toks : List String) : Option (LNIRCode × List String) :=
  match fuel, toks with
  | 0, _ => none
  | _, [] => none
  | f + 1, tag :: rest =>
    match tag with
    | "C_let" =>
      match rest with
      | dstT :: rest1 => do
        let dst ← decodeNat dstT
        let (ty, rest2) ← decodeTypeTokens f rest1
        let (val, rest3) ← decodeExprTokens f rest2
        let (k, rest4) ← decodeCodeTokens f rest3
        some (.letBind dst ty val k, rest4)
      | [] => none
    | "C_rstore" =>
      match rest with
      | pvT :: ivT :: vvT :: rest1 => do
        let pv ← decodeNat pvT
        let iv ← decodeNat ivT
        let vv ← decodeNat vvT
        let (ty, rest2) ← decodeTypeTokens f rest1
        let (k, rest3) ← decodeCodeTokens f rest2
        some (.rawStore pv iv vv ty k, rest3)
      | _ => none
    | "C_inc" =>
      match rest with
      | ovT :: cntT :: rest1 => do
        let ov ← decodeNat ovT
        let cnt ← decodeNat cntT
        let (k, rest2) ← decodeCodeTokens f rest1
        some (.incRef ov cnt k, rest2)
      | _ => none
    | "C_dec" =>
      match rest with
      | ovT :: cntT :: rest1 => do
        let ov ← decodeNat ovT
        let cnt ← decodeNat cntT
        let (k, rest2) ← decodeCodeTokens f rest1
        some (.decRef ov cnt k, rest2)
      | _ => none
    | "C_ite" =>
      match rest with
      | cvT :: rest1 => do
        let cv ← decodeNat cvT
        let (t, rest2) ← decodeCodeTokens f rest1
        let (e, rest3) ← decodeCodeTokens f rest2
        some (.ite cv t e, rest3)
      | [] => none
    | "C_seq" =>
      match rest with
      | ivT :: lvT :: hvT :: avT :: aiT :: rest1 => do
        let iv ← decodeNat ivT
        let lv ← decodeNat lvT
        let hv ← decodeNat hvT
        let av ← decodeNat avT
        let ai ← decodeNat aiT
        let (aty, rest2) ← decodeTypeTokens f rest1
        let (step, rest3) ← decodeCodeTokens f rest2
        let (k, rest4) ← decodeCodeTokens f rest3
        some (.seqFor iv lv hv av ai aty step k, rest4)
      | _ => none
    | "C_par" =>
      match rest with
      | ovT :: lvT :: rest1 => do
        let ov ← decodeNat ovT
        let lv ← decodeNat lvT
        let (ins, rest2) ← decodeNatListTokens rest1
        let (ety, rest3) ← decodeTypeTokens f rest2
        let (kern, rest4) ← decodeKernelTokens f rest3
        let (k, rest5) ← decodeCodeTokens f rest4
        some (.parFor ov lv ins ety kern k, rest5)
      | _ => none
    | "C_ret" =>
      match rest with
      | vT :: rest1 => do
        let v ← decodeNat vT
        some (.ret v, rest1)
      | [] => none
    | "C_unreach" =>
      some (.unreachable, rest)
    | _ => none

private def encodeParamTokens (p : LNIRParam) : List String :=
  encodeNat p.id :: hexEncodeString p.name :: encodeBool p.borrow :: encodeTypeTokens p.ty

private def decodeParamTokens (fuel : Nat) (toks : List String) : Option (LNIRParam × List String) :=
  match toks with
  | idT :: nameHex :: borrowT :: rest => do
    let id ← decodeNat idT
    let name ← hexDecodeString nameHex
    let borrow ← decodeBool borrowT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some ({ id, name, ty, borrow }, rest1)
  | _ => none

private def decodeParamList (fuel : Nat) : Nat → List String → Option (List LNIRParam × List String)
  | 0, toks => some ([], toks)
  | n + 1, toks => do
    let (p, rest1) ← decodeParamTokens fuel toks
    let (ps, rest2) ← decodeParamList fuel n rest1
    some (p :: ps, rest2)

private def encodeDeclTokens (d : LNIRDecl) : List String :=
  let paramToks := d.params.foldr (fun p acc => encodeParamTokens p ++ acc) []
  "D_decl" ::
    hexEncodeString d.name ::
    encodeAssurance d.assurance ::
    encodeBool d.isGpuCand ::
    encodeNat d.params.length ::
    paramToks ++
    encodeTypeTokens d.retTy ++
    encodeCodeTokens d.body

private def decodeDeclTokens (fuel : Nat) (toks : List String) : Option (LNIRDecl × List String) :=
  match toks with
  | "D_decl" :: nameHex :: assT :: gpuT :: pLenT :: rest => do
    let name ← hexDecodeString nameHex
    let assurance ← decodeAssurance assT
    let isGpuCand ← decodeBool gpuT
    let pLen ← decodeNat pLenT
    let (params, rest1) ← decodeParamList fuel pLen rest
    let (retTy, rest2) ← decodeTypeTokens fuel rest1
    let (body, rest3) ← decodeCodeTokens fuel rest2
    some ({ name, params, retTy, body, assurance, isGpuCand }, rest3)
  | _ => none

private def decodeDeclList (fuel : Nat) : Nat → List String → Option (List LNIRDecl × List String)
  | 0, toks => some ([], toks)
  | n + 1, toks => do
    let (d, rest1) ← decodeDeclTokens fuel toks
    let (ds, rest2) ← decodeDeclList fuel n rest1
    some (d :: ds, rest2)

private def escapeJsonCodec (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | other => acc.push other
  ) ""

private def extractJsonFieldCodec (json : String) (key : String) : Option String :=
  let pat := "\"" ++ key ++ "\":\""
  match json.splitOn pat with
  | _ :: afterKey :: _ =>
    match afterKey.splitOn "\"" with
    | val :: _ => some val
    | [] => none
  | _ => none

/-- Serialize an `LNIRModule` into the deterministic, lossless `LNIR_WIRE_V1` token wire format. -/
def LNIRModule.toWire (m : LNIRModule) : String :=
  let declToks := m.decls.foldr (fun d acc => encodeDeclTokens d ++ acc) []
  let allToks := "LNIR_WIRE_V1" :: hexEncodeString m.moduleName :: encodeNat m.decls.length :: declToks
  String.intercalate "|" allToks

/-- Serialize a single `LNIRDecl` to JSON metadata. -/
def LNIRDecl.toJson (d : LNIRDecl) : String :=
  let paramsJson := String.intercalate "," (d.params.map fun p =>
    "{" ++
    s!"\"id\":{p.id}," ++
    s!"\"name\":\"{escapeJsonCodec p.name}\"," ++
    s!"\"ty\":\"{escapeJsonCodec p.ty.toLLVMType}\"," ++
    s!"\"borrow\":{if p.borrow then "true" else "false"}" ++
    "}")
  "{" ++
  s!"\"name\":\"{escapeJsonCodec d.name}\"," ++
  s!"\"retTy\":\"{escapeJsonCodec d.retTy.toLLVMType}\"," ++
  s!"\"assurance\":\"{d.assurance.toString}\"," ++
  s!"\"isGpuCand\":{if d.isGpuCand then "true" else "false"}," ++
  s!"\"structuralHash\":\"{d.structuralHash}\"," ++
  s!"\"params\":[{paramsJson}]" ++
  "}"

/-- Serialize an `LNIRModule` to JSON (including lossless embedded `wire` payload). -/
def LNIRModule.toJson (m : LNIRModule) : String :=
  let declsJson := String.intercalate "," (m.decls.map LNIRDecl.toJson)
  let wirePayload := m.toWire
  "{" ++
  "\"schemaVersion\":\"lean-native-lnir-v1\"," ++
  s!"\"moduleName\":\"{escapeJsonCodec m.moduleName}\"," ++
  s!"\"declCount\":{m.decls.length}," ++
  s!"\"decls\":[{declsJson}]," ++
  s!"\"wire\":\"{escapeJsonCodec wirePayload}\"" ++
  "}"

/-- Deserialize an `LNIRModule` from `LNIR_WIRE_V1` wire format (or named/JSON module). -/
def LNIRModule.fromWire? (s : String) : Option LNIRModule :=
  let trimmed := s.trimAscii.toString
  if trimmed == "canonical" || trimmed == "LeanNative.Benchmarks.Canonical" then
    some Codec.mkCanonicalBenchmarkModule
  else if trimmed == "fastcheck" || trimmed == "LeanNative.FastCheck.Sample" then
    some mkFastCheckSampleModule
  else
    let rawWire :=
      if trimmed.startsWith "{" then
        (extractJsonFieldCodec trimmed "wire").getD trimmed
      else
        trimmed
    match rawWire.splitOn "|" with
    | "LNIR_WIRE_V1" :: modNameHex :: declCountTok :: rest => do
      let moduleName ← hexDecodeString modNameHex
      let declCount ← decodeNat declCountTok
      let (decls, rem) ← decodeDeclList 4096 declCount rest
      if rem.isEmpty then
        some { moduleName, decls }
      else
        none
    | _ =>
      match extractJsonFieldCodec trimmed "moduleName" with
      | some "LeanNative.Benchmarks.Canonical" => some Codec.mkCanonicalBenchmarkModule
      | some "LeanNative.FastCheck.Sample" => some mkFastCheckSampleModule
      | _ => none

/-- Deserialize an `LNIRModule` from JSON (`LNIRModule.toJson`) or wire format. -/
def LNIRModule.fromJson? (s : String) : Option LNIRModule :=
  LNIRModule.fromWire? s

end LeanNative.IR
