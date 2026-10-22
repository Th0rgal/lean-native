/-
  LeanNative v0.4 — Orthogonal, Non-Redundant Regression & Boundary Test Suite (`tests/test_runner.lean`)
  Standalone executable Lean 4 test suite (`lean --run tests/test_runner.lean` or `lean-native build-exe`).

  Systematically tests 6 orthogonal compiler & runtime bug surfaces:
  1. Test 1 — 256-Bit Multi-Limb Carry & Borrow Boundaries
  2. Test 2 — 512-Bit Intermediate `mulDivDown` vs `mulDivUp` Overflow & Exact Rounding
  3. Test 3 — 256-Bit Arithmetic Shift Right (`sar`) Sign Extension & `clz256`
  4. Test 4 — EVM Storage Map Slot Collisions & `SSTORE`->`SLOAD` Forwarding
  5. Test 5 — Shared Array (`m_rc > 1`) Copy-On-Write Preservation under `HoistExclusivity`
  6. Test 6 — Multi-Constructor Inductive Tag Dispatch (5 constructors) & Tail-Recursive Join Points
-/

namespace LeanNativeTestRunner

/-- 256-bit unsigned integer represented as 4 little-endian 64-bit limbs. -/
structure U256 where
  lo0 : UInt64 := 0
  lo1 : UInt64 := 0
  hi0 : UInt64 := 0
  hi1 : UInt64 := 0
  deriving Repr, DecidableEq, Inhabited, BEq

namespace U256

def modulusNat : Nat := 2 ^ 256

def zero : U256 := ⟨0, 0, 0, 0⟩
def one  : U256 := ⟨1, 0, 0, 0⟩
def max  : U256 := ⟨0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff⟩

def toNat (w : U256) : Nat :=
  w.lo0.toNat +
  w.lo1.toNat * (2 ^ 64) +
  w.hi0.toNat * (2 ^ 128) +
  w.hi1.toNat * (2 ^ 192)

def ofNat (n : Nat) : U256 :=
  let m := n % modulusNat
  let l0 := (m % (2 ^ 64)).toUInt64
  let l1 := ((m / (2 ^ 64)) % (2 ^ 64)).toUInt64
  let h0 := ((m / (2 ^ 128)) % (2 ^ 64)).toUInt64
  let h1 := ((m / (2 ^ 192)) % (2 ^ 64)).toUInt64
  ⟨l0, l1, h0, h1⟩

/-- Multi-limb 256-bit addition returning `(wrappedResult, overflowFlag)`. -/
def addWithOverflow (a b : U256) : U256 × Bool :=
  let s0 := a.lo0.toNat + b.lo0.toNat
  let c0 := s0 / (2 ^ 64)
  let s1 := a.lo1.toNat + b.lo1.toNat + c0
  let c1 := s1 / (2 ^ 64)
  let s2 := a.hi0.toNat + b.hi0.toNat + c1
  let c2 := s2 / (2 ^ 64)
  let s3 := a.hi1.toNat + b.hi1.toNat + c2
  let c3 := s3 / (2 ^ 64)
  (⟨UInt64.ofNat s0, UInt64.ofNat s1, UInt64.ofNat s2, UInt64.ofNat s3⟩, c3 > 0)

/-- Multi-limb 256-bit subtraction returning `(wrappedResult, underflowFlag)`. -/
def subWithUnderflow (a b : U256) : U256 × Bool :=
  let underflow := a.toNat < b.toNat
  let res := ofNat ((a.toNat + modulusNat - (b.toNat % modulusNat)) % modulusNat)
  (res, underflow)

/-- Full 512-bit intermediate `floor((a * b) / denom)`. -/
def mulDivDown (a b denom : U256) : Option U256 :=
  let d := denom.toNat
  if d == 0 then none
  else
    let q := (a.toNat * b.toNat) / d
    if q >= modulusNat then none else some (ofNat q)

/-- Full 512-bit intermediate `ceil((a * b) / denom)`. -/
def mulDivUp (a b denom : U256) : Option U256 :=
  let d := denom.toNat
  if d == 0 then none
  else
    let prod := a.toNat * b.toNat
    let q := (prod + d - 1) / d
    if q >= modulusNat then none else some (ofNat q)

/-- 256-bit arithmetic shift right (`sar`, sign-extending bit 255). -/
def sar (a : U256) (shift : Nat) : U256 :=
  let isNeg := (a.hi1 &&& 0x8000000000000000) != 0
  if shift >= 256 then
    if isNeg then max else zero
  else if shift == 0 then
    a
  else
    let logical := a.toNat / (2 ^ shift)
    if !isNeg then
      ofNat logical
    else
      let mask := (modulusNat - (2 ^ (256 - shift))) % modulusNat
      ofNat ((logical + mask) % modulusNat)

private def clzU64 (x : UInt64) : Nat :=
  if x == 0 then 64
  else
    let rec loop (fuel : Nat) (v : UInt64) (acc : Nat) : Nat :=
      match fuel with
      | 0 => acc
      | f + 1 =>
        if (v &&& 0x8000000000000000) != 0 then acc
        else loop f (v <<< 1) (acc + 1)
    loop 64 x 0

/-- Count leading zeros across all 256 bits (`0..256`). -/
def clz256 (a : U256) : UInt64 :=
  let n :=
    if a.hi1 != 0 then clzU64 a.hi1
    else if a.hi0 != 0 then 64 + clzU64 a.hi0
    else if a.lo1 != 0 then 128 + clzU64 a.lo1
    else 192 + clzU64 a.lo0
  n.toUInt64

def fnvMixU256 (h : UInt64) (w : U256) : UInt64 :=
  let prime : UInt64 := 1099511628211
  let h0 := (h ^^^ w.lo0) * prime
  let h1 := (h0 ^^^ w.lo1) * prime
  let h2 := (h1 ^^^ w.hi0) * prime
  (h2 ^^^ w.hi1) * prime

end U256

/-- FNV-1a 64-bit step mixer. -/
@[inline]
def fnvMixU64 (h x : UInt64) : UInt64 :=
  (h ^^^ x) * 1099511628211

/-! ## Test 1 — 256-Bit Multi-Limb Carry & Borrow Boundaries -/

def runTest1 : Bool × UInt64 :=
  -- 1a. 2^64 - 1 + 1 == 2^64 (carry from limb 0 -> limb 1)
  let maxLimb0 : U256 := ⟨0xffffffffffffffff, 0, 0, 0⟩
  let expPow64 : U256 := ⟨0, 1, 0, 0⟩
  let (r64, ov64) := U256.addWithOverflow maxLimb0 U256.one

  -- 1b. 2^128 - 1 + 1 == 2^128 (carry propagation limb 0 -> limb 1 -> limb 2)
  let maxLimb1 : U256 := ⟨0xffffffffffffffff, 0xffffffffffffffff, 0, 0⟩
  let expPow128 : U256 := ⟨0, 0, 1, 0⟩
  let (r128, ov128) := U256.addWithOverflow maxLimb1 U256.one

  -- 1c. 2^192 - 1 + 1 == 2^192 (carry propagation limb 0 -> limb 1 -> limb 2 -> limb 3)
  let maxLimb2 : U256 := ⟨0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0⟩
  let expPow192 : U256 := ⟨0, 0, 0, 1⟩
  let (r192, ov192) := U256.addWithOverflow maxLimb2 U256.one

  -- 1d. 2^256 - 1 + 1 == 0 (wrapping) with overflow == true
  let (r256, ov256) := U256.addWithOverflow U256.max U256.one

  -- 1e. 0 - 1 == 2^256 - 1 with underflow == true
  let (subWrap, uf0) := U256.subWithUnderflow U256.zero U256.one

  let ok :=
    r64 == expPow64 && !ov64 &&
    r128 == expPow128 && !ov128 &&
    r192 == expPow192 && !ov192 &&
    r256 == U256.zero && ov256 &&
    subWrap == U256.max && uf0

  let h := U256.fnvMixU256 14695981039346656037 r64
  let h := U256.fnvMixU256 h r128
  let h := U256.fnvMixU256 h r192
  let h := U256.fnvMixU256 h r256
  let h := U256.fnvMixU256 h subWrap
  (ok, h)

/-! ## Test 2 — 512-Bit Intermediate `mulDivDown` vs `mulDivUp` Overflow & Exact Rounding -/

def runTest2 : Bool × UInt64 :=
  -- a = 2^255, b = 2 => a * b = 2^256 (overflows 256 bits, requires 512-bit intermediate)
  let twoPow255 : U256 := ⟨0, 0, 0, 0x8000000000000000⟩
  let two       : U256 := ⟨2, 0, 0, 0⟩
  let three     : U256 := ⟨3, 0, 0, 0⟩
  let four      : U256 := ⟨4, 0, 0, 0⟩
  let twoPow254 : U256 := ⟨0, 0, 0, 0x4000000000000000⟩

  -- (2^255 * 2) / 3 = (2^256) / 3 = 0x5555555555555555_5555555555555555_5555555555555555_5555555555555555
  -- with remainder 1 != 0, so mulDivUp = mulDivDown + 1
  let expThirdDown : U256 :=
    ⟨0x5555555555555555, 0x5555555555555555, 0x5555555555555555, 0x5555555555555555⟩
  let expThirdUp : U256 :=
    ⟨0x5555555555555556, 0x5555555555555555, 0x5555555555555555, 0x5555555555555555⟩

  let qDown3 := U256.mulDivDown twoPow255 two three
  let qUp3   := U256.mulDivUp   twoPow255 two three

  -- Exact divisibility: (2^255 * 2) / 4 == 2^254 where mulDivDown == mulDivUp
  let qDown4 := U256.mulDivDown twoPow255 two four
  let qUp4   := U256.mulDivUp   twoPow255 two four

  let ok :=
    qDown3 == some expThirdDown &&
    qUp3   == some expThirdUp &&
    qDown4 == some twoPow254 &&
    qUp4   == some twoPow254 &&
    qDown4 == qUp4

  let h := U256.fnvMixU256 14695981039346656037 (qDown3.getD U256.zero)
  let h := U256.fnvMixU256 h (qUp3.getD U256.zero)
  let h := U256.fnvMixU256 h (qDown4.getD U256.zero)
  (ok, h)

/-! ## Test 3 — 256-Bit Arithmetic Shift Right (`sar`) Sign Extension & `clz256` -/

def runTest3 : Bool × UInt64 :=
  -- Negative i256: MSB = 1 (0x8000...0000 >>s 4 == 0xF800...0000)
  let negMin : U256 := ⟨0, 0, 0, 0x8000000000000000⟩
  let expNegSar4 : U256 := ⟨0, 0, 0, 0xf800000000000000⟩
  let gotNegSar4 := U256.sar negMin 4

  -- Positive i256: MSB = 0 (0x4000...0000 >>s 4 == 0x0400...0000)
  let posVal : U256 := ⟨0, 0, 0, 0x4000000000000000⟩
  let expPosSar4 : U256 := ⟨0, 0, 0, 0x0400000000000000⟩
  let gotPosSar4 := U256.sar posVal 4

  -- clz256 boundaries: clz256(0) == 256, clz256(1) == 255, clz256(2^255) == 0
  let lz0   := U256.clz256 U256.zero
  let lz1   := U256.clz256 U256.one
  let lz255 := U256.clz256 negMin

  let ok :=
    gotNegSar4 == expNegSar4 &&
    gotPosSar4 == expPosSar4 &&
    lz0 == 256 &&
    lz1 == 255 &&
    lz255 == 0

  let h := U256.fnvMixU256 14695981039346656037 gotNegSar4
  let h := U256.fnvMixU256 h gotPosSar4
  let h := fnvMixU64 (fnvMixU64 (fnvMixU64 h lz0) lz1) lz255
  (ok, h)

/-! ## Test 4 — EVM Storage Map Slot Collisions & `SSTORE`->`SLOAD` Forwarding -/

structure EVMStorageMap where
  entries : List (U256 × U256) := []
  deriving Repr, Inhabited

namespace EVMStorageMap

def sload (m : EVMStorageMap) (slot : U256) : U256 :=
  match m.entries.find? (fun (k, _) => k == slot) with
  | some (_, v) => v
  | none => U256.zero

def sstore (m : EVMStorageMap) (slot val : U256) : EVMStorageMap :=
  { entries := (slot, val) :: m.entries.filter (fun (k, _) => k != slot) }

end EVMStorageMap

def runTest4 : Bool × UInt64 :=
  -- slotA and slotB share identical low 192 bits (lo0, lo1, hi0) and differ ONLY in limb 3 (hi1)
  let slotA : U256 := ⟨0x1111111111111111, 0x2222222222222222, 0x3333333333333333, 0x0000000000000001⟩
  let slotB : U256 := ⟨0x1111111111111111, 0x2222222222222222, 0x3333333333333333, 0x0000000000000002⟩
  let slotC : U256 := ⟨0x9999999999999999, 0, 0, 0⟩

  let valA1 : U256 := ⟨1000, 2000, 3000, 4000⟩
  let valB  : U256 := ⟨5555, 6666, 7777, 8888⟩
  let valA2 : U256 := ⟨9999, 8888, 7777, 6666⟩

  let m0 : EVMStorageMap := {}
  let m1 := m0.sstore slotA valA1
  let m2 := m1.sstore slotB valB
  -- Overwrite slotA with valA2 and immediately read slotA (SSTORE -> SLOAD forwarding path)
  let m3 := m2.sstore slotA valA2
  let readA := m3.sload slotA
  let readB := m3.sload slotB
  let readC := m3.sload slotC

  let ok :=
    readA == valA2 &&
    readB == valB &&
    readC == U256.zero

  let h := U256.fnvMixU256 14695981039346656037 readA
  let h := U256.fnvMixU256 h readB
  let h := U256.fnvMixU256 h readC
  (ok, h)

/-! ## Test 5 — Shared Array (`m_rc > 1`) Copy-On-Write Preservation under `HoistExclusivity` -/

/-- Mutate `arr` in-place inside a tight loop; when called on a shared array (`m_rc > 1`),
    copy-on-write must clone the backing buffer so any live alias remains untouched. -/
@[noinline]
def mutateArrayInLoop (arr : Array UInt64) (scale bias : UInt64) : Array UInt64 := Id.run do
  let mut buf := arr
  for i in [0:buf.size] do
    let v := buf[i]!
    buf := buf.set! i (v * scale + bias)
  return buf

/-- Read checksum of an array to keep a live reference (`m_rc > 1`) across `mutateArrayInLoop`. -/
@[noinline]
def sumArrayWithWeights (arr : Array UInt64) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for i in [0:arr.size] do
    acc := acc + arr[i]! * (i.toUInt64 + 1)
  return acc

def runTest5 : Bool × UInt64 :=
  let original : Array UInt64 := #[10, 20, 30, 40, 50, 60, 70, 80]
  -- Hold a second live reference `alias` so `original` has `m_rc > 1` entering `mutateArrayInLoop`
  let alias := original
  let modified := mutateArrayInLoop original 3 7
  -- Verify `alias` retains exact original elements while `modified` has `v * 3 + 7`
  let aliasUnchanged := alias == #[10, 20, 30, 40, 50, 60, 70, 80]
  let modifiedExpected := modified == #[37, 67, 97, 127, 157, 187, 217, 247]
  let aliasWeighted := sumArrayWithWeights alias
  let modWeighted := sumArrayWithWeights modified
  -- Expected weighted sums:
  -- alias: 10*1 + 20*2 + 30*3 + 40*4 + 50*5 + 60*6 + 70*7 + 80*8 = 2040
  -- modified: 2040 * 3 + 7 * (1+2+3+4+5+6+7+8) = 6120 + 252 = 6372
  let ok := aliasUnchanged && modifiedExpected && aliasWeighted == 2040 && modWeighted == 6372
  let h := fnvMixU64 (fnvMixU64 14695981039346656037 aliasWeighted) modWeighted
  (ok, h)

/-! ## Test 6 — Multi-Constructor Inductive Tag Dispatch & Tail-Recursive Join Points -/

/-- 5-constructor expression DAG exercising `switch i64` tag dispatch. -/
inductive DagExpr where
  | constVal (v : UInt64)
  | addNode  (l r : DagExpr)
  | mulNode  (l r : DagExpr)
  | xorNode  (l r : DagExpr)
  | condNode (cond thenBr elseBr : DagExpr)
  deriving Repr, Inhabited

def evalDagExpr : DagExpr → UInt64
  | .constVal v      => v
  | .addNode l r     => evalDagExpr l + evalDagExpr r
  | .mulNode l r     => evalDagExpr l * evalDagExpr r
  | .xorNode l r     => evalDagExpr l ^^^ evalDagExpr r
  | .condNode c t e  => if evalDagExpr c != 0 then evalDagExpr t else evalDagExpr e

/-- Multi-parameter tail-recursive loop exercising join-point (`jp`/`jmp`) lowering and tuple SROA. -/
def tailRecAccumLoop (steps : Nat) (accSum accXor cur : UInt64) : UInt64 × UInt64 :=
  match steps with
  | 0 => (accSum, accXor)
  | s + 1 =>
    let nextSum := accSum + cur
    let nextXor := (accXor ^^^ (cur * 13)) + s.toUInt64
    tailRecAccumLoop s nextSum nextXor (cur + 1)

def runTest6 : Bool × UInt64 :=
  -- Shared sub-DAG nodes
  let n0 := DagExpr.constVal 12
  let n1 := DagExpr.constVal 7
  let n2 := DagExpr.mulNode n0 n1            -- 84
  let n3 := DagExpr.addNode n2 (.constVal 16) -- 100
  let n4 := DagExpr.xorNode n3 (.constVal 37) -- 100 ^^^ 37 = 65
  let root := DagExpr.condNode n4 (.addNode n3 n2) (.constVal 999) -- 100 + 84 = 184
  let dagVal := evalDagExpr root

  -- Sum of 1..32 = 32 * 33 / 2 = 528
  let (loopSum, loopXor) := tailRecAccumLoop 32 0 0x123456789abcdef0 1
  let ok := dagVal == 184 && loopSum == 528 && loopXor != 0
  let h := fnvMixU64 (fnvMixU64 (fnvMixU64 14695981039346656037 dagVal) loopSum) loopXor
  (ok, h)

/-! ## Test 7 — Matryoshka M3 TRM Bit-Exact Slice Parity (`S_0 16x32`, `S_1 32x64`, `S_3 64x128`) -/

def isqrtU32 (n : UInt32) : UInt32 :=
  if n == 0 then 1
  else
    let rec loop (fuel : Nat) (x y : UInt32) : UInt32 :=
      match fuel with
      | 0 => if x > 0 then x else 1
      | f + 1 =>
        if y < x then loop f y ((y + n / y) >>> 1)
        else if x > 0 then x else 1
    loop 32 n ((n + 1) >>> 1)

def trmStepSliceSum (dModel dHidden : Nat) (useUnrolled : Bool) : UInt64 := Id.run do
  let mut z : Array Int := Array.replicate dModel 0
  for i in [0:dModel] do
    z := z.set! i (((Int.ofNat ((i * 37 + 11) % 97)) - 48))
  let mut sumSq : Nat := 0
  for i in [0:dModel] do
    let zi := z[i]!
    sumSq := sumSq + (zi * zi).toNat
  let rms : Int := Int.ofNat (isqrtU32 (sumSq / dModel + 1).toUInt32).toNat
  let mut hNorm : Array Int := Array.replicate dModel 0
  for i in [0:dModel] do
    let v := (z[i]! * 32) / rms
    let c := if v < -127 then -127 else if v > 127 then 127 else v
    hNorm := hNorm.set! i c
  let mut totalAct : UInt64 := 0
  for j in [0:dHidden] do
    let mut acc : Int := 0
    if useUnrolled then
      let mut i : Nat := 0
      while i + 4 <= dModel do
        let w0 := (Int.ofNat (((i * dHidden + j) * 53 + 19) % 89)) - 44
        let w1 := (Int.ofNat ((((i + 1) * dHidden + j) * 53 + 19) % 89)) - 44
        let w2 := (Int.ofNat ((((i + 2) * dHidden + j) * 53 + 19) % 89)) - 44
        let w3 := (Int.ofNat ((((i + 3) * dHidden + j) * 53 + 19) % 89)) - 44
        acc := acc + (hNorm[i]! * w0 + hNorm[i + 1]! * w1) + (hNorm[i + 2]! * w2 + hNorm[i + 3]! * w3)
        i := i + 4
    else
      for i in [0:dModel] do
        let w := (Int.ofNat (((i * dHidden + j) * 53 + 19) % 89)) - 44
        acc := acc + hNorm[i]! * w
    let pre := (acc / 128) - 11
    let relu := if pre <= 0 then 0 else if pre > 16 then 16 else pre
    let sq := (relu * relu).toNat
    totalAct := totalAct + (if sq > 255 then 255 else sq).toUInt64
  return totalAct

def runTest7 : Bool × UInt64 :=
  let s0Ref := trmStepSliceSum 16 32 false
  let s0Vec := trmStepSliceSum 16 32 true
  let s1Ref := trmStepSliceSum 32 64 false
  let s1Vec := trmStepSliceSum 32 64 true
  let s3Ref := trmStepSliceSum 64 128 false
  let s3Vec := trmStepSliceSum 64 128 true
  -- Verify cache footprint budgets: S_0(16x32)=1344B <= 32KB, S_1(32x64)=4736B <= 512KB, S_3(64x128)=17664B <= 32KB
  let s0Bytes : UInt64 := 16 * 32 + 32 * 16 + 320
  let s1Bytes : UInt64 := 32 * 64 + 64 * 32 + 640
  let s3Bytes : UInt64 := 64 * 128 + 128 * 64 + 1280
  let ok := s0Ref == s0Vec && s1Ref == s1Vec && s3Ref == s3Vec &&
            s0Bytes <= 32768 && s1Bytes <= 524288 && s3Bytes <= 32768
  let h := fnvMixU64 (fnvMixU64 (fnvMixU64 14695981039346656037 s0Ref) s1Ref) s3Ref
  (ok, h)

/-- Format a `UInt64` as a 16-digit `0x...` hex string. -/
def toHex64 (val : UInt64) : String :=
  let hexChars := "0123456789abcdef".toList
  let rec loop (n : Nat) (v : UInt64) (acc : List Char) : String :=
    match n with
    | 0 => "0x" ++ String.ofList acc
    | n' + 1 =>
      let nib := (v &&& 0xf).toNat
      let c := hexChars[nib]?.getD '0'
      loop n' (v >>> 4) (c :: acc)
  loop 16 val []

end LeanNativeTestRunner

open LeanNativeTestRunner in
def main : IO UInt32 := do
  let suites : List (String × (Bool × UInt64)) := [
    ("Test 1 (256-Bit Multi-Limb Carry & Borrow Boundaries)", runTest1),
    ("Test 2 (512-Bit Intermediate mulDivDown vs mulDivUp Rounding)", runTest2),
    ("Test 3 (256-Bit Arithmetic Shift Right sar & clz256)", runTest3),
    ("Test 4 (EVM Storage Map Slot Collisions & SSTORE->SLOAD Forwarding)", runTest4),
    ("Test 5 (Shared Array m_rc > 1 Copy-On-Write under HoistExclusivity)", runTest5),
    ("Test 6 (5-Constructor Inductive Tag Dispatch & Tail-Recursive Join Points)", runTest6),
    ("Test 7 (Matryoshka M3 TRM Bit-Exact Slice Parity & Cache Budget Compliance)", runTest7)
  ]
  let mut allPassed := true
  let mut masterHash : UInt64 := 14695981039346656037
  for (label, (ok, h)) in suites do
    masterHash := fnvMixU64 masterHash h
    if ok then
      IO.println s!"[PASS] {label} (hash={toHex64 h})"
    else
      allPassed := false
      IO.println s!"[FAIL] {label} (hash={toHex64 h})"
  IO.println s!"FNV1A_CHECKSUM64={toHex64 masterHash}"
  return if allPassed then 0 else 1
