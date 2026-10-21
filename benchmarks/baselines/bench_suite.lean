/-
  benchmarks/baselines/bench_suite.lean
  Official Lean 4 baseline benchmark suite for `lean-native` cross-architecture evaluation.
  Computes exact deterministic 64-bit outputs/checksums identical to `bench_cpp.cpp`,
  `bench_cuda.cu`, and `bench_lean_native.c`.
-/

@[inline]
def fnv1aU64 (h : UInt64) (val : UInt64) : UInt64 :=
  (h ^^^ val) * 1099511628211

def fnvOffset : UInt64 := 14695981039346656037

-- Prevent constant folding across IO boundary using an opaque runtime zero offset
@[noinline]
def runtimeZero : IO UInt64 := do
  let t ← IO.monoNanosNow
  if t == 999999999999999999 then return 1 else return 0

-- 1. collatz_steps (N = 5,000,000)
partial def collatzLen (x : UInt64) (steps : UInt64) : UInt64 :=
  if x <= 1 then steps
  else if x % 2 == 0 then
    collatzLen (x / 2) (steps + 1)
  else
    collatzLen (3 * x + 1) (steps + 1)

partial def collatzLoop (i : UInt64) (n : UInt64) (acc : UInt64) : UInt64 :=
  if i > n then acc
  else collatzLoop (i + 1) n (acc + collatzLen i 0)

@[noinline]
def benchCollatzSteps (n : UInt64) : UInt64 :=
  collatzLoop 1 n 0

-- 2. tuple_accum_sum (N = 50,000,000)
-- Standard Lean 4 baseline: allocates boxed `Prod UInt64 UInt64` on each step
-- when passed through a polymorphic / non-inlined step combinator, whereas
-- `lean-native` `UnboxTupleSROA` eliminates the heap box into two 64-bit registers.
@[noinline]
def applyStep {α : Type} (f : UInt64 → α → α) (i : UInt64) (x : α) : α :=
  f i x

@[inline]
def tupleStep (i : UInt64) (p : UInt64 × UInt64) : UInt64 × UInt64 :=
  let a := p.1
  let b := p.2
  (a + (i ^^^ b), b + (i * 3 + 1))

partial def tupleLoop (i : UInt64) (n : UInt64) (p : UInt64 × UInt64) : UInt64 × UInt64 :=
  if i >= n then p
  else tupleLoop (i + 1) n (applyStep tupleStep i p)

@[noinline]
def benchTupleAccumSum (n : UInt64) : UInt64 :=
  let res := tupleLoop 0 n (1, 2)
  res.1 ^^^ res.2

-- 3. sarray_scale_bias (N = 10,000,000)
partial def initScaleArr (i : Nat) (n : Nat) (arr : Array UInt64) : Array UInt64 :=
  if i >= n then arr
  else
    let ui := i.toUInt64
    let v := ui * 6364136223846793005 + 1442695040888963407
    initScaleArr (i + 1) n (arr.push v)

partial def scalePass (i : Nat) (n : Nat) (scale : UInt64) (arr : Array UInt64) : Array UInt64 :=
  if i < n then
    let v := arr[i]!
    scalePass (i + 1) n scale (arr.set! i (v * scale + 7))
  else arr

partial def hashStride (i : Nat) (n : Nat) (stride : Nat) (arr : Array UInt64) (h : UInt64) : UInt64 :=
  if i >= n then h
  else hashStride (i + stride) n stride arr (fnv1aU64 h arr[i]!)

@[noinline]
def benchSarrayScaleBias (n : Nat) (scale : UInt64) (arr : Array UInt64) : UInt64 :=
  let arr1 := scalePass 0 n scale arr
  let arr2 := scalePass 0 n scale arr1
  let h := hashStride 0 n 64 arr2 fnvOffset
  fnv1aU64 h arr2[n - 1]!

-- 4. dot_product_u64 (N = 10,000,000)
partial def initDotArrs (i : Nat) (n : Nat) (a b : Array UInt64) : Array UInt64 × Array UInt64 :=
  if i >= n then (a, b)
  else
    let ui := i.toUInt64
    let va := (ui * 11400714819323198485 + 1) &&& 0xFFFFFFFF
    let vb := (ui * 14029467366897019727 + 3) &&& 0xFFFFFFFF
    initDotArrs (i + 1) n (a.push va) (b.push vb)

partial def dotLoop (i : Nat) (n : Nat) (a b : Array UInt64) (sum : UInt64) : UInt64 :=
  if i >= n then sum
  else dotLoop (i + 1) n a b (sum + a[i]! * b[i]!)

@[noinline]
def benchDotProductU64 (n : Nat) (a b : Array UInt64) (initSum : UInt64) : UInt64 :=
  dotLoop 0 n a b initSum

-- 5. saxpy_kernel (N = 16,777,216)
partial def initSaxpyArrs (i : Nat) (n : Nat) (x y : Array UInt64) : Array UInt64 × Array UInt64 :=
  if i >= n then (x, y)
  else
    let ui := i.toUInt64
    let vx := ui * 2654435761 + 7
    let vy := ui * 2246822519 + 13
    initSaxpyArrs (i + 1) n (x.push vx) (y.push vy)

partial def saxpyLoop (i : Nat) (n : Nat) (alpha : UInt64) (x y : Array UInt64) : Array UInt64 :=
  if i >= n then y
  else
    let vy := alpha * x[i]! + y[i]!
    saxpyLoop (i + 1) n alpha x (y.set! i vy)

@[noinline]
def benchSaxpyKernel (n : Nat) (alpha : UInt64) (x y : Array UInt64) : UInt64 :=
  let yOut := saxpyLoop 0 n alpha x y
  let h := hashStride 0 n 256 yOut fnvOffset
  fnv1aU64 h yOut[n - 1]!

-- 6. matmul_tiled_u64 (M = 512)
partial def initMatmulArrs (i : Nat) (total : Nat) (a b c : Array UInt64) : Array UInt64 × Array UInt64 × Array UInt64 :=
  if i >= total then (a, b, c)
  else
    let ui := i.toUInt64
    let va := (ui * 6364136223846793005 + 1) &&& 0xFFFF
    let vb := (ui * 2862933555777941757 + 3) &&& 0xFFFF
    initMatmulArrs (i + 1) total (a.push va) (b.push vb) (c.push 0)

partial def matmulInnerJ (j : Nat) (m : Nat) (rowOff : Nat) (kOff : Nat) (aik : UInt64) (b c : Array UInt64) : Array UInt64 :=
  if j >= m then c
  else
    let idx := rowOff + j
    let v := c[idx]! + aik * b[kOff + j]!
    matmulInnerJ (j + 1) m rowOff kOff aik b (c.set! idx v)

partial def matmulInnerK (k : Nat) (m : Nat) (rowOff : Nat) (a b c : Array UInt64) : Array UInt64 :=
  if k >= m then c
  else
    let aik := a[rowOff + k]!
    let c' := matmulInnerJ 0 m rowOff (k * m) aik b c
    matmulInnerK (k + 1) m rowOff a b c'

partial def matmulOuterI (i : Nat) (m : Nat) (a b c : Array UInt64) : Array UInt64 :=
  if i >= m then c
  else
    let c' := matmulInnerK 0 m (i * m) a b c
    matmulOuterI (i + 1) m a b c'

@[noinline]
def benchMatmulTiledU64 (m : Nat) (a b c : Array UInt64) : UInt64 :=
  let cOut := matmulOuterI 0 m a b c
  hashStride 0 (m * m) 1 cOut fnvOffset

-- 7. evm_gas_schedule_u64 (N = 10,000,000)
-- Standard Lean 4 baseline: models EVMYulLean 2.0 `Gas.lean` memory expansion & Keccak256 dynamic gas
-- with boxed structure / tuple step before `lean-native` `UnboxTupleSROA` + `AlgebraicOpt` + SIMD.
@[inline]
def evmGasStep (i : UInt64) (acc : UInt64 × UInt64) : UInt64 × UInt64 :=
  let oldW := (i * 2654435761 + 11) &&& 0x7FFF
  let reqW := (i * 2246822519 + 29) &&& 0xFFFF
  let dataW := (i * 3266489917 + 7) &&& 0xFF
  let newW := if reqW > oldW then reqW else oldW
  let newCost := 3 * newW + (newW * newW) / 512
  let oldCost := 3 * oldW + (oldW * oldW) / 512
  let opGas := (newCost - oldCost) + 30 + 6 * dataW
  (acc.1 + opGas, acc.2 ^^^ newW)

partial def evmGasLoop (i : UInt64) (n : UInt64) (acc : UInt64 × UInt64) : UInt64 × UInt64 :=
  if i >= n then acc
  else evmGasLoop (i + 1) n (applyStep evmGasStep i acc)

@[noinline]
def benchEvmGasScheduleU64 (n : UInt64) : UInt64 :=
  (evmGasLoop 0 n (0, 0)).1

-- 8. keccak256_sponge_u64 (N = 2,000,000)
-- Standard Lean 4 baseline: models EVMYulLean 2.0 `PureKeccak256.lean` 5-lane sponge permutation
-- across 8 rounds (theta/rho/pi/chi/iota) with boxed 5-tuple state before `UnboxTupleSROA` + SIMD.
@[inline]
def rotl64 (x : UInt64) (r : UInt64) : UInt64 :=
  (x <<< r) ||| (x >>> (64 - r))

@[inline]
def keccakRound (rc : UInt64) (st : UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (s0, s1, s2, s3, s4) := st
  let d0 := s4 ^^^ rotl64 s1 1
  let d1 := s0 ^^^ rotl64 s2 1
  let d2 := s1 ^^^ rotl64 s3 1
  let d3 := s2 ^^^ rotl64 s4 1
  let d4 := s3 ^^^ rotl64 s0 1
  let b0 := s0 ^^^ d0
  let b1 := rotl64 (s1 ^^^ d1) 44
  let b2 := rotl64 (s2 ^^^ d2) 43
  let b3 := rotl64 (s3 ^^^ d3) 21
  let b4 := rotl64 (s4 ^^^ d4) 14
  let n0 := b0 ^^^ ((~~~b1) &&& b2) ^^^ rc
  let n1 := b1 ^^^ ((~~~b2) &&& b3)
  let n2 := b2 ^^^ ((~~~b3) &&& b4)
  let n3 := b3 ^^^ ((~~~b4) &&& b0)
  let n4 := b4 ^^^ ((~~~b0) &&& b1)
  (n0, n1, n2, n3, n4)

@[inline]
def keccakStep (i : UInt64) (acc : UInt64 × UInt64) : UInt64 × UInt64 :=
  let s0 := i * 6364136223846793005 + 1
  let s1 := i * 2862933555777941757 + 3
  let s2 := i * 11400714819323198485 + 5
  let s3 := i * 14029467366897019727 + 7
  let s4 := i * 3266489917 + 11
  let st := (s0, s1, s2, s3, s4)
  let st := keccakRound 0x0000000000000001 st
  let st := keccakRound 0x0000000000008082 st
  let st := keccakRound 0x800000000000808a st
  let st := keccakRound 0x8000000080008000 st
  let st := keccakRound 0x000000000000808b st
  let st := keccakRound 0x0000000080000001 st
  let st := keccakRound 0x8000000080008081 st
  let st := keccakRound 0x8000000000008009 st
  let (r0, r1, r2, r3, r4) := st
  let sum := r0 + r1 + r2 + r3 + r4
  (acc.1 ^^^ sum, acc.2 + r0)

partial def keccakLoop (i : UInt64) (n : UInt64) (acc : UInt64 × UInt64) : UInt64 × UInt64 :=
  if i >= n then acc
  else keccakLoop (i + 1) n (applyStep keccakStep i acc)

@[noinline]
def benchKeccak256SpongeU64 (n : UInt64) : UInt64 :=
  (keccakLoop 0 n (0, 0)).1

-- 9. uint256_wad_muldiv_u64 (N = 5,000,000)
-- Standard Lean 4 baseline: models Verity 2.0 `TickLib.wMulDown` + `UInt256BitVecBridge.lean`
-- multi-limb 128-bit carry and 64x64->128 widening multiply via 32-bit schoolbook split in pure UInt64.
@[inline]
def mul128HiLo (a b : UInt64) : UInt64 × UInt64 :=
  let mask32 : UInt64 := 0xFFFFFFFF
  let a0 := a &&& mask32
  let a1 := a >>> 32
  let b0 := b &&& mask32
  let b1 := b >>> 32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := (p00 >>> 32) + (p01 &&& mask32) + (p10 &&& mask32)
  let lo := (p00 &&& mask32) ||| (mid <<< 32)
  let hi := p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)
  (lo, hi)

@[inline]
def uint256WadStep (i : UInt64) (acc : UInt64 × UInt64) : UInt64 × UInt64 :=
  let x0 := i * 6364136223846793005 + 1442695040888963407
  let x1 := i * 2862933555777941757 + 3
  let y0 := (i ^^^ 0x5555555555555555) * 11400714819323198485 + 7
  let y1 := i * 3266489917 + 11
  let s0 := x0 + y0
  let carry : UInt64 := if s0 < x0 then 1 else 0
  let s1 := x1 + y1 + carry
  let (lo0, hi0) := mul128HiLo x0 y0
  let (lo1, hi1) := mul128HiLo s0 1000000000000000000
  let stepVal := s0 ^^^ s1 ^^^ hi0 ^^^ hi1 ^^^ (lo0 >>> 32) ^^^ (lo1 >>> 32)
  (acc.1 + stepVal, acc.2 ^^^ s1)

partial def uint256WadLoop (i : UInt64) (n : UInt64) (acc : UInt64 × UInt64) : UInt64 × UInt64 :=
  if i >= n then acc
  else uint256WadLoop (i + 1) n (applyStep uint256WadStep i acc)

@[noinline]
def benchUint256WadMuldivU64 (n : UInt64) : UInt64 :=
  (uint256WadLoop 0 n (0, 0)).1

-- Holdout 1: holdout_bitwise
partial def holdoutBitwiseLoop (i : UInt64) (n : UInt64) (acc : UInt64) : UInt64 :=
  if i >= n then acc
  else
    let x := i + acc
    let v := (x * 8) + (x &&& x) - (x ^^^ x) + (x / 4)
    holdoutBitwiseLoop (i + 1) n (acc ^^^ (v + i * 17))

@[noinline]
def benchHoldoutBitwise (n : UInt64) : UInt64 :=
  holdoutBitwiseLoop 0 n 0x123456789ABCDEF0

-- Holdout 2: holdout_loop_bounds
partial def holdoutBoundsLoop (i : UInt64) (n : UInt64) (sum1 sum2 : UInt64) : UInt64 :=
  if i >= n then sum1 ^^^ sum2
  else
    let s1 : UInt64 := sum1 + ((i * (5 : UInt64) + (3 : UInt64)) ^^^ (sum2 &&& (0xFF : UInt64)))
    let s2 : UInt64 := (sum2 * (13 : UInt64) + i) ^^^ (s1 >>> (3 : UInt64))
    holdoutBoundsLoop (i + 1) n s1 s2

@[noinline]
def benchHoldoutLoopBounds (n : UInt64) : UInt64 :=
  holdoutBoundsLoop 0 n 0 1

@[noinline]
def forceIO (v : UInt64) : IO UInt64 := do
  let ref ← IO.mkRef v
  ref.get

def main (args : List String) : IO Unit := do
  let filter := args.headD "all"
  let z ← runtimeZero
  let zNat := z.toNat

  if filter == "all" || filter == "collatz_steps" then
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchCollatzSteps (5000000 + z))
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH collatz_steps checksum={c} time_ms={dt}"

  if filter == "all" || filter == "tuple_accum_sum" then
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchTupleAccumSum (50000000 + z))
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH tuple_accum_sum checksum={c} time_ms={dt}"

  if filter == "all" || filter == "sarray_scale_bias" then
    let n := 10000000
    let arr := initScaleArr 0 n (Array.mkEmpty n)
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchSarrayScaleBias (n + zNat) (3 + z) arr)
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH sarray_scale_bias checksum={c} time_ms={dt}"

  if filter == "all" || filter == "dot_product_u64" then
    let n := 10000000
    let (a, b) := initDotArrs 0 n (Array.mkEmpty n) (Array.mkEmpty n)
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchDotProductU64 (n + zNat) a b z)
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH dot_product_u64 checksum={c} time_ms={dt}"

  if filter == "all" || filter == "saxpy_kernel" then
    let n := 16777216
    let (x, y) := initSaxpyArrs 0 n (Array.mkEmpty n) (Array.mkEmpty n)
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchSaxpyKernel (n + zNat) (314159 + z) x y)
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH saxpy_kernel checksum={c} time_ms={dt}"

  if filter == "all" || filter == "matmul_tiled_u64" then
    let m := 512
    let (a, b, cArr) := initMatmulArrs 0 (m * m) (Array.mkEmpty (m * m)) (Array.mkEmpty (m * m)) (Array.mkEmpty (m * m))
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchMatmulTiledU64 (m + zNat) a b cArr)
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH matmul_tiled_u64 checksum={c} time_ms={dt}"

  if filter == "all" || filter == "evm_gas_schedule_u64" then
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchEvmGasScheduleU64 (10000000 + z))
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH evm_gas_schedule_u64 checksum={c} time_ms={dt}"

  if filter == "all" || filter == "keccak256_sponge_u64" then
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchKeccak256SpongeU64 (2000000 + z))
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH keccak256_sponge_u64 checksum={c} time_ms={dt}"

  if filter == "all" || filter == "uint256_wad_muldiv_u64" then
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchUint256WadMuldivU64 (5000000 + z))
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH uint256_wad_muldiv_u64 checksum={c} time_ms={dt}"

  if filter == "all" || filter == "holdout_bitwise" then
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchHoldoutBitwise (10000000 + z))
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH holdout_bitwise checksum={c} time_ms={dt}"

  if filter == "all" || filter == "holdout_loop_bounds" then
    let t0 ← IO.monoNanosNow
    let c ← forceIO (benchHoldoutLoopBounds (10000000 + z))
    let t1 ← IO.monoNanosNow
    let dt := (t1 - t0).toFloat / 1000000.0
    IO.println s!"BENCH holdout_loop_bounds checksum={c} time_ms={dt}"
