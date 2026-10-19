/-
  LeanNative v0.4 Showcase Example 2 — `examples/saxpy_matmul_gpu.lean`
  Data-Parallel `SAXPY`, Tree-Reduced `dotProduct`, and `16x16 Tiled MatMul` Kernel Showcase

  Computes deterministic 64-bit reference outputs matching the three `lean-native` hardware targets:
  1. CPU LLVM 18 SIMD (`loop-vectorize`, `slp-vectorizer`, 4-way unrolled reductions)
  2. NVIDIA CUDA PTX 8.0 (`sm_90` grid-stride `saxpy`, `.shared` tree-reduction `dotProduct`, 16x16 `.shared` tiled `matmul`)
  3. Apple Metal MSL 3.0 (`threadgroup` barrier reductions and 16x16 `threadgroup` tiled matrix multiplication)
-/

namespace SaxpyMatmulGpu

/-- 1. Data-parallel `SAXPY` kernel (`out[i] = alpha * xs[i] + ys[i]`). -/
def saxpyKernel (alpha : UInt64) (xs ys : Array UInt64) : Array UInt64 := Id.run do
  let n := Nat.min xs.size ys.size
  let mut out := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (alpha * xs[i]! + ys[i]!)
  return out

/-- 2. Data-parallel `dotProduct` kernel (`sum_{i=0}^{n-1} xs[i] * ys[i]`),
    matching 4-way SIMD unrolling and GPU `.shared` / `threadgroup` tree reduction. -/
def dotProductKernel (xs ys : Array UInt64) : UInt64 := Id.run do
  let n := Nat.min xs.size ys.size
  let mut acc0 : UInt64 := 0
  let mut acc1 : UInt64 := 0
  let mut acc2 : UInt64 := 0
  let mut acc3 : UInt64 := 0
  let nVec := (n / 4) * 4
  let mut i : Nat := 0
  while i < nVec do
    acc0 := acc0 + xs[i]! * ys[i]!
    acc1 := acc1 + xs[i + 1]! * ys[i + 1]!
    acc2 := acc2 + xs[i + 2]! * ys[i + 2]!
    acc3 := acc3 + xs[i + 3]! * ys[i + 3]!
    i := i + 4
  let mut total := (acc0 + acc1) + (acc2 + acc3)
  while i < n do
    total := total + xs[i]! * ys[i]!
    i := i + 1
  return total

/-- 3a. Reference naive `N x N` dense matrix multiplication (`C = A * B`). -/
def matmulNaive (dim : Nat) (matA matB : Array UInt64) : Array UInt64 := Id.run do
  let mut matC := Array.replicate (dim * dim) (0 : UInt64)
  for row in [0:dim] do
    for col in [0:dim] do
      let mut sum : UInt64 := 0
      for k in [0:dim] do
        sum := sum + matA[row * dim + k]! * matB[k * dim + col]!
      matC := matC.set! (row * dim + col) sum
  return matC

/-- 3b. `16x16` Cooperative Tiled Matrix Multiplication (`TILE = 16`),
    matching PTX 8.0 `.shared .align 8 .b8 tileA_raw[2048]` and Metal MSL 3.0 `threadgroup ulong tileA[256]`. -/
def matmulTiled16x16 (dim : Nat) (matA matB : Array UInt64) : Array UInt64 := Id.run do
  let tile : Nat := 16
  let mut matC := Array.replicate (dim * dim) (0 : UInt64)
  let numTiles := (dim + tile - 1) / tile
  for blockRow in [0:numTiles] do
    for blockCol in [0:numTiles] do
      for ty in [0:tile] do
        for tx in [0:tile] do
          let row := blockRow * tile + ty
          let col := blockCol * tile + tx
          if row < dim && col < dim then
            let mut acc : UInt64 := 0
            for t in [0:numTiles] do
              for k in [0:tile] do
                let aCol := t * tile + k
                let bRow := t * tile + k
                let aVal := if aCol < dim then matA[row * dim + aCol]! else 0
                let bVal := if bRow < dim then matB[bRow * dim + col]! else 0
                acc := acc + aVal * bVal
            matC := matC.set! (row * dim + col) acc
  return matC

/-- FNV-1a 64-bit array digest for cross-backend verification. -/
def fnvHashArray (arr : Array UInt64) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for x in arr do
    h := (h ^^^ x) * 1099511628211
  return h

def runShowcase : Bool × UInt64 × UInt64 × UInt64 × UInt64 := Id.run do
  let n : Nat := 256
  let mut xs := Array.mkEmpty n
  let mut ys := Array.mkEmpty n
  for i in [0:n] do
    let u := i.toUInt64
    xs := xs.push (u * 3 + 1)
    ys := ys.push (u * 5 + 2)

  let saxpyOut := saxpyKernel 4 xs ys
  let saxpyHash := fnvHashArray saxpyOut
  let dotOut := dotProductKernel xs ys

  -- 32x32 matrix multiplication (4 tiles of 16x16)
  let dim : Nat := 32
  let mut matA := Array.mkEmpty (dim * dim)
  let mut matB := Array.mkEmpty (dim * dim)
  for idx in [0:dim * dim] do
    let u := idx.toUInt64
    matA := matA.push ((u * 7 + 3) % 97)
    matB := matB.push ((u * 11 + 5) % 89)

  let cNaive := matmulNaive dim matA matB
  let cTiled := matmulTiled16x16 dim matA matB
  let matmulParityOk := cNaive == cTiled
  let matmulHash := fnvHashArray cTiled

  -- Verify first & last elements of SAXPY:
  -- i=0: 4 * 1 + 2 = 6; i=255: 4 * (255*3 + 1) + (255*5 + 2) = 4*766 + 1277 = 4341
  let saxpyBoundsOk := saxpyOut[0]! == 6 && saxpyOut[255]! == 4341
  let masterChecksum := ((saxpyHash ^^^ dotOut) * 1099511628211 ^^^ matmulHash) * 1099511628211
  return (matmulParityOk && saxpyBoundsOk, saxpyHash, dotOut, matmulHash, masterChecksum)

end SaxpyMatmulGpu

open SaxpyMatmulGpu in
def main : IO UInt32 := do
  let (ok, saxpyHash, dotVal, matmulHash, masterChecksum) := runShowcase
  IO.println "=== LeanNative v0.4 Showcase: Data-Parallel SAXPY, DotProduct & 16x16 Tiled MatMul ==="
  IO.println s!"  SAXPY (N=256, alpha=4) FNV64         : {saxpyHash}"
  IO.println s!"  DotProduct (N=256, 4-way SIMD)       : {dotVal}"
  IO.println s!"  MatMul 32x32 (16x16 Tiled == Naive)  : {ok} (FNV64={matmulHash})"
  IO.println s!"  Cross-Backend Reference Checksum     : {masterChecksum}"
  if ok then
    IO.println "[PASS] examples/saxpy_matmul_gpu.lean verified."
    return 0
  else
    IO.println "[FAIL] examples/saxpy_matmul_gpu.lean verification failed."
    return 1
