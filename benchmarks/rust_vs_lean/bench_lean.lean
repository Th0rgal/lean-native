/-
  benchmarks/rust_vs_lean/bench_lean.lean
  Deterministic 20-algorithm benchmark corpus in pure Lean 4.
  Used by both:
    1. Official Lean 4 compiler (`lean -c` + `clang -O3`)
    2. `lean-native` (`lean-native build-exe` with verified LNIR + LLVM 18 native pipeline)
  Prints: `BENCH:<name>:<elapsed_ns>:<checksum_u64>`
-/

@[inline] def rotl64 (x : UInt64) (k : UInt64) : UInt64 :=
  (x <<< k) ||| (x >>> (64 - k))

@[inline] def rotr64 (x : UInt64) (k : UInt64) : UInt64 :=
  (x >>> k) ||| (x <<< (64 - k))

@[inline] def popcount64 (x : UInt64) : UInt64 :=
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0f0f0f0f0f0f0f0f
  let h01 : UInt64 := 0x0101010101010101
  let v : UInt64 := x - ((x >>> 1) &&& m1)
  let v : UInt64 := (v &&& m2) + ((v >>> 2) &&& m2)
  let v : UInt64 := (v + (v >>> 4)) &&& m4
  (v * h01) >>> 56

@[inline] def mul64Hi (x y : UInt64) : UInt64 :=
  let xLo := x &&& 0xffffffff
  let xHi := x >>> 32
  let yLo := y &&& 0xffffffff
  let yHi := y >>> 32
  let p0 := xLo * yLo
  let p1 := xLo * yHi
  let p2 := xHi * yLo
  let p3 := xHi * yHi
  let cy := ((p0 >>> 32) + (p1 &&& 0xffffffff) + (p2 &&& 0xffffffff)) >>> 32
  p3 + (p1 >>> 32) + (p2 >>> 32) + cy

-- 1. collatz_steps
partial def collatzOne (n : UInt64) (steps : UInt64) : UInt64 :=
  if n <= 1 then steps
  else
    let isOdd := n &&& 1
    let nextEven := n >>> 1
    let nextOdd := n * 3 + 1
    let nextN := if isOdd != 0 then nextOdd else nextEven
    collatzOne nextN (steps + 1)

def benchCollatzSteps (limit : UInt64) : UInt64 := Id.run do
  let mut total : UInt64 := 0
  let mut i : UInt64 := 1
  while i <= limit do
    total := total + collatzOne i 0
    i := i + 1
  return total

-- 2. tuple_accum_sum
def benchTupleAccumSum (iters : UInt64) : UInt64 := Id.run do
  let mut pair : UInt64 × UInt64 := (1, 2)
  let mut i : UInt64 := 0
  while i < iters do
    let a := pair.1
    let b := pair.2
    let na := a + b + (i &&& 7)
    let nb := (b ^^^ (na >>> 3)) + i
    pair := (na, nb)
    i := i + 1
  return pair.1 + pair.2

-- 3. sarray_scale_bias
def benchSArrayScaleBias (n : Nat) (rounds : UInt64) : UInt64 := Id.run do
  let mut buf : Array UInt64 := Array.mkEmpty n
  for i in [0:n] do
    buf := buf.push (i.toUInt64 * 13 + 5)
  let mut r : UInt64 := 0
  while r < rounds do
    let scale : UInt64 := 3 + (r &&& 1)
    let bias : UInt64 := 7 + r
    for i in [0:n] do
      let x := buf[i]!
      buf := buf.set! i (x * scale + bias)
    r := r + 1
  let mut sum : UInt64 := 0
  for i in [0:n] do
    sum := sum + buf[i]!
  return sum

-- 4. dot_product_u64
def benchDotProductU64 (n : Nat) (rounds : UInt64) : UInt64 := Id.run do
  let mut a : Array UInt64 := Array.mkEmpty n
  let mut b : Array UInt64 := Array.mkEmpty n
  for i in [0:n] do
    a := a.push (((i * 17 + 3) &&& 0xFFFF).toUInt64)
    b := b.push (((i * 31 + 11) &&& 0xFFFF).toUInt64)
  let mut total : UInt64 := 0
  let mut r : UInt64 := 0
  while r < rounds do
    let mut acc : UInt64 := 0
    for i in [0:n] do
      acc := acc + a[i]! * b[i]!
    total := total + (acc + r)
    r := r + 1
  return total

-- 5. saxpy_kernel
def benchSaxpyKernel (n : Nat) (rounds : UInt64) : UInt64 := Id.run do
  let mut x : Array UInt64 := Array.mkEmpty n
  let mut y : Array UInt64 := Array.mkEmpty n
  for i in [0:n] do
    x := x.push (((i * 7 + 1) &&& 0xFFFF).toUInt64)
    y := y.push (((i * 19 + 9) &&& 0xFFFF).toUInt64)
  let mut r : UInt64 := 0
  while r < rounds do
    let alpha : UInt64 := 5 + (r &&& 3)
    for i in [0:n] do
      y := y.set! i (alpha * x[i]! + y[i]!)
    r := r + 1
  let mut sum : UInt64 := 0
  for i in [0:n] do
    sum := sum + y[i]!
  return sum

-- 6. matmul_tiled_u64
def benchMatmulTiledU64 (dim : Nat) : UInt64 := Id.run do
  let total := dim * dim
  let mut a : Array UInt64 := Array.mkEmpty total
  let mut b : Array UInt64 := Array.mkEmpty total
  let mut c : Array UInt64 := Array.replicate total 0
  for i in [0:total] do
    a := a.push (((i * 13 + 7) &&& 0xFF).toUInt64)
    b := b.push (((i * 29 + 3) &&& 0xFF).toUInt64)
  for i in [0:dim] do
    for k in [0:dim] do
      let aik := a[i * dim + k]!
      let rowC := i * dim
      let rowB := k * dim
      for j in [0:dim] do
        let cur := c[rowC + j]!
        c := c.set! (rowC + j) (cur + aik * b[rowB + j]!)
  let mut checksum : UInt64 := 0
  for i in [0:total] do
    checksum := checksum + c[i]!
  return checksum

-- 7. binary_trees
inductive BenchTree where
  | leaf (v : UInt64)
  | node (l r : BenchTree) (v : UInt64)
  deriving Inhabited, Nonempty

partial def makeBenchTree (depth : UInt64) (seed : UInt64) : BenchTree :=
  if depth == 0 then
    .leaf seed
  else
    let l := makeBenchTree (depth - 1) (seed * 3 + 1)
    let r := makeBenchTree (depth - 1) (seed * 3 + 2)
    .node l r seed

partial def checkBenchTree : BenchTree → UInt64
  | .leaf v => v
  | .node l r v => (checkBenchTree l + checkBenchTree r) ^^^ v

def benchBinaryTrees (depth : UInt64) (iters : UInt64) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  let mut i : UInt64 := 0
  while i < iters do
    let t := makeBenchTree depth (i + 1)
    acc := acc + checkBenchTree t
    i := i + 1
  return acc

-- 8. nbody
def benchNbody (steps : UInt64) : UInt64 := Id.run do
  let mut px : Array UInt64 := #[1000, 2500, 4200, 6100, 8300]
  let mut py : Array UInt64 := #[1500, 3100, 1900, 5400, 7200]
  let mut pz : Array UInt64 := #[2000, 1200, 3800, 4900, 6500]
  let mut vx : Array UInt64 := #[10, 20, 15, 25, 30]
  let mut vy : Array UInt64 := #[12, 18, 22, 14, 28]
  let mut vz : Array UInt64 := #[8, 24, 16, 19, 11]
  let mass : Array UInt64 := #[100, 40, 60, 80, 50]
  let mut s : UInt64 := 0
  while s < steps do
    for i in [0:5] do
      for j in [i+1:5] do
        let dx := px[i]! - px[j]!
        let dy := py[i]! - py[j]!
        let dz := pz[i]! - pz[j]!
        let dist2 := ((dx * dx + dy * dy + dz * dz) &&& 0xFFFF) + 1
        let mag := (65536 : UInt64) / dist2
        let fx := dx * mag
        let fy := dy * mag
        let fz := dz * mag
        let mj := mass[j]!
        let mi := mass[i]!
        vx := vx.set! i (vx[i]! - ((fx * mj) >>> 8))
        vy := vy.set! i (vy[i]! - ((fy * mj) >>> 8))
        vz := vz.set! i (vz[i]! - ((fz * mj) >>> 8))
        vx := vx.set! j (vx[j]! + ((fx * mi) >>> 8))
        vy := vy.set! j (vy[j]! + ((fy * mi) >>> 8))
        vz := vz.set! j (vz[j]! + ((fz * mi) >>> 8))
    for i in [0:5] do
      px := px.set! i (px[i]! + vx[i]!)
      py := py.set! i (py[i]! + vy[i]!)
      pz := pz.set! i (pz[i]! + vz[i]!)
    s := s + 1
  let mut energy : UInt64 := 0
  for i in [0:5] do
    energy := energy + (px[i]! ^^^ rotl64 py[i]! 13 ^^^ rotl64 pz[i]! 27 ^^^ vx[i]! ^^^ vy[i]! ^^^ vz[i]!)
  return energy

-- 9. spectral_norm
def benchSpectralNorm (n : Nat) (sweeps : UInt64) : UInt64 := Id.run do
  let mut u : Array UInt64 := Array.replicate n 1024
  let mut v : Array UInt64 := Array.replicate n 0
  let mut tmp : Array UInt64 := Array.replicate n 0
  let mut sw : UInt64 := 0
  while sw < sweeps do
    for i in [0:n] do
      let mut sum : UInt64 := 0
      for j in [0:n] do
        let ij := (i + j).toUInt64
        let denom := ((ij * (ij + 1) / 2 + i.toUInt64 + 1) &&& 0xFF)
        sum := sum + u[j]! * (denom + 1)
      tmp := tmp.set! i (sum >>> 8)
    for i in [0:n] do
      let mut sum : UInt64 := 0
      for j in [0:n] do
        let ij := (i + j).toUInt64
        let denom := ((ij * (ij + 1) / 2 + j.toUInt64 + 1) &&& 0xFF)
        sum := sum + tmp[j]! * (denom + 1)
      v := v.set! i (sum >>> 8)
    for i in [0:n] do
      u := u.set! i (v[i]! &&& 0xFFFFFFFF)
    sw := sw + 1
  let mut acc : UInt64 := 0
  for i in [0:n] do
    acc := acc + u[i]! * v[i]!
  return acc

-- 10. fannkuch_redux
def benchFannkuchRedux (iters : UInt64) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  let mut seed : UInt64 := 0
  while seed < iters do
    let mut p : Array UInt64 := #[0, 1, 2, 3, 4, 5, 6, 7]
    let mut s := seed * 0x9E3779B97F4A7C15 + 1
    let mut idx : Nat := 7
    while idx >= 1 do
      s := s * 6364136223846793005 + 1442695040888963407
      let j := ((s >>> 32).toNat) % (idx + 1)
      let tmp := p[idx]!
      p := p.set! idx p[j]!
      p := p.set! j tmp
      idx := idx - 1
    let mut flips : UInt64 := 0
    let mut guard : UInt64 := 0
    while p[0]! != 0 && guard < 32 do
      let k := p[0]!.toNat
      let mut lo : Nat := 0
      let mut hi : Nat := k
      while lo < hi do
        let t := p[lo]!
        p := p.set! lo p[hi]!
        p := p.set! hi t
        lo := lo + 1
        hi := hi - 1
      flips := flips + 1
      guard := guard + 1
    checksum := checksum + flips * ((seed &&& 15) + 1)
    seed := seed + 1
  return checksum

-- 11. mandelbrot_simd (Fixed-Point Q16.16 using non-negative offset or exact 64-bit two's complement)
@[inline] def sar64_16 (x : UInt64) : UInt64 :=
  if (x &&& 0x8000000000000000) != 0 then
    (x >>> 16) ||| 0xFFFF000000000000
  else
    x >>> 16

@[inline] def sgt64 (a b : UInt64) : Bool :=
  (a + 0x8000000000000000) > (b + 0x8000000000000000)

def benchMandelbrotSimd (width height maxIter : UInt64) : UInt64 := Id.run do
  let mut totalIters : UInt64 := 0
  let mut py : UInt64 := 0
  while py < height do
    let ci : UInt64 := (py * 131072) / height - 65536
    let mut px : UInt64 := 0
    while px < width do
      let cr : UInt64 := (px * 196608) / width - 131072
      let mut zr : UInt64 := 0
      let mut zi : UInt64 := 0
      let mut it : UInt64 := 0
      while it < maxIter do
        let zr2 := sar64_16 (zr * zr)
        let zi2 := sar64_16 (zi * zi)
        if sgt64 (zr2 + zi2) 262144 then
          break
        zi := sar64_16 (2 * zr * zi) + ci
        zr := zr2 - zi2 + cr
        it := it + 1
      totalIters := totalIters + it
      px := px + 1
    py := py + 1
  return totalIters

-- 12. robin_hood_htab
def benchRobinHoodHtab (numOps : UInt64) : UInt64 := Id.run do
  let cap : Nat := 4096
  let mask : Nat := cap - 1
  let emptyKey : UInt64 := 0xFFFFFFFFFFFFFFFF
  let mut keys : Array UInt64 := Array.replicate cap emptyKey
  let mut vals : Array UInt64 := Array.replicate cap 0
  let mut i : UInt64 := 0
  while i < numOps do
    let k := (i * 0x9E3779B97F4A7C15) &&& 0x7FF
    let v := i * 31 + 17
    let mut slot := (((k * 0xBF58476D1CE4E5B9) >>> 32).toNat) &&& mask
    let mut done := false
    while !done do
      let ks := keys[slot]!
      if ks == emptyKey || ks == k then
        keys := keys.set! slot k
        vals := vals.set! slot (vals[slot]! + v)
        done := true
      else
        slot := (slot + 1) &&& mask
    i := i + 1
  let mut sum : UInt64 := 0
  let mut j : UInt64 := 0
  while j < numOps do
    let k := (j * 0x9E3779B97F4A7C15) &&& 0x7FF
    let mut slot := (((k * 0xBF58476D1CE4E5B9) >>> 32).toNat) &&& mask
    let mut done := false
    while !done do
      let ks := keys[slot]!
      if ks == k then
        sum := sum + vals[slot]!
        done := true
      else if ks == emptyKey then
        done := true
      else
        slot := (slot + 1) &&& mask
    j := j + 1
  return sum

-- 13. sha256_compress
def benchSha256Compress (blocks : UInt64) : UInt64 := Id.run do
  let mut s0 : UInt64 := 0x6a09e667bb67ae85
  let mut s1 : UInt64 := 0x3c6ef372a54ff53a
  let mut s2 : UInt64 := 0x510e527f9b05688c
  let mut s3 : UInt64 := 0x1f83d9ab5be0cd19
  let mut b : UInt64 := 0
  while b < blocks do
    let mut w := b * 0x9E3779B97F4A7C15 + 0x428a2f98d728ae22
    let mut r : UInt64 := 0
    while r < 64 do
      let e0 := rotr64 s0 2 ^^^ rotr64 s0 13 ^^^ rotr64 s0 22
      let maj := (s0 &&& s1) ^^^ (s0 &&& s2) ^^^ (s1 &&& s2)
      let e1 := rotr64 s3 6 ^^^ rotr64 s3 11 ^^^ rotr64 s3 25
      let ch := (s3 &&& s1) ^^^ ((~~~s3) &&& s2)
      let temp1 := s3 + e1 + ch + w + r
      let temp2 := e0 + maj
      s3 := s2
      s2 := s1
      s1 := s0
      s0 := temp1 + temp2
      w := rotl64 w 7 + 0x7137449123ef65cd
      r := r + 1
    b := b + 1
  return s0 ^^^ s1 ^^^ s2 ^^^ s3

-- 14. keccak_f1600
def benchKeccakF1600 (perms : UInt64) : UInt64 := Id.run do
  let mut a0 : UInt64 := 0x123456789ABCDEF0
  let mut a1 : UInt64 := 0x0FEDCBA987654321
  let mut a2 : UInt64 := 0xCAFEBABEDEADBEEF
  let mut a3 : UInt64 := 0x0123456789ABCDEF
  let mut a4 : UInt64 := 0xF0E1D2C3B4A59687
  let mut p : UInt64 := 0
  while p < perms do
    a0 := a0 ^^^ p
    let mut r : UInt64 := 0
    while r < 24 do
      let c := a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4
      let d := rotl64 c 1 ^^^ rotr64 c 1
      a0 := rotl64 (a0 ^^^ d) 1
      a1 := rotl64 (a1 ^^^ d) 3
      a2 := rotl64 (a2 ^^^ d) 6
      a3 := rotl64 (a3 ^^^ d) 10
      a4 := rotl64 (a4 ^^^ d) 15
      let t0 := a0 ^^^ ((~~~a1) &&& a2)
      let t1 := a1 ^^^ ((~~~a2) &&& a3)
      let t2 := a2 ^^^ ((~~~a3) &&& a4)
      let t3 := a3 ^^^ ((~~~a4) &&& a0)
      let t4 := a4 ^^^ ((~~~a0) &&& a1)
      a0 := t0 ^^^ (r * 0x0000000080008081)
      a1 := t1
      a2 := t2
      a3 := t3
      a4 := t4
      r := r + 1
    p := p + 1
  return a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4

-- 15. mul_div_512
def benchMulDiv512 (iters : UInt64) : UInt64 := Id.run do
  let mut acc0 : UInt64 := 0x1122334455667788
  let mut acc1 : UInt64 := 0x99AABBCCDDEEFF00
  let mut acc2 : UInt64 := 0x0102030405060708
  let mut acc3 : UInt64 := 0xF1E2D3C4B5A69788
  let mut i : UInt64 := 1
  while i <= iters do
    let x := i * 0x9E3779B97F4A7C15 + 1
    let y := (i * 0xBF58476D1CE4E5B9) ||| 1
    let lo0 := acc0 * x
    let hi0 := mul64Hi acc0 x
    let p1 := acc1 * x
    let h1 := mul64Hi acc1 x
    let lo1 := p1 + hi0
    let c1 : UInt64 := if lo1 < p1 then 1 else 0
    let hi1 := h1 + c1
    let p2 := acc2 * x
    let h2 := mul64Hi acc2 x
    let lo2 := p2 + hi1
    let c2 : UInt64 := if lo2 < p2 then 1 else 0
    let hi2 := h2 + c2
    let p3 := acc3 * x
    let lo3 := p3 + hi2
    let d := (y &&& 0xFFFFFFFF) + 3
    acc0 := (lo0 / d) + lo1
    acc1 := (lo1 / d) + lo2
    acc2 := (lo2 / d) + lo3
    acc3 := (lo3 / d) ^^^ lo0
    i := i + 1
  return acc0 ^^^ acc1 ^^^ acc2 ^^^ acc3

-- 16. radix_sort_u64
def benchRadixSortU64 (n : Nat) (rounds : UInt64) : UInt64 := Id.run do
  let mut src : Array UInt64 := Array.replicate n 0
  let mut dst : Array UInt64 := Array.replicate n 0
  let mut checksum : UInt64 := 0
  let shifts : Array UInt64 := #[0, 8, 16, 24]
  let mut r : UInt64 := 0
  while r < rounds do
    for i in [0:n] do
      src := src.set! i (((i.toUInt64 * 0x9E3779B97F4A7C15) + r) &&& 0xFFFFFFFF)
    for sh in shifts do
      let mut count : Array Nat := Array.replicate 256 0
      for i in [0:n] do
        let b := ((src[i]! >>> sh) &&& 0xFF).toNat
        count := count.set! b (count[b]! + 1)
      let mut pref : Array Nat := Array.replicate 256 0
      let mut running : Nat := 0
      for b in [0:256] do
        pref := pref.set! b running
        running := running + count[b]!
      for i in [0:n] do
        let v := src[i]!
        let b := ((v >>> sh) &&& 0xFF).toNat
        let pos := pref[b]!
        dst := dst.set! pos v
        pref := pref.set! b (pos + 1)
      let tmp := src
      src := dst
      dst := tmp
    checksum := checksum + (src[0]! ^^^ src[n / 2]! ^^^ src[n - 1]!)
    r := r + 1
  return checksum

-- 17. dijkstra_pairing_heap
def benchDijkstraPairingHeap (numNodes : Nat) (rounds : UInt64) : UInt64 := Id.run do
  let mut dist : Array UInt64 := Array.replicate numNodes 0
  let mut visited : Array UInt64 := Array.replicate numNodes 0
  let mut total : UInt64 := 0
  let mut r : UInt64 := 0
  while r < rounds do
    for i in [0:numNodes] do
      dist := dist.set! i 1000000000
      visited := visited.set! i 0
    dist := dist.set! 0 0
    for _ in [0:numNodes] do
      let mut u : Nat := 0
      let mut best : UInt64 := 0xFFFFFFFFFFFFFFFF
      for v in [0:numNodes] do
        if visited[v]! == 0 && dist[v]! < best then
          best := dist[v]!
          u := v
      visited := visited.set! u 1
      let du := dist[u]!
      for deg in [1:9] do
        let target := (u * 7 + deg * 13 + r.toNat) &&& (numNodes - 1)
        let weight := (((Nat.xor u target) + deg * 5) &&& 63).toUInt64 + 1
        let cand := du + weight
        if cand < dist[target]! then
          dist := dist.set! target cand
    total := total + (dist[numNodes - 1]! ^^^ dist[numNodes / 2]!)
    r := r + 1
  return total

-- 18. regex_dfa_step
def benchRegexDfaStep (len : UInt64) (rounds : UInt64) : UInt64 := Id.run do
  let mut trans : Array UInt64 := Array.replicate (64 * 16) 0
  for s in [0:64] do
    for c in [0:16] do
      let nxt := (Nat.xor (s * 5 + c * 3 + 1) (s / 4)) &&& 63
      trans := trans.set! (s * 16 + c) nxt.toUInt64
  let mut matchCount : UInt64 := 0
  let mut r : UInt64 := 0
  while r < rounds do
    let mut state : Nat := 0
    let mut z : UInt64 := r + 0x123456789ABCDEF0
    let mut i : UInt64 := 0
    while i < len do
      z := z * 6364136223846793005 + 1
      let sym := ((z >>> 56) &&& 15).toNat
      state := (trans[state * 16 + sym]!).toNat
      if state == 63 then
        matchCount := matchCount + 1
      i := i + 1
    matchCount := matchCount + state.toUInt64
    r := r + 1
  return matchCount

-- 19. json_simd_scanner
def benchJsonSimdScanner (words : UInt64) (rounds : UInt64) : UInt64 := Id.run do
  let mut structCount : UInt64 := 0
  let mut r : UInt64 := 0
  while r < rounds do
    let mut quoteParity : UInt64 := 0
    let mut x : UInt64 := r * 0x9E3779B97F4A7C15 + 0x227B7D3A2C5B5D22
    let mut i : UInt64 := 0
    while i < words do
      x := (rotl64 x 13) * 0xBF58476D1CE4E5B9 + 0x22007B007D003A2C
      let xq := x ^^^ 0x2222222222222222
      let xl := x ^^^ 0x7B7B7B7B7B7B7B7B
      let xr := x ^^^ 0x7D7D7D7D7D7D7D7D
      let eqQuote := (xq - 0x0101010101010101) &&& (~~~xq) &&& 0x8080808080808080
      let eqLbrace := (xl - 0x0101010101010101) &&& (~~~xl) &&& 0x8080808080808080
      let eqRbrace := (xr - 0x0101010101010101) &&& (~~~xr) &&& 0x8080808080808080
      quoteParity := quoteParity ^^^ ((popcount64 eqQuote) &&& 1)
      let active := (eqLbrace ||| eqRbrace) &&& (quoteParity - 1)
      structCount := structCount + popcount64 active
      i := i + 1
    r := r + 1
  return structCount

-- 20. sparse_matmul_csr
def benchSparseMatmulCsr (rows nnzPerRow : Nat) (rounds : UInt64) : UInt64 := Id.run do
  let totalNnz := rows * nnzPerRow
  let mut colIdx : Array Nat := Array.replicate totalNnz 0
  let mut vals : Array UInt64 := Array.replicate totalNnz 0
  let mut x : Array UInt64 := Array.replicate rows 0
  let mut y : Array UInt64 := Array.replicate rows 0
  for i in [0:rows] do
    x := x.set! i (((i * 11 + 3) &&& 0xFF).toUInt64)
    for k in [0:nnzPerRow] do
      let idx := i * nnzPerRow + k
      colIdx := colIdx.set! idx ((i * 7 + k * 31 + 5) &&& (rows - 1))
      vals := vals.set! idx (((idx * 17 + 1) &&& 0xFF).toUInt64)
  let mut checksum : UInt64 := 0
  let mut r : UInt64 := 0
  while r < rounds do
    for i in [0:rows] do
      let mut sum : UInt64 := 0
      let base := i * nnzPerRow
      for k in [0:nnzPerRow] do
        let c := colIdx[base + k]!
        sum := sum + vals[base + k]! * x[c]!
      y := y.set! i (sum + r)
    let tmp := x
    x := y
    y := tmp
    checksum := checksum + (x[0]! ^^^ x[rows / 2]! ^^^ x[rows - 1]!)
    r := r + 1
  return checksum

@[noinline]
def runtimeZero : IO UInt64 := do
  let t ← IO.monoNanosNow
  if t == 999999999999999999 then return 1 else return 0

@[noinline]
def forceIO (v : UInt64) : IO UInt64 := do
  let ref ← IO.mkRef v
  ref.get

def runEntry (name : String) (filter : String) (f : UInt64 → UInt64) : IO Unit := do
  if filter != "all" && filter != name then
    return ()
  let z0 ← runtimeZero
  let _ ← forceIO (f z0)
  let z1 ← runtimeZero
  let t0 ← IO.monoNanosNow
  let res ← forceIO (f z1)
  let t1 ← IO.monoNanosNow
  let dt := t1 - t0
  IO.println s!"BENCH:{name}:{dt}:{res}"

def main (args : List String) : IO Unit := do
  let filter := args.headD "all"
  runEntry "collatz_steps" filter (fun z => benchCollatzSteps (100000 + z))
  runEntry "tuple_accum_sum" filter (fun z => benchTupleAccumSum (2000000 + z))
  runEntry "sarray_scale_bias" filter (fun z => benchSArrayScaleBias 65536 (40 + z))
  runEntry "dot_product_u64" filter (fun z => benchDotProductU64 65536 (40 + z))
  runEntry "saxpy_kernel" filter (fun z => benchSaxpyKernel 65536 (40 + z))
  runEntry "matmul_tiled_u64" filter (fun z => benchMatmulTiledU64 (192 + z.toNat))
  runEntry "binary_trees" filter (fun z => benchBinaryTrees 11 (200 + z))
  runEntry "nbody" filter (fun z => benchNbody (200000 + z))
  runEntry "spectral_norm" filter (fun z => benchSpectralNorm 128 (30 + z))
  runEntry "fannkuch_redux" filter (fun z => benchFannkuchRedux (100000 + z))
  runEntry "mandelbrot_simd" filter (fun z => benchMandelbrotSimd 256 256 (64 + z))
  runEntry "robin_hood_htab" filter (fun z => benchRobinHoodHtab (131072 + z))
  runEntry "sha256_compress" filter (fun z => benchSha256Compress (25000 + z))
  runEntry "keccak_f1600" filter (fun z => benchKeccakF1600 (50000 + z))
  runEntry "mul_div_512" filter (fun z => benchMulDiv512 (1000000 + z))
  runEntry "radix_sort_u64" filter (fun z => benchRadixSortU64 16384 (20 + z))
  runEntry "dijkstra_pairing_heap" filter (fun z => benchDijkstraPairingHeap 256 (20 + z))
  runEntry "regex_dfa_step" filter (fun z => benchRegexDfaStep 65536 (20 + z))
  runEntry "json_simd_scanner" filter (fun z => benchJsonSimdScanner 65536 (20 + z))
  runEntry "sparse_matmul_csr" filter (fun z => benchSparseMatmulCsr 2048 16 (40 + z))
