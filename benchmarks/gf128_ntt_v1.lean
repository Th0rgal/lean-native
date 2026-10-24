structure U128 where (lo hi : UInt64)
@[noinline] def clmul64 (a b : UInt64) : UInt64 := let rec go (i : Nat) (acc : UInt64) : UInt64 := if _ : i < 64 then let iu := i.toUInt64; go (i + 1) (if ((b >>> iu) &&& 1) == 1 then acc ^^^ (a <<< iu) else acc) else acc; go 0 0
@[noinline] def clmul64Hi (a b : UInt64) : UInt64 := let rec go (i : Nat) (acc : UInt64) : UInt64 := if _ : i < 64 then let iu := i.toUInt64; go (i + 1) (if ((b >>> iu) &&& 1) == 1 then acc ^^^ (a >>> (64 - iu)) else acc) else acc; go 1 0
def gf128Mul (a b : U128) : U128 := let c0 := clmul64 a.lo b.lo; let c1 := clmul64Hi a.lo b.lo ^^^ clmul64 a.lo b.hi ^^^ clmul64 a.hi b.lo; let c2 := clmul64Hi a.lo b.hi ^^^ clmul64Hi a.hi b.lo ^^^ clmul64 a.hi b.hi; let c3 := clmul64Hi a.hi b.hi; let c1' := c1 ^^^ clmul64 c3 0x87; let c2' := c2 ^^^ clmul64Hi c3 0x87; { lo := c0 ^^^ clmul64 c2' 0x87, hi := c1' ^^^ clmul64Hi c2' 0x87 }
def mix128 (x : U128) (rounds : UInt64) : U128 := Id.run do
  let mut vlo := x.lo; let mut vhi := x.hi; let mut i : UInt64 := 0
  while i < rounds do let v := gf128Mul { lo := vlo ^^^ ((i * 0x9e3779b97f4a7c15) ^^^ 0x0123456789abcdef), hi := vhi ^^^ ((i * 0xd1b54a32d192ed03) ^^^ 0xfedcba9876543210) } { lo := 0x1f1e1d1c1b1a1918, hi := 0x1716151413121110 }; vlo := v.lo; vhi := v.hi; i := i + 1
  return { lo := vlo, hi := vhi }
def modAdd (a b : UInt64) : UInt64 := let s := a + b; if s >= 998244353 then s - 998244353 else s
def modSub (a b : UInt64) : UInt64 := if a >= b then a - b else a + 998244353 - b
def modMul (a b : UInt64) : UInt64 := (a * b) % 998244353
def modPow (a e : UInt64) : UInt64 := Id.run do
  let mut base := a; let mut exp := e; let mut out : UInt64 := 1; let mut i : UInt64 := 0
  while i < 32 do out := if (exp &&& 1) != 0 then modMul out base else out; base := modMul base base; exp := exp >>> 1; i := i + 1
  return out
def bitReverse8 (i : UInt64) : UInt64 := ((i &&& 1) <<< 7) ||| (((i >>> 1) &&& 1) <<< 6) ||| (((i >>> 2) &&& 1) <<< 5) ||| (((i >>> 3) &&& 1) <<< 4) ||| (((i >>> 4) &&& 1) <<< 3) ||| (((i >>> 5) &&& 1) <<< 2) ||| (((i >>> 6) &&& 1) <<< 1) ||| ((i >>> 7) &&& 1)
def ntt (input : Array UInt64) (_invert : Bool) : Array UInt64 := Id.run do
  let n : UInt64 := input.size.toUInt64; let mut a := input; let mut idx : UInt64 := 0
  while idx < n do
    let rev := bitReverse8 idx; a := if idx < rev then let i := idx.toNat; let r := rev.toNat; let t := a[i]!; (a.set! i a[r]!).set! r t else a; idx := idx + 1
  let mut len : UInt64 := 2
  while len <= n do
    let len2 := len * 2; let wlen2 := modPow 3 (998244352 / len2); let wlen1 := modMul wlen2 wlen2; let h1 := len >>> 1; let mut base : UInt64 := 0
    while base < n do
      let mut w1 : UInt64 := 1; let mut w2 : UInt64 := 1; let mut w3 : UInt64 := 911660635; let mut i : UInt64 := 0
      while i < h1 do
        let i0 := (base + i).toNat; let i1 := (base + i + h1).toNat; let i2 := (base + i + len).toNat; let i3 := (base + i + len + h1).toNat; let a0 := a[i0]!; let a1 := modMul a[i1]! w1; let a2 := a[i2]!; let a3 := modMul a[i3]! w1; let u0 := modAdd a0 a1; let u1 := modSub a0 a1; let v0 := modMul (modAdd a2 a3) w2; let v1 := modMul (modSub a2 a3) w3; a := (((a.set! i0 (modAdd u0 v0)).set! i1 (modAdd u1 v1)).set! i2 (modSub u0 v0)).set! i3 (modSub u1 v1); w1 := modMul w1 wlen1; w2 := modMul w2 wlen2; w3 := modMul w3 wlen2; i := i + 1
      base := base + len2
    len := len * 4
  return a
def runGf128 (rounds : UInt64) : UInt64 := let v := mix128 { lo := 0x0123456789abcdef, hi := 0xfedcba9876543210 } rounds; v.lo ^^^ (v.hi * 0x9e3779b97f4a7c15)
def runNtt (rounds : UInt64) : UInt64 := Id.run do
  let mut total : UInt64 := 0; let mut r : UInt64 := 0
  while r < rounds do
    let mut xs : Array UInt64 := Array.mkEmpty 256; let mut i : UInt64 := 0; while i < 256 do xs := xs.push ((i * 17 + r * 13 + 7) % 998244353); i := i + 1
    let ys := ntt xs false; total := total + ys[0]! + ys[127]!; r := r + 1
  return total
@[noinline] def runtimeZero : IO UInt64 := do let t ← IO.monoNanosNow; if t == 999999999999999999 then return 1 else return 0
@[noinline] def forceIO (v : UInt64) : IO UInt64 := do let ref ← IO.mkRef v; ref.get
def runEntry (name : String) (f : UInt64 → UInt64) : IO Unit := do let z0 ← runtimeZero; let _ ← forceIO (f z0); let z1 ← runtimeZero; let t0 ← IO.monoNanosNow; let result ← forceIO (f z1); let t1 ← IO.monoNanosNow; IO.println s!"BENCH:{name}:checksum={result}:time_ns={t1 - t0}"
def main (_args : List String) : IO Unit := do runEntry "gf128_scalar" (fun z => runGf128 (4096 + z)); runEntry "ntt_modular" (fun z => runNtt (64 + z))
