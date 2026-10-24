structure U128 where lo : UInt64; hi : UInt64
def gf128Mul (a b : U128) : U128 := Id.run do
  let mut xlo := a.lo; let mut xhi := a.hi; let mut ylo := b.lo; let mut yhi := b.hi; let mut lo : UInt64 := 0; let mut hi : UInt64 := 0; let mut i : UInt64 := 0
  while i < 128 do
    let mask : UInt64 := 0 - (ylo &&& 1); lo := lo ^^^ (xlo &&& mask); hi := hi ^^^ (xhi &&& mask); let carry := xhi >>> 63
    let nxlo := (xlo <<< 1) ^^^ (0x87 &&& (0 - carry)); let nxhi := (xhi <<< 1) ||| (xlo >>> 63); xlo := nxlo; xhi := nxhi; ylo := (ylo >>> 1) ||| (yhi <<< 63); yhi := yhi >>> 1; i := i + 1
  return { lo, hi }
def mix128 (x : U128) (rounds : UInt64) : U128 := Id.run do
  let mut vlo := x.lo; let mut vhi := x.hi; let mut i : UInt64 := 0
  while i < rounds do
    let v := gf128Mul { lo := vlo ^^^ ((i * 0x9e3779b97f4a7c15) ^^^ 0x0123456789abcdef), hi := vhi ^^^ ((i * 0xd1b54a32d192ed03) ^^^ 0xfedcba9876543210) } { lo := 0x1f1e1d1c1b1a1918, hi := 0x1716151413121110 }
    vlo := v.lo; vhi := v.hi; i := i + 1
  return { lo := vlo, hi := vhi }
def modAdd (a b : UInt64) : UInt64 := let s := a + b; if s >= 998244353 then s - 998244353 else s
def modSub (a b : UInt64) : UInt64 := if a >= b then a - b else a + 998244353 - b
def modMul (a b : UInt64) : UInt64 := (a * b) % 998244353
def modPow (a e : UInt64) : UInt64 := Id.run do
  let mut base := a; let mut exp := e; let mut out : UInt64 := 1; let mut i : UInt64 := 0
  while i < 32 do if (exp &&& 1) != 0 then out := modMul out base; base := modMul base base; exp := exp >>> 1; i := i + 1
  return out
def bitReverse8 (i : Nat) : Nat := ((i &&& 1) <<< 7) ||| (((i >>> 1) &&& 1) <<< 6) ||| (((i >>> 2) &&& 1) <<< 5) ||| (((i >>> 3) &&& 1) <<< 4) ||| (((i >>> 4) &&& 1) <<< 3) ||| (((i >>> 5) &&& 1) <<< 2) ||| (((i >>> 6) &&& 1) <<< 1) ||| ((i >>> 7) &&& 1)
def ntt (input : Array UInt64) (invert : Bool) : Array UInt64 := Id.run do
  let n := input.size; let mut a := input; for i in [0:n] do let rev := bitReverse8 i; if i < rev then let t := a[i]!; a := a.set! i a[rev]!; a := a.set! rev t
  let mut len : Nat := 2
  while len <= n do
    let wlen := if invert then modPow 3 998244351 else modPow 3 ((998244353 - 1) / len).toUInt64; let half := len / 2; let mut base : Nat := 0
    while base < n do
      let mut w : UInt64 := 1; for i in [0:half] do let u := a[base + i]!; let v := modMul a[base + i + half]! w; a := a.set! (base + i) (modAdd u v); a := a.set! (base + i + half) (modSub u v); w := modMul w wlen
      base := base + len
    len := len * 2
  if invert then let invN := modPow n.toUInt64 998244351; for i in [0:n] do a := a.set! i (modMul a[i]! invN)
  return a
def runGf128 (rounds : UInt64) : UInt64 := let v := mix128 { lo := 0x0123456789abcdef, hi := 0xfedcba9876543210 } rounds; v.lo ^^^ (v.hi * 0x9e3779b97f4a7c15)
def runNtt (rounds : UInt64) : UInt64 := Id.run do
  let mut total : UInt64 := 0; let mut r : UInt64 := 0
  while r < rounds do let mut xs : Array UInt64 := Array.mkEmpty 256; for i in [0:256] do xs := xs.push (((i.toUInt64 * 17 + r * 13 + 7) % 998244353)); let ys := ntt xs false; total := total + ys[0]! + ys[127]!; r := r + 1
  return total
@[noinline] def runtimeZero : IO UInt64 := do let t ← IO.monoNanosNow; if t == 999999999999999999 then return 1 else return 0
@[noinline] def forceIO (v : UInt64) : IO UInt64 := do let ref ← IO.mkRef v; ref.get
def runEntry (name : String) (f : UInt64 → UInt64) : IO Unit := do let z0 ← runtimeZero; let _ ← forceIO (f z0); let z1 ← runtimeZero; let t0 ← IO.monoNanosNow; let result ← forceIO (f z1); let t1 ← IO.monoNanosNow; IO.println s!"BENCH:{name}:checksum={result}:time_ns={t1 - t0}"
def main (_args : List String) : IO Unit := do runEntry "gf128_scalar" (fun z => runGf128 (4096 + z)); runEntry "ntt_modular" (fun z => runNtt (64 + z))
