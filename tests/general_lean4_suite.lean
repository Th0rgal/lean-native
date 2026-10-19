/-
  LeanNative v0.2 — General-Purpose Lean 4 Compilation Test Suite
  Exercises:
  1. Multi-constructor algebraic data types (`Expr` with 4 constructors, `Tree α` with 2 constructors)
  2. Higher-order closures & partial applications (`Array.map`, `Array.foldl`, custom combinators)
  3. Contiguous `ByteArray` and `FloatArray` operations
  4. Monadic state/exception transformers (`StateT UInt64 (Except String) UInt64`)
  5. `IO` output printing a deterministic 64-bit checksum of all test results
-/

namespace GeneralLean4Suite

/-- 1a. Multi-constructor expression ADT (4 constructors). -/
inductive Expr where
  | lit (v : UInt64)
  | add (a b : Expr)
  | mul (a b : Expr)
  | ite (c t e : Expr)
  deriving Repr, Inhabited

/-- Evaluate an `Expr` recursively (exercises multi-way constructor tag dispatch). -/
def evalExpr : Expr → UInt64
  | .lit v     => v
  | .add a b   => evalExpr a + evalExpr b
  | .mul a b   => evalExpr a * evalExpr b
  | .ite c t e => if evalExpr c != 0 then evalExpr t else evalExpr e

/-- 1b. Polymorphic binary tree ADT. -/
inductive Tree (α : Type) where
  | leaf (v : α)
  | node (l r : Tree α)
  deriving Repr, Inhabited

/-- Fold a `Tree` using higher-order leaf and node functions. -/
def foldTree {α β : Type} (onLeaf : α → β) (onNode : β → β → β) : Tree α → β
  | .leaf v   => onLeaf v
  | .node l r => onNode (foldTree onLeaf onNode l) (foldTree onLeaf onNode r)

/-- Build a balanced binary tree of depth `d` rooted at `seed`. -/
def buildTree : Nat → UInt64 → Tree UInt64
  | 0, seed => .leaf (seed * 13 + 7)
  | d + 1, seed =>
    .node (buildTree d (seed * 2 + 1)) (buildTree d (seed * 2 + 2))

/-- 2. Higher-order combinators, partial applications, `Array.map`, and `Array.foldl`. -/
def applyTwice {α : Type} (f : α → α) (x : α) : α :=
  f (f x)

def affineStep (scale bias x : UInt64) : UInt64 :=
  x * scale + bias

def runClosureSuite : UInt64 :=
  let base : Array UInt64 := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  let stepFn : UInt64 → UInt64 := affineStep 5 3
  let mapped := base.map (applyTwice stepFn)
  mapped.foldl (fun acc v => acc * 31 + v) 0

/-- 3a. Contiguous `ByteArray` construction and rolling FNV-like checksum. -/
def runByteArraySuite (n : Nat) : UInt64 := Id.run do
  let mut ba := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    ba := ba.push ((i * 17 + 43).toUInt8)
  let mut acc : UInt64 := 14695981039346656037
  for i in [0:ba.size] do
    let b := ba.get! i
    acc := (acc ^^^ b.toUInt64) * 1099511628211
  return acc

/-- 3b. Contiguous `FloatArray` dot-product and scaling kernel. -/
def runFloatArraySuite (n : Nat) : UInt64 := Id.run do
  let mut xs := FloatArray.emptyWithCapacity n
  let mut ys := FloatArray.emptyWithCapacity n
  for i in [0:n] do
    let fi := i.toFloat
    xs := xs.push (fi * 1.5 + 0.5)
    ys := ys.push (fi * 0.25 + 2.0)
  let mut dot : Float := 0.0
  for i in [0:xs.size] do
    dot := dot + xs.get! i * ys.get! i
  return (dot * 100.0).toUInt64

/-- 4. Monadic `StateT UInt64 (Except String) UInt64` pipeline. -/
abbrev CalcM := StateT UInt64 (Except String)

def monadicStep (delta : UInt64) (limit : UInt64) : CalcM UInt64 := do
  let s ← get
  let next := s * 3 + delta
  if next > limit then
    throw "limit exceeded"
  else
    set next
    return next

def runMonadSuite : UInt64 :=
  let prog : CalcM UInt64 := do
    let a ← monadicStep 7 1000000
    let b ← monadicStep 11 1000000
    let c ← monadicStep 19 1000000
    return a + b + c
  match prog.run 5 with
  | .ok (val, finalSt) => val * 131 + finalSt
  | .error _           => 0

/-- 5. Combine all suite outputs into a deterministic 64-bit checksum. -/
def computeSuiteChecksum : UInt64 :=
  let sampleExpr : Expr :=
    .add
      (.mul (.lit 6) (.lit 7))
      (.ite (.lit 1) (.add (.lit 100) (.lit 23)) (.lit 999))
  let exprRes := evalExpr sampleExpr
  let tree := buildTree 5 3
  let treeRes := foldTree (fun x => x) (fun l r => l * 3 + r + 1) tree
  let closureRes := runClosureSuite
  let byteRes := runByteArraySuite 64
  let floatRes := runFloatArraySuite 32
  let monadRes := runMonadSuite
  let mix (h x : UInt64) : UInt64 := (h ^^^ x) * 6364136223846793005 + 1442695040888963407
  let h0 : UInt64 := 0x9e3779b97f4a7c15
  let h1 := mix h0 exprRes
  let h2 := mix h1 treeRes
  let h3 := mix h2 closureRes
  let h4 := mix h3 byteRes
  let h5 := mix h4 floatRes
  let h6 := mix h5 monadRes
  h6

end GeneralLean4Suite

def main : IO Unit := do
  let exprVal := GeneralLean4Suite.evalExpr
    (.add (.mul (.lit 6) (.lit 7)) (.ite (.lit 1) (.add (.lit 100) (.lit 23)) (.lit 999)))
  let treeVal := GeneralLean4Suite.foldTree
    (fun x => x) (fun l r => l * 3 + r + 1) (GeneralLean4Suite.buildTree 5 3)
  let closureVal := GeneralLean4Suite.runClosureSuite
  let byteVal := GeneralLean4Suite.runByteArraySuite 64
  let floatVal := GeneralLean4Suite.runFloatArraySuite 32
  let monadVal := GeneralLean4Suite.runMonadSuite
  let checksum := GeneralLean4Suite.computeSuiteChecksum
  IO.println s!"expr={exprVal} tree={treeVal} closure={closureVal} bytes={byteVal} floats={floatVal} monad={monadVal}"
  IO.println s!"CHECKSUM64={checksum}"
