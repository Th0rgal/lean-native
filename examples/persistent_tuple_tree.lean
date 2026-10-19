/-
  LeanNative v0.4 Showcase Example 3 — `examples/persistent_tuple_tree.lean`
  Persistent Functional Red-Black Search Trees + Unboxed Tuple Accumulators (`Prod UInt64 UInt64`)
  + Exclusive In-Place Scalar Arrays

  Demonstrates:
  1. Persistent functional Red-Black Tree (`RBTree`) with Okasaki balance invariants, sharing
     unmodified subtrees across versions (`t1` vs `t2`).
  2. Multi-accumulator tree fold returning `Prod UInt64 UInt64` (`(keyWeightedSum, valueXorDigest)`),
     exercising `UnboxTupleSROA` across recursive join points.
  3. Exclusive in-place scalar array transformation (`HoistExclusivity`) fed by the tree's flattened key-value stream.
-/

namespace PersistentTupleTree

inductive Color where
  | red
  | black
  deriving Repr, DecidableEq, Inhabited, BEq

inductive RBTree where
  | leaf
  | node (c : Color) (left : RBTree) (key : UInt64) (val : UInt64) (right : RBTree)
  deriving Repr, Inhabited

namespace RBTree

/-- Okasaki Red-Black Tree balance operation restoring red-red invariants functionally. -/
def balance (c : Color) (left : RBTree) (k v : UInt64) (right : RBTree) : RBTree :=
  match c, left, k, v, right with
  | .black, .node .red (.node .red a xk xv b) yk yv cTree, zk, zv, d =>
    .node .red (.node .black a xk xv b) yk yv (.node .black cTree zk zv d)
  | .black, .node .red a xk xv (.node .red b yk yv cTree), zk, zv, d =>
    .node .red (.node .black a xk xv b) yk yv (.node .black cTree zk zv d)
  | .black, a, xk, xv, .node .red (.node .red b yk yv cTree) zk zv d =>
    .node .red (.node .black a xk xv b) yk yv (.node .black cTree zk zv d)
  | .black, a, xk, xv, .node .red b yk yv (.node .red cTree zk zv d) =>
    .node .red (.node .black a xk xv b) yk yv (.node .black cTree zk zv d)
  | col, l, key, val, r =>
    .node col l key val r

def ins (t : RBTree) (k v : UInt64) : RBTree :=
  match t with
  | .leaf => .node .red .leaf k v .leaf
  | .node col l curK curV r =>
    if k < curK then
      balance col (ins l k v) curK curV r
    else if curK < k then
      balance col l curK curV (ins r k v)
    else
      .node col l k v r

/-- Persistent insertion returning a new root while preserving all previous tree versions. -/
def insert (t : RBTree) (k v : UInt64) : RBTree :=
  match ins t k v with
  | .node _ l rootK rootV r => .node .black l rootK rootV r
  | .leaf => .leaf

/-- Lookup key `k` in `RBTree`. -/
def find? (t : RBTree) (k : UInt64) : Option UInt64 :=
  match t with
  | .leaf => none
  | .node _ l curK curV r =>
    if k < curK then find? l k
    else if curK < k then find? r k
    else some curV

/-- Accumulate `(sumOfKeysAndVals, xorDigest)` across the tree using an unboxed 2-tuple (`Prod UInt64 UInt64`). -/
def foldTupleAccum (t : RBTree) (acc : UInt64 × UInt64) : UInt64 × UInt64 :=
  match t with
  | .leaf => acc
  | .node _ l k v r =>
    let (sL, xL) := foldTupleAccum l acc
    let sMid := sL + k * 31 + v
    let xMid := (xL ^^^ (k * 1315423911 + v)) * 1099511628211
    foldTupleAccum r (sMid, xMid)

end RBTree

/-- Tail-recursive tuple accumulator loop (`UnboxTupleSROA` + `HoistExclusivity` showcase). -/
def transformExclusiveBuffer (arr : Array UInt64) (seedTuple : UInt64 × UInt64) : Array UInt64 × (UInt64 × UInt64) := Id.run do
  let mut buf := arr
  let mut s := seedTuple.1
  let mut x := seedTuple.2
  for i in [0:buf.size] do
    let elem := buf[i]!
    let updated := elem * 3 + (s &&& 0xff)
    buf := buf.set! i updated
    s := s + updated
    x := (x ^^^ updated) * 1099511628211
  return (buf, (s, x))

def runPersistentTreeSuite : Bool × UInt64 × UInt64 × UInt64 := Id.run do
  -- Build base persistent tree `t1` with 64 keys
  let mut t1 : RBTree := .leaf
  let mut initArr := Array.mkEmpty 64
  for i in [0:64] do
    let k := ((i * 37 + 13) % 256).toUInt64
    let v := (i * 100 + 7).toUInt64
    t1 := t1.insert k v
    initArr := initArr.push (k + v)

  -- Create persistent branched version `t2` by inserting/overwriting 16 keys without mutating `t1`
  let mut t2 := t1
  for j in [0:16] do
    let k := ((j * 37 + 13) % 256).toUInt64
    t2 := t2.insert k 999999

  -- Verify persistence: key 13 (`i = 0`) still maps to `7` in `t1` and `999999` in `t2`
  let v1Key13 := t1.find? 13
  let v2Key13 := t2.find? 13
  let persistenceOk := v1Key13 == some 7 && v2Key13 == some 999999

  let tup1 := t1.foldTupleAccum (0, 14695981039346656037)
  let tup2 := t2.foldTupleAccum (0, 14695981039346656037)
  let (_, (finalSum, finalXor)) := transformExclusiveBuffer initArr tup1

  let ok := persistenceOk && tup1.1 != tup2.1 && finalSum > tup1.1
  let checksum := ((tup1.2 ^^^ tup2.2) * 1099511628211) ^^^ finalXor
  return (ok, tup1.1, tup2.1, checksum)

end PersistentTupleTree

open PersistentTupleTree in
def main : IO UInt32 := do
  let (ok, sumV1, sumV2, checksum) := runPersistentTreeSuite
  IO.println "=== LeanNative v0.4 Showcase: Persistent Red-Black Tree & Unboxed Tuple Accumulators ==="
  IO.println s!"  Persistent Snapshot v1 Tuple Sum : {sumV1}"
  IO.println s!"  Branched Snapshot v2 Tuple Sum   : {sumV2}"
  IO.println s!"  Persistence & Tuple SROA Check   : {if ok then "VALID" else "FAILED"}"
  IO.println s!"  Deterministic 64-Bit Checksum    : {checksum}"
  if ok then
    IO.println "[PASS] examples/persistent_tuple_tree.lean verified."
    return 0
  else
    IO.println "[FAIL] examples/persistent_tuple_tree.lean verification failed."
    return 1
