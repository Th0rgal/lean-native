/-
  LeanNative v0.4 Showcase Example 1 — `examples/verity_amm_vault.lean`
  EVM 256-Bit Constant-Product AMM & ERC-4626 Tokenized Vault with FastCheck Falsification

  Demonstrates:
  1. 256-bit 4-limb (`UInt256`) EVM arithmetic with full 512-bit intermediate `mulDivDown` & `mulDivUp`.
  2. ERC-4626 Vault directional rounding rules:
     - `deposit(assets)` -> mints `shares = mulDivDown(assets, totalShares, totalAssets)` (rounds DOWN, favoring vault).
     - `mint(shares)`    -> requires `assets = mulDivUp(shares, totalAssets, totalShares)` (rounds UP, favoring vault).
     - `withdraw(assets)`-> burns `shares = mulDivUp(assets, totalShares, totalAssets)` (rounds UP, favoring vault).
     - `redeem(shares)`  -> sends `assets = mulDivDown(shares, totalAssets, totalShares)` (rounds DOWN, favoring vault).
  3. Constant-Product AMM (`x * y >= k`) swap execution with 30 bps fee and `mulDivDown` output rounding.
  4. Solvency invariant verification (`assets_after * total_shares_before >= assets_before * total_shares_after`)
     across 1,000 SplitMix64 random & boundary operations.
  5. Intentional rounding-reversal bug (`buggyDepositMintShares` using `mulDivUp` instead of `mulDivDown`)
     creating a share-inflation / vault-draining counterexample caught immediately by FastCheck!
-/

namespace VerityAmmVault

/-- 256-bit unsigned EVM word (`uint256`) represented as four 64-bit limbs. -/
structure UInt256 where
  lo0 : UInt64 := 0
  lo1 : UInt64 := 0
  hi0 : UInt64 := 0
  hi1 : UInt64 := 0
  deriving Repr, DecidableEq, Inhabited, BEq

namespace UInt256

def modulusNat : Nat := 2 ^ 256
def zero : UInt256 := ⟨0, 0, 0, 0⟩
def one  : UInt256 := ⟨1, 0, 0, 0⟩
def wad  : UInt256 := ⟨1000000000000000000, 0, 0, 0⟩ -- 10^18

def toNat (w : UInt256) : Nat :=
  w.lo0.toNat +
  w.lo1.toNat * (2 ^ 64) +
  w.hi0.toNat * (2 ^ 128) +
  w.hi1.toNat * (2 ^ 192)

def ofNat (n : Nat) : UInt256 :=
  let m := n % modulusNat
  let l0 := (m % (2 ^ 64)).toUInt64
  let l1 := ((m / (2 ^ 64)) % (2 ^ 64)).toUInt64
  let h0 := ((m / (2 ^ 128)) % (2 ^ 64)).toUInt64
  let h1 := ((m / (2 ^ 192)) % (2 ^ 64)).toUInt64
  ⟨l0, l1, h0, h1⟩

def ofUInt64 (x : UInt64) : UInt256 := ⟨x, 0, 0, 0⟩

def addChecked (a b : UInt256) : Option UInt256 :=
  let s := a.toNat + b.toNat
  if s >= modulusNat then none else some (ofNat s)

def subChecked (a b : UInt256) : Option UInt256 :=
  if a.toNat < b.toNat then none else some (ofNat (a.toNat - b.toNat))

/-- Full 512-bit intermediate `floor((a * b) / denom)` (`mulDivDown` in EVM/Verity). -/
def mulDivDown (a b denom : UInt256) : Option UInt256 :=
  let d := denom.toNat
  if d == 0 then none
  else
    let q := (a.toNat * b.toNat) / d
    if q >= modulusNat then none else some (ofNat q)

/-- Full 512-bit intermediate `ceil((a * b) / denom)` (`mulDivUp` in EVM/Verity). -/
def mulDivUp (a b denom : UInt256) : Option UInt256 :=
  let d := denom.toNat
  if d == 0 then none
  else
    let prod := a.toNat * b.toNat
    let q := (prod + d - 1) / d
    if q >= modulusNat then none else some (ofNat q)

end UInt256

/-- ERC-4626 Vault state tracking `totalAssets` and `totalShares`. -/
structure VaultState where
  totalAssets : UInt256
  totalShares : UInt256
  deriving Repr, DecidableEq, Inhabited

/-- Constant-Product AMM Pool state (`reserveX * reserveY >= k`). -/
structure AmmPool where
  reserveX : UInt256
  reserveY : UInt256
  deriving Repr, DecidableEq, Inhabited

/-- Sound ERC-4626 `deposit`: mints `shares = mulDivDown(assetsIn, totalShares, totalAssets)`. -/
def vaultDepositSound (st : VaultState) (assetsIn : UInt256) : Option (VaultState × UInt256) := do
  let sharesMinted ←
    if st.totalShares == UInt256.zero || st.totalAssets == UInt256.zero then
      some assetsIn
    else
      UInt256.mulDivDown assetsIn st.totalShares st.totalAssets
  let newAssets ← UInt256.addChecked st.totalAssets assetsIn
  let newShares ← UInt256.addChecked st.totalShares sharesMinted
  some ({ totalAssets := newAssets, totalShares := newShares }, sharesMinted)

/-- Sound ERC-4626 `mint`: requires `assetsIn = mulDivUp(sharesOut, totalAssets, totalShares)`. -/
def vaultMintSound (st : VaultState) (sharesOut : UInt256) : Option (VaultState × UInt256) := do
  let assetsRequired ←
    if st.totalShares == UInt256.zero || st.totalAssets == UInt256.zero then
      some sharesOut
    else
      UInt256.mulDivUp sharesOut st.totalAssets st.totalShares
  let newAssets ← UInt256.addChecked st.totalAssets assetsRequired
  let newShares ← UInt256.addChecked st.totalShares sharesOut
  some ({ totalAssets := newAssets, totalShares := newShares }, assetsRequired)

/-- Sound ERC-4626 `redeem`: returns `assetsOut = mulDivDown(sharesBurned, totalAssets, totalShares)`. -/
def vaultRedeemSound (st : VaultState) (sharesBurned : UInt256) : Option (VaultState × UInt256) := do
  if st.totalShares.toNat == 0 || sharesBurned.toNat > st.totalShares.toNat then
    none
  else
    let assetsOut ← UInt256.mulDivDown sharesBurned st.totalAssets st.totalShares
    let newAssets ← UInt256.subChecked st.totalAssets assetsOut
    let newShares ← UInt256.subChecked st.totalShares sharesBurned
    some ({ totalAssets := newAssets, totalShares := newShares }, assetsOut)

/-- BUGGY ERC-4626 `deposit` that reverses `mulDivDown` -> `mulDivUp` when minting shares,
    allowing an attacker to inflate shares and violate the vault solvency invariant! -/
def vaultDepositBuggyReversedRounding (st : VaultState) (assetsIn : UInt256) : Option (VaultState × UInt256) := do
  let sharesMinted ←
    if st.totalShares == UInt256.zero || st.totalAssets == UInt256.zero then
      some assetsIn
    else
      -- BUG: uses mulDivUp instead of mulDivDown when minting shares!
      UInt256.mulDivUp assetsIn st.totalShares st.totalAssets
  let newAssets ← UInt256.addChecked st.totalAssets assetsIn
  let newShares ← UInt256.addChecked st.totalShares sharesMinted
  some ({ totalAssets := newAssets, totalShares := newShares }, sharesMinted)

/-- Vault Solvency / Share-Price Non-Dilution Invariant (512-bit exact cross-multiplication):
    `assets_after * total_shares_before >= assets_before * total_shares_after`. -/
def checkVaultSolvencyInvariant (before after : VaultState) : Bool :=
  let lhs := after.totalAssets.toNat * before.totalShares.toNat
  let rhs := before.totalAssets.toNat * after.totalShares.toNat
  decide (lhs >= rhs)

/-- Constant-Product AMM Swap (`amountIn` of X for Y with 30 bps fee, rounding output DOWN via `mulDivDown`). -/
def ammSwapXForY (pool : AmmPool) (amountInX : UInt256) : Option (AmmPool × UInt256) := do
  let feeScale : UInt256 := UInt256.ofUInt64 10000
  let netInX ← UInt256.mulDivDown amountInX (UInt256.ofUInt64 9970) feeScale
  let newReserveX ← UInt256.addChecked pool.reserveX netInX
  let amountOutY ← UInt256.mulDivDown pool.reserveY netInX newReserveX
  let fullReserveX ← UInt256.addChecked pool.reserveX amountInX
  let newReserveY ← UInt256.subChecked pool.reserveY amountOutY
  some ({ reserveX := fullReserveX, reserveY := newReserveY }, amountOutY)

/-- Constant-Product Invariant (`k_after >= k_before`). -/
def checkAmmConstantProductInvariant (before after : AmmPool) : Bool :=
  decide (after.reserveX.toNat * after.reserveY.toNat >= before.reserveX.toNat * before.reserveY.toNat)

/-- SplitMix64 PRNG step for deterministic FastCheck sweep. -/
@[inline]
def splitmix64 (state : UInt64) : UInt64 × UInt64 :=
  let s' := state + 0x9e3779b97f4a7c15
  let z1 := (s' ^^^ (s' >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  (z2 ^^^ (z2 >>> 31), s')

/-- Run 1,000 random & boundary swaps and vault transitions, verifying sound solvency and catching
    the reversed-rounding share-inflation bug via FastCheck. -/
def runVerityAmmVaultSuite (numTrials : Nat := 1000) : Bool × Nat × Option (Nat × UInt64 × UInt64 × UInt64) × UInt64 := Id.run do
  let mut rng : UInt64 := 0xCAFEBABE87654321
  let mut vault : VaultState := {
    totalAssets := UInt256.ofUInt64 1000000003,
    totalShares := UInt256.ofUInt64 1000000000
  }
  let mut pool : AmmPool := {
    reserveX := UInt256.wad,
    reserveY := UInt256.wad
  }
  let mut soundPassed : Nat := 0
  let mut allSoundOk : Bool := true
  let mut firstBuggyCex : Option (Nat × UInt64 × UInt64 × UInt64) := none
  let mut hashAcc : UInt64 := 14695981039346656037

  for trial in [0:numTrials] do
    let (r1, rng1) := splitmix64 rng
    let (r2, rng2) := splitmix64 rng1
    rng := rng2
    let amount : UInt256 :=
      if trial == 0 then UInt256.one
      else if trial == 1 then UInt256.ofUInt64 3
      else if trial == 2 then UInt256.ofUInt64 7
      else UInt256.ofUInt64 ((r1 % 50000000) + 1)

    -- 1. Check whether buggy reversed rounding violates vault solvency on current state
    if firstBuggyCex.isNone then
      match vaultDepositBuggyReversedRounding vault amount with
      | some (buggyAfter, mintedBuggy) =>
        if !checkVaultSolvencyInvariant vault buggyAfter then
          firstBuggyCex := some (trial, amount.lo0, mintedBuggy.lo0, vault.totalAssets.lo0)
      | none => pure ()

    -- 2. Execute sound ERC-4626 operation (deposit / mint / redeem)
    let opKind := r2 % 3
    let nextVaultOpt :=
      if opKind == 0 then
        vaultDepositSound vault amount
      else if opKind == 1 then
        vaultMintSound vault amount
      else
        let redeemAmt := UInt256.ofUInt64 ((amount.lo0 % (vault.totalShares.lo0 / 4 + 1)) + 1)
        vaultRedeemSound vault redeemAmt

    match nextVaultOpt with
    | some (nextVault, outVal) =>
      if checkVaultSolvencyInvariant vault nextVault then
        soundPassed := soundPassed + 1
        vault := nextVault
        hashAcc := (hashAcc ^^^ outVal.lo0) * 1099511628211
      else
        allSoundOk := false
    | none =>
      allSoundOk := false

    -- 3. Execute Constant-Product AMM swap and verify k_after >= k_before
    match ammSwapXForY pool amount with
    | some (nextPool, outY) =>
      if checkAmmConstantProductInvariant pool nextPool then
        pool := nextPool
        hashAcc := (hashAcc ^^^ outY.lo0) * 1099511628211
      else
        allSoundOk := false
    | none =>
      allSoundOk := false

  return (allSoundOk && soundPassed == numTrials && firstBuggyCex.isSome, soundPassed, firstBuggyCex, hashAcc)

end VerityAmmVault

open VerityAmmVault in
def main : IO UInt32 := do
  let (ok, passedCount, cexOpt, checksum) := runVerityAmmVaultSuite 1000
  IO.println "=== LeanNative v0.4 Showcase: EVM 256-Bit Constant-Product AMM & ERC-4626 Vault ==="
  IO.println s!"  Sound Vault + AMM Transitions Verified : {passedCount}/1000 (Solvency & Constant-Product k_after >= k_before)"
  match cexOpt with
  | some (trialIdx, assetsIn, sharesMinted, prevAssets) =>
    IO.println s!"  FastCheck Reversed-Rounding Falsifier  : CAUGHT at sample #{trialIdx} (assetsIn={assetsIn}, inflatedSharesMinted={sharesMinted}, prevTotalAssets={prevAssets})"
  | none =>
    IO.println "  FastCheck Reversed-Rounding Falsifier  : MISSED (unexpected)"
  IO.println s!"  Deterministic 64-Bit Checksum          : {checksum}"
  if ok then
    IO.println "[PASS] examples/verity_amm_vault.lean verified."
    return 0
  else
    IO.println "[FAIL] examples/verity_amm_vault.lean invariant check failed."
    return 1
