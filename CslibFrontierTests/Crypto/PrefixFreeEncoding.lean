/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Primitives.BlockCipher.LengthPrependedCBCMAC
public import CslibFrontier.Crypto.Primitives.PRF.PrefixFreeEncoding

/-!
# Tests for Deterministic Prefix-Free Encodings

Concrete evaluations, client applications, empty-message counterexample, and axiom checks for
`CslibFrontier.Crypto.PRF.IsPrefixFreeEncoding`, `stopBitEncode`, and
`isPrefixFreeEncoding_prependLength`.
-/

public section

namespace CslibFrontierTests.Crypto.PrefixFreeEncoding

open Cslib Cslib.Crypto Cslib.Crypto.PRF

private def blk01 : BitString 2 := fun i => decide (i.1 = 1)
private def blk10 : BitString 2 := fun i => decide (i.1 = 0)

/-- Concrete `decide` evaluation of `stopBitEncode` on two 2-bit blocks, showing stop bit `false`
on the first block, stop bit `true` on the second block, and no prefix collision with `[blk01]`. -/
example :
    stopBitEncode [blk01, blk10] =
      [Fin.snoc (α := fun _ => Bool) blk01 false, Fin.snoc (α := fun _ => Bool) blk10 true] ∧
    ¬ (stopBitEncode [blk01] <+: stopBitEncode [blk01, blk10]) := by
  decide

/-- Counterexample: `stopBitEncode` on unrestricted `List (BitString n)` fails
`IsPrefixFreeEncoding` because `stopBitEncode [] = []`. -/
theorem not_isPrefixFreeEncoding_stopBitEncode_list (n : ℕ) :
    ¬ IsPrefixFreeEncoding (stopBitEncode (n := n)) :=
  fun h => h.ne_nil [] rfl

/-- Bounded-domain corollary via `IsPrefixFreeEncoding.comp_injective` together with the length
bound `length_stopBitEncode`. -/
example (n ℓ : ℕ) :
    IsPrefixFreeEncoding
      (fun m : {m : List (BitString n) // m ≠ [] ∧ m.length ≤ ℓ} => stopBitEncode m.1) ∧
    ∀ m : {m : List (BitString n) // m ≠ [] ∧ m.length ≤ ℓ},
      (stopBitEncode m.1).length ≤ ℓ := by
  refine ⟨(isPrefixFreeEncoding_stopBitEncode n).comp_injective
      (e := fun m : {m : List (BitString n) // m ≠ [] ∧ m.length ≤ ℓ} => ⟨m.1, m.2.1⟩)
      fun _ _ h =>
        Subtype.ext (congrArg (fun x : {m : List (BitString n) // m ≠ []} => x.1) h),
    fun m => by rw [length_stopBitEncode]; exact m.2.2⟩

/-- Method 1 (`isPrefixFreeEncoding_prependLength`) instantiated with `blockCountBlock`
(`3 < 2 ^ 8`). -/
example :
    IsPrefixFreeEncoding
      (fun x : LengthPrependedInput 8 3 =>
        cbcInputBlocks (prependLength (blockCountBlock (n := 8) (L := 3) (by decide)) x)) :=
  isPrefixFreeEncoding_prependLength (blockCountBlock_injective (n := 8) (L := 3) (by decide))

/-- `blockCountBlock`-prepended messages satisfy the `iff_forall_prefix` characterization. -/
example (x y : LengthPrependedInput 8 3)
    (hpre : cbcInputBlocks (prependLength (blockCountBlock (n := 8) (L := 3) (by decide)) x) <+:
      cbcInputBlocks (prependLength (blockCountBlock (n := 8) (L := 3) (by decide)) y)) :
    x = y :=
  (IsPrefixFreeEncoding.iff_forall_prefix.mp
    (isPrefixFreeEncoding_prependLength
      (blockCountBlock_injective (n := 8) (L := 3) (by decide)))).2 x y hpre

/-- info: 'Cslib.Crypto.PRF.isPrefixFreeEncoding_stopBitEncode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isPrefixFreeEncoding_stopBitEncode

/-- info: 'Cslib.Crypto.isPrefixFreeEncoding_prependLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isPrefixFreeEncoding_prependLength

end CslibFrontierTests.Crypto.PrefixFreeEncoding
