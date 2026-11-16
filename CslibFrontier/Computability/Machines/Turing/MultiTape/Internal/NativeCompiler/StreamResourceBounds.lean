/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamFold

/-!
# Resource bounds for retained streaming folds

This module bounds the actual time and workspace maps of `streamFoldPair` directly from the
construction formula. The time theorem charges every streamed occurrence and both callbacks; the
workspace theorem keeps the callback peak, encoded-value peak and fixed tape count separate.
Neither theorem selects a machine from an existential computability certificate.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.streamFoldPairTime_le`: a per-round time bound for
  the retained stream table.
* `Turing.MultiTapeTM.Internal.NativeCompiler.streamFoldPairWorkspace_le`: a peak workspace bound
  for the same table.

## References

These construction-derived bounds are original.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Encodings

/-- Bound the retained stream clock from uniform callback and encoded-value bounds. The
coefficients are the literal framing, callback lifting, round and finalization charges in
`streamFoldPairTime`. -/
theorem streamFoldPairTime_le
    {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon}
    {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF)
    (input : Sigma × List Alpha) (emitTime nextTime finishTime lengthBound : ℕ)
    (hinput : (encPair encS (encList encA) input).length ≤ lengthBound)
    (hstate : ∀ j, j ≤ input.2.length →
      (encS (streamState input.1 next input.2 j)).length ≤ lengthBound)
    (helem : ∀ j (hj : j < input.2.length),
      (encA input.2[j]).length ≤ lengthBound)
    (hemit : ∀ j (hj : j < input.2.length),
      emitCompiler.time (streamState input.1 next input.2 j, input.2[j]) ≤ emitTime)
    (hnext : ∀ j (hj : j < input.2.length),
      nextCompiler.time (streamState input.1 next input.2 j, input.2[j]) ≤ nextTime)
    (hfinish : finishCompiler.time
      (streamState input.1 next input.2 input.2.length) ≤ finishTime) :
    streamFoldPairTime nextCompiler emitCompiler finishCompiler input ≤
      input.2.length * (emitTime + nextTime + 46 * lengthBound + 60) +
        finishTime + 24 * lengthBound + 40 := by
  have hinitial : (encS input.1).length ≤ lengthBound := by
    simpa only [streamState_zero] using hstate 0 (Nat.zero_le _)
  have hfinal := hstate input.2.length le_rfl
  have hlist : (encList encA input.2).length ≤ lengthBound :=
    (length_le_encPair_right encS (encList encA) input).trans hinput
  have hcount : input.2.length ≤ lengthBound :=
    (length_le_length_encList encA input.2).trans hlist
  have hround : ∀ j ∈ Finset.range input.2.length,
      streamFoldPairRoundCost nextCompiler emitCompiler input j ≤
        emitTime + nextTime + 46 * lengthBound + 60 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hstateNow := hstate j hj'.le
    have hstateNext := hstate (j + 1) (by omega)
    have helemNow := helem j hj'
    have hemitNow := hemit j hj'
    have hnextNow := hnext j hj'
    simp only [streamFoldPairRoundCost, hj', dite_true, inputFromWordTime, onWordsTime,
      streamFramedNext, comp, encodeFrame, encBits_apply, length_frame]
    rw [← streamState_succ input.1 next input.2 hj']
    omega
  have hsum :
      (∑ j ∈ Finset.range input.2.length,
        streamFoldPairRoundCost nextCompiler emitCompiler input j) ≤
        input.2.length * (emitTime + nextTime + 46 * lengthBound + 60) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range input.2.length,
          (emitTime + nextTime + 46 * lengthBound + 60) := by
            exact Finset.sum_le_sum fun j hj => hround j hj
      _ = input.2.length * (emitTime + nextTime + 46 * lengthBound + 60) := by
            simp [Nat.mul_comm]
  simp only [streamFoldPairTime, streamUnframedFinish, comp, unframeValue,
    ofTransducer, inputFromWordTime, encFramed_apply, length_frame] at hfinish ⊢
  omega

/-- Bound the retained stream workspace from the actual peak callback workspace, peak encoded
state/element length and final callback workspace. `K` remains the exact fixed tape count of the
assembled stream table. -/
theorem streamFoldPairWorkspace_le
    {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon}
    {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF)
    (sMax lMax : Sigma × List Alpha → ℕ) (input : Sigma × List Alpha)
    (spaceBound lengthBound finishWorkspace : ℕ)
    (hsMax : sMax input ≤ spaceBound)
    (hlMax : lMax input ≤ lengthBound)
    (hinitial : (encS input.1).length ≤ lengthBound)
    (hfinal : (encS (streamState input.1 next input.2 input.2.length)).length ≤ lengthBound)
    (hfinish : finishCompiler.workspace
      (streamState input.1 next input.2 input.2.length) ≤ finishWorkspace) :
    let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
    streamFoldPairWorkspace nextCompiler emitCompiler finishCompiler sMax lMax input ≤
      2 * K * (spaceBound + 16 * lengthBound + 4 * K + 26) + finishWorkspace +
        13 * lengthBound + 8 * finishCompiler.tapeCount + 5 * K + 43 := by
  dsimp only
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  have hinner :
      sMax input + 16 * lMax input + 4 * K + 26 ≤
        spaceBound + 16 * lengthBound + 4 * K + 26 := by
    omega
  have hbulk := Nat.mul_le_mul_left (2 * K) hinner
  have hsub₁ : K - ((streamUnframedFinish finishCompiler).tapeCount + 2) ≤ K :=
    Nat.sub_le _ _
  have hsub₂ : K - 1 ≤ K := Nat.sub_le _ _
  simp only [streamFoldPairWorkspace, K, streamUnframedFinish, comp, unframeValue,
    ofTransducer, inputFromWordWorkspace, encFramed_apply, length_frame, Nat.max_eq_right]
    at hbulk hsub₁ hsub₂ hfinish ⊢
  omega

end Turing.MultiTapeTM.Internal.NativeCompiler
