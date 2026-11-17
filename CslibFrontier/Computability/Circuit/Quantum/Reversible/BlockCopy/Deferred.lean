/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Reversible.BlockCopy
public import CslibFrontier.Computability.Circuit.Quantum.Parallel
public import CslibFrontier.Foundations.Quantum.Measurement.Deferred

/-!
# Deferred readout from a reversible block copy

A disjoint CNOT block copy into zero target qubits is the physical-register realization of the
existing `coherentRecord` isometry.  Splitting the target block from the rest of the register
turns the copied source value into the first factor and retains every other qubit exactly.

This matrix identity is the register-layout bridge used by the query-free classical-interaction
controller.  Applying `densityConj` and the existing double-record partial-trace theorem therefore
preserves arbitrary mixed inputs and inaccessible references; no diagonal-input hypothesis is
needed.

## Main results

* `Cslib.Quantum.Circuit.matrix_blockCopyCodes_zeroTarget`: a physical CNOT copy into a zero
  target is exactly `coherentRecord` after the target-register split.
-/

public section

namespace Cslib.Quantum.Circuit

open Matrix GateCode

/-- **A zero-target block copy is a coherent classical record.**  The target block is split out
as the first factor.  The recorded label reads the source block from the uniquely reconstructed
zero-target input, so callers supply no complement embedding or semantic premise.

The equality is between rectangular matrices: columns are states of all non-target qubits, while
rows are the copied target label together with those same qubits.  It therefore rewrites directly
under `densityConj`, including after tensoring both sides with an inaccessible reference. -/
theorem matrix_blockCopyCodes_zeroTarget {source target count width : ℕ}
    (hdisjoint : source + count ≤ target ∨ target + count ≤ source)
    (hsource : source + count ≤ width) (htarget : target + count ≤ width) :
    let targetEmbedding := blockEmb target htarget
    let Rest := {j : Fin width // ¬ ∃ i, targetEmbedding i = j}
    let sourceLabel : (Rest → Bool) → Fin count → Bool :=
      fun rest i =>
        (splitEquiv targetEmbedding).symm (fun _ => false, rest)
          ⟨source + i, by omega⟩
    ((matrix (ofCodes width (blockCopyCodes source target count)) : Matrix _ _ ℂ)).submatrix
        (fun p => (splitEquiv targetEmbedding).symm p)
        (fun rest => (splitEquiv targetEmbedding).symm (fun _ => false, rest)) =
      coherentRecord sourceLabel := by
  classical
  dsimp only
  let targetEmbedding := blockEmb target htarget
  let sourceLabel := fun rest :
      ({j : Fin width // ¬ ∃ i, targetEmbedding i = j} → Bool) =>
    fun i : Fin count =>
      (splitEquiv targetEmbedding).symm (fun _ => false, rest)
        ⟨source + i, by omega⟩
  have hclass : IsClassical width (blockCopyCodes source target count) :=
    isClassical_blockCopyCodes hdisjoint hsource htarget
  have hrunSplit (rest : {j : Fin width // ¬ ∃ i, targetEmbedding i = j} → Bool) :
      splitEquiv targetEmbedding
          (classicalRun (blockCopyCodes source target count)
            ((splitEquiv targetEmbedding).symm (fun _ => false, rest))) =
        (sourceLabel rest, rest) := by
    rw [classicalRun_blockCopyCodes_zeroTarget hdisjoint hsource htarget _
      (fun i => splitEquiv_symm_apply_wire _ _ _ i)]
    apply Prod.ext
    · funext i
      rw [splitEquiv_apply_fst]
      simp only [Function.comp_apply, targetEmbedding, glue_apply_emb]
      exact readBit_of_lt _ (c := source + i) (by omega)
    · funext j
      rw [splitEquiv_apply_snd]
      dsimp only
      rw [glue_of_not _ _ _ (not_exists.mp j.2), splitEquiv_symm_apply_of_not]
  ext ⟨label, restOut⟩ restIn
  change (matrix (ofCodes width (blockCopyCodes source target count)) : Matrix _ _ ℂ)
      ((splitEquiv targetEmbedding).symm (label, restOut))
      ((splitEquiv targetEmbedding).symm (fun _ => false, restIn)) =
    coherentRecord sourceLabel (label, restOut) restIn
  rw [← eval_ket_apply, eval_ofCodes_ket hclass]
  simp only [ket_apply, coherentRecord]
  have heq :
      (splitEquiv targetEmbedding).symm (label, restOut) =
          classicalRun (blockCopyCodes source target count)
            ((splitEquiv targetEmbedding).symm (fun _ => false, restIn)) ↔
        (label, restOut) = (sourceLabel restIn, restIn) := by
    constructor
    · intro h
      have hs := congrArg (splitEquiv targetEmbedding) h
      rw [hrunSplit] at hs
      simpa only [Equiv.apply_symm_apply] using hs
    · intro h
      apply (splitEquiv targetEmbedding).injective
      rw [hrunSplit]
      simpa only [Equiv.apply_symm_apply] using h
  rw [if_congr heq rfl rfl]

end Cslib.Quantum.Circuit
