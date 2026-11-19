/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.Pasting
import Mathlib.Algebra.Field.ZMod

/-! # Pasting on three slices over the field with three elements -/

set_option linter.privateModule false

open Cslib.PCP.LowIndividualDegree MvPolynomial

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev F := ZMod 3

private def nodes : Fin 3 ↪ F := (ZMod.finEquiv 3).toEquiv.toEmbedding

private noncomputable def zeroSlice : BoundedPolynomial F 1 1 := ⟨0, by simp⟩

private noncomputable def linearSlice : BoundedPolynomial F 1 1 := ⟨X 0, by
  intro i
  simp [Subsingleton.elim i 0]⟩

private noncomputable def productPoly : BoundedPolynomial F 2 1 :=
  ⟨X (Fin.last 1) * X (Fin.castSucc (0 : Fin 1)), fun i => by
    apply (degreeOf_mul_le _ _ _).trans
    fin_cases i <;> simp [degreeOf_X]⟩

private noncomputable def partialSlices (i : Fin 3) : Option (BoundedPolynomial F 1 1) :=
  if i = 0 then some zeroSlice else if i = 1 then some linearSlice else none

/-- Two compatible slices and one failure recover the bivariate product. -/
example : pasteOutcome nodes partialSlices = some productPoly := by
  apply (pasteOutcome_eq_some_iff _ _ _).mpr
  constructor
  · have hs : successfulSlices partialSlices = {0, 1} := by
      ext i
      fin_cases i <;> simp [partialSlices]
    rw [hs]
    decide
  · unfold FitsSlices
    intro i q h
    fin_cases i
    · have hq : q = zeroSlice := by simpa [partialSlices, eq_comm] using h
      subst q
      apply Subtype.ext
      change specializeLast (0 : F) productPoly.val = _
      change specializeLast (0 : F) (X (Fin.last 1) * X (Fin.castSucc (0 : Fin 1))) = 0
      rw [map_mul, specializeLast_X_last, specializeLast_X_castSucc, map_zero, zero_mul]
    · have hq : q = linearSlice := by simpa [partialSlices, eq_comm] using h
      subst q
      apply Subtype.ext
      change specializeLast (1 : F) productPoly.val = _
      change specializeLast (1 : F) (X (Fin.last 1) * X (Fin.castSucc (0 : Fin 1))) = X 0
      rw [map_mul, specializeLast_X_last, specializeLast_X_castSucc, map_one, one_mul]
    · simp [partialSlices] at h

private noncomputable def inconsistentSlices (i : Fin 3) :
    Option (BoundedPolynomial F 1 1) :=
  if i = 2 then some linearSlice else some zeroSlice

/-- Once two zero slices force the zero polynomial, an incompatible third slice fails. -/
example : pasteOutcome nodes inconsistentSlices = none := by
  cases h : pasteOutcome nodes inconsistentSlices with
  | none => rfl
  | some p =>
    exfalso
    have hf := (pasteOutcome_eq_some_iff _ _ _).mp h
    have hzero : p.val = 0 := by
      apply eq_of_specializeLast_eq (s := ({0, 1} : Finset (Fin 3))) nodes.injective.injOn
      · exact (p.prop (Fin.last 1)).trans_lt (by decide)
      · simp
      · intro j hj
        have hne : j ≠ 2 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl <;> decide
        have hv := hf.2 j zeroSlice (by simp [inconsistentSlices, hne])
        change specializeLast (nodes j) p.val = specializeLast (nodes j) (0 : MvPolynomial _ _)
        rw [map_zero]
        exact congrArg Subtype.val hv
    have hv := hf.2 (2 : Fin 3) linearSlice (by simp [inconsistentSlices])
    have hv' : specializeLast (nodes (2 : Fin 3)) p.val = X 0 := congrArg Subtype.val hv
    rw [hzero, map_zero] at hv'
    exact (X_ne_zero (R := F) (0 : Fin 1)) hv'.symm
