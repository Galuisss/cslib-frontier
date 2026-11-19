/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.CompletedMeasurement
import CslibFrontier.Foundations.Quantum.Algebra.SequentialBinomial

/-! # An interior coordinate of a sequential projective measurement -/

set_option linter.privateModule false

open Cslib.Quantum Cslib.Quantum.Measurement
open scoped ComplexOrder BigOperators

private def instructions (j : Fin 3) : Cslib.Quantum.Measurement Bool ℂ :=
  const (j == 1)

private theorem projective (j : Fin 3) : (instructions j).IsProjective :=
  isProjective_const _

/-- In the sequence false, true, false, keeping just the middle outcome
gives the full effect for true. -/
example :
    (∑ g : Fin 3 → Bool, if g 1 = true then
      (sequentialProjective instructions projective).effect g else 0) = 1 := by
  rw [sequentialProjective_marginal]
  have h : (instructions 1).effect true = 1 := by simp [instructions, const]
  simp only [h, mul_one]
  exact sum_transcriptProduct_mul_star _ (fun _ => projective _)

/-- The complementary outcome at the same position has zero effect. -/
example :
    (∑ g : Fin 3 → Bool, if g 1 = false then
      (sequentialProjective instructions projective).effect g else 0) = 0 := by
  rw [sequentialProjective_marginal]
  have h : (instructions 1).effect false = 0 := by simp [instructions, const]
  simp [h]


private noncomputable def scalarState : AlgState ℂ where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  monotone' _ _ h := h
  map_one' := rfl

/-- A two-measurement prefix has zero average commutator defect in the scalar strategy.
The measured outcomes depend on the sampled questions. -/
example :
    (𝔼 x : Fin 3 → Fin 3,
      prefixCommutatorDefect scalarState (instructions ∘ x) (2 : Fin 3)) = 0 := by
  apply le_antisymm
  · have hp (x y : Fin 3) :
        pairCommutatorDefect scalarState (instructions x) (instructions y) = 0 :=
      pairCommutatorDefect_eq_zero _ _ _ fun _ _ => Commute.all _ _
    have h := average_prefixCommutatorDefect_le scalarState instructions instructions
      projective projective (fun _ _ _ _ => Commute.all _ _) (2 : Fin 3)
      (χ := 0) (ζ := 0) (by simp [hp]) (by simp)
    simpa using h
  · exact Finset.expect_nonneg fun _ _ => prefixCommutatorDefect_nonneg _ _ _


private def certainSuccess : Measurement (Option Bool) ℂ := const (some true)
private def certainFailure : Measurement (Option Bool) ℂ := const none

/-- The successful part contributes one unit of discrepancy, and the failure effect
contributes a second unit. The factor two in the completion bound is attained. -/
example : successfulCopyDefect scalarState certainSuccess certainFailure = 1 ∧
    copyDefect scalarState certainSuccess certainFailure = 2 := by
  unfold successfulCopyDefect copyDefect
  norm_num [certainSuccess, certainFailure, const, Fintype.sum_option, AlgState.norm_one,
    AlgState.norm_neg]


/-- Two independent scalar questions have exactly the binomial effect for at least one success. -/
example :
    (𝔼 x : Fin 2 → Fin 3, ∑ g with 1 ≤ transcriptSuccessCount id g,
      (scalarState ((sequentialProjective (instructions ∘ x) (fun j => projective (x j))).effect
        g)).re) =
      (scalarState (binomialAtLeast 2 1 (averageSuccessEffect instructions id))).re := by
  have hp (x y : Fin 3) :
      pairCommutatorDefect scalarState (instructions x) (instructions y) = 0 :=
    pairCommutatorDefect_eq_zero _ _ _ fun _ _ => Commute.all _ _
  have h := abs_sequentialSuccess_sub_binomialAtLeast_le scalarState instructions instructions
    projective projective (fun _ _ _ _ => Commute.all _ _) id 2 1
    (χ := 0) (ζ := 0) (by simp [hp]) (by simp)
  simp only [mul_zero, add_zero, Real.sqrt_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
