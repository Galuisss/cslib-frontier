/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# State-dependent bounds for measurement distributions

Inserting all effects of a measurement between two families of operators gives a sum of
matrix coefficients bounded by the product of the families' state norms. In particular,
the bound has no factor for the number of outcomes of the inserted measurement.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset

variable {A α β : Type*} [Fintype α] [Fintype β] [Ring A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A] [SelfAdjointDecompose A]
  [TopologicalSpace A] [T2Space A] [IsSemitopologicalRing A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- Cauchy–Schwarz for a sum of coefficients weighted by the effects of a measurement. -/
theorem sum_abs_re_apply_star_mul_effect_mul_le (φ : AlgState A) (M : Measurement β A)
    (u v : α → A) :
    (∑ a, ∑ b, |(φ (star (u a) * M.effect b * v a)).re|) ≤
      √(∑ a, φ.norm (u a) ^ 2) * √(∑ a, φ.norm (v a) ^ 2) := by
  let R (b : β) := CFC.sqrt (M.effect b)
  have hR (b : β) : star (R b) * R b = M.effect b := by
    rw [(CFC.sqrt_nonneg (M.effect b)).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (M.nonneg b)
  have hnorm (w : α → A) :
      (∑ p : α × β, φ.norm (R p.2 * w p.1) ^ 2) = ∑ a, φ.norm (w a) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    have heq (b : β) :
        star (R b * w a) * (R b * w a) = star (w a) * (M.effect b * w a) := by
      rw [star_mul, mul_assoc, ← mul_assoc (star (R b)), hR]
    simp only [AlgState.norm_sq, heq]
    rw [← Complex.re_sum, ← map_sum, ← mul_sum, ← sum_mul, M.sum_effect, one_mul]
  rw [← Fintype.sum_prod_type fun p : α × β => |(φ (star (u p.1) * M.effect p.2 * v p.1)).re|]
  calc
    _ ≤ ∑ p : α × β, φ.norm (R p.2 * u p.1) * φ.norm (R p.2 * v p.1) := by
      refine sum_le_sum fun ⟨a, b⟩ _ => ?_
      have hcoeff : star (R b * u a) * (R b * v a) = star (u a) * M.effect b * v a := by
        rw [star_mul, mul_assoc, ← mul_assoc (star (R b)), hR, mul_assoc]
      rw [← hcoeff]
      exact (Complex.abs_re_le_norm _).trans (φ.norm_apply_star_mul_le _ _)
    _ ≤ _ := by
      rw [← hnorm u, ← hnorm v]
      exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- Replacing the operators on both sides of a measurement changes the resulting weights
by at most the state-norm distance of the replacement times the sum of the two norms. -/
theorem sum_abs_re_apply_conjugation_sub_le (φ : AlgState A) (M : Measurement β A)
    (u v : α → A) :
    (∑ a, ∑ b, |(φ (star (u a) * M.effect b * u a)).re -
        (φ (star (v a) * M.effect b * v a)).re|) ≤
      √(∑ a, φ.norm (u a - v a) ^ 2) *
        (√(∑ a, φ.norm (u a) ^ 2) + √(∑ a, φ.norm (v a) ^ 2)) := by
  let w : α → A := fun a => u a - v a
  have hdiff (a : α) (b : β) :
      (φ (star (u a) * M.effect b * u a)).re - (φ (star (v a) * M.effect b * v a)).re =
        (φ (star (u a) * M.effect b * w a)).re +
          (φ (star (w a) * M.effect b * v a)).re := by
    rw [← Complex.sub_re, ← Complex.add_re, ← map_sub, ← map_add]
    congr 2
    simp only [w, star_sub]
    noncomm_ring
  simp_rw [hdiff]
  change _ ≤ √(∑ a, φ.norm (w a) ^ 2) *
    (√(∑ a, φ.norm (u a) ^ 2) + √(∑ a, φ.norm (v a) ^ 2))
  calc
    _ ≤ ∑ a, ∑ b, (|(φ (star (u a) * M.effect b * w a)).re| +
          |(φ (star (w a) * M.effect b * v a)).re|) :=
      sum_le_sum fun a _ => sum_le_sum fun b _ => abs_add_le _ _
    _ ≤ _ := by
      simp only [sum_add_distrib, mul_add,
        mul_comm (√(∑ a, φ.norm (w a) ^ 2)) (√(∑ a, φ.norm (u a) ^ 2))]
      exact add_le_add (M.sum_abs_re_apply_star_mul_effect_mul_le φ u w)
        (M.sum_abs_re_apply_star_mul_effect_mul_le φ w v)

omit [T2Space A] [IsSemitopologicalRing A] in
private theorem sum_effect_norm_sq_le_one (φ : AlgState A) (P : Measurement α A) :
    (∑ a, φ.norm (P.effect a) ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ a, (φ (P.effect a)).re := by
      refine sum_le_sum fun a _ => φ.norm_sq_le_of_star_mul_le ?_
      rw [(P.nonneg a).isSelfAdjoint.star_eq]
      exact P.effect_mul_self_le a
    _ = 1 := by rw [← Complex.re_sum, ← map_sum, P.sum_effect, φ.map_one, Complex.one_re]

/-- Replacing one measurement inside a quadratic expression changes its weights by at
most twice the state-dependent distance between the two families of effects. -/
theorem sum_abs_re_apply_effect_conjugation_sub_le (φ : AlgState A) (M : Measurement β A)
    (P Q : Measurement α A) :
    (∑ a, ∑ b, |(φ (P.effect a * M.effect b * P.effect a)).re -
        (φ (Q.effect a * M.effect b * Q.effect a)).re|) ≤
      2 * √(∑ a, φ.norm (P.effect a - Q.effect a) ^ 2) := by
  have h := M.sum_abs_re_apply_conjugation_sub_le φ P.effect Q.effect
  have hP (a : α) := (P.nonneg a).isSelfAdjoint.star_eq
  have hQ (a : α) := (Q.nonneg a).isSelfAdjoint.star_eq
  simp_rw [hP, hQ] at h
  refine h.trans ?_
  rw [mul_comm 2]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  simpa only [Real.sqrt_one, one_add_one_eq_two] using add_le_add
    (Real.sqrt_le_sqrt (sum_effect_norm_sq_le_one φ P))
    (Real.sqrt_le_sqrt (sum_effect_norm_sq_le_one φ Q))

/-- A projective measurement commuting with `M` can be moved to the same side as `M`
with an error controlled by its distance from the replacement. -/
theorem sum_abs_re_apply_effect_mul_sub_conjugation_le (φ : AlgState A)
    (M : Measurement β A) (P Q : Measurement α A) (hP : P.IsProjective)
    (hcomm : ∀ a b, Commute (P.effect a) (M.effect b)) :
    (∑ a, ∑ b, |(φ (P.effect a * M.effect b)).re -
        (φ (Q.effect a * M.effect b * Q.effect a)).re|) ≤
      2 * √(∑ a, φ.norm (P.effect a - Q.effect a) ^ 2) := by
  have h (a : α) (b : β) :
      P.effect a * M.effect b * P.effect a = P.effect a * M.effect b := by
    rw [mul_assoc, (hcomm a b).symm.eq, ← mul_assoc, hP a]
  simpa only [h] using M.sum_abs_re_apply_effect_conjugation_sub_le φ P Q

end Cslib.Quantum.Measurement
