/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.FourierMeasurement
public import CslibFrontier.Foundations.Quantum.LocalOrthogonalization
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Order
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import CslibFrontier.Foundations.Quantum.Algebra.Expect

/-!
# Rounding approximately linear observables

Let `A(a)`, for `a ∈ {0,1}ⁿ`, be `±1` observables on `ℂ^ι` that are linear on average in a state
`φ`: `E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - δ`. Then there are observables `χ(a)` on the same
space that are unitary and **exactly linear**, `χ(a) χ(a') = χ(a + a')`, and close on average:
`E_a ‖A(a) - χ(a)‖²_φ ≤ 40δ` (`Cslib.Quantum.exists_isProjective_charObs_of_linear`). They are the
character observables of a projective measurement with outcomes in `{0,1}ⁿ`.

This is a **same-space variant with constant `40`** of
[Natarajan and Vidick, §3, Theorem 10][NatarajanVidick2017] (arXiv:1610.03574v1), not that theorem
itself. The source's conclusion is `E_a ‖A(a) - χ(a)‖² ≤ 2δ` in our normalization, for observables
on a dilated space `ℂ^ι ⊗ ℂ^{ι'}`: it dilates the Fourier measurement of `A`
(`Cslib.Quantum.fourierMeasurement`) to a projective measurement with an ancilla (Naimark). Here
the Fourier measurement, which is almost projective, is orthogonalized in place by de la Salle's
theorem, at the cost of the constant. So the rounded observables stay on `ℂ^ι`, and since the
estimate holds in every state, they stay on one party's factor in a tensor-product strategy
(`Cslib.Quantum.exists_isProjective_charObs_kroneckerOne_of_linear`).

The same-space construction extends to self-adjoint contractions with error `84δ`.
Their Fourier squares can have total mass below the identity. The proof keeps
the remaining effect as an extra outcome while orthogonalizing the measurement,
then merges it into the zero character.

## Main results

* `Cslib.Quantum.exists_isProjective_charObs_of_linear`: rounding to exactly linear unitaries.
* `Cslib.Quantum.exists_isProjective_charObs_of_linear_contractions`: rounding self-adjoint
  contractions on the original matrix space.
* `Cslib.Quantum.exists_isProjective_charObs_kroneckerOne_of_linear`: the same for one party of a
  tensor-product strategy.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
* [M. de la Salle, *Orthogonalization of positive operator valued measures*][delaSalle2022]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator

variable {ι κ n : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype n]
  [DecidableEq n]

/-- **Rounding approximately linear observables**, a same-space variant of
[Natarajan and Vidick, §3, Theorem 10][NatarajanVidick2017] with constant `40`. If the `±1`
observables `A(a)` on `ℂ^ι` satisfy `E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - δ`, then a projective
measurement `P` on `ℂ^ι` has unitary, exactly linear character observables with
`E_a ‖A(a) - χ_P(a)‖²_φ ≤ 40δ`. -/
theorem exists_isProjective_charObs_of_linear (φ : AlgState (Matrix ι ι ℂ))
    (A : (n → Bool) → Matrix ι ι ℂ) (hA : ∀ a, IsSelfAdjoint (A a)) (hA2 : ∀ a, A a * A a = 1)
    {δ : ℝ} (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm (A a - P.charObs a) ^ 2 ≤ 40 * δ := by
  set B := fourierMeasurement A hA hA2
  have hB : 1 - 2 * δ ≤ ∑ u, (φ (B.effect u * B.effect u)).re :=
    one_sub_le_sum_fourierMeasurement_sq hA hA2 φ hδ
  obtain ⟨P, hP, hU, hmul, hBP⟩ := Measurement.exists_isProjective_charObs φ B hB
  refine ⟨P, hP, hU, hmul, ?_⟩
  have hAB : 𝔼 a, φ.norm (A a - B.charObs a) ^ 2 ≤ 2 * δ :=
    expect_norm_sub_walshSum_sq_le hA hA2 φ hδ
  linarith only [φ.expect_norm_sub_sq_le_through univ A B.charObs P.charObs, hAB, hBP]

open Cslib.BitString in
/-- Near-linear self-adjoint contractions on a finite complex matrix space admit a
projective character measurement on the same space. The error is independent of
the number of bit strings and the matrix dimension. -/
theorem exists_isProjective_charObs_of_linear_contractions
    (φ : AlgState (Matrix ι ι ℂ)) (A : (n → Bool) → Matrix ι ι ℂ)
    (hA : ∀ a, IsSelfAdjoint (A a)) (hcontract : ∀ a, A a * A a ≤ 1)
    {δ : ℝ} (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm (A a - P.charObs a) ^ 2 ≤ 84 * δ := by
  classical
  let D (u : n → Bool) := fourierCoeff A u * fourierCoeff A u
  have hTotal : ∑ u, D u ≤ 1 := by
    dsimp only [D]
    rw [sum_fourierCoeff_mul_self_eq]
    have hscale : (((Fintype.card (n → Bool) : ℚ≥0)⁻¹ : ℚ≥0) : ℝ) =
        ((2 : ℝ) ^ Fintype.card n)⁻¹ := by
      rw [NNRat.cast_inv, Fintype.card_fun, Fintype.card_bool]
      push_cast
      rfl
    rw [← hscale, NNRat.cast_smul_eq_nnqsmul ℝ]
    change (𝔼 a, A a * A a) ≤ 1
    simpa only [Fintype.expect_const] using
      (expect_le_expect (s := (univ : Finset (n → Bool))) fun a _ => hcontract a)
  let B : Measurement (Option (n → Bool)) (Matrix ι ι ℂ) :=
    { effect := fun o => o.elim (1 - ∑ u, D u) D
      nonneg := fun o => by
        cases o with
        | none => exact sub_nonneg.mpr hTotal
        | some u => exact fourierCoeff_mul_self_nonneg hA u
      sum_effect := by
        rw [Fintype.sum_option]
        change 1 - (∑ u, D u) + (∑ u, D u) = 1
        exact sub_add_cancel _ _ }
  obtain ⟨hmass, hfourth⟩ := one_sub_le_fourierCoeff_moments_of_linear hA φ hTotal hδ
  have hB : 1 - 2 * δ ≤ ∑ o, (φ (B.effect o * B.effect o)).re := by
    rw [Fintype.sum_option]
    have hnone : 0 ≤ (φ (B.effect none * B.effect none)).re := by
      have h := star_mul_self_nonneg (B.effect none)
      rw [(B.nonneg none).isSelfAdjoint.star_eq] at h
      exact φ.re_apply_nonneg h
    change 1 - 2 * δ ≤ (φ (B.effect none * B.effect none)).re + ∑ u, (φ (D u * D u)).re
    exact hfourth.trans (le_add_of_nonneg_left hnone)
  obtain ⟨Q, hQ, hBQ⟩ := Measurement.exists_isProjective_sum_norm_sub_sq_le_of_le φ B hB
  let fill : Option (n → Bool) → (n → Bool) := fun o => o.getD 0
  let P := Q.map fill
  have hP : P.IsProjective := hQ.map fill
  refine ⟨P, hP, hP.charObs_mem_unitary, hP.charObs_mul, ?_⟩
  have hchar (M : Measurement (Option (n → Bool)) (Matrix ι ι ℂ)) (a : n → Bool) :
      (M.map fill).charObs a = walshSum (fun u => M.effect (some u)) a + M.effect none := by
    rw [Measurement.charObs_eq_observable_map, Measurement.map_map, Measurement.observable_map,
      Fintype.sum_option]
    simp only [fill, Function.comp_apply, Option.getD_none, Option.getD_some, dotProduct_zero,
      Bool.zero_eq_false, signVal_false, Complex.ofReal_one, one_smul, walshSum, add_comm]
  have hnone : φ.norm (B.effect none) ^ 2 ≤ δ := by
    rw [φ.norm_sq, (B.nonneg none).isSelfAdjoint.star_eq]
    refine (φ.re_apply_mono (mul_self_le_self_of_nonneg_of_le_one
      (B.nonneg none) (B.effect_le_one none))).trans ?_
    change (φ (1 - ∑ u, D u)).re ≤ δ
    rw [map_sub, AlgState.map_one, Complex.sub_re, Complex.one_re]
    linarith only [hmass]
  have hD := expect_norm_sub_walshSum_sq_le_of_contractions hA φ hcontract hTotal hδ
  have hAclose : 𝔼 a, φ.norm (A a - (B.map fill).charObs a) ^ 2 ≤ 6 * δ := by
    have h := φ.expect_norm_sub_sq_le_through univ A (walshSum D) (B.map fill).charObs
    have heq (a : n → Bool) :
        φ.norm (walshSum D a - (B.map fill).charObs a) = φ.norm (B.effect none) := by
      rw [hchar]
      change φ.norm (walshSum D a - (walshSum D a + B.effect none)) = _
      rw [sub_add_eq_sub_sub, sub_self, zero_sub, AlgState.norm_neg]
    simp only [heq, Fintype.expect_const] at h
    linarith only [h, hD, hnone]
  let E (u : n → Bool) := B.effect (some u) - Q.effect (some u)
  let remainder := B.effect none - Q.effect none
  have hPclose : 𝔼 a, φ.norm ((B.map fill).charObs a - P.charObs a) ^ 2 ≤ 36 * δ := by
    have heq (a : n → Bool) :
        (B.map fill).charObs a - P.charObs a = walshSum E a + remainder := by
      rw [hchar, hchar Q]
      change _ = walshSum ((fun u => B.effect (some u)) - fun u => Q.effect (some u)) a +
        remainder
      rw [← walshSum_sub]
      unfold remainder
      abel
    have hp (a : n → Bool) : φ.norm (walshSum E a + remainder) ^ 2 ≤
        2 * φ.norm (walshSum E a) ^ 2 + 2 * φ.norm remainder ^ 2 := by
      simpa only [add_sub_cancel_right, sub_zero] using
        φ.norm_sub_sq_le_through (walshSum E a + remainder) remainder 0
    simp only [heq]
    have h := expect_le_expect (s := (univ : Finset (n → Bool))) fun a _ => hp a
    rw [expect_add_distrib, ← mul_expect, Fintype.expect_const, expect_norm_walshSum_sq] at h
    rw [Fintype.sum_option] at hBQ
    change φ.norm remainder ^ 2 + ∑ u, φ.norm (E u) ^ 2 ≤ 9 * (2 * δ) at hBQ
    linarith only [h, hBQ]
  linarith only [φ.expect_norm_sub_sq_le_through univ A (B.map fill).charObs P.charObs,
    hAclose, hPclose]

/-- **Rounding for one party of a tensor-product strategy.** If the first party's `±1` observables
`A(a)` on `ℂ^ι` satisfy `E_{a,b} Re φ(A(a) A(b) A(a + b) ⊗ 1) ≥ 1 - δ` in the joint state `φ`,
then a projective measurement `P` on `ℂ^ι` has unitary, exactly linear character observables with
`E_a ‖(A(a) - χ_P(a)) ⊗ 1‖²_φ ≤ 40δ`. -/
theorem exists_isProjective_charObs_kroneckerOne_of_linear
    (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ)) (A : (n → Bool) → Matrix ι ι ℂ)
    (hA : ∀ a, IsSelfAdjoint (A a)) (hA2 : ∀ a, A a * A a = 1) {δ : ℝ}
    (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ ((A a * A b * A (a + b)) ⊗ₖ 1)).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm ((A a - P.charObs a) ⊗ₖ 1) ^ 2 ≤ 40 * δ := by
  obtain ⟨P, hP, hU, hmul, h⟩ := exists_isProjective_charObs_of_linear
    (φ.comap kroneckerOne (OrderHomClass.mono _)) A hA hA2 hδ
  refine ⟨P, hP, hU, hmul, ?_⟩
  simpa only [AlgState.norm_comap, kroneckerOne_apply] using h

end Cslib.Quantum
