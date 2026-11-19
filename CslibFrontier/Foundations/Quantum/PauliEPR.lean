/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
public import CslibFrontier.Foundations.Quantum.PauliTwirl
import CslibFrontier.Foundations.Quantum.Algebra.CharacterFamily
import CslibFrontier.Foundations.Quantum.Algebra.Expect
import CslibFrontier.Foundations.Quantum.DensityMatrix.Pure
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# EPR projection from paired Pauli strings

Averaging the same Pauli string on both halves gives the rank-one projection onto
the maximally entangled state. The phase average removes unequal bit strings and
the translation average makes all remaining diagonal amplitudes equal.

## Main definitions

* `Cslib.Quantum.extractedRegisterEmbedding`: place a two-register operator beside ancillas.
* `Cslib.Quantum.extractedEprProjection`: the EPR projector in player order.

## Main results

* `Cslib.Quantum.expect_pauliString_kronecker_self`: the paired Pauli projection.
* `Cslib.Quantum.norm_sub_eprProjector_sq_le`: disagreement on the two families bounds
  the squared weight outside the EPR subspace.
-/

public section

namespace Cslib.Quantum

open Matrix Finset BitString
open scoped BigOperators Kronecker MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform paired Pauli average is the projection onto the EPR vector on the
two extracted bit-string registers. -/
theorem expect_pauliString_kronecker_self :
    (𝔼 a : ι → Bool, 𝔼 b : ι → Bool, pauliString a b ⊗ₖ pauliString a b) =
      pureState (maxEntangled (ι → Bool)) := by
  have hcard : (Fintype.card (ι → Bool) : ℂ) = (2 : ℂ) ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_bool]
    push_cast
    rfl
  have hcard_ne : (Fintype.card (ι → Bool) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hscale :
      (((Real.sqrt (Fintype.card (ι → Bool)))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (Fintype.card (ι → Bool)))⁻¹ : ℝ) : ℂ) =
        (Fintype.card (ι → Bool) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast
    rfl
  ext ⟨x, x'⟩ ⟨y, y'⟩
  have hentry (a : ι → Bool) :
      (𝔼 b : ι → Bool, pauliString a b ⊗ₖ pauliString a b) (x, x') (y, y') =
        if y = y' ∧ y = x + a ∧ y' = x' + a then 1 else 0 := by
    simp only [Finset.expect, Matrix.smul_apply, Matrix.sum_apply, Matrix.kronecker_apply,
      pauliString_apply, ← NNRat.cast_smul_eq_nnqsmul ℂ, NNRat.cast_inv, NNRat.cast_natCast,
      Finset.card_univ, smul_eq_mul]
    by_cases hx : y = x + a <;> by_cases hx' : y' = x' + a
    · simp only [ite_eq_left hx, ite_eq_left hx']
      simp_rw [← Complex.ofReal_mul]
      rw [sum_signVal_mul_signVal, ← hcard]
      by_cases h : y = y'
      · rw [ite_eq_left h, ite_eq_left ⟨h, hx, hx'⟩, inv_mul_cancel₀ hcard_ne]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1), mul_zero]
    · simp [hx, hx']
    · simp [hx, hx']
    · simp [hx, hx']
  simp only [Finset.expect, Matrix.smul_apply, Matrix.sum_apply, ← NNRat.cast_smul_eq_nnqsmul ℂ,
    NNRat.cast_inv, NNRat.cast_natCast, Finset.card_univ, smul_eq_mul, pureState_apply,
    maxEntangled_apply] at hentry ⊢
  simp only [hentry]
  by_cases hy : y = y'
  · subst y'
    by_cases hx : x = x'
    · subst x'
      have hshift (a : ι → Bool) : y = x + a ↔ a = x + y := by
        constructor
        · intro h
          rw [h, BitString.add_cancel_left]
        · rintro rfl
          rw [BitString.add_cancel_left]
      simp only [true_and, and_self, hshift, sum_ite_eq', mem_univ, ite_true, mul_one,
        Complex.star_def, Complex.conj_ofReal, hscale]
    · have hfalse (a : ι → Bool) : ¬(y = x + a ∧ y = x' + a) := by
        rintro ⟨h, h'⟩
        exact hx (add_right_cancel (h.symm.trans h'))
      simp [hx, hfalse]
  · simp [hy]

private theorem norm_mul_sq_eq_of_star_mul_self
    (φ : AlgState (Matrix ((ι → Bool) × (ι → Bool)) ((ι → Bool) × (ι → Bool)) ℂ))
    {U : Matrix ((ι → Bool) × (ι → Bool)) ((ι → Bool) × (ι → Bool)) ℂ}
    (hU : star U * U = 1) (M : Matrix ((ι → Bool) × (ι → Bool)) ((ι → Bool) × (ι → Bool)) ℂ) :
    φ.norm (U * M) ^ 2 = φ.norm M ^ 2 := by
  rw [φ.norm_sq, φ.norm_sq, star_mul, ← mul_assoc (star M * star U),
    mul_assoc (star M), hU, mul_one]

private theorem norm_kronecker_self_sub_one_sq_eq
    (φ : AlgState (Matrix ((ι → Bool) × (ι → Bool)) ((ι → Bool) × (ι → Bool)) ℂ))
    (M : Matrix (ι → Bool) (ι → Bool) ℂ) (hM : IsSelfAdjoint M) (hM2 : M * M = 1) :
    φ.norm (M ⊗ₖ M - 1) ^ 2 =
      φ.norm (kroneckerOne (κ := ι → Bool) M - oneKronecker M) ^ 2 := by
  let X := kroneckerOne (κ := ι → Bool) M
  let Y := oneKronecker (ι := ι → Bool) M
  have hX : star X * X = 1 := by simp only [X, ← map_star, ← map_mul, hM.star_eq, hM2, map_one]
  have h : X * (X - Y) = 1 - M ⊗ₖ M := by
    have hx : X * X = 1 := by simp only [X, ← map_mul, hM2, map_one]
    rw [mul_sub, hx]
    simp only [X, Y, kroneckerOne_apply, oneKronecker_apply, ← mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul]
  rw [φ.norm_sub_comm (M ⊗ₖ M), ← h, norm_mul_sq_eq_of_star_mul_self φ hX]

/-- Agreement of the two ideal X and Z families controls the part of a state outside
the EPR projection. The state may be the restriction of a state with extra registers. -/
theorem norm_sub_eprProjector_sq_le
    (φ : AlgState (Matrix ((ι → Bool) × (ι → Bool)) ((ι → Bool) × (ι → Bool)) ℂ)) :
    φ.norm (pureState (maxEntangled (ι → Bool)) - 1) ^ 2 ≤
      2 * ((𝔼 a, φ.norm (kroneckerOne (pauliXPow a) - oneKronecker (pauliXPow a)) ^ 2) +
        (𝔼 b, φ.norm (kroneckerOne (pauliZPow b) - oneKronecker (pauliZPow b)) ^ 2)) := by
  rw [← expect_pauliString_kronecker_self]
  refine (φ.norm_expect_sub_sq_le univ univ_nonempty _ _).trans ?_
  have hJ (a : ι → Bool) := φ.norm_expect_sub_sq_le univ univ_nonempty
    (fun b => pauliString a b ⊗ₖ pauliString a b) 1
  refine (expect_le_expect fun a _ => hJ a).trans ?_
  have hpt (a b : ι → Bool) :
      φ.norm (pauliString a b ⊗ₖ pauliString a b - 1) ^ 2 ≤
        2 * φ.norm (kroneckerOne (pauliXPow a) - oneKronecker (pauliXPow a)) ^ 2 +
        2 * φ.norm (kroneckerOne (pauliZPow b) - oneKronecker (pauliZPow b)) ^ 2 := by
    let U := pauliXPow a ⊗ₖ pauliXPow a
    let V := pauliZPow b ⊗ₖ pauliZPow b
    have hU : star U * U = 1 := by
      simp only [U, Matrix.star_eq_conjTranspose, conjTranspose_kronecker,
        (pauliXPow_isHermitian a).eq, ← mul_kronecker_mul, pauliXPow_mul_self, one_kronecker_one]
    have hUV : pauliString a b ⊗ₖ pauliString a b = U * V := by
      rw [← mul_kronecker_mul]
      rw [pauliString]
    have hdiff : U * V - U = U * (V - 1) := by rw [mul_sub, mul_one]
    have h := φ.norm_sub_sq_le_through (U * V) U 1
    rw [hdiff, norm_mul_sq_eq_of_star_mul_self φ hU] at h
    rw [hUV]
    change _ ≤ _ at h
    rw [show V = pauliZPow b ⊗ₖ pauliZPow b from rfl,
      show U = pauliXPow a ⊗ₖ pauliXPow a from rfl,
      norm_kronecker_self_sub_one_sq_eq φ _ (pauliZPow_isHermitian b).isSelfAdjoint
        (pauliZPow_mul_self b),
      norm_kronecker_self_sub_one_sq_eq φ _ (pauliXPow_isHermitian a).isSelfAdjoint
        (pauliXPow_mul_self a), add_comm] at h
    exact h
  have h := expect_le_expect (s := (univ : Finset (ι → Bool))) fun a _ =>
    expect_le_expect (s := (univ : Finset (ι → Bool))) fun b _ => hpt a b
  simp only [expect_add_distrib, Fintype.expect_const, ← mul_expect] at h
  linarith only [h]


section Projection

variable {Q J K : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

/-- Place an operator on the extracted registers, with identities on both ancillas.
The target basis keeps each register beside its player's ancilla. -/
noncomputable def extractedRegisterEmbedding :
    Matrix (Q × Q) (Q × Q) ℂ →⋆ₐ[ℂ] Matrix ((Q × J) × Q × K) ((Q × J) × Q × K) ℂ :=
  (reindexStarAlgEquiv ℂ ℂ (Equiv.prodProdProdComm Q J Q K).symm).toStarAlgHom.comp
    (kroneckerOne (κ := J × K))

/-- A first-side register operator remains on the first side after placing the ancillas. -/
theorem extractedRegisterEmbedding_left (A : Matrix Q Q ℂ) :
    extractedRegisterEmbedding (J := J) (K := K) (kroneckerOne A) =
      kroneckerOne (κ := Q × K) (A ⊗ₖ (1 : Matrix J J ℂ)) := by
  ext ⟨⟨i, j⟩, k, l⟩ ⟨⟨i', j'⟩, k', l'⟩
  change (A i i' * (1 : Matrix Q Q ℂ) k k') * (1 : Matrix (J × K) (J × K) ℂ)
      (j, l) (j', l') =
    (A i i' * (1 : Matrix J J ℂ) j j') * (1 : Matrix (Q × K) (Q × K) ℂ) (k, l) (k', l')
  rw [← one_kronecker_one, ← one_kronecker_one]
  simp only [kronecker_apply]
  ring

/-- A second-side register operator remains on the second side after placing the ancillas. -/
theorem extractedRegisterEmbedding_right (A : Matrix Q Q ℂ) :
    extractedRegisterEmbedding (J := J) (K := K) (oneKronecker A) =
      oneKronecker (ι := Q × J) (A ⊗ₖ (1 : Matrix K K ℂ)) := by
  ext ⟨⟨i, j⟩, k, l⟩ ⟨⟨i', j'⟩, k', l'⟩
  change ((1 : Matrix Q Q ℂ) i i' * A k k') * (1 : Matrix (J × K) (J × K) ℂ)
      (j, l) (j', l') =
    (1 : Matrix (Q × J) (Q × J) ℂ) (i, j) (i', j') * (A k k' * (1 : Matrix K K ℂ) l l')
  rw [← one_kronecker_one, ← one_kronecker_one]
  simp only [kronecker_apply]
  ring

/-- Projection onto the EPR state on the two extracted registers, with the
identity on both ancillary registers. The registers are in player order. -/
@[expose] noncomputable def extractedEprProjection :
    Matrix ((Q × J) × Q × K) ((Q × J) × Q × K) ℂ :=
  extractedRegisterEmbedding (J := J) (K := K) (pureState (maxEntangled Q))


/-- Regrouping the extracted registers puts the pure EPR projector before both ancillas. -/
theorem reindex_extractedEprProjection :
    let e := Equiv.prodProdProdComm Q J Q K
    reindex e e (extractedEprProjection (Q := Q) (J := J) (K := K)) =
      pureState (maxEntangled Q) ⊗ₖ (1 : Matrix (J × K) (J × K) ℂ) := by
  intro e
  ext p q
  change (pureState (maxEntangled Q) ⊗ₖ (1 : Matrix (J × K) (J × K) ℂ))
    (e (e.symm p)) (e (e.symm q)) = _
  rw [e.apply_symm_apply, e.apply_symm_apply]

/-- The extracted EPR projection is self-adjoint. -/
theorem isHermitian_extractedEprProjection :
    (extractedEprProjection (Q := Q) (J := J) (K := K)).IsHermitian := by
  rw [IsHermitian, ← Matrix.star_eq_conjTranspose, extractedEprProjection, ← map_star,
    Matrix.star_eq_conjTranspose, (posSemidef_pureState (maxEntangled Q)).isHermitian.eq]

/-- The extracted EPR projection is idempotent. -/
theorem extractedEprProjection_mul_self [Nonempty Q] :
    extractedEprProjection (Q := Q) (J := J) (K := K) * extractedEprProjection =
      extractedEprProjection := by
  rw [extractedEprProjection, ← map_mul, pureState_mul_self_of_norm_eq_one _ norm_maxEntangled]


end Projection

end Cslib.Quantum
