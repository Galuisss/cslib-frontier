/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingGame

/-!
# Diagonal linearity seeds in the Pauli braiding game

Conditioning the linearity branch on equal strings in the original pair, a fixed
basis and a fixed role assignment retains a fraction `1 / (4 * 2^n)` of the seeds.
The remaining choices are the common string, the other player's dummy, and the check.
This isolates the probability cost of using these rounds to analyze the zero string.

## Main definitions

* `Cslib.PCP.pauliBraidingDiagonalGame`: the conditioned linearity verifier.

## Main results

* `Cslib.PCP.rejection_pauliBraidingDiagonalGame_le`: transfer of the rejection budget.
-/

public section

namespace Cslib.PCP

variable {n : ℕ} [Nonempty (Fin n)] {Q A : Type*}

/-- Fix the roles and keep exactly the seeds at which the original two strings coincide. -/
@[expose] def SymmetricLinearitySeed.diagonal (n : ℕ) (roles : Bool) :
    (Fin 3 × (Fin n → Bool) × (Fin n → Bool)) ↪ SymmetricLinearitySeed n where
  toFun := fun (k, a, dummy) => ⟨roles, k, a, a, dummy⟩
  inj' := by
    rintro ⟨k, a, d⟩ ⟨k', a', d'⟩ h
    cases h
    rfl

/-- The symmetric linearity round with a fixed basis and role assignment and equal original
strings. The check, common string and dummy remain independent and uniform. -/
@[expose] noncomputable def pauliBraidingDiagonalGame (n : ℕ) [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool) :
    SeededGame (Fin 3 × (Fin n → Bool) × (Fin n → Bool))
      (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) :=
  (pauliBraidingGame n G special decode).pullbackSeed (Probability.PMF.uniformOfFintype _)
    fun r => .linearity basis (SymmetricLinearitySeed.diagonal n roles r)

/-- For a fixed role and basis, the diagonal round's rejection contributes its actual
sampling mass to the rejection probability of the linearity branch. -/
theorem rejection_pauliBraidingDiagonalGame_le
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (answer : PauliBraidingQuestion n Q → PauliBraidingQuestion n Q →
      PMF (((Bool × Bool) ⊕ A) × ((Bool × Bool) ⊕ A))) :
    (1 - (pauliBraidingDiagonalGame n G special decode roles basis).answersWinProb answer) /
        (4 * Fintype.card (Fin n → Bool)) ≤
      1 - (pauliBraidingBranchGame n G special decode 0).answersWinProb answer := by
  let game := pauliBraidingGame n G special decode
  let seedLaw := Probability.PMF.uniformOfFintype (SymmetricLinearitySeed n)
  let fixedBasis := game.pullbackSeed seedLaw (PauliBraidingSeed.linearity basis)
  let diagonal := pauliBraidingDiagonalGame n G special decode roles basis
  let linearity := pauliBraidingBranchGame n G special decode 0
  have hbasis := game.weighted_rejection_le_of_bind_seed (Probability.PMF.uniformOfFintype Bool)
    (fun basis => seedLaw.map (PauliBraidingSeed.linearity basis)) answer basis
  have hmass : ((Probability.PMF.uniformOfFintype Bool) basis).toReal = (2 : ℝ)⁻¹ := by
    rw [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
    norm_num
  rw [hmass, ← game.answersWinProb_pullbackSeed seedLaw (PauliBraidingSeed.linearity basis) answer]
    at hbasis
  change (2 : ℝ)⁻¹ * (1 - fixedBasis.answersWinProb answer) ≤
    1 - linearity.answersWinProb answer at hbasis
  have hdiag := fixedBasis.weighted_rejection_pullback_uniform_le
    (SymmetricLinearitySeed.diagonal n roles) answer
  let size : ℝ := Fintype.card (Fin n → Bool)
  have hsize : size ≠ 0 := by
    dsimp [size]
    exact_mod_cast Fintype.card_ne_zero
  have hcard :
      (Fintype.card (Fin 3 × (Fin n → Bool) × (Fin n → Bool)) : ℝ) /
        Fintype.card (SymmetricLinearitySeed n) = (2 * size)⁻¹ := by
    rw [Fintype.card_congr (SymmetricLinearitySeed.equivProd n)]
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    change 3 * (size * size) / (2 * (3 * (size * (size * size)))) = _
    field_simp
  rw [hcard] at hdiag
  change (2 * size)⁻¹ * (1 - diagonal.answersWinProb answer) ≤
    1 - fixedBasis.answersWinProb answer at hdiag
  have h := (mul_le_mul_of_nonneg_left hdiag (by norm_num : 0 ≤ (2 : ℝ)⁻¹)).trans hbasis
  change (1 - diagonal.answersWinProb answer) / (4 * size) ≤ 1 - linearity.answersWinProb answer
  convert h using 1
  rw [div_eq_mul_inv, ← mul_assoc, ← mul_inv]
  ring

end Cslib.PCP
