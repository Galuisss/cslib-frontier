/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LinearityDiagonal
public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingGame
import CslibFrontier.Foundations.Data.Finset.Expect

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

open scoped BigOperators

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

/-- The visible question for zero with a dummy in one of the two bases. -/
@[expose] def pauliBraidingZeroQuestion (basis : Bool) (dummy : Fin n → Bool) :
    PauliBraidingQuestion n Q :=
  .basis basis (cond (BitString.lexSwap (0 : Fin n → Bool) dummy) Prod.swap id (0, dummy))

/-- Decode the bit checked at zero by the diagonal linearity test. Equal strings retain
the original order, so when the dummy is zero the first bit is checked. -/
@[expose] def pauliBraidingZeroBit (dummy : Fin n → Bool) : (Bool × Bool) ⊕ A → Bool :=
  Sum.elim (fun bits => (cond (BitString.lexSwap (0 : Fin n → Bool) dummy) Prod.swap id bits).1)
    (fun _ => false)

omit [Nonempty (Fin n)] in
open BitString in
/-- The linearity and consistency decoders at zero agree away from the duplicated
zero query. They also agree at the tie in the X basis. -/
theorem pauliBraidingZero_decoding (basis : Bool) (dummy : Fin n → Bool)
    (h : dummy ≠ 0 ∨ basis = false) :
    let q := PauliConsistencyQuestion.ofChecked basis 0 dummy
    q.toBraidingQuestion = (pauliBraidingZeroQuestion basis dummy : PauliBraidingQuestion n Q) ∧
      (Sum.elim q.braidingCheckedBit (fun _ : A => false)) = pauliBraidingZeroBit dummy := by
  intro q
  cases basis
  · exact ⟨rfl, rfl⟩
  have hn : dummy ≠ 0 := h.resolve_right Bool.noConfusion
  have hswap := lexSwap_reverse (Ne.symm hn)
  change PauliConsistencyQuestion.toBraidingQuestion ⟨dummy, 0, true⟩ =
      (pauliBraidingZeroQuestion true dummy : PauliBraidingQuestion n Q) ∧
    Sum.elim (PauliConsistencyQuestion.braidingCheckedBit ⟨dummy, 0, true⟩)
      (fun _ : A => false) = pauliBraidingZeroBit dummy
  constructor
  · simp only [PauliConsistencyQuestion.toBraidingQuestion, pauliBraidingZeroQuestion, hswap]
    cases lexSwap (0 : Fin n → Bool) dummy <;> rfl
  · funext answer
    cases answer with
    | inr malformed => rfl
    | inl bits =>
      simp only [pauliBraidingZeroBit, Sum.elim_inl,
        PauliConsistencyQuestion.braidingCheckedBit, PauliConsistencyQuestion.checkedBit, hswap]
      cases lexSwap (0 : Fin n → Bool) dummy <;> rfl

open BitString Finset Quantum in
/-- For either role assignment, the three checks of a diagonal round bound the point
player’s probability of a true decoded answer at zero.
Malformed answers are decoded as false and still rejected by the verifier. -/
theorem prob_true_le_pauliBraidingDiagonal {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜)
    (a dummy : Fin n → Bool) :
    let game := pauliBraidingDiagonalGame n G special decode roles basis
    let logical := cond roles S.swap S
    let loss (k : Fin 3) :=
      1 - ({ game with seed := PMF.pure (k, a, dummy) }).commutingWinProb S
    ((logical.bob (pauliBraidingZeroQuestion basis dummy)).map
      (pauliBraidingZeroBit dummy)).prob logical.state true ≤ loss 0 + loss 1 + loss 2 := by
  classical
  intro game logical loss
  let x : PauliBraidingQuestion n Q := .basis basis (a, a)
  let point (c : Fin n → Bool) : PauliBraidingQuestion n Q :=
    .basis basis (cond (lexSwap c dummy) Prod.swap id (c, dummy))
  let pair : (Bool × Bool) ⊕ A → Bool × Bool := Sum.elim id (fun _ => (false, false))
  let pointRead (c : Fin n → Bool) (ans : (Bool × Bool) ⊕ A) : Bool :=
    (cond (lexSwap c dummy) Prod.swap id (pair ans)).1
  have hread : pointRead 0 = pauliBraidingZeroBit dummy := by
    funext ans
    cases ans with
    | inl bits => rfl
    | inr bad =>
      change (cond (lexSwap (0 : Fin n → Bool) dummy) Prod.swap id (false, false)).1 = false
      cases lexSwap (0 : Fin n → Bool) dummy <;> rfl
  have htie : lexSwap a a = false := by simp [lexSwap]
  have hquery (k : Fin 3) : game.query (k, a, dummy) =
      cond roles Prod.swap id (x, point (linearityQuery k a a)) := by
    cases roles <;>
      simp only [game, pauliBraidingDiagonalGame, SeededGame.pullbackSeed, Function.comp_apply,
      pauliBraidingGame, pauliBraidingBranchGame, SymmetricLinearitySeed.diagonal,
        Function.Embedding.coeFn_mk, symmetricLinearityGame, htie, Bool.cond_false,
        Bool.cond_true, id_eq, Prod.swap_prod_mk, x, point]
  have hcheck (k : Fin 3) (p q : (Bool × Bool) ⊕ A)
      (h : game.accepts (k, a, dummy) (cond roles q p) (cond roles p q)) :
      pointRead (linearityQuery k a a) q = linearityCheck k (pair p) := by
    cases roles <;> cases p <;> cases q
    all_goals
      first
      | exact False.elim h
      | simpa only [game, pauliBraidingDiagonalGame, SeededGame.pullbackSeed, pauliBraidingGame,
          pauliBraidingBranchGame, SymmetricLinearitySeed.diagonal, Function.Embedding.coeFn_mk,
          symmetricLinearityGame, htie, Bool.cond_false, Bool.cond_true, id_eq, Prod.swap_prod_mk,
          pointRead, pair, Sum.elim_inl] using h
  have hcompare (k : Fin 3) :
      (∑ p, ∑ q, if pointRead (linearityQuery k a a) q = linearityCheck k (pair p) then 0
        else logical.prob x (point (linearityQuery k a a)) p q) ≤ loss k := by
    rw [show loss k = _ from game.one_sub_commutingWinProb_pure_seed (k, a, dummy) S, hquery]
    have hloss :
        (∑ p, ∑ q, if game.accepts (k, a, dummy) (cond roles q p) (cond roles p q) then 0
          else logical.prob x (point (linearityQuery k a a)) p q) =
        ∑ p, ∑ q, if game.accepts (k, a, dummy) p q then 0 else
          S.prob (cond roles Prod.swap id (x, point (linearityQuery k a a))).1
            (cond roles Prod.swap id (x, point (linearityQuery k a a))).2 p q := by
      cases roles
      · rfl
      · simp only [logical, Bool.cond_true, Prod.swap_prod_mk, S.prob_swap]
        exact sum_comm
    rw [← hloss]
    refine sum_le_sum fun p _ => sum_le_sum fun q _ => ?_
    by_cases h : game.accepts (k, a, dummy) (cond roles q p) (cond roles p q)
    · simp only [h, hcheck k p q h, ite_true, le_refl]
    · simp only [h, ite_false]
      split_ifs
      · exact logical.prob_nonneg _ _ _ _
      · exact le_rfl
  have hzero : linearityQuery 2 a a = 0 := by simp [linearityQuery]
  change ((logical.bob (point 0)).map (pauliBraidingZeroBit dummy)).prob logical.state true ≤ _
  rw [← hread]
  have h := logical.prob_true_le_diagonal_linearity x (point a) (point 0) pair
    (pointRead a) (pointRead 0)
  have h0 := hcompare 0
  have h1 := hcompare 1
  have h2 := hcompare 2
  rw [hzero] at h2
  simp only [linearityQuery, linearityCheck, Fin.reduceEq, ite_true, ite_false] at h0 h1
  simp only [linearityCheck, Fin.reduceEq, ite_false] at h2
  dsimp only at h
  linarith only [h, h0, h1, h2]

open Finset Quantum in
/-- The probability of a true decoded zero answer, averaged over the dummy and weighted by
the uniform mass of zero, is at most twelve times the linearity-branch rejection probability. -/
theorem expect_prob_true_pauliBraidingZero_le {𝒜 : Type*} [Fintype A] [Ring 𝒜] [StarRing 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (roles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let logical := cond roles S.swap S
    (𝔼 dummy, ((logical.bob (pauliBraidingZeroQuestion basis dummy)).map
      (pauliBraidingZeroBit dummy)).prob logical.state true) / Fintype.card (Fin n → Bool) ≤
      12 * (1 - (pauliBraidingBranchGame n G special decode 0).commutingWinProb S) := by
  intro logical
  let game := pauliBraidingDiagonalGame n G special decode roles basis
  let lose (r : Fin 3 × (Fin n → Bool) × (Fin n → Bool)) :=
    1 - ({ game with seed := PMF.pure r }).commutingWinProb S
  let bad (dummy : Fin n → Bool) :=
    ((logical.bob (pauliBraidingZeroQuestion basis dummy)).map
      (pauliBraidingZeroBit dummy)).prob logical.state true
  have hlocal (a dummy : Fin n → Bool) :
      bad dummy ≤ lose (0, a, dummy) + lose (1, a, dummy) + lose (2, a, dummy) :=
    prob_true_le_pauliBraidingDiagonal G special decode roles basis S a dummy
  have havg : (𝔼 dummy, bad dummy) ≤ 3 * (𝔼 r, lose r) := by
    have h := expect_le_expect (s := (univ : Finset (Fin n → Bool))) fun a _ =>
      expect_le_expect (s := (univ : Finset (Fin n → Bool))) fun dummy _ => hlocal a dummy
    simp only [Fintype.expect_const] at h
    refine h.trans_eq ?_
    rw [Fintype.expect_prod_type]
    simp_rw [Fintype.expect_prod_type]
    rw [Finset.expect_comm univ univ (fun k a => 𝔼 d, lose (k, a, d)), Finset.mul_expect]
    refine expect_congr rfl fun a _ => ?_
    rw [Finset.expect_comm univ univ (fun k d => lose (k, a, d)), Finset.mul_expect]
    refine expect_congr rfl fun d _ => ?_
    rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_three, Fintype.card_fin]
    push_cast
    ring
  have hscore : (𝔼 r, lose r) = 1 - game.commutingWinProb S := by
    unfold SeededGame.commutingWinProb
    rw [SeededGame.rejection_eq_sum]
    change _ = ∑ r, ((Probability.PMF.uniformOfFintype _) r).toReal * lose r
    simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ← mul_sum, Fintype.expect_eq_sum_div_card]
    ring
  rw [hscore] at havg
  have hbudget := rejection_pauliBraidingDiagonalGame_le G special decode roles basis S.answers
  change (1 - game.commutingWinProb S) / (4 * Fintype.card (Fin n → Bool)) ≤ _ at hbudget
  change (𝔼 dummy, bad dummy) / Fintype.card (Fin n → Bool) ≤ _
  refine (div_le_div_of_nonneg_right havg (by positivity)).trans ?_
  rw [show 3 * (1 - game.commutingWinProb S) / (Fintype.card (Fin n → Bool) : ℝ) =
      12 * ((1 - game.commutingWinProb S) / (4 * Fintype.card (Fin n → Bool))) by ring]
  exact mul_le_mul_of_nonneg_left hbudget (by norm_num)

end Cslib.PCP
