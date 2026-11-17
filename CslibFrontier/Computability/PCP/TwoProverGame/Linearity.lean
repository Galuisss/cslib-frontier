/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Foundations.Quantum.Algebra.LinearityTest
public import CslibFrontier.Foundations.Quantum.Algebra.CStar
public import CslibFrontier.Probability.PMF.Expect
public import CslibFrontier.Foundations.Data.BitString.Sign

/-!
# The two-player linearity test

The **linearity test** (`Cslib.PCP.linearityTest`) is the two-player game in which the verifier
draws `a, b ∈ {0,1}ⁿ` uniformly, sends the pair `(a, b)` to the *pair player* (Bob), and sends
`c`, equal with probability `1/3` each to `a`, `b` or `a + b`, to the *point player* (Alice). Alice
answers a bit `γ` and Bob answers bits `(α, β)`. The verifier checks consistency, `γ = α` if
`c = a` and `γ = β` if `c = b`, and linearity, `γ = α ⊕ β` if `c = a + b`.

A commuting-operator strategy with projective measurements that wins with probability `1 - ε`
makes Alice's observables `A(c)` linear on average
(`Cslib.PCP.CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest`):

`E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - 6ε - 2√(12ε)`.

Each test passes with probability at least `1 - 3ε`. The consistency tests bound the distances
between Alice's observables and the marginals of Bob's, and the linearity test bounds the
correlation of `A(a + b)` with the product of Bob's marginals, which for a projective measurement
is the parity observable. Linearity from consistency
(`Cslib.Quantum.one_sub_le_expect_re_apply_mul_mul`) then gives the bound.

This is the game of [Natarajan and Vidick, §3, Figure 1][NatarajanVidick2017]
(arXiv:1610.03574v1) in an asymmetric form, and the estimate is the commuting-operator,
point-player form of their Theorem 11. The source labels the players at random and sends Bob a
second, uniformly random query, so that symmetric strategies apply; here one player always gets a
point and the other a pair, which hides the test type without the extra query. As in the source,
the strategy's measurements are assumed projective. Removing that assumption, and the remaining
steps toward Pauli rigidity, are tracked in cslib-community/cslib-frontier#6149.

## Main definitions

* `Cslib.PCP.linearityTest`: the two-player linearity test.

## Main results

* `Cslib.PCP.CommutingStrategy.sum_ite_prob_eq`: the probability that the point player's bit
  matches a function of the other answer, as a correlation.
* `Cslib.PCP.CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest`: winning the
  linearity test makes the point player's observables linear on average.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

@[expose] public section

namespace Cslib.PCP

open Finset Quantum
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The query sent to the point player in each of the three tests: `a`, `b` or `a + b`. -/
def linearityQuery (k : Fin 3) (a b : n → Bool) : n → Bool :=
  if k = 0 then a else if k = 1 then b else a + b

/-- The **two-player linearity test**. The pair player gets `(a, b)` uniformly at random, and the
point player gets `a`, `b` or `a + b`, each with probability `1/3`. The verifier accepts the bit
`γ` and the bits `(α, β)` when `γ = α` if the point is `a`, `γ = β` if it is `b`, and `γ = α ⊕ β`
if it is `a + b`. -/
noncomputable def linearityTest (n : Type*) [Fintype n] [DecidableEq n] :
    TwoProverGame (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) where
  questions := (Probability.PMF.uniformOfFintype (Fin 3 × (n → Bool) × (n → Bool))).map
    fun ⟨k, a, b⟩ => (linearityQuery k a b, (a, b))
  accepts c q γ r := (c = q.1 → γ = r.1) ∧ (c = q.2 → γ = r.2) ∧ (c = q.1 + q.2 → γ = (r.1 ^^ r.2))

instance (c : n → Bool) (q : (n → Bool) × (n → Bool)) (γ : Bool) (r : Bool × Bool) :
    Decidable ((linearityTest n).accepts c q γ r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

namespace CommutingStrategy

variable {X Y B 𝒜 : Type*} [Fintype B] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [Algebra ℂ 𝒜]

/-- The probability that the bit `γ` of the first player equals `g(r)` for the answer `r` of the
second is the correlation of their observables: `(1 + Re φ(A_x G_y)) / 2`, where `G_y` is the
observable of the second player's measurement post-processed by `g`. -/
theorem sum_ite_prob_eq (S : CommutingStrategy X Y Bool B 𝒜) (g : B → Bool) (x : X) (y : Y) :
    ∑ γ, ∑ r, (if γ = g r then S.prob x y γ r else 0) =
      (1 + (S.state ((S.alice x).observable * ((S.bob y).map g).observable)).re) / 2 := by
  classical
  have h : ∀ γ, ∑ r, (if γ = g r then S.prob x y γ r else 0) =
      (S.state ((S.alice x).effect γ * ((S.bob y).map g).effect γ)).re := by
    intro γ
    rw [Measurement.map_effect, mul_sum, map_sum, Complex.re_sum, sum_filter]
    refine sum_congr rfl fun r _ => ?_
    simp only [prob, eq_comm]
  simp only [h, Fintype.sum_bool]
  set s := (S.alice x).effect false
  set t := (S.alice x).effect true
  set u := ((S.bob y).map g).effect false
  set v := ((S.bob y).map g).effect true
  have hst : t = 1 - s := by
    have := (S.alice x).sum_effect
    rw [Fintype.sum_bool] at this
    exact eq_sub_of_add_eq this
  have huv : v = 1 - u := by
    have := ((S.bob y).map g).sum_effect
    rw [Fintype.sum_bool] at this
    exact eq_sub_of_add_eq this
  have key : 1 + (s - t) * (u - v) = (t * v + s * u) + (t * v + s * u) := by
    rw [hst, huv]; noncomm_ring
  rw [Measurement.observable, Measurement.observable, ← Complex.add_re, ← map_add]
  change _ = (1 + (S.state ((s - t) * (u - v))).re) / 2
  have h1 : (1 : ℝ) = (S.state 1).re := by rw [S.state.map_one, Complex.one_re]
  rw [h1, ← Complex.add_re, ← map_add, key]
  simp only [map_add, Complex.add_re]
  ring

end CommutingStrategy

variable {α 𝒜 : Type*} [Fintype α] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [Algebra ℂ 𝒜] in
/-- The observable of a post-processed measurement: `∑_r (-1)^{g(r)} M_r`. -/
theorem _root_.Cslib.Quantum.Measurement.observable_map (M : Measurement α 𝒜) (g : α → Bool) :
    (M.map g).observable = ∑ r, (BitString.signVal (g r) : ℂ) • M.effect r := by
  classical
  simp only [Measurement.observable, Measurement.map_effect, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun r _ => ?_
  cases g r <;> simp [BitString.signVal]

namespace CommutingStrategy

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

private theorem commute_observable {X Y B : Type*} [Fintype B]
    (S : CommutingStrategy X Y Bool B 𝒜) (g : B → Bool) (x : X) (y : Y) :
    Commute (((S.bob y).map g).observable) ((S.alice x).observable) := by
  classical
  simp only [Measurement.observable, Measurement.map_effect]
  refine (Commute.sub_left ?_ ?_) <;> refine Commute.sum_left _ _ _ fun r _ => ?_ <;>
    exact ((S.commute x y false r).sub_left (S.commute x y true r)).symm

private theorem norm_eq_one (φ : AlgState 𝒜) {U : 𝒜} (hU : U ∈ unitary 𝒜) : φ.norm U = 1 := by
  rw [AlgState.norm_eq_sqrt, Unitary.star_mul_self_of_mem hU, φ.map_one, Complex.one_re,
    Real.sqrt_one]

private theorem observable_mem_unitary {M : Measurement Bool 𝒜} (hM : M.IsProjective) :
    M.observable ∈ unitary 𝒜 := by
  rw [Unitary.mem_iff, M.isSelfAdjoint_observable.star_eq]
  exact ⟨Measurement.observable_mul_self hM, Measurement.observable_mul_self hM⟩

private theorem re_apply_mul_le_one (φ : AlgState 𝒜) {U V : 𝒜} (hU : U ∈ unitary 𝒜)
    (hUsa : IsSelfAdjoint U) (hV : V ∈ unitary 𝒜) : (φ (U * V)).re ≤ 1 := by
  have h := φ.re_apply_star_mul_le U V
  rwa [hUsa.star_eq, norm_eq_one φ hU, norm_eq_one φ hV, one_mul] at h

private theorem norm_sub_sq_eq (φ : AlgState 𝒜) {U V : 𝒜} (hU : IsSelfAdjoint U)
    (hV : IsSelfAdjoint V) (hU2 : U * U = 1) (hV2 : V * V = 1) (hc : Commute V U) :
    φ.norm (U - V) ^ 2 = 2 - 2 * (φ (U * V)).re := by
  have e : (U - V) * (U - V) = (1 + 1) - (U * V + U * V) := by
    rw [sub_mul, mul_sub, mul_sub, hU2, hV2, hc.eq]; abel
  rw [φ.norm_sq, star_sub, hU.star_eq, hV.star_eq, e, map_sub, map_add, map_add, φ.map_one,
    Complex.sub_re, Complex.add_re, Complex.add_re, Complex.one_re]
  ring

/-- The product of the observables of two bits of a projective measurement is the observable of
their parity. -/
private theorem observable_map_fst_mul_snd {M : Measurement (Bool × Bool) 𝒜}
    (hM : M.IsProjective) :
    (M.map Prod.fst).observable * (M.map Prod.snd).observable =
      (M.map fun r => r.1 ^^ r.2).observable := by
  rw [Measurement.observable_map, Measurement.observable_map, Measurement.observable_map,
    hM.sum_smul_mul_sum_smul]
  refine sum_congr rfl fun r _ => ?_
  rw [BitString.signVal_xor, Complex.ofReal_mul]

/-- **Winning the linearity test makes the point player's observables linear.** A
commuting-operator strategy with projective measurements that wins the linearity test with
probability at least `1 - ε` has `E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - 6ε - 2√(12ε)` for the
observables `A(c)` of the point player. -/
theorem one_sub_le_expect_re_apply_mul_mul_of_linearityTest
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜)
    (hA : ∀ c, (S.alice c).IsProjective) (hB : ∀ q, (S.bob q).IsProjective) {ε : ℝ}
    (hε : 1 - ε ≤ (linearityTest n).commutingWinProb S) :
    1 - 6 * ε - √(12 * ε) - √(12 * ε) ≤
      𝔼 a, 𝔼 b, (S.state ((S.alice a).observable * (S.alice b).observable *
        (S.alice (a + b)).observable)).re := by
  classical
  set φ := S.state
  let A : (n → Bool) → 𝒜 := fun c => (S.alice c).observable
  let G : Fin 3 → Bool × Bool → Bool := fun k =>
    if k = 0 then Prod.fst else if k = 1 then Prod.snd else fun r => r.1 ^^ r.2
  let N : Fin 3 → (n → Bool) → (n → Bool) → 𝒜 := fun k a b => ((S.bob (a, b)).map (G k)).observable
  let C : Fin 3 → (n → Bool) → (n → Bool) → ℝ := fun k a b =>
    (φ (A (linearityQuery k a b) * N k a b)).re
  have hAu : ∀ c, A c ∈ unitary 𝒜 := fun c => observable_mem_unitary (hA c)
  have hNu : ∀ k a b, N k a b ∈ unitary 𝒜 := fun k a b => observable_mem_unitary ((hB _).map _)
  have hC1 : ∀ k a b, C k a b ≤ 1 := fun k a b =>
    re_apply_mul_le_one φ (hAu _) (S.alice _).isSelfAdjoint_observable (hNu k a b)
  have hwin : (linearityTest n).commutingWinProb S ≤
      1 / 2 + (𝔼 a, 𝔼 b, C 0 a b + 𝔼 a, 𝔼 b, C 1 a b + 𝔼 a, 𝔼 b, C 2 a b) / 6 := by
    have hF : ∀ k a b, (∑ γ, ∑ r, if (linearityTest n).accepts (linearityQuery k a b) (a, b) γ r
        then S.prob (linearityQuery k a b) (a, b) γ r else 0) ≤ (1 + C k a b) / 2 := by
      intro k a b
      rw [show (1 + C k a b) / 2 = ∑ γ, ∑ r, (if γ = G k r then
        S.prob (linearityQuery k a b) (a, b) γ r else 0) from (sum_ite_prob_eq S (G k) _ _).symm]
      refine sum_le_sum fun γ _ => sum_le_sum fun r _ => ?_
      have hacc : (linearityTest n).accepts (linearityQuery k a b) (a, b) γ r → γ = G k r := by
        rintro ⟨h₀, h₁, h₂⟩
        fin_cases k
        · exact h₀ (by simp [linearityQuery])
        · exact h₁ (by simp [linearityQuery])
        · exact h₂ (by simp [linearityQuery])
      split_ifs with h₁ h₂ h₂
      · exact le_rfl
      · exact absurd (hacc h₁) h₂
      · exact S.prob_nonneg _ _ _ _
      · exact le_rfl
    have hq : (linearityTest n).questions =
        (Probability.PMF.uniformOfFintype (Fin 3 × (n → Bool) × (n → Bool))).map
          fun ⟨k, a, b⟩ => (linearityQuery k a b, (a, b)) := rfl
    rw [TwoProverGame.commutingWinProb_eq_sum, ← Fintype.sum_prod_type', hq,
      Probability.PMF.sum_map_mul]
    calc _ ≤ ∑ k : Fin 3 × (n → Bool) × (n → Bool),
          (Fintype.card (Fin 3 × (n → Bool) × (n → Bool)) : ℝ)⁻¹ *
            ((1 + C k.1 k.2.1 k.2.2) / 2) := by
          refine sum_le_sum fun ⟨k, a, b⟩ _ => ?_
          rw [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
          exact mul_le_mul_of_nonneg_left (hF k a b) (by positivity)
      _ = _ := by
          rw [← mul_sum, Fintype.sum_prod_type, Fin.sum_univ_three]
          simp only [Fintype.sum_prod_type, Fintype.expect_eq_sum_div_card, Fintype.card_prod,
            Fintype.card_fin, ← sum_div, add_div, sum_add_distrib, sum_const, card_univ,
            nsmul_eq_mul]
          have hK : (Fintype.card (n → Bool) : ℝ) ≠ 0 := by positivity
          push_cast
          field_simp
          ring
  have hE : ∀ k, 𝔼 a, 𝔼 b, C k a b ≤ 1 := fun k => by
    calc 𝔼 a, 𝔼 b, C k a b ≤ 𝔼 _a : n → Bool, 𝔼 _b : n → Bool, (1 : ℝ) :=
          expect_le_expect fun a _ => expect_le_expect fun b _ => hC1 k a b
      _ = 1 := by simp only [Fintype.expect_const]
  have hc : ∀ k a b c, Commute (N k a b) (A c) := fun k a b c => commute_observable S _ _ _
  have hNsa : ∀ k a b, IsSelfAdjoint (N k a b) := fun k a b =>
    Measurement.isSelfAdjoint_observable _
  have hN2 : ∀ k a b, N k a b * N k a b = 1 := fun k a b =>
    Measurement.observable_mul_self ((hB _).map _)
  have hdist : ∀ k a b, φ.norm (A (linearityQuery k a b) - N k a b) ^ 2 = 2 - 2 * C k a b :=
    fun k a b => norm_sub_sq_eq φ (S.alice _).isSelfAdjoint_observable (hNsa k a b)
      (Measurement.observable_mul_self (hA _)) (hN2 k a b) (hc k a b _)
  have hdistE : ∀ k, 𝔼 a, 𝔼 b, φ.norm (A (linearityQuery k a b) - N k a b) ^ 2 =
      2 - 2 * 𝔼 a, 𝔼 b, C k a b := fun k => by
    simp only [hdist, expect_sub_distrib, ← mul_expect, Fintype.expect_const]
  have hL : 1 - 6 * ε ≤ 𝔼 a, 𝔼 b, (φ (N 0 a b * N 1 a b * A (a + b))).re := by
    have e : ∀ a b, (φ (N 0 a b * N 1 a b * A (a + b))).re = C 2 a b := fun a b => by
      simp only [C, N, G, linearityQuery, Fin.reduceEq, ite_true, ite_false,
        observable_map_fst_mul_snd (hB (a, b))]
      rw [(commute_observable S _ (a + b) (a, b)).eq]
    simp only [e]
    linarith [hE 0, hE 1, hE 2]
  have h₁ : 𝔼 a, 𝔼 b, φ.norm (A a - N 0 a b) ^ 2 ≤ 12 * ε := by
    have := hdistE 0
    simp only [linearityQuery, ite_true] at this
    rw [this]
    linarith [hE 0, hE 1, hE 2]
  have h₂ : 𝔼 a, 𝔼 b, φ.norm (A b - N 1 a b) ^ 2 ≤ 12 * ε := by
    have := hdistE 1
    simp only [linearityQuery, Fin.reduceEq, ite_true, ite_false] at this
    rw [this]
    linarith [hE 0, hE 1, hE 2]
  exact one_sub_le_expect_re_apply_mul_mul φ A (N 0) (N 1) hAu (hNu 0) (hc 0) (hc 1) hL h₁ h₂

end CommutingStrategy

end Cslib.PCP
