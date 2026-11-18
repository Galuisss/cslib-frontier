/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.CHSHRigidity
public import CslibFrontier.Foundations.Quantum.Algebra.Braiding

/-!
# The anticommutation test

The Pauli braiding test of [Natarajan and Vidick, §4.1, Figure 2][NatarajanVidick2017]
(arXiv:1610.03574v1, p. 17) certifies anticommutation through an *anticommutation game*: for each
pair `(a, b)` with `a · b = 1`, the players play a game whose second player answers the special
questions `q_X`, `q_Z` with observables `X'(a, b)`, `Z'(a, b)`, and near-optimal play forces these
to nearly anticommute. The CHSH game is such a game (their Lemma 9, p. 14). The consistency test
then ties `X'(a, b)` to the first player's linearity-test observable `X(a)`, and `Z'(a, b)` to
`Z(b)`.

This file carries the anticommutation from the game's observables to `X(a)`, `Z(b)` on average,
for commuting-operator strategies in any C⋆-algebra, with explicit constants. For every pair with
`a · b = 1` let `G(a, b)` be a commuting-operator strategy for CHSH in the shared state `φ`, whose
first player's observables are `X'(a, b)` and `Z'(a, b)` (the second player of the source's
anticommutation game; the roles in CHSH are symmetric) and which wins with probability at least
`cos²(π/8) - ε(a, b)`. If `X(a)`, `Z(b)` are unitaries commuting with `Z'(a, b)`, `X'(a, b)`, then
(`Cslib.PCP.expect_anticommDefectSq_le_of_chsh`)

`E_{a,b} [a · b = 1] ‖X(a) Z(b) + Z(b) X(a)‖²_φ ≤
9 (E [a · b = 1] ‖X(a) - X'(a, b)‖²_φ + E [a · b = 1] ‖Z(b) - Z'(a, b)‖²_φ +
K E [a · b = 1] ε(a, b))`

with `K = (4 + 2√2)² · 8√2` (`Cslib.PCP.chshAnticommConst`): CHSH rigidity
(`Cslib.PCP.CommutingStrategy.anticomm_of_chsh`) bounds the anticommutation of `X'`, `Z'`, and the
transfer through consistency (`Cslib.Quantum.norm_mul_sub_smul_mul_le_of_consistent`) moves it to
`X`, `Z`. Composed with the braiding and Pauli-family bounds
(`Cslib.Quantum.expect_norm_pauliFamily_sub_sq_le_of_anticommute`), this bounds the Pauli-family
defect by the consistency distances, the CHSH deficits and the linearity defects
(`Cslib.PCP.expect_norm_pauliFamily_sub_sq_le_of_chsh`). This is the computation of
[Natarajan and Vidick, §4.3.2, Lemma 18][NatarajanVidick2017] (p. 21) for the CHSH game, with the
masked unconditional average in place of the conditional one.

Deriving the consistency distances from the consistency test, and the full Pauli braiding test as a
game, are tracked in cslib-community/cslib-frontier#6149.

## Main definitions

* `Cslib.PCP.chshAnticommConst`: the constant `(4 + 2√2)² · 8√2`.

## Main results

* `Cslib.PCP.expect_anticommDefectSq_le_of_chsh`: anticommutation of the linearity-test observables
  from the CHSH anticommutation test and consistency.
* `Cslib.PCP.expect_norm_pauliFamily_sub_sq_le_of_chsh`: the Pauli-family defect from the CHSH
  anticommutation test, consistency and linearity.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

public section

namespace Cslib.PCP

open Finset Quantum
open scoped BigOperators Real

/-- The constant `(4 + 2√2)² · 8√2` relating the squared anticommutation defect of a CHSH strategy
to its deficit from the optimal winning probability. -/
noncomputable def chshAnticommConst : ℝ :=
  (4 + 2 * √2) ^ 2 * (8 * √2)

theorem chshAnticommConst_nonneg : 0 ≤ chshAnticommConst := by
  unfold chshAnticommConst; positivity

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
  [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- The squared anticommutation defect of the first player's observables in a CHSH strategy is at
most `K ε` when it wins with probability at least `cos²(π/8) - ε`. -/
theorem norm_anticomm_sq_le_of_chsh (G : CommutingStrategy Bool Bool Bool Bool 𝒜) {ε : ℝ}
    (h : Real.cos (π / 8) ^ 2 - ε ≤ TwoProverGame.chsh.commutingWinProb G) :
    G.state.norm ((G.alice false).observable * (G.alice true).observable +
      (G.alice true).observable * (G.alice false).observable) ^ 2 ≤ chshAnticommConst * ε := by
  have hε : 0 ≤ ε := by linarith [TwoProverGame.commutingWinProb_chsh_le G]
  have h₁ := AlgState.approx_iff.mp (G.anticomm_of_chsh h)
  rw [sub_zero] at h₁
  calc _ ≤ chshRigidityError ε ^ 2 := pow_le_pow_left₀ (G.state.norm_nonneg _) h₁ 2
    _ = chshAnticommConst * ε := by
        unfold chshRigidityError chshAnticommConst
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Anticommutation from the CHSH anticommutation test and consistency.** For every pair with
`a · b = 1`, let the CHSH strategy `G(a, b)` in the state `φ` have projective first-player
measurements with observables `X'(a, b)`, `Z'(a, b)`, and win with probability at least
`cos²(π/8) - ε(a, b)`. If the unitaries `X(a)`, `Z(b)` commute with `Z'(a, b)`, `X'(a, b)`, the
averaged masked anticommutation defect of `X`, `Z` is at most
`9 (E [a·b = 1] ‖X(a) - X'(a, b)‖² + E [a·b = 1] ‖Z(b) - Z'(a, b)‖² + K E [a·b = 1] ε(a, b))`. -/
theorem expect_anticommDefectSq_le_of_chsh (φ : AlgState 𝒜) (X Z : (ι → Bool) → 𝒜)
    (G : (ι → Bool) → (ι → Bool) → CommutingStrategy Bool Bool Bool Bool 𝒜)
    (hφ : ∀ a b, (G a b).state = φ) (hX : ∀ a, X a ∈ unitary 𝒜) (hZ : ∀ b, Z b ∈ unitary 𝒜)
    (hG : ∀ a b x, ((G a b).alice x).IsProjective)
    (hXZ' : ∀ a b, Commute (X a) ((G a b).alice true).observable)
    (hZX' : ∀ a b, Commute (Z b) ((G a b).alice false).observable) (ε : (ι → Bool) → (ι → Bool) → ℝ)
    (hε : ∀ a b, a ⬝ᵥ b = true →
      Real.cos (π / 8) ^ 2 - ε a b ≤ TwoProverGame.chsh.commutingWinProb (G a b)) :
    𝔼 a, 𝔼 b, anticommDefectSq φ X Z a b ≤
      9 * (𝔼 a, 𝔼 b, (if a ⬝ᵥ b = true then
          φ.norm (X a - ((G a b).alice false).observable) ^ 2 else 0) +
        𝔼 a, 𝔼 b, (if a ⬝ᵥ b = true then
          φ.norm (Z b - ((G a b).alice true).observable) ^ 2 else 0) +
        chshAnticommConst * 𝔼 a, 𝔼 b, (if a ⬝ᵥ b = true then ε a b else 0)) := by
  have hpt : ∀ a b, anticommDefectSq φ X Z a b ≤
      9 * ((if a ⬝ᵥ b = true then φ.norm (X a - ((G a b).alice false).observable) ^ 2 else 0) +
        (if a ⬝ᵥ b = true then φ.norm (Z b - ((G a b).alice true).observable) ^ 2 else 0) +
        chshAnticommConst * (if a ⬝ᵥ b = true then ε a b else 0)) := by
    intro a b
    by_cases hab : a ⬝ᵥ b = true
    · simp only [hab, ite_true, anticommDefectSq_of_dotProduct_eq_true φ X Z hab]
      set X' := ((G a b).alice false).observable
      set Z' := ((G a b).alice true).observable
      have hX' : X' ∈ unitary 𝒜 := (hG a b false).observable_mem_unitary
      have hZ' : Z' ∈ unitary 𝒜 := (hG a b true).observable_mem_unitary
      have htr := norm_mul_sub_smul_mul_le_of_consistent φ (hX a) (hZ b) hX' hZ' (hXZ' a b)
        (hZX' a b) (s := -1) (by simp)
      have hR := norm_anticomm_sq_le_of_chsh (G a b) (hε a b hab)
      rw [hφ] at hR
      simp only [neg_one_smul, sub_neg_eq_add] at htr
      rw [add_comm (Z b * X a)] at htr
      set x := φ.norm (X a - X') with hx
      set z := φ.norm (Z b - Z') with hz
      set w := φ.norm (X' * Z' + Z' * X')
      have h0 := φ.norm_nonneg (X a * Z b + Z b * X a)
      have hx0 := φ.norm_nonneg (X a - X')
      have hz0 := φ.norm_nonneg (Z b - Z')
      have hw0 := φ.norm_nonneg (X' * Z' + Z' * X')
      have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ![(2 : ℝ), 2, 1] ![x, z, w]
      simp only [Fin.sum_univ_three, Matrix.cons_val] at hCS
      calc φ.norm (X a * Z b + Z b * X a) ^ 2 ≤ (2 * x + 2 * z + w) ^ 2 :=
            pow_le_pow_left₀ h0 htr 2
        _ ≤ 9 * (x ^ 2 + z ^ 2 + w ^ 2) := by linarith
        _ ≤ 9 * (x ^ 2 + z ^ 2 + chshAnticommConst * ε a b) := by linarith
    · have hab' : a ⬝ᵥ b = false := by simpa using hab
      simp only [hab, Bool.false_eq_true, ite_false, mul_zero, add_zero,
        anticommDefectSq_of_dotProduct_eq_false φ X Z hab', le_refl]
  calc 𝔼 a, 𝔼 b, anticommDefectSq φ X Z a b ≤ 𝔼 a, 𝔼 b, 9 * (_ + _ + _) :=
        expect_le_expect fun a _ => expect_le_expect fun b _ => hpt a b
    _ = _ := by simp only [← mul_expect, expect_add_distrib]

/-- **The Pauli-family defect from the CHSH anticommutation test, consistency and linearity.** Let
Alice's unitaries `X(a)`, `Z(b)` with `X(0) = 1` have consistent unitary copies `X''(a)`, `Z''(b)`
for Bob, commuting with them, as in the linearity and consistency tests, and let the CHSH
strategies `G(a, b)` be as in `Cslib.PCP.expect_anticommDefectSq_le_of_chsh`. Then the
multiplicative defect `E_{p,q} ‖P(p) P(q) - P(pq)‖²_φ` of the Pauli family
`P(a, b, s) = s X(a) Z(b)` is bounded by the consistency distances, the CHSH deficits and the
linearity defects. -/
theorem expect_norm_pauliFamily_sub_sq_le_of_chsh (φ : AlgState 𝒜) (X Z X'' Z'' : (ι → Bool) → 𝒜)
    (G : (ι → Bool) → (ι → Bool) → CommutingStrategy Bool Bool Bool Bool 𝒜)
    (hφ : ∀ a b, (G a b).state = φ) (hX : ∀ a, X a ∈ unitary 𝒜) (hZ : ∀ b, Z b ∈ unitary 𝒜)
    (hX'' : ∀ a, X'' a ∈ unitary 𝒜) (hZ'' : ∀ b, Z'' b ∈ unitary 𝒜)
    (hXZ'' : ∀ a b, Commute (X a) (Z'' b)) (hZZ'' : ∀ b b', Commute (Z b) (Z'' b'))
    (hZX'' : ∀ b a, Commute (Z b) (X'' a)) (hX0 : X 0 = 1)
    (hG : ∀ a b x, ((G a b).alice x).IsProjective)
    (hXZ' : ∀ a b, Commute (X a) ((G a b).alice true).observable)
    (hZX' : ∀ a b, Commute (Z b) ((G a b).alice false).observable) (ε : (ι → Bool) → (ι → Bool) → ℝ)
    (hε : ∀ a b, a ⬝ᵥ b = true →
      Real.cos (π / 8) ^ 2 - ε a b ≤ TwoProverGame.chsh.commutingWinProb (G a b)) :
    𝔼 p, 𝔼 q, φ.norm (pauliFamily X Z p * pauliFamily X Z q - pauliFamily X Z (p * q)) ^ 2 ≤
      5 * (40 * 𝔼 c, φ.norm (Z c - Z'' c) ^ 2 + 32 * 𝔼 a, φ.norm (X a - X'' a) ^ 2 +
        33 * (9 * (𝔼 a, 𝔼 b, (if a ⬝ᵥ b = true then
            φ.norm (X a - ((G a b).alice false).observable) ^ 2 else 0) +
          𝔼 a, 𝔼 b, (if a ⬝ᵥ b = true then
            φ.norm (Z b - ((G a b).alice true).observable) ^ 2 else 0) +
          chshAnticommConst * 𝔼 a, 𝔼 b, (if a ⬝ᵥ b = true then ε a b else 0))) +
        𝔼 a, 𝔼 a', φ.norm (X a * X a' - X (a + a')) ^ 2 +
        33 * 𝔼 b, 𝔼 b', φ.norm (Z b * Z b' - Z (b + b')) ^ 2) := by
  have h₁ := expect_norm_pauliFamily_sub_sq_le_of_anticommute φ X Z X'' Z'' hX hZ hX'' hZ'' hXZ''
    hZZ'' hZX'' hX0
  have h₂ := expect_anticommDefectSq_le_of_chsh φ X Z G hφ hX hZ hG hXZ' hZX' ε hε
  refine h₁.trans ?_
  linarith

end Cslib.PCP
