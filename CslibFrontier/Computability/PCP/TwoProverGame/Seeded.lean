/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
import CslibFrontier.Probability.PMF.Event

/-!
# Two-prover games with private verifier randomness

In a `Cslib.PCP.TwoProverGame` the verifier's decision depends only on the questions and the
answers. Many verifiers keep randomness of their own: the linearity test selects which check to
run, the Pauli braiding test selects a subtest and a role for each player, and when two choices of
the private randomness produce the same questions, the verifier may still decide differently. A
**seeded game** (`Cslib.PCP.SeededGame`) records this: the verifier draws a seed `r ∼ seed`, sends
the questions `query r`, and accepts the answers `(a, b)` when `accepts r a b`. The players see
only the questions.

The winning probability of answer distributions `ans x y` (`Cslib.PCP.SeededGame.answersWinProb`),
and so of tensor-product and commuting-operator strategies
(`Cslib.PCP.SeededGame.quantumWinProb`, `Cslib.PCP.SeededGame.commutingWinProb`), is the
probability that the verifier accepts; for finite seeds and answers it is
`∑_r Pr[r] ∑_{a,b} [accepts r a b] Pr[(a, b) | query r]`
(`Cslib.PCP.SeededGame.answersWinProb_eq_sum`, `Cslib.PCP.SeededGame.commutingWinProb_eq_sum`).
Every two-prover game is a seeded game with the questions as the seed
(`Cslib.PCP.TwoProverGame.toSeeded`), with the same winning probabilities
(`Cslib.PCP.TwoProverGame.answersWinProb_toSeeded`).

## Main definitions

* `Cslib.PCP.SeededGame`: a two-prover game with private verifier randomness.
* `Cslib.PCP.SeededGame.answersWinProb`, `Cslib.PCP.SeededGame.quantumWinProb`,
  `Cslib.PCP.SeededGame.commutingWinProb`: winning probabilities.
* `Cslib.PCP.TwoProverGame.toSeeded`: a two-prover game as a seeded game.

## Main results

* `Cslib.PCP.SeededGame.answersWinProb_eq_sum`: the winning probability as a sum.
* `Cslib.PCP.TwoProverGame.answersWinProb_toSeeded`: two-prover games embed.
-/

@[expose] public section

namespace Cslib.PCP

open Finset Quantum

/-- A **two-prover game with private verifier randomness**: the verifier draws a seed `r` from
`seed`, sends the questions `query r`, and accepts the answers `(a, b)` when `accepts r a b`. -/
structure SeededGame (R X Y A B : Type*) where
  /-- The distribution of the verifier's seed. -/
  seed : PMF R
  /-- The questions sent on the seed `r`. -/
  query : R → X × Y
  /-- The verifier's decision on the seed `r` and the answers. -/
  accepts : R → A → B → Prop

namespace SeededGame

variable {R X Y A B : Type*} (G : SeededGame R X Y A B)

/-- The verdict of `G` on a seed and answers. -/
def AcceptsRound : R × A × B → Prop
  | (r, (a, b)) => G.accepts r a b

/-- The probability of winning `G` when the answers to questions `(x, y)` are drawn from
`ans x y`. -/
noncomputable def answersWinProb (ans : X → Y → PMF (A × B)) : ℝ :=
  ((G.seed.bind fun r => (ans (G.query r).1 (G.query r).2).map fun ab => (r, ab)).toOuterMeasure
    {z | G.AcceptsRound z}).toReal

theorem answersWinProb_nonneg (ans : X → Y → PMF (A × B)) : 0 ≤ G.answersWinProb ans :=
  ENNReal.toReal_nonneg

theorem answersWinProb_le_one (ans : X → Y → PMF (A × B)) : G.answersWinProb ans ≤ 1 :=
  (ENNReal.toReal_mono ENNReal.one_ne_top
    (Cslib.Probability.PMF.toOuterMeasure_le_one _ _)).trans_eq ENNReal.toReal_one

/-- The winning probability `∑_r Pr[r] ∑_{a,b} [accepts r a b] Pr[(a, b) | query r]`. -/
theorem answersWinProb_eq_sum [Fintype R] [Fintype A] [Fintype B]
    [∀ r a b, Decidable (G.accepts r a b)] (ans : X → Y → PMF (A × B)) :
    G.answersWinProb ans = ∑ r, (G.seed r).toReal * ∑ a, ∑ b,
      if G.accepts r a b then (ans (G.query r).1 (G.query r).2 (a, b)).toReal else 0 := by
  rw [answersWinProb, PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum
    fun r _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply,
    Cslib.Probability.PMF.toOuterMeasure_apply_toReal, ← Finset.univ_product_univ,
    Finset.sum_product]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, AcceptsRound]

/-- The probability that the tensor-product strategy `S` wins `G`. -/
noncomputable def quantumWinProb [Fintype A] [Fintype B] {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (S : QuantumStrategy X Y A B ι κ) : ℝ :=
  G.answersWinProb S.answers

section Commuting

variable {𝒜 : Type*} [Fintype A] [Fintype B] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- The probability that the commuting-operator strategy `S` wins `G`. -/
noncomputable def commutingWinProb (S : CommutingStrategy X Y A B 𝒜) : ℝ :=
  G.answersWinProb S.answers

/-- The winning probability of a commuting-operator strategy:
`∑_r Pr[r] ∑_{a,b} [accepts r a b] Re φ(P_x^a Q_y^b)` with `(x, y) = query r`. -/
theorem commutingWinProb_eq_sum [Fintype R] [∀ r a b, Decidable (G.accepts r a b)]
    (S : CommutingStrategy X Y A B 𝒜) :
    G.commutingWinProb S = ∑ r, (G.seed r).toReal * ∑ a, ∑ b,
      if G.accepts r a b then S.prob (G.query r).1 (G.query r).2 a b else 0 := by
  rw [commutingWinProb, answersWinProb_eq_sum]
  simp only [S.answers_apply, ENNReal.toReal_ofReal (S.prob_nonneg _ _ _ _)]

end Commuting

end SeededGame

namespace TwoProverGame

variable {X Y A B : Type*} (G : TwoProverGame X Y A B)

/-- A two-prover game as a seeded game: the seed is the pair of questions. -/
def toSeeded : SeededGame (X × Y) X Y A B where
  seed := G.questions
  query := id
  accepts q a b := G.accepts q.1 q.2 a b

/-- A two-prover game and its seeded form have the same winning probabilities. -/
theorem answersWinProb_toSeeded (ans : X → Y → PMF (A × B)) :
    G.toSeeded.answersWinProb ans = G.answersWinProb ans :=
  rfl

end TwoProverGame

end Cslib.PCP
