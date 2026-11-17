/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.Linearity

/-! # The two-player linearity test

Checked clients: the acceptance probability of a matching check as a correlation, and linearity
of the point player's observables from the winning probability. A concrete instance: the honest
linear answers `γ = s·c`, `(α, β) = (s·a, s·b)` pass every check, for every query triple, so the
test is complete for the linear functions.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearityGame

open Cslib Cslib.PCP Cslib.Quantum Finset Matrix
open scoped BigOperators

/-- The acceptance probability of `γ = g(r)` as a correlation. -/
example {X Y B 𝒜 : Type} [Fintype B] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [Algebra ℂ 𝒜] (S : CommutingStrategy X Y Bool B 𝒜) (g : B → Bool) (x : X) (y : Y) :
    ∑ γ, ∑ r, (if γ = g r then S.prob x y γ r else 0) =
      (1 + (S.state ((S.alice x).observable * ((S.bob y).map g).observable)).re) / 2 :=
  CommutingStrategy.sum_ite_prob_eq S g x y

/-- **Winning the linearity test** makes the point player's observables linear on average. -/
example {n 𝒜 : Type} [Fintype n] [DecidableEq n] [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜]
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜)
    (hA : ∀ c, (S.alice c).IsProjective) (hB : ∀ q, (S.bob q).IsProjective) {ε : ℝ}
    (hε : 1 - ε ≤ (linearityTest n).commutingWinProb S) :
    1 - 6 * ε - √(12 * ε) - √(12 * ε) ≤
      𝔼 a, 𝔼 b, (S.state ((S.alice a).observable * (S.alice b).observable *
        (S.alice (a + b)).observable)).re :=
  CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest S hA hB hε

/-- **Completeness for linear functions** (concrete, two bits): the honest answers of the linear
function `c ↦ s·c` pass every check of the linearity test. -/
example : ∀ s a b : Fin 2 → Bool, ∀ k : Fin 3,
    (linearityTest (Fin 2)).accepts (linearityQuery k a b) (a, b) (s ⬝ᵥ linearityQuery k a b)
      (s ⬝ᵥ a, s ⬝ᵥ b) := by
  decide

end CslibFrontierTests.LinearityGame
