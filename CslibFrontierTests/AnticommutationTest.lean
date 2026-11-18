/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.AnticommutationTest
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # The anticommutation test

Checked clients: anticommutation of the linearity-test observables from the CHSH anticommutation
test and consistency, in any star-ordered algebra with a continuous functional calculus. A concrete
instance: the optimal EPR strategy for CHSH wins with probability exactly `cos²(π/8)`, so the
squared anticommutation defect of its first player's observables is `0` in its state.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.AnticommutationTest

open Cslib Cslib.PCP Cslib.Quantum Finset Matrix
open scoped BigOperators Real MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- **Anticommutation from the CHSH anticommutation test and consistency.** -/
example {ι 𝒜 : Type} [Fintype ι] [DecidableEq ι] [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] (φ : AlgState 𝒜) (X Z : (ι → Bool) → 𝒜)
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
        chshAnticommConst * 𝔼 a, 𝔼 b, (if a ⬝ᵥ b = true then ε a b else 0)) :=
  expect_anticommDefectSq_le_of_chsh φ X Z G hφ hX hZ hG hXZ' hZX' ε hε

/-- **Concrete instance**: the optimal EPR strategy's first-player observables anticommute
exactly in its state. -/
example : TwoProverGame.chshEPR.toCommuting.state.norm
    ((TwoProverGame.chshEPR.toCommuting.alice false).observable *
        (TwoProverGame.chshEPR.toCommuting.alice true).observable +
      (TwoProverGame.chshEPR.toCommuting.alice true).observable *
        (TwoProverGame.chshEPR.toCommuting.alice false).observable) ^ 2 ≤ 0 := by
  have h := norm_anticomm_sq_le_of_chsh TwoProverGame.chshEPR.toCommuting (ε := 0) (by
    rw [TwoProverGame.commutingWinProb_toCommuting, TwoProverGame.quantumWinProb_chsh_chshEPR,
      sub_zero])
  simpa using h

end CslibFrontierTests.AnticommutationTest
