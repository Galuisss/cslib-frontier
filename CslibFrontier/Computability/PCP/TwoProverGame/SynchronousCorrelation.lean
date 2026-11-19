/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
import CslibFrontier.Foundations.Quantum.Algebra.MeasurementDistance

/-!
# Moving a projective measurement to the other player's system

The error in the joint probabilities is controlled by the state-dependent distance between the
original measurement and its replacement on Bob's space. The estimate uses the full sum over
both answer sets, as in the switching argument of [Vidick2022].
-/

public section

open Cslib.Quantum Matrix
open scoped MatrixOrder Kronecker

namespace Cslib.PCP.QuantumStrategy

variable {ι κ X Y A B : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype A] [Fintype B]

/-- Replacing Alice's projective measurement by operators on Bob's space changes the joint
weights by at most twice the state-dependent distance between the two families. -/
theorem sum_abs_prob_sub_re_apply_conjugation_le (S : QuantumStrategy X Y A B ι κ)
    (x : X) (y : Y) (N : POVM A κ)
    (hP : ∀ a, (S.alice x).effect a * (S.alice x).effect a = (S.alice x).effect a) :
    (∑ a, ∑ b, |S.prob x y a b -
        (S.toCommuting.state ((1 ⊗ₖ N.effect a) * (S.toCommuting.bob y).effect b *
          (1 ⊗ₖ N.effect a))).re|) ≤
      2 * √(∑ a, S.toCommuting.state.norm
        ((S.toCommuting.alice x).effect a - 1 ⊗ₖ N.effect a) ^ 2) := by
  have hproj : (S.toCommuting.alice x).IsProjective := by
    intro a
    change ((S.alice x).effect a ⊗ₖ (1 : Matrix κ κ ℂ)) *
      ((S.alice x).effect a ⊗ₖ 1) = (S.alice x).effect a ⊗ₖ 1
    rw [← Matrix.mul_kronecker_mul, hP a, Matrix.one_mul]
  simp_rw [← S.prob_toCommuting]
  exact (S.toCommuting.bob y).sum_abs_re_apply_effect_mul_sub_conjugation_le
    S.toCommuting.state (S.toCommuting.alice x) (rightMeasurement N) hproj
    (S.toCommuting.commute x y)

end Cslib.PCP.QuantumStrategy
