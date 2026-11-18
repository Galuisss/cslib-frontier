/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.ConsistencyTest
import CslibFrontier.Foundations.Data.BitString.OddPairs
import CslibFrontier.Foundations.Quantum.POVM
import CslibFrontier.Probability.PMF

/-! # Special-question consistency checks

A deterministic strategy on one-bit questions agrees on the first bit but disagrees on the
second. The corresponding accepting and rejecting rounds give probabilities one and zero.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ConsistencyTest

open Cslib Cslib.PCP Cslib.Quantum
open scoped ComplexOrder MatrixOrder

variable (φ : AlgState (Matrix (Fin 1) (Fin 1) ℂ))

private noncomputable def strategy :
    CommutingStrategy (((Unit → Bool) × (Unit → Bool)) × Bool)
      (((Unit → Bool) × (Unit → Bool)) × Bool) (Bool × Bool) Bool
      (Matrix (Fin 1) (Fin 1) ℂ) where
  state := φ
  alice _ := Measurement.const (false, true)
  bob _ := Measurement.const false
  commute _ _ a b := by
    simp only [Measurement.const]
    split_ifs <;> simp [Commute, SemiconjBy]

/-- The first coordinate agrees and the second one disagrees. -/
example :
    (pauliSpecialQuestionTest Unit false).commutingWinProb (strategy φ) = 1 ∧
      (pauliSpecialQuestionTest Unit true).commutingWinProb (strategy φ) = 0 := by
  let := BitString.oddPairs_nonempty (ι := Unit)
  constructor
  · rw [pauliSpecialQuestionTest, SeededGame.commutingWinProb_eq_sum,
      ← Probability.PMF.sum_toReal (Probability.PMF.uniformOfFintype ↥(BitString.oddPairs Unit))]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [SeededGame.bitAgreement, CommutingStrategy.prob, strategy, Measurement.const,
      Fintype.sum_prod_type, φ.map_one]
  · rw [pauliSpecialQuestionTest, SeededGame.commutingWinProb_eq_sum]
    simp [SeededGame.bitAgreement, CommutingStrategy.prob, strategy, Measurement.const,
      Fintype.sum_prod_type]

end CslibFrontierTests.ConsistencyTest
