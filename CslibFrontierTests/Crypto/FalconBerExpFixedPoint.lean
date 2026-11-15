/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.Falcon.BerExpFixedPoint
import Mathlib.Tactic.NormNum

/-!
# Tests for the Falcon v1.2 fixed-point BerExp connector

These ordinary-import clients check the maximum threshold and capped-shift endpoint, exact
acceptance masses, the positive-output boundary and the complete source/static resource ledger.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.FalconBerExpFixedPoint

open Cslib Cslib.Crypto.Falcon

public section

private abbrev zeroExponent : ApproxExpExponentInput := ⟨0, by norm_num [approxExpScale]⟩
private abbrev oneScaling : ApproxExpScalingInput := ⟨2 ^ 63, by norm_num [approxExpScale]⟩
private abbrev zeroShift : Fin 64 := ⟨0, by norm_num⟩
private abbrev cappedShift : Fin 64 := ⟨63, by norm_num⟩

private theorem endpointPositive :
    0 < approxExpFixedPoint zeroExponent oneScaling := by
  rw [approxExpFixedPoint_zero_x]
  norm_num [oneScaling]

/-- At `x63 = 0`, `ccs63 = 2^63` and shift zero, line 4 yields the largest 64-bit threshold. -/
#guard (berExpFixedPointThreshold zeroExponent oneScaling zeroShift endpointPositive).val ==
  2 ^ 64 - 1

/-- At the capped shift 63, the same maximal numerator yields threshold one. -/
#guard (berExpFixedPointThreshold zeroExponent oneScaling cappedShift endpointPositive).val == 1

example : 1 ≤ 2 * approxExpFixedPoint zeroExponent oneScaling :=
  berExpFixedPointThreshold_noUnderflow zeroExponent oneScaling endpointPositive

example :
    (berExpFixedPointThreshold zeroExponent oneScaling zeroShift endpointPositive).val < 2 ^ 64 :=
  berExpFixedPointThreshold_lt_twoPow64 zeroExponent oneScaling zeroShift endpointPositive

/-- The maximal threshold rejects exactly one of the `2^64` uniform words. -/
example :
    (ProbComp.eval
      (berExpFixedPointCoin zeroExponent oneScaling zeroShift endpointPositive) false).toReal =
        1 / (2 ^ 64 : ℝ) := by
  rw [PMF.toReal_false_eq_one_sub, eval_berExpFixedPointCoin_true_toReal]
  norm_num [approxExpFixedPoint_zero_x]

/-- The capped shift endpoint accepts exactly one of the `2^64` uniform words. -/
example :
    (ProbComp.eval
      (berExpFixedPointCoin zeroExponent oneScaling cappedShift endpointPositive) true).toReal =
        1 / (2 ^ 64 : ℝ) := by
  rw [eval_berExpFixedPointCoin_true_toReal]
  norm_num [approxExpFixedPoint_zero_x]

private abbrev endpointLedger : BerExpFixedPointLedger :=
  berExpFixedPointLedger zeroExponent oneScaling 100 2

#guard endpointLedger.approxExp.mulShiftCount == 13
#guard endpointLedger.approxExp.subtractionCount == 12
#guard endpointLedger.approxExp.randomBits == 0
#guard endpointLedger.approxExp.oracleQueries == 0
#guard endpointLedger.approxExp.handlerCalls == 0
#guard endpointLedger.thresholdDoublingCount == 1
#guard endpointLedger.thresholdSubtractionCount == 1
#guard endpointLedger.thresholdRightShiftCount == 1
#guard endpointLedger.thresholdWordComparisonCount == 1
#guard endpointLedger.randomBits == 64
#guard endpointLedger.oracleQueries == 0
#guard endpointLedger.handlerCalls == 0
#guard endpointLedger.coefficientTablePayloadBits == 832
#guard endpointLedger.controlProgramBits == 100
#guard endpointLedger.coefficientTableCopies == 2
#guard endpointLedger.retainedBits == 1764

example : endpointLedger.approxExp.mulShiftCount = 13 ∧
    endpointLedger.approxExp.subtractionCount = 12 ∧
    endpointLedger.thresholdDoublingCount = 1 ∧
    endpointLedger.thresholdSubtractionCount = 1 ∧
    endpointLedger.thresholdRightShiftCount = 1 ∧
    endpointLedger.thresholdWordComparisonCount = 1 :=
  berExpFixedPointLedger_operations zeroExponent oneScaling 100 2

example : endpointLedger.approxExp.randomBits = 0 ∧
    endpointLedger.approxExp.oracleQueries = 0 ∧
    endpointLedger.approxExp.handlerCalls = 0 ∧
    endpointLedger.randomBits = 64 ∧ endpointLedger.oracleQueries = 0 ∧
    endpointLedger.handlerCalls = 0 :=
  berExpFixedPointLedger_randomness zeroExponent oneScaling 100 2

example : endpointLedger.coefficientTablePayloadBits = 832 ∧
    endpointLedger.controlProgramBits = 100 ∧ endpointLedger.coefficientTableCopies = 2 ∧
    endpointLedger.retainedBits = 1764 := by
  simpa using berExpFixedPointLedger_staticSize zeroExponent oneScaling 100 2

end

end CslibFrontierTests.Crypto.FalconBerExpFixedPoint
