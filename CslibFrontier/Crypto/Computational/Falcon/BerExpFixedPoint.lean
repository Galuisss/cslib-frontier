/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Falcon.ApproxExp
public import CslibFrontier.Crypto.Computational.Falcon.BerExp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega

/-!
# Falcon v1.2 fixed-point BerExp connector

Falcon v1.2 Algorithm 14 line 4 converts Algorithm 13's fixed-point output `y` into the 64-bit
threshold `(2 * y - 1) >> s`, where `s` has already been capped at 63. This module connects the
exact rounded-input `ApproxExp` core to the exact 64-bit threshold coin. It requires positivity of
the fixed-point output explicitly: the wider total input type includes `ccs63 = 0`, and natural
subtraction must not silently model the reference C implementation's unsigned underflow there.

`berExpFixedPointCoin` draws a fixed 64 fair bits and performs one strict word comparison. It has
the same conditional acceptance mass as Algorithm 14 after its threshold has been computed, but
not the reference implementation's lazy one-to-eight-byte consumption trace. The source ledger
records the thirteen `ApproxExp` multiply/shifts, twelve Horner subtractions, one threshold
doubling, subtraction and right shift, one word comparison and 64 random bits. These are
source-level operations, not native steps. Its retained-size coordinate reuses the exact 832-bit
coefficient payload and charges each installed table occurrence, while leaving the control-program
encoding length explicit.

This is not a floating-point model: it does not construct `s` or the rounded inputs from real
values, prove positivity from SamplerZ's range, bound approximation error, or prove a Gaussian
sampling, retry, runtime, workspace, security or asymptotic theorem. It also does not claim
conformance with the still-developing FN-DSA / FIPS 206 interface ([NISTPQC2026]).

## Main definitions

* `Cslib.Crypto.Falcon.berExpFixedPointThreshold`: Algorithm 14 line 4 on bounded integer inputs.
* `Cslib.Crypto.Falcon.berExpFixedPointCoin`: the composed exact 64-bit threshold experiment.
* `Cslib.Crypto.Falcon.BerExpFixedPointLedger`,
  `Cslib.Crypto.Falcon.berExpFixedPointLedger`: the composed source-operation, randomness and
  retained-size ledger.

## Main results

* `Cslib.Crypto.Falcon.berExpFixedPointThreshold_noUnderflow`: the explicit positivity premise
  makes line 4's subtraction nontruncating.
* `Cslib.Crypto.Falcon.berExpFixedPointThreshold_val`: the threshold is exactly the source formula.
* `Cslib.Crypto.Falcon.berExpFixedPointThreshold_lt_twoPow64`: the threshold fits the unsigned
  64-bit range.
* `Cslib.Crypto.Falcon.eval_berExpFixedPointCoin_true`: the composed acceptance mass is exactly the
  constructed threshold divided by `2^64`.
* `Cslib.Crypto.Falcon.berExpFixedPointLedger_operations`,
  `Cslib.Crypto.Falcon.berExpFixedPointLedger_randomness`,
  `Cslib.Crypto.Falcon.berExpFixedPointLedger_staticSize`: exact ledger coordinates.

## References

* [Falcon team, *Falcon: Fast-Fourier Lattice-based Compact Signatures over NTRU*, Round 3
  submission, version 1.2][Falcon2020], Section 3.9.3, Algorithms 13--15; especially Algorithm 14,
  lines 1--10.
* Pinned [Falcon2020] archive,
  `Reference_Implementation/falcon512/falcon512int/sign.c::BerExp`, lines 1043--1087 (threshold at
  line 1074), and `sampler`, lines 1107--1173.
* [National Institute of Standards and Technology, *Post-Quantum Cryptography
  Standardization*][NISTPQC2026].
-/

public section

namespace Cslib.Crypto.Falcon

open Probability

/-- Algorithm 14 line 4 after `ApproxExp` and the capped shift have been computed.

The positivity premise excludes the total extension's zero-output case, where natural subtraction
would truncate while the reference C expression uses unsigned arithmetic. -/
@[expose] def berExpFixedPointThreshold
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) (shift : Fin 64)
    (hpositive : 0 < approxExpFixedPoint x63 ccs63) : BerExpThreshold :=
  ⟨(2 * approxExpFixedPoint x63 ccs63 - 1) / 2 ^ shift.val, by
    have houtput := approxExpFixedPoint_le_scale x63 ccs63
    have hnontrunc : 1 ≤ 2 * approxExpFixedPoint x63 ccs63 := by omega
    have hnumerator : 2 * approxExpFixedPoint x63 ccs63 - 1 < 2 ^ 64 := by
      norm_num [approxExpScale] at houtput ⊢
      omega
    exact (Nat.div_le_self _ _).trans_lt hnumerator⟩

/-- The positive-output premise makes Algorithm 14 line 4's subtraction nontruncating. -/
theorem berExpFixedPointThreshold_noUnderflow
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput)
    (hpositive : 0 < approxExpFixedPoint x63 ccs63) :
    1 ≤ 2 * approxExpFixedPoint x63 ccs63 := by
  omega

/-- The constructed threshold is exactly Algorithm 14 line 4's integer formula. -/
@[simp] theorem berExpFixedPointThreshold_val
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) (shift : Fin 64)
    (hpositive : 0 < approxExpFixedPoint x63 ccs63) :
    (berExpFixedPointThreshold x63 ccs63 shift hpositive).val =
      (2 * approxExpFixedPoint x63 ccs63 - 1) / 2 ^ shift.val := by
  rfl

/-- The constructed threshold fits strictly below the unsigned 64-bit modulus. -/
theorem berExpFixedPointThreshold_lt_twoPow64
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) (shift : Fin 64)
    (hpositive : 0 < approxExpFixedPoint x63 ccs63) :
    (berExpFixedPointThreshold x63 ccs63 shift hpositive).val < 2 ^ 64 :=
  (berExpFixedPointThreshold x63 ccs63 shift hpositive).isLt

/-- The fixed-point `ApproxExp` output composed with Algorithm 14's exact threshold coin. -/
noncomputable def berExpFixedPointCoin
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) (shift : Fin 64)
    (hpositive : 0 < approxExpFixedPoint x63 ccs63) : ProbComp Bool :=
  berExpThresholdCoin (berExpFixedPointThreshold x63 ccs63 shift hpositive)

/-- The composed coin accepts with the exact constructed threshold divided by `2^64`. -/
theorem eval_berExpFixedPointCoin_true
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) (shift : Fin 64)
    (hpositive : 0 < approxExpFixedPoint x63 ccs63) :
    ProbComp.eval (berExpFixedPointCoin x63 ccs63 shift hpositive) true =
      (((2 * approxExpFixedPoint x63 ccs63 - 1) / 2 ^ shift.val : ℕ) : ENNReal) /
        2 ^ 64 := by
  simpa only [berExpFixedPointCoin, berExpFixedPointThreshold_val] using
    eval_berExpThresholdCoin_true (berExpFixedPointThreshold x63 ccs63 shift hpositive)

/-- Real-valued form of the exact composed acceptance mass. -/
theorem eval_berExpFixedPointCoin_true_toReal
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) (shift : Fin 64)
    (hpositive : 0 < approxExpFixedPoint x63 ccs63) :
    (ProbComp.eval (berExpFixedPointCoin x63 ccs63 shift hpositive) true).toReal =
      (((2 * approxExpFixedPoint x63 ccs63 - 1) / 2 ^ shift.val : ℕ) : ℝ) /
        2 ^ 64 := by
  simpa only [berExpFixedPointCoin, berExpFixedPointThreshold_val] using
    eval_berExpThresholdCoin_true_toReal
      (berExpFixedPointThreshold x63 ccs63 shift hpositive)

/-- Source-operation, randomness and retained-size ledger for the fixed-point BerExp composition.

The single word comparison and 64 random bits describe the denotational experiment, not the
reference implementation's lazy byte trace. `controlProgramBits` is supplied by a future concrete
encoder, and `coefficientTableCopies` counts installed occurrences. -/
structure BerExpFixedPointLedger where
  /-- The structurally linked Algorithm 13 run and its deterministic ledger. -/
  approxExp : ApproxExpRun
  /-- Doublings used to scale the ApproxExp output from 63 to 64 fractional bits. -/
  thresholdDoublingCount : ℕ
  /-- Subtractions used to replace a possible `2^64` endpoint by `2^64 - 1`. -/
  thresholdSubtractionCount : ℕ
  /-- Right shifts by the capped exponent. -/
  thresholdRightShiftCount : ℕ
  /-- Strict 64-bit comparisons in the denotational threshold experiment. -/
  thresholdWordComparisonCount : ℕ
  /-- Fair random bits drawn by the denotational threshold experiment. -/
  randomBits : ℕ
  /-- External oracle queries. -/
  oracleQueries : ℕ
  /-- External handler calls. -/
  handlerCalls : ℕ
  /-- Unframed payload of one installed coefficient table. -/
  coefficientTablePayloadBits : ℕ
  /-- Caller-supplied encoded control-program length. -/
  controlProgramBits : ℕ
  /-- Number of installed coefficient-table occurrences. -/
  coefficientTableCopies : ℕ
  /-- Control-program bits plus all installed coefficient-table payloads. -/
  retainedBits : ℕ
  deriving DecidableEq

/-- The source ledger for one fixed-point ApproxExp/threshold-coin composition. -/
@[expose] def berExpFixedPointLedger
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput)
    (controlProgramBits coefficientTableCopies : ℕ) : BerExpFixedPointLedger :=
  ⟨approxExpRun x63 ccs63, 1, 1, 1, 1, 64, 0, 0, approxExpTablePayloadBits,
    controlProgramBits, coefficientTableCopies,
    approxExpRetainedBits controlProgramBits coefficientTableCopies⟩

/-- The composed ledger records the exact source-level arithmetic and comparison counts. -/
theorem berExpFixedPointLedger_operations
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput)
    (controlProgramBits coefficientTableCopies : ℕ) :
    (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).approxExp.mulShiftCount = 13 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).approxExp.subtractionCount = 12 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).thresholdDoublingCount = 1 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).thresholdSubtractionCount = 1 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).thresholdRightShiftCount = 1 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).thresholdWordComparisonCount = 1 := by
  have hcounts := approxExpRun_ledger x63 ccs63
  dsimp only [berExpFixedPointLedger]
  exact ⟨hcounts.1, hcounts.2, rfl, rfl, rfl, rfl⟩

/-- The composed ledger retains ApproxExp's zero external-resource coordinates and charges the
fixed 64 fair bits of the denotational coin. -/
theorem berExpFixedPointLedger_randomness
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput)
    (controlProgramBits coefficientTableCopies : ℕ) :
    (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).approxExp.randomBits = 0 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).approxExp.oracleQueries = 0 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).approxExp.handlerCalls = 0 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).randomBits = 64 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).oracleQueries = 0 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).handlerCalls = 0 := by
  have hresources := approxExpRun_deterministicResources x63 ccs63
  dsimp only [berExpFixedPointLedger]
  exact ⟨hresources.1, hresources.2.1, hresources.2.2, rfl, rfl, rfl⟩

/-- The composed ledger reuses the exact table payload and charges every installed occurrence.

The result is a retained-size formula, not a concrete native control-program encoding theorem. -/
theorem berExpFixedPointLedger_staticSize
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput)
    (controlProgramBits coefficientTableCopies : ℕ) :
    (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).coefficientTablePayloadBits = 832 ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).controlProgramBits = controlProgramBits ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).coefficientTableCopies = coefficientTableCopies ∧
      (berExpFixedPointLedger x63 ccs63 controlProgramBits
        coefficientTableCopies).retainedBits =
          controlProgramBits + coefficientTableCopies * 832 := by
  simp [berExpFixedPointLedger, approxExpRetainedBits]

end Cslib.Crypto.Falcon
