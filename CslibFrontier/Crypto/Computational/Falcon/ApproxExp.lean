/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega

/-!
# Falcon v1.2 ApproxExp fixed-point core

Falcon v1.2 Algorithm 13 evaluates a degree-twelve polynomial with thirteen 64-bit coefficients.
After the real inputs have been rounded to `x63 = ⌊2^63 x⌋` and
`ccs63 = ⌊2^63 ccs⌋`, each Horner product is shifted right by 63 bits. This module implements
that exact integer recurrence. The inputs are intrinsically bounded by `2^63`; values with
`x63 > ⌊2^63 ln 2⌋` are a total bounded extension, not Falcon source inputs.

`approxExp_horner_safe` verifies the source's intermediate arithmetic claim: at every round the
state is at most `2^63`, the subtrahend is at most the next coefficient, and hence natural-number
subtraction does not truncate. `approxExp_hornerProduct_lt_twoPow126` separately gives the
source's strict 126-bit Horner-product bound. The published Algorithm 13 includes the endpoint
`ccs = 1`; its final scaling product can equal `2^126` at `x = 0`, so it is stated separately with
a non-strict bound. The pinned
integer reference implementation instead realizes sub-unit fixed-point multiplication by
doubling a scaled input and taking the high 64 product bits. This module does not formalize the
floating-point conversion or assert reference-C equivalence at endpoint representability cases.

The coefficient payload is exactly `13 * 64 = 832` unframed bits. The retained-size account
`approxExpRetainedBits` adds one such payload for each installed table occurrence to a
caller-supplied control-program encoding length. It is not a native program encoder, step count,
workspace bound, or replacement for the shared attack-resource profile. The deterministic core
uses no randomness, oracle, or handler. `approxExpRun` structurally records the source-level
multiply/shift and subtraction ledger together with exact zero random-bit, oracle-query and
handler-call coordinates; these operation counts are not machine-step costs.

This module proves neither a numerical approximation-error bound nor a Gaussian sampling or
security theorem. NIST lists FN-DSA / FIPS 206 as still under development as of 13 November 2026
([NISTPQC2026]); this Falcon v1.2 component does not claim conformance with that future standard.

## Main definitions

* `Cslib.Crypto.Falcon.ApproxExpExponentInput`: rounded `x` values below `2^63`.
* `Cslib.Crypto.Falcon.ApproxExpScalingInput`: rounded `ccs` values in `0, ..., 2^63`.
* `Cslib.Crypto.Falcon.approxExpCoefficients`: Algorithm 13's thirteen 64-bit coefficients.
* `Cslib.Crypto.Falcon.ApproxExpRun`, `Cslib.Crypto.Falcon.approxExpRun`: the result and
  source-operation ledger.
* `Cslib.Crypto.Falcon.approxExpFixedPoint`: the exact rounded-input Algorithm 13 recurrence.
* `Cslib.Crypto.Falcon.approxExpRetainedBits`: occurrence-aware table and control-program
  retained size.

## Main results

* `Cslib.Crypto.Falcon.approxExp_horner_safe`: every Horner subtraction and intermediate state is
  within the published fixed-point bounds.
* `Cslib.Crypto.Falcon.approxExp_hornerProduct_lt_twoPow126`: every Horner product is strictly
  below `2^126`.
* `Cslib.Crypto.Falcon.approxExp_scalingProduct_le_twoPow126`: the final scaling product is at
  most `2^126`.
* `Cslib.Crypto.Falcon.approxExpRun_ledger`: every complete run records exactly thirteen
  multiply/shifts and twelve subtractions.
* `Cslib.Crypto.Falcon.approxExpRun_deterministicResources`: every complete run records zero
  random bits, oracle queries and handler calls.
* `Cslib.Crypto.Falcon.approxExpFixedPoint_zero_x`,
  `Cslib.Crypto.Falcon.approxExpFixedPoint_zero_ccs`: endpoint behavior.

## References

* [Falcon team, *Falcon: Fast-Fourier Lattice-based Compact Signatures over NTRU*, Round 3
  submission, version 1.2][Falcon2020], Section 3.9.3, Algorithm 13.
* Pinned [Falcon2020] archive,
  `Reference_Implementation/falcon512/falcon512int/fpr.c::fpr_expm_p63`, lines 514--598.
* [National Institute of Standards and Technology, *Post-Quantum Cryptography
  Standardization*][NISTPQC2026].
-/

public section

namespace Cslib.Crypto.Falcon

/-- The fixed-point scale used by Falcon v1.2 Algorithm 13. -/
@[expose] def approxExpScale : ℕ := 2 ^ 63

/-- A rounded Algorithm 13 exponent input below `2^63`.

For source calls, `x63` additionally comes from an `x ∈ [0, ln 2]`; the wider type is a total
bounded extension. -/
abbrev ApproxExpExponentInput := Fin approxExpScale

/-- A rounded Algorithm 13 scaling input in `0, ..., 2^63`, including published endpoint
`ccs = 1`. -/
abbrev ApproxExpScalingInput := Fin (approxExpScale + 1)

/-- The thirteen 64-bit coefficients `C[0], ..., C[12]` from Falcon v1.2 Algorithm 13. -/
@[expose] def approxExpCoefficients : List ℕ :=
  [0x00000004741183A3,
   0x00000036548CFC06,
   0x0000024FDCBF140A,
   0x0000171D939DE045,
   0x0000D00CF58F6F84,
   0x000680681CF796E3,
   0x002D82D8305B0FEA,
   0x011111110E066FD0,
   0x0555555555070F00,
   0x155555555581FF00,
   0x400000000002B400,
   0x7FFFFFFFFFFF4800,
   0x8000000000000000]

@[simp] theorem approxExpCoefficients_length : approxExpCoefficients.length = 13 := by
  rfl

/-- Multiply two fixed-point integers and shift the exact product right by 63 bits. -/
@[expose] def approxExpMulShift63 (a b : ℕ) : ℕ :=
  a * b / approxExpScale

/-- The output and source-operation ledger of an Algorithm 13 evaluation. -/
structure ApproxExpRun where
  /-- Fixed-point output of this run. -/
  output : ℕ
  /-- Number of fixed-point multiply/shift operations. -/
  mulShiftCount : ℕ
  /-- Number of subtractions. -/
  subtractionCount : ℕ
  /-- Number of random bits consumed. -/
  randomBits : ℕ
  /-- Number of external oracle queries. -/
  oracleQueries : ℕ
  /-- Number of external handler calls. -/
  handlerCalls : ℕ
  deriving DecidableEq

/-- Instrumented Horner evaluation after the initial coefficient has been loaded. -/
@[expose] def approxExpHornerRun (x63 : ApproxExpExponentInput) : ℕ → List ℕ → ApproxExpRun
  | y, [] => ⟨y, 0, 0, 0, 0, 0⟩
  | y, coefficient :: coefficients =>
      let run := approxExpHornerRun x63
        (coefficient - approxExpMulShift63 x63.val y) coefficients
      ⟨run.output, run.mulShiftCount + 1, run.subtractionCount + 1,
        run.randomBits, run.oracleQueries, run.handlerCalls⟩

/-- Output projection of the instrumented Horner evaluation. -/
@[expose] def approxExpHorner
    (x63 : ApproxExpExponentInput) (y : ℕ) (coefficients : List ℕ) : ℕ :=
  (approxExpHornerRun x63 y coefficients).output

/-- The Horner ledger contains one multiply/shift for every consumed coefficient. -/
@[simp] theorem approxExpHornerRun_mulShiftCount
    (x63 : ApproxExpExponentInput) (y : ℕ) (coefficients : List ℕ) :
    (approxExpHornerRun x63 y coefficients).mulShiftCount = coefficients.length := by
  induction coefficients generalizing y with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp [approxExpHornerRun, ih]

/-- The Horner ledger contains one subtraction for every consumed coefficient. -/
@[simp] theorem approxExpHornerRun_subtractionCount
    (x63 : ApproxExpExponentInput) (y : ℕ) (coefficients : List ℕ) :
    (approxExpHornerRun x63 y coefficients).subtractionCount = coefficients.length := by
  induction coefficients generalizing y with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp [approxExpHornerRun, ih]

/-- The deterministic Horner core consumes no random bits and makes no external oracle or handler
calls. -/
theorem approxExpHornerRun_deterministicResources
    (x63 : ApproxExpExponentInput) (y : ℕ) (coefficients : List ℕ) :
    (approxExpHornerRun x63 y coefficients).randomBits = 0 ∧
      (approxExpHornerRun x63 y coefficients).oracleQueries = 0 ∧
      (approxExpHornerRun x63 y coefficients).handlerCalls = 0 := by
  induction coefficients generalizing y with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simpa only [approxExpHornerRun] using ih _

/-- Every state and subtraction in a Horner suffix is within Algorithm 13's integer range. -/
@[expose] def ApproxExpHornerSafe (x63 : ApproxExpExponentInput) : ℕ → List ℕ → Prop
  | y, [] => y ≤ approxExpScale
  | y, coefficient :: coefficients =>
      y ≤ approxExpScale ∧
        approxExpMulShift63 x63.val y ≤ coefficient ∧
        ApproxExpHornerSafe x63
          (coefficient - approxExpMulShift63 x63.val y) coefficients

private theorem approxExpMulShift63_le_right {a b : ℕ} (ha : a ≤ approxExpScale) :
    approxExpMulShift63 a b ≤ b := by
  unfold approxExpMulShift63
  calc
    a * b / approxExpScale ≤ approxExpScale * b / approxExpScale :=
      Nat.div_le_div_right (Nat.mul_le_mul_right b ha)
    _ = b := by simp [approxExpScale, Nat.mul_comm]

/-- A Horner product is strictly below `2^126`, as required by the published 126-bit
intermediate bound. -/
theorem approxExp_hornerProduct_lt_twoPow126 (x63 : ApproxExpExponentInput) {y : ℕ}
    (hy : y ≤ approxExpScale) : x63.val * y < 2 ^ 126 := by
  have hx : x63.val ≤ approxExpScale - 1 := by omega
  calc
    x63.val * y ≤ (approxExpScale - 1) * approxExpScale := Nat.mul_le_mul hx hy
    _ < 2 ^ 126 := by norm_num [approxExpScale, ← pow_add]

/-- The final scaling product is at most `2^126`. Unlike the Horner products, equality occurs at
the published endpoint `x = 0`, `ccs = 1`, where the Horner result and `ccs63` are both `2^63`.
The exact-natural implementation retains that product before shifting it right by 63 bits. -/
theorem approxExp_scalingProduct_le_twoPow126 (ccs63 : ApproxExpScalingInput) {y : ℕ}
    (hy : y ≤ approxExpScale) : ccs63.val * y ≤ 2 ^ 126 := by
  calc
    ccs63.val * y ≤ approxExpScale * approxExpScale :=
      Nat.mul_le_mul (Nat.le_of_lt_succ ccs63.isLt) hy
    _ = 2 ^ 126 := by norm_num [approxExpScale, ← pow_add]

private theorem approxExpHornerSafe_of_chain (x63 : ApproxExpExponentInput) :
    ∀ (coefficients : List ℕ) (previous y : ℕ),
      (previous :: coefficients).IsChain (· ≤ ·) →
      (∀ coefficient ∈ previous :: coefficients, coefficient ≤ approxExpScale) →
      y ≤ previous → ApproxExpHornerSafe x63 y coefficients := by
  intro coefficients
  induction coefficients with
  | nil =>
      intro previous y _ hbounded hy
      simpa only [ApproxExpHornerSafe] using
        hy.trans (hbounded previous (by simp))
  | cons coefficient coefficients ih =>
      intro previous y hchain hbounded hy
      have hprevious : previous ≤ coefficient :=
        (List.isChain_cons_cons.mp hchain).1
      have hmul : approxExpMulShift63 x63.val y ≤ coefficient :=
        (approxExpMulShift63_le_right (Nat.le_of_lt x63.isLt)).trans
          (hy.trans hprevious)
      simp only [ApproxExpHornerSafe]
      refine ⟨hy.trans (hbounded previous (by simp)), hmul, ?_⟩
      apply ih coefficient
      · exact (List.isChain_cons_cons.mp hchain).2
      · intro c hc
        exact hbounded c (List.mem_cons_of_mem previous hc)
      · exact Nat.sub_le coefficient _

private theorem approxExpCoefficients_isChain :
    approxExpCoefficients.IsChain (· ≤ ·) := by
  norm_num [approxExpCoefficients]

private theorem approxExpCoefficient_le_scale (coefficient : ℕ)
    (hcoefficient : coefficient ∈ approxExpCoefficients) :
    coefficient ≤ approxExpScale := by
  simp only [approxExpCoefficients, List.mem_cons, List.mem_singleton] at hcoefficient
  rcases hcoefficient with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    norm_num [approxExpScale]

/-- All twelve Horner rounds satisfy the bounded-state and no-underflow invariants asserted after
Algorithm 13. Combined with `approxExp_hornerProduct_lt_twoPow126`, this verifies every intermediate
arithmetic obligation needed to interpret the recurrence over unbounded naturals. -/
theorem approxExp_horner_safe (x63 : ApproxExpExponentInput) :
    ApproxExpHornerSafe x63 (approxExpCoefficients.headD 0)
      approxExpCoefficients.tail := by
  apply approxExpHornerSafe_of_chain x63
  · simpa only [approxExpCoefficients] using approxExpCoefficients_isChain
  · intro coefficient hcoefficient
    apply approxExpCoefficient_le_scale coefficient
    simpa only [approxExpCoefficients] using hcoefficient
  · rfl

private theorem approxExpHorner_le_scale (x63 : ApproxExpExponentInput) :
    ∀ (y : ℕ) (coefficients : List ℕ), ApproxExpHornerSafe x63 y coefficients →
      approxExpHorner x63 y coefficients ≤ approxExpScale := by
  intro y coefficients
  induction coefficients generalizing y with
  | nil => simpa only [approxExpHorner, approxExpHornerRun, ApproxExpHornerSafe]
  | cons coefficient coefficients ih =>
      intro hsafe
      simpa only [approxExpHorner, approxExpHornerRun] using ih _ hsafe.2.2

/-- Complete instrumented Algorithm 13 evaluation. The final scaling contributes one additional
multiply/shift and no subtraction beyond the Horner ledger. -/
@[expose] def approxExpRun
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) : ApproxExpRun :=
  let horner := approxExpHornerRun x63
    (approxExpCoefficients.headD 0) approxExpCoefficients.tail
  ⟨approxExpMulShift63 ccs63.val horner.output,
    horner.mulShiftCount + 1, horner.subtractionCount,
    horner.randomBits, horner.oracleQueries, horner.handlerCalls⟩

/-- Falcon v1.2 Algorithm 13 after both real inputs have been rounded to 63-bit fixed-point
integers. This follows the published recurrence, including its `ccs63 = 2^63` endpoint. At
`x63 = 0` and `ccs63 = 2^63`, the exact final product is `2^126` before division by `2^63`;
reference-C equivalence at that endpoint is not asserted. -/
@[expose] def approxExpFixedPoint
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) : ℕ :=
  (approxExpRun x63 ccs63).output

/-- The rounded fixed-point result stays in `0, ..., 2^63`. -/
theorem approxExpFixedPoint_le_scale
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) :
    approxExpFixedPoint x63 ccs63 ≤ approxExpScale := by
  simp only [approxExpFixedPoint, approxExpRun]
  exact (approxExpMulShift63_le_right (Nat.le_of_lt_succ ccs63.isLt)).trans
    (approxExpHorner_le_scale x63 _ _ (approxExp_horner_safe x63))

/-- At `x = 0`, Algorithm 13 returns the rounded scaling factor exactly. -/
@[simp] theorem approxExpFixedPoint_zero_x (ccs63 : ApproxExpScalingInput) :
    approxExpFixedPoint ⟨0, by norm_num [approxExpScale]⟩ ccs63 = ccs63.val := by
  simp [approxExpFixedPoint, approxExpRun, approxExpHornerRun, approxExpCoefficients,
    approxExpMulShift63, approxExpScale]

/-- A zero scaling factor makes the Algorithm 13 result zero. -/
@[simp] theorem approxExpFixedPoint_zero_ccs (x63 : ApproxExpExponentInput) :
    approxExpFixedPoint x63 ⟨0, by norm_num [approxExpScale]⟩ = 0 := by
  simp [approxExpFixedPoint, approxExpRun, approxExpMulShift63]

/-- Number of Horner rounds, derived from the single coefficient table. -/
@[expose] def approxExpHornerRounds : ℕ := approxExpCoefficients.length - 1

/-- Number of fixed-point multiply/shift operations: twelve Horner products and final scaling. -/
@[expose] def approxExpMulShiftCount : ℕ := approxExpHornerRounds + 1

/-- Number of subtractions in the Horner recurrence. -/
@[expose] def approxExpSubtractionCount : ℕ := approxExpHornerRounds

/-- Unframed payload of the single 13-entry, 64-bit coefficient table. -/
@[expose] def approxExpTablePayloadBits : ℕ := approxExpCoefficients.length * 64

@[simp] theorem approxExp_hornerRounds_eq : approxExpHornerRounds = 12 := by
  rfl

@[simp] theorem approxExp_mulShiftCount_eq : approxExpMulShiftCount = 13 := by
  rfl

@[simp] theorem approxExp_subtractionCount_eq : approxExpSubtractionCount = 12 := by
  rfl

@[simp] theorem approxExp_tablePayloadBits_eq : approxExpTablePayloadBits = 832 := by
  rfl

/-- The ledger of every complete Algorithm 13 run agrees with the table-derived source counts. -/
theorem approxExpRun_counts (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) :
    (approxExpRun x63 ccs63).mulShiftCount = approxExpMulShiftCount ∧
      (approxExpRun x63 ccs63).subtractionCount = approxExpSubtractionCount := by
  simp [approxExpRun, approxExpMulShiftCount, approxExpSubtractionCount,
    approxExpHornerRounds, approxExpCoefficients]

/-- Every complete Algorithm 13 run records exactly thirteen multiply/shifts and twelve
subtractions. These are source-operation counts, not native steps or a runtime theorem. -/
theorem approxExpRun_ledger (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) :
    (approxExpRun x63 ccs63).mulShiftCount = 13 ∧
      (approxExpRun x63 ccs63).subtractionCount = 12 := by
  simpa only [approxExp_mulShiftCount_eq, approxExp_subtractionCount_eq] using
    approxExpRun_counts x63 ccs63

/-- Every complete Algorithm 13 run records zero random bits, external oracle queries and
external handler calls. These exact source coordinates are separate from a future machine-cost or
attack-resource profile. -/
theorem approxExpRun_deterministicResources
    (x63 : ApproxExpExponentInput) (ccs63 : ApproxExpScalingInput) :
    (approxExpRun x63 ccs63).randomBits = 0 ∧
      (approxExpRun x63 ccs63).oracleQueries = 0 ∧
      (approxExpRun x63 ccs63).handlerCalls = 0 := by
  simpa only [approxExpRun] using approxExpHornerRun_deterministicResources x63
    (approxExpCoefficients.headD 0) approxExpCoefficients.tail

/-- Occurrence-aware retained bits for an encoded control program and installed table copies.

`controlProgramBits` is supplied by a future concrete encoder. `tableCopies` counts physical table
occurrences, so a table shared by several callers is charged once and duplicated inline tables are
charged once per copy. -/
@[expose] def approxExpRetainedBits (controlProgramBits tableCopies : ℕ) : ℕ :=
  controlProgramBits + tableCopies * approxExpTablePayloadBits

@[simp] theorem approxExpRetainedBits_one (controlProgramBits : ℕ) :
    approxExpRetainedBits controlProgramBits 1 = controlProgramBits + 832 := by
  simp [approxExpRetainedBits]

@[simp] theorem approxExpRetainedBits_two (controlProgramBits : ℕ) :
    approxExpRetainedBits controlProgramBits 2 = controlProgramBits + 1664 := by
  simp [approxExpRetainedBits]

end Cslib.Crypto.Falcon
