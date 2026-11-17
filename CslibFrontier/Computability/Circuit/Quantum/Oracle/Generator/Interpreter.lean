/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Generator
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Clock
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Interpreter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec

/-!
# Polynomial native interpretation of an existing uniform-generator certificate

This construction consumes an arbitrary existing `GeneratorCertificate`; it does
not restrict the admitted circuit family to generators originally assembled with `NativeCompiler`.
Its installed program contains the certified description and a literal polynomial clock. The
certificate's possibly noncomputable time schedule is used only to prove that the clock suffices.

The result retains the actual interpreter table, its complete static description, its separate
native time and workspace maps, and its exact emitted circuit-description word. Explicit
length-indexed polynomial schedules bound both native resource maps. This is the generator
interpretation component of the open HQC reduction in issue #5281, not its security theorem.

## Main definitions

* `Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate.toNativeCompiler`: interpret a
  certified generator using explicit dominating polynomial constants.

## Main results

The construction derives exact output correctness from the adversary's certificate and the
halted-run extension law. `toNativeCompiler_resources_le` bounds its actual native time and
visited workspace by separate polynomial schedules. No correctness or efficiency premise about
the constructed interpreter is required.
-/

public section

namespace Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate

open Turing MultiTapeTM Internal NativeCompiler

private noncomputable def clockedInputCompiler (c d : ℕ) :
    NativeCompiler
      (fun input : OracleInputSize =>
        (encOracleInputSize input, c * ((encOracleInputSize input).length + 1) ^ d))
      encOracleInputSize (encPair encBits encUnary) := by
  let inputWord : NativeCompiler (fun input : OracleInputSize => encOracleInputSize input)
      encOracleInputSize encBits :=
    (identity encOracleInputSize).ofOutputEq fun _ => rfl
  let length := unaryDecoder.comp inputWord
  let clock := (unaryPolynomialClock c d).comp length
  exact inputWord.pair clock

private theorem clockedInputCompiler_resources_le (c d : ℕ) (input : OracleInputSize) :
    let n := (encOracleInputSize input).length
    (clockedInputCompiler c d).time input ≤
        100100 * (c + 1) * (d + 1) * (n + 1) ^ (d + 2) ∧
      (clockedInputCompiler c d).workspace input ≤
        1000100 * (c + 1) * (d + 1) ^ 2 * (n + 1) ^ (d + 2) +
          100 * (unaryPolynomialClock c d).tapeCount := by
  let n := (encOracleInputSize input).length
  let K := (unaryPolynomialClock c d).tapeCount
  have ht : (clockedInputCompiler c d).time input ≤
      (unaryPolynomialClock c d).time n + 100 * (n + 1) := by
    simp only [clockedInputCompiler, pair, NativeCompiler.comp, identity, ofOutputEq, unaryDecoder,
      ofTransducer, encodeFrame, encBits_apply, encUnary_apply, List.length_replicate]
    dsimp only [n]
    omega
  have hs : (clockedInputCompiler c d).workspace input ≤
      (unaryPolynomialClock c d).workspace n + 100 * (n + K + 1) := by
    simp only [clockedInputCompiler, pair, NativeCompiler.comp, identity, ofOutputEq, unaryDecoder,
      ofTransducer, encodeFrame, encBits_apply, encUnary_apply, List.length_replicate]
    dsimp only [n, K]
    omega
  have hpow : n + 1 ≤ (n + 1) ^ (d + 2) := Nat.le_self_pow (by omega) _
  have htScale : n + 1 ≤ (c + 1) * (d + 1) * (n + 1) ^ (d + 2) :=
    hpow.trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega)))
  have hsScale : n + 1 ≤ (c + 1) * (d + 1) ^ 2 * (n + 1) ^ (d + 2) :=
    hpow.trans (Nat.le_mul_of_pos_left _
      (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))))
  have htClock := unaryPolynomialClock_time_le c d n
  have hsClock := unaryPolynomialClock_workspace_le c d n
  constructor
  · nlinarith
  · dsimp only [K] at hs
    nlinarith

/-- Retain an executable interpreter for a certified generator. The literal constants `c,d`
determine the executed clock. The polynomial upper-bound hypothesis is discharged from
`certificate.time_polynomiallyBounded` via `polynomiallyBounded_iff_le`; its proof does not enter
the transition table. The complete installed program is charged by the returned compiler's
`staticBits`, once rather than once per simulated step. -/
noncomputable def toNativeCompiler {F : UniformOracleCircuitFamily}
    (certificate : F.GeneratorCertificate) (c d : ℕ)
    (hclock : ∀ n, certificate.time n ≤ c * (n + 1) ^ d) :
    NativeCompiler
      (fun input : OracleInputSize =>
        F.description input.securityParameter input.classicalInputLength)
      encOracleInputSize encOracleCircuitDescription := by
  let interpreted :=
    (simulateBitOutputCompiler certificate.code).comp (clockedInputCompiler c d)
  refine interpreted.ofOutputEq ?_
  intro input
  have hrun := Universal.simulate_eq_of_halted
    (hclock (encOracleInputSize input).length) (certificate.computes input)
  change encOracleCircuitDescription
      (F.description input.securityParameter input.classicalInputLength) =
    ((Universal.simulate certificate.code
        ((encOracleInputSize input).map Universal.eBit)
        (c * ((encOracleInputSize input).length + 1) ^ d)).1).map
      (fun symbol => decide (symbol = 1))
  rw [hrun, List.map_map]
  change _ = List.map (fun bit : Bool => decide (bit.toNat = 1))
    (encOracleCircuitDescription (F.description input.securityParameter input.classicalInputLength))
  simp only [Bool.toNat_eq_one, Bool.decide_eq_true, List.map_id']

private theorem toNativeCompiler_resources_le_interpreter {F : UniformOracleCircuitFamily}
    (certificate : F.GeneratorCertificate) (c d : ℕ)
    (hclock : ∀ n, certificate.time n ≤ c * (n + 1) ^ d) (input : OracleInputSize) :
    let word := encOracleInputSize input
    let n := word.length
    let count := c * (n + 1) ^ d
    let interpreter := simulateBitOutputCompiler certificate.code
    let K := max (clockedInputCompiler c d).tapeCount interpreter.tapeCount
    (certificate.toNativeCompiler c d hclock).time input ≤
        interpreter.time (word, count) +
          100200 * (c + 1) * (d + 1) * (n + 1) ^ (d + 2) ∧
      (certificate.toNativeCompiler c d hclock).workspace input ≤
        interpreter.workspace (word, count) +
          1000200 * (c + 1) * (d + 1) ^ 2 * (n + 1) ^ (d + 2) +
          100 * (unaryPolynomialClock c d).tapeCount + 6 * K := by
  let n := (encOracleInputSize input).length
  let P := (c + 1) * (d + 1) * (n + 1) ^ (d + 2)
  let Q := (c + 1) * (d + 1) ^ 2 * (n + 1) ^ (d + 2)
  have hi := clockedInputCompiler_resources_le c d input
  have hpow : n + 1 ≤ (n + 1) ^ (d + 2) := Nat.le_self_pow (by omega) _
  have hnP : n + 1 ≤ P :=
    hpow.trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega)))
  have hPCount : c * (n + 1) ^ d ≤ P := by
    apply Nat.mul_le_mul
    · exact (Nat.le_succ c).trans (Nat.le_mul_of_pos_right _ (by omega))
    · exact Nat.pow_le_pow_right (by omega) (by omega)
  have hPQ : P ≤ Q := by
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_left
    exact Nat.le_self_pow (by omega) _
  have hm :
      (encPair encBits encUnary
        (encOracleInputSize input, c * (n + 1) ^ d)).length ≤ 3 * P := by
    simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
    change 2 * n + 1 + c * (n + 1) ^ d ≤ 3 * P
    omega
  constructor
  · change (clockedInputCompiler c d).time input +
        (simulateBitOutputCompiler certificate.code).time
          (encOracleInputSize input, c * (n + 1) ^ d) +
        4 * (encPair encBits encUnary
          (encOracleInputSize input, c * (n + 1) ^ d)).length + 9 ≤ _
    have ht := hi.1
    dsimp only [P] at hm hnP
    nlinarith
  · change (clockedInputCompiler c d).workspace input +
        (simulateBitOutputCompiler certificate.code).workspace
          (encOracleInputSize input, c * (n + 1) ^ d) +
        5 * (encPair encBits encUnary
          (encOracleInputSize input, c * (n + 1) ^ d)).length +
        (6 * max (clockedInputCompiler c d).tapeCount
          (simulateBitOutputCompiler certificate.code).tapeCount + 20) ≤ _
    have hs := hi.2
    have hmQ := hm.trans (Nat.mul_le_mul_left 3 hPQ)
    have hnQ := hnP.trans hPQ
    dsimp only [Q] at hmQ hnQ
    nlinarith

/-- Length-indexed native interpreter time schedule. The clock contributes degree
`max d 1` to the simulated input size; the cubic interpreter cost and the separately constructed
unary clock are charged independently. `certificate.code` is fixed in this schedule. -/
def toNativeCompilerTimeBound {F : UniformOracleCircuitFamily}
    (certificate : F.GeneratorCertificate) (c d n : ℕ) : ℕ :=
  let M := Universal.descLen certificate.code +
    (Universal.eCfg (Universal.init certificate.code)).length + 1
  10 ^ 41 * M ^ 4 * ((c + 1) * (n + 1) ^ max d 1) ^ 3 +
    100200 * (c + 1) * (d + 1) * (n + 1) ^ (d + 2)

/-- Length-indexed visited-workspace schedule of the native interpreter and its unary clock.
The interpreter's actual tape count and the clock/composition tape charges remain explicit;
this schedule does not substitute running time for workspace. -/
noncomputable def toNativeCompilerWorkspaceBound {F : UniformOracleCircuitFamily}
    (certificate : F.GeneratorCertificate) (c d n : ℕ) : ℕ :=
  let interpreter := simulateBitOutputCompiler certificate.code
  let M := Universal.descLen certificate.code +
    (Universal.eCfg (Universal.init certificate.code)).length + 1
  10 ^ 42 * (interpreter.tapeCount + 1) ^ 2 * M ^ 4 *
      ((c + 1) * (n + 1) ^ max d 1) ^ 2 +
    1000200 * (c + 1) * (d + 1) ^ 2 * (n + 1) ^ (d + 2) +
    100 * (unaryPolynomialClock c d).tapeCount +
      6 * max (clockedInputCompiler c d).tapeCount interpreter.tapeCount

/-- The actual native interpreter's length-indexed time schedule is polynomial for every fixed
certified description and fixed literal clock constants. -/
theorem toNativeCompilerTimeBound_polynomiallyBounded {F : UniformOracleCircuitFamily}
    (certificate : F.GeneratorCertificate) (c d : ℕ) :
    PolynomiallyBounded (certificate.toNativeCompilerTimeBound c d) := by
  unfold toNativeCompilerTimeBound
  fun_prop

/-- The native visited-workspace schedule is polynomial independently of the time schedule. -/
theorem toNativeCompilerWorkspaceBound_polynomiallyBounded {F : UniformOracleCircuitFamily}
    (certificate : F.GeneratorCertificate) (c d : ℕ) :
    PolynomiallyBounded (certificate.toNativeCompilerWorkspaceBound c d) := by
  unfold toNativeCompilerWorkspaceBound
  fun_prop

private theorem clockedInputSize_le (c d n : ℕ) :
    n + c * (n + 1) ^ d + 1 ≤ (c + 1) * (n + 1) ^ max d 1 := by
  have hlinear : n + 1 ≤ (n + 1) ^ max d 1 :=
    Nat.le_self_pow (by omega) _
  have hpower : (n + 1) ^ d ≤ (n + 1) ^ max d 1 :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
  calc
    _ = (n + 1) + c * (n + 1) ^ d := by omega
    _ ≤ (n + 1) ^ max d 1 + c * (n + 1) ^ max d 1 :=
      Nat.add_le_add hlinear (Nat.mul_le_mul_left c hpower)
    _ = _ := by ring

/-- The retained interpretation of any existing generator certificate obeys explicit polynomial
schedules for native time and visited workspace. Only the original generator's clock bound is
assumed; the interpreter's resource bounds are proved from its actual transition table. -/
theorem toNativeCompiler_resources_le {F : UniformOracleCircuitFamily}
    (certificate : F.GeneratorCertificate) (c d : ℕ)
    (hclock : ∀ n, certificate.time n ≤ c * (n + 1) ^ d) (input : OracleInputSize) :
    (certificate.toNativeCompiler c d hclock).time input ≤
        certificate.toNativeCompilerTimeBound c d (encOracleInputSize input).length ∧
      (certificate.toNativeCompiler c d hclock).workspace input ≤
        certificate.toNativeCompilerWorkspaceBound c d (encOracleInputSize input).length := by
  let word := encOracleInputSize input
  let n := word.length
  let count := c * (n + 1) ^ d
  let M := Universal.descLen certificate.code +
    (Universal.eCfg (Universal.init certificate.code)).length + 1
  let interpreter := simulateBitOutputCompiler certificate.code
  have hsize := clockedInputSize_le c d n
  have ht := simulateBitOutputCompiler_time_le certificate.code word count
  have hs := simulateBitOutputCompiler_workspace_le certificate.code word count
  have hnative := toNativeCompiler_resources_le_interpreter certificate c d hclock input
  have htScale : 10 ^ 41 * M ^ 4 * (n + count + 1) ^ 3 ≤
      10 ^ 41 * M ^ 4 * ((c + 1) * (n + 1) ^ max d 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 3)
  have hsScale : 10 ^ 42 * (interpreter.tapeCount + 1) ^ 2 * M ^ 4 *
        (n + count + 1) ^ 2 ≤
      10 ^ 42 * (interpreter.tapeCount + 1) ^ 2 * M ^ 4 *
        ((c + 1) * (n + 1) ^ max d 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 2)
  constructor
  · exact hnative.1.trans (Nat.add_le_add_right (ht.trans htScale) _)
  · exact hnative.2.trans (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (hs.trans hsScale) _) _) _)

end Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate
