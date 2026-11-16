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
# Concrete interpretation of an existing uniform-generator certificate

This concrete-only construction consumes an arbitrary existing `GeneratorCertificate`; it does
not restrict the admitted circuit family to generators originally assembled with `NativeCompiler`.
Its installed program contains the certified description and a literal polynomial clock. The
certificate's possibly noncomputable time schedule is used only to prove that the clock suffices.

The result retains the actual interpreter table, its complete static description, its separate
native time and workspace maps, and its exact emitted circuit-description word. Polynomial
majorants for those native maps remain open in issue #5281; this component does not yet supply
the asymptotic efficiency witness for the HQC reduction.

## Main definitions

* `Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate.toNativeCompiler`: interpret a
  certified generator using explicit dominating polynomial constants.

## Main results

The construction derives exact output correctness from the adversary's certificate and the
halted-run extension law. No correctness premise about the constructed interpreter is required.
-/

public section

namespace Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate

open Turing MultiTapeTM Internal NativeCompiler

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
  let inputWord : NativeCompiler (fun input : OracleInputSize => encOracleInputSize input)
      encOracleInputSize encBits :=
    (identity encOracleInputSize).ofOutputEq fun _ => rfl
  let length := unaryDecoder.comp inputWord
  let clock := (unaryPolynomialClock c d).comp length
  let interpreted := (simulateBitOutputCompiler certificate.code).comp (inputWord.pair clock)
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

end Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate
