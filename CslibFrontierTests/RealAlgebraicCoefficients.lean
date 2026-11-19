/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (finite-field coefficient and controlled-access regression tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledCoefficients
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledSigns
import CslibFrontier.Computability.Complexity.RealAlgebraic.CoefficientEvaluation
import Mathlib.Tactic.FinCases

/-! Extraction covers zero variables, absent coefficients, mixed terms and actual certificates. -/

public section
namespace CslibFrontierTests.RealAlgebraicCoefficients

open Cslib.Complexity Cslib.Complexity.RealAlgebraic Turing.MultiTapeTM MvPolynomial

-- A zero-variable grid has one empty tuple, rather than no tuples.
example : multivariateCoefficientResidue 5 0 [] (fun _ => 3) = 3 := by rfl

-- The unary extractor recovers an ordinary nonzero coefficient and an index above the degree.
example : coefficientResidue 5 1 (fun z => (2 * z + 3) % 5) = 2 := by rfl
example : coefficientResidue 5 3 (fun z => (2 * z + 3) % 5) = 0 := by rfl

-- Defaulting absent exponent entries to zero selects the constant term.
example : multivariateCoefficientResidue 5 1 [] (fun z =>
    (2 * z[0]?.getD 0 + 3) % 5) = 3 := by rfl

/-- An actual controlled two-variable family with a mixed term and negative constant. -/
noncomputable def mixed :
    Controlled (fun _ : List Bool => X (0 : Fin 2) * X (1 : Fin 2) + C (-2)) encBits 0 :=
  ((Controlled.coordinate (.const 2) (fun _ => (0 : Fin 2)) (.const 0)).mul
    (Controlled.coordinate (.const 2) (fun _ => (1 : Fin 2)) (.const 1))).add
      (Controlled.constant (.const 2) (fun _ => -2) (.const (-2)))

private noncomputable def exponent : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

private theorem exponent_code (_w : List Bool) (i : Fin 2) :
    ([1, 1] : List ℕ)[i.val]?.getD 0 = exponent i := by
  fin_cases i <;> simp [exponent]

-- Certificate construction is uniform; neither polynomial coefficients nor a grid are inputs.
example : IntegerResidueAccess.InCountingFunction
    (mixed.coefficientAccess (fun _ => exponent) (fun _ => [1, 1]) exponent_code) 1 encBits :=
  mixed.coefficientAccess_mem Decoder.bits (fun _ => exponent)
    (ComputableInPolyTime.const [1, 1]) exponent_code

example : (fun _ : List Bool =>
    ((X (0 : Fin 2) * X (1 : Fin 2) + C (-2) : MvPolynomial (Fin 2) ℤ).coeff
      exponent).sign) ∈ CountingFunction 8 encBits encIntBin := by
  exact mixed.coefficientSign_mem Decoder.bits (fun _ => exponent)
    (ComputableInPolyTime.const [1, 1]) exponent_code

/-- A zero-variable family uses its source evaluator directly for integer signs. -/
noncomputable def integerFamily :
    Controlled (fun _ : List Bool => C (-37) : List Bool → MvPolynomial (Fin 0) ℤ) encBits 0 :=
  Controlled.constant (.const 0) (fun _ => -37) (.const (-37))

example : (fun _ : List Bool => (-37 : ℤ).sign) ∈ CountingFunction 8 encBits encIntBin := by
  simpa [coeff_C] using integerFamily.sign_mem Decoder.bits

end CslibFrontierTests.RealAlgebraicCoefficients
