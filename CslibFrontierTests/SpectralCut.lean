/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.SpectralCut

/-! # Spectral cuts of an unequal two-coordinate spectrum -/

set_option linter.privateModule false

open Cslib.Quantum Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius MatrixOrder

private noncomputable def testSpectrum (b : Bool) : ℝ := if b then 3 / 4 else 1 / 4

/-- Only the two off-diagonal entries contribute, with the same positive gap. -/
example (A : Matrix Bool Bool ℂ) :
    ∫ t : ℝ, ‖A * diagonalCut testSpectrum t - diagonalCut testSpectrum t * A‖ ^ 2 =
      (‖A false true‖ ^ 2 + ‖A true false‖ ^ 2) / 2 := by
  rw [integral_norm_commutator_diagonalCut_sq testSpectrum (by
    intro b
    cases b <;> norm_num [testSpectrum])]
  norm_num [Fintype.sum_bool, testSpectrum]
  ring

/-- The trace state divides the squared Frobenius norm by the dimension. -/
example (A : Matrix Bool Bool ℂ) :
    (AlgState.normalizedMatrixTrace : AlgState (Matrix Bool Bool ℂ)).norm A ^ 2 =
      ‖A‖ ^ 2 / 2 := by
  simpa using AlgState.norm_sq_normalizedMatrixTrace A

/-- Compression to one coordinate preserves each effect on that coordinate. -/
example (M : Measurement Bool (Matrix Bool Bool ℂ)) (a : Bool) :
    let e : Unit ↪ Bool := ⟨fun _ => false, fun {_ _} _ => Subsingleton.elim _ _⟩
    (M.principalSubmatrix e).effect a () () = M.effect a false false := by
  simp only [Measurement.principalSubmatrix_effect_apply]
  rfl
