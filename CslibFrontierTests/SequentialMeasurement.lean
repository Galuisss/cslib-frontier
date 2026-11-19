/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.SequentialMeasurement

/-! # An interior coordinate of a sequential projective measurement -/

set_option linter.privateModule false

open Cslib.Quantum.Measurement
open scoped ComplexOrder

private def instructions (j : Fin 3) : Cslib.Quantum.Measurement Bool ℂ :=
  const (j == 1)

private theorem projective (j : Fin 3) : (instructions j).IsProjective :=
  isProjective_const _

/-- In the sequence false, true, false, keeping just the middle outcome
gives the full effect for true. -/
example :
    (∑ g : Fin 3 → Bool, if g 1 = true then
      (sequentialProjective instructions projective).effect g else 0) = 1 := by
  rw [sequentialProjective_marginal]
  have h : (instructions 1).effect true = 1 := by simp [instructions, const]
  simp only [h, mul_one]
  exact sum_transcriptProduct_mul_star _ (fun _ => projective _)

/-- The complementary outcome at the same position has zero effect. -/
example :
    (∑ g : Fin 3 → Bool, if g 1 = false then
      (sequentialProjective instructions projective).effect g else 0) = 0 := by
  rw [sequentialProjective_marginal]
  have h : (instructions 1).effect false = 0 := by simp [instructions, const]
  simp [h]
