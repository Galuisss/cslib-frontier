/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SliceBoundedness
import Mathlib.Algebra.Field.ZMod

/-! # A nonzero evaluated slice failure term -/

set_option linter.privateModule false

open Cslib.PCP.LowIndividualDegree Cslib.Quantum Matrix Finset
open scoped BigOperators Real MatrixOrder Matrix.Norms.L2Operator

namespace CslibFrontierTests.LowIndividualDegreeSliceBoundedness

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
private abbrev F := ZMod 2

private def diagonalProjection : Mat := !![1, 0; 0, 0]
private noncomputable def uniformProjection : Mat := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

private theorem diagonalProjection_star : star diagonalProjection = diagonalProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalProjection, Matrix.star_apply]

private theorem uniformProjection_star : star uniformProjection = uniformProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniformProjection, Matrix.star_apply]

private theorem diagonalProjection_sq :
    diagonalProjection * diagonalProjection = diagonalProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [diagonalProjection, Matrix.mul_apply, Fin.sum_univ_two]

private theorem uniformProjection_sq :
    uniformProjection * uniformProjection = uniformProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [uniformProjection, Matrix.mul_apply, Fin.sum_univ_two]

private theorem complement_sq (e : Mat) (he₂ : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  simp only [mul_sub, sub_mul, one_mul, mul_one, he₂, sub_self, sub_zero]

private def binary (e : Mat) (he : star e = e) (he₂ : e * e = e) : Measurement Bool Mat where
  effect b := if b then e else 1 - e
  nonneg b := by
    cases b
    · simpa only [Bool.false_eq_true, ite_false, star_sub, star_one, he, complement_sq e he₂]
        using star_mul_self_nonneg (1 - e)
    · simpa only [ite_true, he, he₂] using star_mul_self_nonneg e
  sum_effect := by simp

private theorem binary_projective (e : Mat) (he : star e = e) (he₂ : e * e = e) :
    (binary e he he₂).IsProjective := by
  intro b
  cases b
  · change (1 - e) * (1 - e) = 1 - e
    exact complement_sq e he₂
  · exact he₂

private noncomputable def zeroSlice : BoundedPolynomial F 0 0 := ⟨0, fun i => Fin.elim0 i⟩

private noncomputable def P : Measurement (Option (BoundedPolynomial F 0 0)) Mat := by
  classical
  exact (binary diagonalProjection diagonalProjection_star diagonalProjection_sq).map
    (fun b => if b then some zeroSlice else none)

private noncomputable def N : Measurement (Option Unit) Mat :=
  (binary uniformProjection uniformProjection_star uniformProjection_sq).map
    (fun b => if b then some () else none)

private noncomputable def B (_ : Point F 0) : Measurement F Mat := Measurement.const 0

private noncomputable def basisVector : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1

private noncomputable def φ : AlgState Mat :=
  AlgState.vector basisVector (EuclideanSpace.orthonormal_single.norm_eq_one 1)

private noncomputable def failureTerm : ℝ :=
  𝔼 u : Point F 0, ∑ a : Unit, ∑ b : F,
    (φ (N.effect (some a) * (evaluatePolynomialMeasurement P u).effect (some b) *
      N.effect (some a) * P.effect none * (B u).effect b)).re

private theorem failureTerm_bound : |failureTerm| ≤ √((φ (P.effect none * 1)).re) := by
  classical
  exact abs_average_evaluated_sandwich_failure_le φ P N
    ((binary_projective _ _ _).map _) ((binary_projective _ _ _).map _)
    B 1 zero_le_one (fun g => (averagePolynomialPointEffect_mem_Icc B g).2)
    (fun a u b => by simp only [B, Measurement.const]; split_ifs
                     · exact Commute.one_right _
                     · exact Commute.zero_right _)
    (fun a u b => by simp only [B, Measurement.const]; split_ifs
                     · exact Commute.one_right _
                     · exact Commute.zero_right _)
    (fun _ => Commute.one_right _) (fun _ => Commute.one_right _)

/-- The example has a genuine nonzero failure contribution and the public bound applies. -/
example : failureTerm = 1 / 4 ∧ |failureTerm| ≤ √((φ (P.effect none * 1)).re) := by
  refine ⟨?_, failureTerm_bound⟩
  classical
  have hP (u : Point F 0) :
      (evaluatePolynomialMeasurement P u).effect (some 0) = diagonalProjection := by
    simp [evaluatePolynomialMeasurement, P, Measurement.map_map, Measurement.map_effect,
      binary, sum_filter, zeroSlice]
  have hPnone : P.effect none = 1 - diagonalProjection := by
    simp [P, Measurement.map_effect, binary, sum_filter]
  have hN : N.effect (some ()) = uniformProjection := by
    simp [N, Measurement.map_effect, binary, sum_filter]
  have hconst (u : Point F 0) :
      (∑ b : F, (φ (N.effect (some ()) *
        (evaluatePolynomialMeasurement P u).effect (some b) * N.effect (some ()) *
        P.effect none * (B u).effect b)).re) =
        (φ (uniformProjection * diagonalProjection * uniformProjection *
          (1 - diagonalProjection))).re := by
    rw [sum_eq_single_of_mem 0 (mem_univ 0)]
    · simp [B, Measurement.const, hP, hPnone, hN]
    · intro b _ hb
      simp [B, Measurement.const, hb]
  simp only [failureTerm, Fintype.sum_unique, hconst, Fintype.expect_const]
  norm_num [φ, AlgState.vector_apply, basisVector, EuclideanSpace.single, Matrix.mul_apply,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, uniformProjection,
    diagonalProjection,
    Matrix.one_apply]

end CslibFrontierTests.LowIndividualDegreeSliceBoundedness
