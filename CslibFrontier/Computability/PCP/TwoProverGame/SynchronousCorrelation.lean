/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Computability.PCP.TwoProverGame.AlmostSynchronousReduction
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import CslibFrontier.Foundations.Quantum.Algebra.DensityState
import CslibFrontier.Foundations.Quantum.DensityMatrix.Linear
import CslibFrontier.Foundations.Quantum.DensityMatrix.Pure
import CslibFrontier.Foundations.Quantum.POVM.Density
import CslibFrontier.Foundations.Quantum.Algebra.MeasurementDistance
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Correlation estimates for almost-synchronous strategies

Moving a projective measurement to Bob's space changes the joint probabilities by at most
twice the state-dependent distance to its replacement. With Bob's original measurement as
the replacement, consistency bounds the average error by the diagonal synchrony defect.

The resulting sequential weights are linear in Bob's reduced density. When that density
is decomposed into components and the rounded projections commute with their component
densities, their mixture of product weights can be compared to the sequential weights.
These are steps toward the synchronous correlation approximation of [Vidick2022].
-/

public section

open Cslib.Quantum Matrix Finset
open scoped MatrixOrder Kronecker

namespace Cslib.PCP.QuantumStrategy

variable {ι κ X Y A B : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype A] [Fintype B]

/-- Replacing Alice's projective measurement by operators on Bob's space changes the joint
weights by at most twice the state-dependent distance between the two families. -/
theorem sum_abs_prob_sub_re_apply_conjugation_le (S : QuantumStrategy X Y A B ι κ)
    (x : X) (y : Y) (N : POVM A κ)
    (hP : ∀ a, (S.alice x).effect a * (S.alice x).effect a = (S.alice x).effect a) :
    (∑ a, ∑ b, |S.prob x y a b -
        (S.toCommuting.state ((1 ⊗ₖ N.effect a) * (S.toCommuting.bob y).effect b *
          (1 ⊗ₖ N.effect a))).re|) ≤
      2 * √(∑ a, S.toCommuting.state.norm
        ((S.toCommuting.alice x).effect a - 1 ⊗ₖ N.effect a) ^ 2) := by
  have hproj : (S.toCommuting.alice x).IsProjective := by
    intro a
    change ((S.alice x).effect a ⊗ₖ (1 : Matrix κ κ ℂ)) *
      ((S.alice x).effect a ⊗ₖ 1) = (S.alice x).effect a ⊗ₖ 1
    rw [← Matrix.mul_kronecker_mul, hP a, Matrix.one_mul]
  simp_rw [← S.prob_toCommuting]
  exact (S.toCommuting.bob y).sum_abs_re_apply_effect_mul_sub_conjugation_le
    S.toCommuting.state (S.toCommuting.alice x) (rightMeasurement N) hproj
    (S.toCommuting.commute x y)

/-- The averaged switching error depends on the first marginal of the joint question law.
The replacement may be a POVM on a space of different dimension from Alice's. -/
theorem sum_abs_prob_sub_re_apply_conjugation_le_of_questions [Fintype X] [Fintype Y]
    (S : QuantumStrategy X Y A B ι κ) (N : X → POVM A κ) (μ : PMF (X × Y))
    (hP : ∀ x a, (S.alice x).effect a * (S.alice x).effect a = (S.alice x).effect a) :
    (∑ q, (μ q).toReal * ∑ a, ∑ b, |S.prob q.1 q.2 a b -
        (S.toCommuting.state ((1 ⊗ₖ (N q.1).effect a) * (S.toCommuting.bob q.2).effect b *
          (1 ⊗ₖ (N q.1).effect a))).re|) ≤
      2 * √(∑ x, ((μ.map Prod.fst) x).toReal * ∑ a, S.toCommuting.state.norm
        ((S.toCommuting.alice x).effect a - 1 ⊗ₖ (N x).effect a) ^ 2) := by
  let E (x : X) := ∑ a, S.toCommuting.state.norm
    ((S.toCommuting.alice x).effect a - 1 ⊗ₖ (N x).effect a) ^ 2
  calc
    _ ≤ ∑ q : X × Y, (μ q).toReal * (2 * √(E q.1)) :=
      sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
        (S.sum_abs_prob_sub_re_apply_conjugation_le q.1 q.2 (N q.1) (hP q.1))
        ENNReal.toReal_nonneg
    _ = 2 * ∑ q : X × Y, (μ q).toReal * √(E q.1) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => mul_left_comm _ _ _
    _ = 2 * ∑ x, ((μ.map Prod.fst) x).toReal * √(E x) :=
      congrArg (2 * ·) (Cslib.Probability.PMF.sum_map_mul μ Prod.fst (fun x => √(E x))).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [smul_eq_mul, E] using Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
        (t := univ) (w := fun x => ((μ.map Prod.fst) x).toReal) (p := E)
        (fun _ _ => ENNReal.toReal_nonneg) (Cslib.Probability.PMF.sum_toReal _)
        (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)

/-- A sequential weight on Bob's system depends only on his reduced density matrix. -/
theorem bob_conjugation_eq_trace (S : QuantumStrategy X Y A B ι κ)
    (N : POVM A κ) (y : Y) (a : A) (b : B) :
    S.toCommuting.state ((1 ⊗ₖ N.effect a) * (S.toCommuting.bob y).effect b *
      (1 ⊗ₖ N.effect a)) =
      ((N.effect a * (S.bob y).effect b * N.effect a) *
        partialTraceLeft (pureState S.state)).trace := by
  change AlgState.vector S.state S.norm_state ((1 ⊗ₖ N.effect a) *
    (1 ⊗ₖ (S.bob y).effect b) * (1 ⊗ₖ N.effect a)) = _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
    AlgState.vector_apply, ← trace_mul_pureState, trace_mul_partialTraceLeft]

/-- A nearly synchronous strategy with projective Alice measurements is close to the
sequential experiment that applies Bob's measurements for the two questions on his system.
The loss depends only on the synchrony defect under Alice's marginal. -/
theorem sum_abs_prob_sub_bob_sequential_le [Fintype X] (S : QuantumStrategy X X A A ι κ)
    (μ : PMF (X × X))
    (hP : ∀ x a, (S.alice x).effect a * (S.alice x).effect a = (S.alice x).effect a) :
    (∑ q, (μ q).toReal * ∑ a, ∑ b, |S.prob q.1 q.2 a b -
        (((S.bob q.1).effect a * (S.bob q.2).effect b * (S.bob q.1).effect a) *
          partialTraceLeft (pureState S.state)).trace.re|) ≤
      2 * √(2 * S.synchronyDefect (μ.map Prod.fst)) := by
  have h := S.sum_abs_prob_sub_re_apply_conjugation_le_of_questions S.bob μ hP
  simp only [bob_conjugation_eq_trace] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
  rw [synchronyDefect_eq_sum, mul_sum]
  refine sum_le_sum fun x _ => ?_
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have hagree : Measurement.agreement S.toCommuting.state
      (S.toCommuting.alice x) (S.toCommuting.bob x) = ∑ a, S.prob x x a a := by
    unfold Measurement.agreement
    exact sum_congr rfl fun a _ => S.prob_toCommuting x x a a
  have hcons := Measurement.sum_norm_sub_sq_le S.toCommuting.state
    (S.toCommuting.alice x) (S.toCommuting.bob x) (fun a => S.toCommuting.commute x x a a)
  rw [hagree] at hcons
  exact hcons.trans_eq (by ring)

open scoped ComplexOrder in
/-- Bound the error of replacing sequential weights by a mixture of product weights
on invariant density components. The two question coordinates have the same marginal. -/
theorem sum_abs_sequential_sub_mixture_le {σ : Type*} [Fintype σ] [Fintype X]
    (P : X → POVM A κ) (Q : σ → X → POVM A κ)
    (ρ : σ → Matrix κ κ ℂ) (hρ : ∀ s, IsDensityMatrix (ρ s))
    (p : PMF σ) (μ : PMF (X × X)) (hμ : μ.map Prod.snd = μ.map Prod.fst)
    (hP : ∀ x, (P x).toMeasurement.IsProjective)
    (hQ : ∀ s x, (Q s x).toMeasurement.IsProjective)
    (hc : ∀ s x a, Commute ((Q s x).effect a) (ρ s)) :
    (∑ q, (μ q).toReal * ∑ a, ∑ b,
      |(((P q.1).effect a * (P q.2).effect b * (P q.1).effect a) *
          (∑ s, (p s).toReal • ρ s)).trace.re -
        ∑ s, (p s).toReal * (((Q s q.1).effect a * (Q s q.2).effect b) * ρ s).trace.re|) ≤
      4 * √(∑ x, ((μ.map Prod.fst) x).toReal * ∑ s, (p s).toReal * ∑ a,
        (((P x).effect a - (Q s x).effect a) * ((P x).effect a - (Q s x).effect a) *
          ρ s).trace.re) := by
  let E (x : X) (s : σ) := ∑ a, (((P x).effect a - (Q s x).effect a) *
    ((P x).effect a - (Q s x).effect a) * ρ s).trace.re
  have hE (x : X) (s : σ) : 0 ≤ E x s := by
    refine sum_nonneg fun a _ => ?_
    let D := (P x).effect a - (Q s x).effect a
    have hs : star D = D :=
      (((P x).posSemidef a).isHermitian.sub ((Q s x).posSemidef a).isHermitian).eq
    simpa only [AlgState.norm_sq, AlgState.ofDensityMatrix_apply, hs] using
      sq_nonneg ((AlgState.ofDensityMatrix (ρ s) (hρ s)).norm D)
  let M := μ.map Prod.fst
  let V (x : X) := ∑ s, (p s).toReal * √(E x s)
  let W (x : X) := ∑ s, (p s).toReal * E x s
  have hV (x : X) : V x ≤ √(W x) := by
    simpa only [smul_eq_mul, V, W] using Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
      (t := univ) (w := fun s => (p s).toReal) (p := E x)
      (fun _ _ => ENNReal.toReal_nonneg) (Cslib.Probability.PMF.sum_toReal p) (fun s _ => hE x s)
  have hW : (∑ x, (M x).toReal * √(W x)) ≤ √(∑ x, (M x).toReal * W x) := by
    simpa only [smul_eq_mul] using Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
      (t := univ) (w := fun x => (M x).toReal) (p := W)
      (fun _ _ => ENNReal.toReal_nonneg) (Cslib.Probability.PMF.sum_toReal M)
      (fun x _ => sum_nonneg fun s _ => mul_nonneg ENNReal.toReal_nonneg (hE x s))
  have hrow (x y : X) :
      (∑ a, ∑ b,
        |(((P x).effect a * (P y).effect b * (P x).effect a) *
            (∑ s, (p s).toReal • ρ s)).trace.re -
          ∑ s, (p s).toReal * (((Q s x).effect a * (Q s y).effect b) * ρ s).trace.re|) ≤
        2 * (V x + V y) := by
    let L (s : σ) (a b : A) := (((P x).effect a * (P y).effect b * (P x).effect a) * ρ s).trace.re
    let R (s : σ) (a b : A) := (((Q s x).effect a * (Q s y).effect b) * ρ s).trace.re
    have hsplit (a b : A) :
        |(((P x).effect a * (P y).effect b * (P x).effect a) *
            (∑ s, (p s).toReal • ρ s)).trace.re - ∑ s, (p s).toReal * R s a b| ≤
          ∑ s, (p s).toReal * |L s a b - R s a b| := by
      simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Complex.re_sum,
        Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, ← sum_sub_distrib, ← mul_sub]
      simpa only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
        abs_sum_le_sum_abs (fun s => (p s).toReal * (L s a b - R s a b)) univ
    calc
      _ ≤ ∑ a, ∑ b, ∑ s, (p s).toReal * |L s a b - R s a b| :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hsplit a b
      _ = ∑ s, (p s).toReal * ∑ a, ∑ b, |L s a b - R s a b| := by
        calc
          _ = ∑ a, ∑ s, ∑ b, (p s).toReal * |L s a b - R s a b| :=
            sum_congr rfl fun _ _ => sum_comm
          _ = ∑ s, ∑ a, ∑ b, (p s).toReal * |L s a b - R s a b| := sum_comm
          _ = _ := by simp only [mul_sum]
      _ ≤ ∑ s, (p s).toReal * (2 * √(E x s) + 2 * √(E y s)) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
          (POVM.sum_abs_trace_sequential_sub_product_le (hρ s) (P x) (P y) (Q s x) (Q s y)
            (hQ s x) (hP y) (hQ s y) (hc s x)) ENNReal.toReal_nonneg
      _ = _ := by simp only [V, mul_add, mul_sum, sum_add_distrib, mul_left_comm _ (2 : ℝ)]
  calc
    _ ≤ ∑ q : X × X, (μ q).toReal * (2 * (V q.1 + V q.2)) :=
      sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hrow q.1 q.2) ENNReal.toReal_nonneg
    _ = 4 * ∑ x, (M x).toReal * V x := by
      simp only [mul_left_comm _ (2 : ℝ), ← mul_sum, mul_add, sum_add_distrib]
      rw [← Cslib.Probability.PMF.sum_map_mul μ Prod.fst V,
        ← Cslib.Probability.PMF.sum_map_mul μ Prod.snd V, hμ]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hV x) ENNReal.toReal_nonneg).trans hW

end Cslib.PCP.QuantumStrategy
