/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary
public import CslibFrontier.Foundations.Quantum.Measurement.Overlap
public import CslibFrontier.Probability.PMF
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Changing one entry of a coherent value oracle

The query-magnitude argument of [Bennett et al., Theorem 3.3][BBBV1997] bounds the effect of
changing oracle answers on the state of a quantum algorithm. Here each symbol selects a unitary
on the response register, which includes a multi-bit XOR oracle and arbitrary workspace.

For a table fixed before a hidden index is drawn with point probabilities at most δ, changing
that entry changes the acceptance probability of a T-query run by at most 2 T √δ on average.
The final measurement event can depend on the revealed index. This addresses a single
independent point in a finite oracle. Adaptive points chosen during signing require additional
reasoning about the adversary's state.
-/

public section

namespace Cslib.Quantum

open Finset
open scoped BigOperators

variable {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W] [DecidableEq ι]
variable (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
variable (H : ι → α)

private theorem norm_valueOracle_update_sub_le (ψ : ValueState ι V W) (i : ι) (v : α) :
    ‖valueOracle step (Function.update H i v) ψ - valueOracle step H ψ‖ ≤
      2 * ‖querySlice i ψ‖ := by
  let u := valueOracle step (Function.update H i v) ψ
  let w := valueOracle step H ψ
  have hslice (j : ι) : querySlice j (u - w) = querySlice j u - querySlice j w := rfl
  have he : ‖u - w‖ ^ 2 = ‖querySlice i u - querySlice i w‖ ^ 2 := by
    rw [← sum_sq_norm_querySlice, sum_eq_single i, hslice]
    · intro j _ hji
      have hz : querySlice j u = querySlice j w := by
        ext ⟨a, b⟩
        simp only [u, w, querySlice_apply, valueOracle_apply, Function.update_of_ne hji]
      simp [hslice, hz]
    · simp
  calc
    ‖u - w‖ = ‖querySlice i u - querySlice i w‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
    _ ≤ ‖querySlice i u‖ + ‖querySlice i w‖ := norm_sub_le _ _
    _ = _ := by simp [u, w, two_mul]

variable (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) (ψ : ValueState ι V W)

/-- The distance from changing one table entry is at most twice the sum of the unmodified
run's query amplitudes at that index. -/
theorem norm_runValue_update_sub_le (i : ι) (v : α) (T : ℕ) :
    ‖runValue step U ψ (Function.update H i v) T - runValue step U ψ H T‖ ≤
      2 * ∑ t ∈ range T, ‖querySlice i (runValue step U ψ H t)‖ := by
  induction T with
  | zero => simp [runValue]
  | succ T ih =>
    let u := runValue step U ψ (Function.update H i v) T
    let w := runValue step U ψ H T
    rw [runValue, runValue, ← map_sub, LinearIsometry.norm_map, sum_range_succ, mul_add]
    change ‖valueOracle step _ u - valueOracle step H w‖ ≤ _
    calc
      _ ≤ ‖valueOracle step (Function.update H i v) u -
            valueOracle step (Function.update H i v) w‖ +
          ‖valueOracle step (Function.update H i v) w - valueOracle step H w‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        rw [← map_sub, LinearIsometryEquiv.norm_map]
        exact add_le_add ih (norm_valueOracle_update_sub_le step H w i v)

/-- For a fixed table and a hidden index with point masses at most δ, the mean change in
the state norm after T queries is at most `2 T √δ`. -/
theorem mean_norm_runValue_update_sub_le (hψ : ‖ψ‖ = 1) (T : ℕ)
    (p : PMF ι) {δ : ℝ} (hp : ∀ i, (p i).toReal ≤ δ) (newValue : ι → α) :
    ∑ i, (p i).toReal * ‖runValue step U ψ (Function.update H i (newValue i)) T -
        runValue step U ψ H T‖ ≤
      2 * T * Real.sqrt δ := by
  have hmass : ∑ i, (p i).toReal ^ 2 ≤ δ := by
    calc
      _ ≤ ∑ i, (p i).toReal * δ := sum_le_sum fun i _ => by
        rw [sq]
        exact mul_le_mul_of_nonneg_left (hp i) ENNReal.toReal_nonneg
      _ = δ := by rw [← sum_mul, Probability.PMF.sum_toReal, one_mul]
  have hmean (t : ℕ) :
      ∑ i, (p i).toReal * ‖querySlice i (runValue step U ψ H t)‖ ≤ Real.sqrt δ := by
    apply Real.le_sqrt_of_sq_le
    have hcs := sum_mul_sq_le_sq_mul_sq univ (fun i => (p i).toReal)
      (fun i => ‖querySlice i (runValue step U ψ H t)‖)
    rw [sum_sq_norm_querySlice, norm_runValue, hψ, one_pow, mul_one] at hcs
    exact hcs.trans hmass
  calc
    _ ≤ ∑ i, (p i).toReal * (2 * ∑ t ∈ range T, ‖querySlice i (runValue step U ψ H t)‖) := by
      refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      exact norm_runValue_update_sub_le step H U ψ i _ T
    _ = 2 * ∑ t ∈ range T, ∑ i, (p i).toReal * ‖querySlice i (runValue step U ψ H t)‖ := by
      simp only [mul_left_comm ((p _).toReal) 2, mul_sum]
      rw [sum_comm]
    _ ≤ 2 * ∑ _ ∈ range T, Real.sqrt δ := by gcongr with t; exact hmean t
    _ = _ := by simp [mul_assoc]

omit H in
/-- One reprogramming in a finite quantum random oracle. After `T` coherent queries to a
uniform table, the challenger reveals an independently drawn point and optionally refreshes its
value. Both continuations see the point and the current table and may act on the retained state.
The bound applies to their final measurement, including table- and point-dependent tests. -/
theorem abs_reprogrammed_measureProb_sub_le {κ : Type*} [Fintype κ] [Fintype α] [Nonempty α]
    (hψ : ‖ψ‖ = 1) (T : ℕ) (p : PMF ι) {δ : ℝ} (hp : ∀ i, (p i).toReal ≤ δ)
    (post : (ι → α) → ι → ValueState ι V W →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (accept : (ι → α) → ι → Finset κ) :
    |(𝔼 hv : (ι → α) × α, ∑ i, (p i).toReal *
        measureProb (post (Function.update hv.1 i hv.2) i (runValue step U ψ hv.1 T))
          (accept (Function.update hv.1 i hv.2) i)) -
      (𝔼 hv : (ι → α) × α, ∑ i, (p i).toReal *
        measureProb (post hv.1 i (runValue step U ψ hv.1 T)) (accept hv.1 i))| ≤
      2 * T * Real.sqrt δ := by
  let score (H G : ι → α) (i : ι) :=
    measureProb (post G i (runValue step U ψ H T)) (accept G i)
  let change (x : (ι → α) × α) (i : ι) := Function.update x.1 i x.2
  change |(𝔼 hv, ∑ i, (p i).toReal * score hv.1 (change hv i) i) -
    (𝔼 hv : (ι → α) × α, ∑ i, (p i).toReal * score hv.1 hv.1 i)| ≤ _
  have swap (i : ι) : (𝔼 hv, (p i).toReal * score hv.1 (change hv i) i) =
      𝔼 hv, (p i).toReal * score (change hv i) hv.1 i := by
    let f (hv : (ι → α) × α) := (change hv i, hv.1 i)
    have hf : Function.Involutive f := by rintro ⟨a, v⟩; simp [f, change]
    apply Fintype.expect_equiv hf.toPerm
    intro hv
    simp [f, change, Function.Involutive.toPerm]
  rw [expect_sum_comm]
  simp_rw [swap]
  rw [← expect_sum_comm, ← expect_sub_distrib]
  refine (abs_expect_le _ _).trans (expect_le univ_nonempty fun hv _ => ?_)
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun i _ => ?_).trans
    (mean_norm_runValue_update_sub_le step hv.1 U ψ hψ T p hp (fun _ => hv.2))
  rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have bound := abs_measureProb_sub_le_norm_sub
    (ψ := post hv.1 i (runValue step U ψ (change hv i) T))
    (φ := post hv.1 i (runValue step U ψ hv.1 T))
    (by rw [LinearIsometry.norm_map, norm_runValue, hψ])
    (by rw [LinearIsometry.norm_map, norm_runValue, hψ]) (accept hv.1 i)
  simpa [score, change, ← map_sub] using bound

end Cslib.Quantum
