/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.SpectralCut

/-!
# The projectivity defect on spectral cuts

Compression of a measurement creates a defect equal to the mass lost across the cut,
in addition to the original defect on the retained coordinates. This is the defect
estimate used to round the compressed effects in [Vidick, Theorem 3.1][Vidick2022].
-/

public section

open Matrix Finset
open scoped MatrixOrder Matrix.Norms.Frobenius

namespace Cslib.Quantum.Measurement

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

local notation "Cuts" => {s : Finset ι // Finset.Nonempty s}

private abbrev CutBasis (s : Finset ι) := {i : ι // i ∈ s}

private def cutEmbedding (s : Finset ι) : CutBasis s ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩

private noncomputable def squareMass (M : Measurement α (Matrix ι ι ℂ)) (i j : ι) : ℝ :=
  ∑ a, ‖M.effect a i j‖ ^ 2

private theorem squareMass_comm (M : Measurement α (Matrix ι ι ℂ)) (i j : ι) :
    squareMass M i j = squareMass M j i := by
  simp only [squareMass, M.norm_effect_entry_swap _ i j]

private theorem squareMass_nonneg (M : Measurement α (Matrix ι ι ℂ)) (i j : ι) :
    0 ≤ squareMass M i j := sum_nonneg fun a _ => sq_nonneg ‖M.effect a i j‖

private theorem sum_squareMass_col_le_one (M : Measurement α (Matrix ι ι ℂ)) (j : ι) :
    ∑ i, squareMass M i j ≤ 1 := by
  simp_rw [squareMass_comm M _ j]
  unfold squareMass
  rw [sum_comm]
  exact M.sum_norm_effect_row_sq_le_one j

private noncomputable def leakage (M : Measurement α (Matrix ι ι ℂ)) (s : Finset ι) : ℝ :=
  ∑ j ∈ s, ∑ i ∈ univ.filter (· ∉ s), squareMass M i j

private theorem leakage_eq_commutator (M : Measurement α (Matrix ι ι ℂ)) (s : Finset ι) :
    let P := diagonal fun i => if i ∈ s then (1 : ℂ) else 0
    (∑ a, ‖M.effect a * P - P * M.effect a‖ ^ 2) = 2 * leakage M s := by
  intro P
  have hent (a : α) (i j : ι) :
      ‖(M.effect a * P - P * M.effect a) i j‖ ^ 2 =
        (if i ∈ s ∧ j ∉ s then ‖M.effect a i j‖ ^ 2 else 0) +
        (if j ∈ s ∧ i ∉ s then ‖M.effect a i j‖ ^ 2 else 0) := by
    change ‖(M.effect a * P) i j - (P * M.effect a) i j‖ ^ 2 = _
    dsimp only [P]
    rw [mul_diagonal, diagonal_mul]
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [hi, hj]
  have hsplit (a : α) :
      ‖M.effect a * P - P * M.effect a‖ ^ 2 =
        2 * ∑ j ∈ s, ∑ i ∈ univ.filter (· ∉ s), ‖M.effect a i j‖ ^ 2 := by
    rw [frobenius_norm_sq_eq_sum]
    simp_rw [hent, sum_add_distrib]
    have hswap :
        (∑ i, ∑ j, if i ∈ s ∧ j ∉ s then ‖M.effect a i j‖ ^ 2 else 0) =
          ∑ j, ∑ i, if j ∈ s ∧ i ∉ s then ‖M.effect a i j‖ ^ 2 else 0 := by
      refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
      rw [M.norm_effect_entry_swap a j i]
    rw [hswap, sum_comm (f := fun i j => if j ∈ s ∧ i ∉ s then ‖M.effect a i j‖ ^ 2 else 0)]
    have hf :
        (∑ j, ∑ i, if j ∈ s ∧ i ∉ s then ‖M.effect a i j‖ ^ 2 else 0) =
          ∑ j ∈ s, ∑ i ∈ univ.filter (· ∉ s), ‖M.effect a i j‖ ^ 2 := by
      rw [← show (univ.filter (· ∈ s) : Finset ι) = s by ext; simp, sum_filter]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_filter]
      by_cases hj : j ∈ s <;> simp [hj]
    rw [hf]
    ring
  simp_rw [hsplit, ← mul_sum]
  congr 1
  unfold leakage squareMass
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_comm

omit [DecidableEq ι] in
private theorem sum_width_slice (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (f : ι → ℝ) :
    (∑ s : Cuts, diagonalCutWidth d s * ∑ j ∈ s.val, f j) = ∑ j, d j * f j := by
  classical
  calc
    _ = ∑ s : Cuts, ∑ j, (diagonalCutWidth d s * (if j ∈ s.val then 1 else 0)) * f j := by
      refine sum_congr rfl fun s _ => ?_
      rw [← show univ.filter (· ∈ s.val) = s.val by ext; simp, sum_filter, mul_sum]
      exact sum_congr rfl fun j _ => by by_cases hj : j ∈ s.val <;> simp [hj]
    _ = _ := by
      rw [sum_comm]
      simp_rw [← sum_mul, sum_diagonalCutWidth_mem d _ (hd _)]

private theorem weighted_original_defect_le (M : Measurement α (Matrix ι ι ℂ))
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) (δ : ℝ)
    (hagree : 1 - δ ≤ ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) * squareMass M i j) :
    (∑ j, d j * (1 - ∑ i, squareMass M i j)) ≤ δ := by
  have hamgm (i j : ι) : Real.sqrt (d i) * Real.sqrt (d j) ≤ (d i + d j) / 2 := by
    nlinarith [Real.sq_sqrt (hd i), Real.sq_sqrt (hd j),
      sq_nonneg (Real.sqrt (d i) - Real.sqrt (d j))]
  have hsum : (∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) * squareMass M i j) ≤
      ∑ j, d j * ∑ i, squareMass M i j := by
    calc
      _ ≤ ∑ i, ∑ j, ((d i + d j) / 2) * squareMass M i j :=
        sum_le_sum fun i _ => sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hamgm i j) (squareMass_nonneg M i j)
      _ = _ := by
        simp_rw [div_mul_eq_mul_div, ← sum_div, add_mul, sum_add_distrib]
        have hsym : (∑ i, ∑ j, d i * squareMass M i j) =
            ∑ j, ∑ i, d j * squareMass M i j := by
          exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by
            rw [squareMass_comm M j i]
        rw [hsym, sum_comm (f := fun i j => d j * squareMass M i j)]
        simp only [← mul_sum]
        ring
  simp_rw [mul_sub, mul_one, sum_sub_distrib]
  rw [htrace]
  linarith

private theorem cut_defect_eq (M : Measurement α (Matrix ι ι ℂ)) (s : Finset ι) :
    (s.card : ℝ) - ∑ a, ‖(M.principalSubmatrix (cutEmbedding s)).effect a‖ ^ 2 =
      (∑ j ∈ s, (1 - ∑ i, squareMass M i j)) + leakage M s := by
  simp_rw [frobenius_norm_sq_eq_sum, principalSubmatrix_effect_apply]
  change (s.card : ℝ) - (∑ a, ∑ i : CutBasis s, ∑ j : CutBasis s,
    ‖M.effect a i.val j.val‖ ^ 2) = _
  have hmass : (∑ a, ∑ i : CutBasis s, ∑ j : CutBasis s, ‖M.effect a i.val j.val‖ ^ 2) =
      ∑ j ∈ s, ∑ i ∈ s, squareMass M i j := by
    rw [sum_comm]
    simp_rw [sum_comm (f := fun a (j : CutBasis s) => ‖M.effect a _ j.val‖ ^ 2)]
    rw [sum_comm]
    rw [Finset.sum_subtype (F := inferInstanceAs (Fintype (CutBasis s))) s (fun _ => Iff.rfl)]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.sum_subtype (F := inferInstanceAs (Fintype (CutBasis s))) s (fun _ => Iff.rfl)]
    simp only [squareMass]
  rw [hmass]
  unfold leakage
  rw [← sum_add_distrib]
  change (s.card : ℝ) - _ = _
  rw [show (s.card : ℝ) = ∑ _j ∈ s, (1 : ℝ) by simp, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hsplit := sum_filter_add_sum_filter_not univ (· ∈ s) (fun i => squareMass M i j)
  rw [show univ.filter (· ∈ s) = s by ext; simp] at hsplit
  linarith

/-- Width-weighted defect of the compressed POVMs. The defect on each cut is scaled by its
dimension, so this is the average normalized-trace defect with the spectral probability weights. -/
theorem sum_width_compression_defect_le (M : Measurement α (Matrix ι ι ℂ))
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) (δ : ℝ)
    (hagree : 1 - δ ≤ ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) *
      ∑ a, ‖M.effect a i j‖ ^ 2) :
    (∑ s : Cuts, diagonalCutWidth d s *
      ((s.val.card : ℝ) -
        ∑ a, ‖(M.principalSubmatrix (⟨Subtype.val, Subtype.val_injective⟩ :
          {i : ι // i ∈ s.val} ↪ ι)).effect a‖ ^ 2)) ≤ δ + Real.sqrt (2 * δ) := by
  change (∑ s : Cuts, diagonalCutWidth d s * ((s.val.card : ℝ) -
    ∑ a, ‖(M.principalSubmatrix (cutEmbedding s.val)).effect a‖ ^ 2)) ≤ _
  simp_rw [cut_defect_eq, mul_add, sum_add_distrib]
  rw [sum_width_slice d hd]
  have h₁ := weighted_original_defect_le M d hd htrace δ hagree
  have h₂ := M.sum_diagonalCutWidth_norm_commutator_sq_le d hd htrace δ hagree
  simp_rw [leakage_eq_commutator, mul_left_comm _ (2 : ℝ), ← mul_sum] at h₂
  linarith

end Cslib.Quantum.Measurement
