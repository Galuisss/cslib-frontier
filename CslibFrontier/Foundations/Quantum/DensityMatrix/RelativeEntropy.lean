/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefKernel
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PolarDecomposition
import CslibFrontier.Probability.Divergence

/-!
# Quantum relative entropy of finite density matrices

The finite value is the trace of the first state against the difference of the matrix logarithms.
It is finite precisely when the second state's kernel is contained in the first state's kernel.
Nonnegativity follows from classical Gibbs' inequality applied to the two distributions formed
from eigenvalues and squared overlaps of the eigenvectors. This supplies the nonnegativity
used in [Bavarian, Vidick and Yuen, Proposition 5.2][BavarianVidickYuen2022].

## Main results

* `exists_pmf_relativeEntropyReal_eq`: representation of the finite trace formula as a
  classical relative entropy.
* `relativeEntropy_nonneg`: Gibbs' inequality, including the infinite case.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The support of `ρ` is contained in that of `σ`, stated in terms of their kernels. -/
def SupportLE (ρ σ : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0

omit [DecidableEq ι] in
/-- Every matrix has its own support. -/
protected theorem SupportLE.refl (ρ : Matrix ι ι ℂ) : SupportLE ρ ρ :=
  fun _ h => h

omit [DecidableEq ι] in
/-- Support inclusion is transitive. -/
protected theorem SupportLE.trans {ρ σ τ : Matrix ι ι ℂ}
    (hρσ : SupportLE ρ σ) (hστ : SupportLE σ τ) : SupportLE ρ τ :=
  fun x hx => hρσ x (hστ x hx)

omit [DecidableEq ι] in
/-- The support of a positive semidefinite matrix is contained in that of every
larger positive semidefinite matrix. -/
theorem SupportLE.of_le {σ τ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (h : σ ≤ τ) :
    SupportLE σ τ := by
  intro x hx
  apply hσ.dotProduct_mulVec_zero_iff.mp
  have hdiff := ((Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x)
  rw [sub_mulVec, dotProduct_sub, hx, dotProduct_zero, zero_sub, neg_nonneg] at hdiff
  exact le_antisymm hdiff (hσ.dotProduct_mulVec_nonneg x)

omit [DecidableEq ι] in
/-- Support inclusion is preserved by nonnegative weighted sums of the pairs when the
reference matrices are positive semidefinite. -/
theorem SupportLE.sum_smul {κ : Type*} [Fintype κ] (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    {ρ σ : κ → Matrix ι ι ℂ} (hσ : ∀ k, (σ k).PosSemidef) (hs : ∀ k, SupportLE (ρ k) (σ k)) :
    SupportLE (∑ k, w k • ρ k) (∑ k, w k • σ k) := by
  intro x hx
  have hzero := (mulVec_sum_smul_eq_zero_iff univ w σ
    (fun k _ => hw k) (fun k _ => hσ k) x).mp hx
  rw [sum_mulVec]
  refine sum_eq_zero fun k hk => ?_
  rw [smul_mulVec]
  by_cases hwk : w k = 0
  · rw [hwk, zero_smul]
  · rw [hs k x (hzero k hk hwk), smul_zero]

omit [DecidableEq ι] in
/-- A rectangular compression preserves support inclusion when its reference is positive
semidefinite. -/
theorem SupportLE.conjTranspose_mul_mul {κ : Type*} [Fintype κ]
    {ρ σ : Matrix ι ι ℂ} (h : SupportLE ρ σ) (hσ : σ.PosSemidef) (V : Matrix ι κ ℂ) :
    SupportLE (Vᴴ * ρ * V) (Vᴴ * σ * V) := by
  intro x hx
  have he : star (V *ᵥ x) ⬝ᵥ (σ *ᵥ (V *ᵥ x)) = 0 := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, mulVec_mulVec, hx,
      dotProduct_zero]
  have hz := h (V *ᵥ x) (hσ.dotProduct_mulVec_zero_iff.mp he)
  rw [← mulVec_mulVec, ← mulVec_mulVec, hz, mulVec_zero]

omit [DecidableEq ι] in
/-- Principal submatrices inherit support inclusion from a pair with positive semidefinite
reference. -/
theorem SupportLE.submatrix {κ : Type*} [Fintype κ] {ρ σ : Matrix ι ι ℂ}
    (h : SupportLE ρ σ) (hσ : σ.PosSemidef) (f : κ → ι) :
    SupportLE (ρ.submatrix f f) (σ.submatrix f f) := by
  classical
  let V := (1 : Matrix ι ι ℂ).submatrix (Equiv.refl ι) f
  have hcomp (A : Matrix ι ι ℂ) : Vᴴ * A * V = A.submatrix f f := by
    dsimp only [V]
    rw [conjTranspose_submatrix, conjTranspose_one, one_submatrix_mul f (Equiv.refl ι),
      mul_submatrix_one (Equiv.refl ι) f, submatrix_submatrix]
    rfl
  rw [← hcomp ρ, ← hcomp σ]
  exact h.conjTranspose_mul_mul hσ V

/-- The finite trace formula, with the logarithm assigned zero on the kernel. -/
noncomputable def relativeEntropyReal (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace.re

open Classical in
/-- Umegaki relative entropy in nats, taking value infinity on a support mismatch. -/
noncomputable def relativeEntropy (ρ σ : Matrix ι ι ℂ) : WithTop ℝ :=
  if SupportLE ρ σ then (relativeEntropyReal ρ σ : WithTop ℝ) else ⊤

theorem relativeEntropy_of_supportLE {ρ σ : Matrix ι ι ℂ} (h : SupportLE ρ σ) :
    relativeEntropy ρ σ = (relativeEntropyReal ρ σ : WithTop ℝ) := by
  simp only [relativeEntropy, ite_eq_left h]

theorem relativeEntropy_of_not_supportLE {ρ σ : Matrix ι ι ℂ} (h : ¬ SupportLE ρ σ) :
    relativeEntropy ρ σ = ⊤ := by
  simp only [relativeEntropy, ite_eq_right h]

/-- Relabelling both matrix coordinates by one equivalence preserves relative entropy. -/
theorem relativeEntropy_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.PosSemidef) :
    relativeEntropy (reindex e e ρ) (reindex e e σ) = relativeEntropy ρ σ := by
  let F := reindexStarAlgEquiv ℂ ℂ e
  have hσ' : (reindex e e σ).PosSemidef := hσ.submatrix e.symm
  have hsupp : SupportLE (reindex e e ρ) (reindex e e σ) ↔ SupportLE ρ σ := by
    constructor
    · intro h
      simpa only [reindex_apply, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
        using h.submatrix hσ' e
    · exact fun h => h.submatrix hσ e.symm
  by_cases hs : SupportLE ρ σ
  · have htr (A : Matrix ι ι ℂ) : (F A).trace = A.trace := by
      change (reindex e e A).trace = _
      simp only [trace, diag_apply, reindex_apply, submatrix_apply]
      exact e.symm.sum_comp (fun i : ι => A i i)
    have hc : Continuous F := F.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
    have hlog (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
        F (cfc Real.log A) = cfc Real.log (F A) :=
      StarAlgHomClass.map_cfc F Real.log A (A.finite_real_spectrum.continuousOn _)
        hc hA.isSelfAdjoint (hA.isSelfAdjoint.map F)
    rw [relativeEntropy_of_supportLE (hsupp.mpr hs), relativeEntropy_of_supportLE hs]
    change (relativeEntropyReal (F ρ) (F σ) : WithTop ℝ) = _
    rw [relativeEntropyReal, relativeEntropyReal, ← hlog ρ hρ, ← hlog σ hσ.isHermitian,
      ← map_sub, ← map_mul, htr]
  · rw [relativeEntropy_of_not_supportLE (mt hsupp.mp hs), relativeEntropy_of_not_supportLE hs]

private theorem trace_diagonal_mul_conj_re (a b : ι → ℝ) (W : Matrix ι ι ℂ) :
    (diagonal (fun i => (a i : ℂ)) * (W * diagonal (fun j => (b j : ℂ)) * Wᴴ)).trace.re =
      ∑ i, ∑ j, a i * b j * Complex.normSq (W i j) := by
  rw [Matrix.trace, Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [diag_apply, diagonal_mul, Matrix.mul_apply, Finset.mul_sum, Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_diagonal, conjTranspose_apply]
  rw [show (a i : ℂ) * (W i j * (b j : ℂ) * star (W i j)) =
    ((a i : ℂ) * (b j : ℂ)) * (W i j * star (W i j)) by ring]
  rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re]

private theorem eigenvalues_sum_of_density {A : Matrix ι ι ℂ} (h : IsDensityMatrix A) :
    ∑ i, h.posSemidef.isHermitian.eigenvalues i = 1 := by
  have ht := h.posSemidef.isHermitian.trace_eq_sum_eigenvalues
  rw [h.trace_eq_one] at ht
  change (1 : ℂ) = ∑ i, (h.posSemidef.isHermitian.eigenvalues i : ℂ) at ht
  exact_mod_cast ht.symm

private theorem sum_normSq_row (W : Matrix ι ι ℂ) (h : W * Wᴴ = 1) (i : ι) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h' := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) h
  simpa only [Matrix.mul_apply, conjTranspose_apply, Complex.star_def, Complex.mul_conj,
    Complex.re_sum, Complex.ofReal_re, Matrix.one_apply_eq, Complex.one_re] using h'

private theorem sum_normSq_col (W : Matrix ι ι ℂ) (h : Wᴴ * W = 1) (j : ι) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h' : Wᴴ * Wᴴᴴ = 1 := by rwa [conjTranspose_conjTranspose]
  have hr := sum_normSq_row Wᴴ h' j
  simpa only [conjTranspose_apply, Complex.star_def, Complex.normSq_conj] using hr

/-- The trace pairing with a spectral function can be evaluated in the two eigenbases. -/
private theorem trace_mul_cfc_re (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) :
    (A * cfc f B).trace.re = ∑ i, ∑ j, hA.eigenvalues i * f (hB.eigenvalues j) *
      Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
        (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j) := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let D := diagonal (fun i => (hA.eigenvalues i : ℂ))
  let E := diagonal (fun j => (f (hB.eigenvalues j) : ℂ))
  let W : Matrix ι ι ℂ := (U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)
  have hD : A = Unitary.conjStarAlgAut ℂ _ U D := hA.spectral_theorem
  have hE : cfc f B = Unitary.conjStarAlgAut ℂ _ V E := hB.cfc_eq f
  have htrace : (A * cfc f B).trace = (D * (W * E * Wᴴ)).trace := by
    rw [hD, hE, ← trace_conjStarAlgAut (star U), map_mul]
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_conjTranspose]
    have hu : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 := Unitary.coe_star_mul_self U
    simp only [← Matrix.mul_assoc]
    rw [hu, Matrix.one_mul, Matrix.mul_assoc D (U : Matrix ι ι ℂ)ᴴ (U : Matrix ι ι ℂ),
      hu, Matrix.mul_one]
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc]
  rw [htrace]
  exact trace_diagonal_mul_conj_re _ _ _


/-- A source eigenvalue weighted by its overlap with a reference kernel vector vanishes
under support inclusion. -/
theorem eigenvalue_mul_overlap_eq_zero_of_supportLE {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : SupportLE A B) (i j : ι)
    (hj : hB.eigenvalues j = 0) :
    hA.eigenvalues i * Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
        (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j) = 0 := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let D := diagonal (fun k => (hA.eigenvalues k : ℂ))
  have hBv := hB.mulVec_eigenvectorBasis j
  rw [hj] at hBv
  have hAv : A *ᵥ (fun k => (V : Matrix ι ι ℂ) k j) = 0 := by
    apply hs
    simpa only [V, IsHermitian.eigenvectorUnitary_apply, RCLike.ofReal_zero, zero_smul]
      using hBv
  have hcol (k : ι) : (A * (V : Matrix ι ι ℂ)) k j = 0 :=
    congrFun hAv k
  have hAU : (U : Matrix ι ι ℂ)ᴴ * A = D * (U : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    change (U : Matrix ι ι ℂ)ᴴ * Unitary.conjStarAlgAut ℂ _ U D = _
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      show (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 from Unitary.coe_star_mul_self U,
      Matrix.one_mul]
  have hmat : D * ((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)) =
      (U : Matrix ι ι ℂ)ᴴ * (A * (V : Matrix ι ι ℂ)) := by
    rw [← Matrix.mul_assoc, ← hAU, Matrix.mul_assoc]
  have hz := congrArg (fun M : Matrix ι ι ℂ => M i j) hmat
  change (D * ((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ))) i j =
    ((U : Matrix ι ι ℂ)ᴴ * (A * (V : Matrix ι ι ℂ))) i j at hz
  dsimp only [D] at hz
  rw [diagonal_mul, Matrix.mul_apply (M := (U : Matrix ι ι ℂ)ᴴ)
    (N := A * (V : Matrix ι ι ℂ))] at hz
  simp only [hcol, mul_zero, Finset.sum_const_zero] at hz
  rcases mul_eq_zero.mp hz with ha | hw
  · have ha' : hA.eigenvalues i = 0 := Complex.ofReal_eq_zero.mp ha
    rw [ha', zero_mul]
  · change _ * Complex.normSq (((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)) i j) = _
    rw [hw, Complex.normSq_zero, mul_zero]

/-- The squared overlaps with the eigenbasis of the second matrix sum to one in each row. -/
theorem sum_eigenbasis_overlap_row {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : ι) :
    (∑ j, Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
      (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j)) = 1 := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  apply sum_normSq_row
  change ((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)) *
    ((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ))ᴴ = 1
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (V : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)ᴴ (U : Matrix ι ι ℂ),
    show (V : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)ᴴ = 1 from Unitary.coe_mul_star_self V,
    Matrix.one_mul]
  exact Unitary.coe_star_mul_self U

/-- The finite trace formula expressed in the eigenbases of its two arguments. -/
theorem relativeEntropyReal_eq_sum_eigenbasis {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    relativeEntropyReal A B = ∑ i, ∑ j,
      (hA.eigenvalues i * Real.log (hA.eigenvalues i) -
        hA.eigenvalues i * Real.log (hB.eigenvalues j)) *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
          (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j) := by
  have hself : (A * cfc Real.log A).trace.re =
      ∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i) := by
    rw [trace_mul_cfc_re _ _ hA hA,
      show (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1
        from Unitary.coe_star_mul_self hA.eigenvectorUnitary]
    refine sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  rw [relativeEntropyReal, mul_sub, trace_sub, Complex.sub_re, hself, trace_mul_cfc_re _ _ hA hB]
  simp only [sub_mul, sum_sub_distrib, ← Finset.mul_sum, sum_eigenbasis_overlap_row, mul_one]

/-- The finite trace formula equals the classical divergence of the two distributions
obtained by weighting squared eigenbasis overlaps with the two sets of eigenvalues. -/
theorem exists_pmf_relativeEntropyReal_eq {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (hs : SupportLE ρ σ) :
    ∃ p q : PMF (ι × ι), p.support ⊆ q.support ∧
      relativeEntropyReal ρ σ = ∑ z, (p z).toReal * Real.log ((p z).toReal / (q z).toReal) := by
  let hA := hρ.posSemidef.isHermitian
  let hB := hσ.posSemidef.isHermitian
  let a := hA.eigenvalues
  let b := hB.eigenvalues
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let W : Matrix ι ι ℂ := (U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)
  let w (i j : ι) := Complex.normSq (W i j)
  have ha : ∀ i, 0 ≤ a i := hρ.posSemidef.eigenvalues_nonneg
  have hb : ∀ j, 0 ≤ b j := hσ.posSemidef.eigenvalues_nonneg
  have hw (i j : ι) : 0 ≤ w i j := Complex.normSq_nonneg _
  have hrow (i : ι) : ∑ j, w i j = 1 := sum_eigenbasis_overlap_row hA hB i
  have hcol (j : ι) : ∑ i, w i j = 1 := by
    apply sum_normSq_col
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix ι ι ℂ) (U : Matrix ι ι ℂ)ᴴ (V : Matrix ι ι ℂ),
      show (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 from Unitary.coe_mul_star_self U,
      Matrix.one_mul]
    exact Unitary.coe_star_mul_self V
  let p : PMF (ι × ι) := PMF.ofFintype (fun z => ENNReal.ofReal (a z.1 * w z.1 z.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (ha _) (hw _ _)),
      Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hrow, mul_one,
      show ∑ i, a i = 1 from eigenvalues_sum_of_density hρ, ENNReal.ofReal_one])
  let q : PMF (ι × ι) := PMF.ofFintype (fun z => ENNReal.ofReal (b z.2 * w z.1 z.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (hb _) (hw _ _)),
      Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.mul_sum, hcol, mul_one,
      show ∑ j, b j = 1 from eigenvalues_sum_of_density hσ, ENNReal.ofReal_one])
  have hp (i j : ι) : (p (i, j)).toReal = a i * w i j := by
    dsimp only [p]
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (mul_nonneg (ha _) (hw _ _))]
  have hq (i j : ι) : (q (i, j)).toReal = b j * w i j := by
    dsimp only [q]
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (mul_nonneg (hb _) (hw _ _))]
  have hsupp : p.support ⊆ q.support := by
    rintro ⟨i, j⟩ hi
    have hp' : a i * w i j ≠ 0 := by
      rw [← hp]
      exact ENNReal.toReal_ne_zero.mpr ⟨hi, PMF.apply_ne_top _ _⟩
    have hb' : b j ≠ 0 := fun hz =>
      hp' (eigenvalue_mul_overlap_eq_zero_of_supportLE hA hB hs i j hz)
    have hq' : (q (i, j)).toReal ≠ 0 := by
      rw [hq]
      exact mul_ne_zero hb' (right_ne_zero_of_mul hp')
    exact (ENNReal.toReal_ne_zero.mp hq').1
  refine ⟨p, q, hsupp, ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [hp, hq]
  have hterm (i j : ι) : a i * w i j * Real.log (a i * w i j / (b j * w i j)) =
      (a i * Real.log (a i) - a i * Real.log (b j)) * w i j := by
    by_cases hz : a i * w i j = 0
    · rcases mul_eq_zero.mp hz with hz' | hz'
      · simp [hz']
      · simp [hz']
    · have hb' : b j ≠ 0 := fun hz' =>
        hz (eigenvalue_mul_overlap_eq_zero_of_supportLE hA hB hs i j hz')
      rw [mul_div_mul_right _ _ (right_ne_zero_of_mul hz),
        Real.log_div (left_ne_zero_of_mul hz) hb']
      ring
  rw [relativeEntropyReal_eq_sum_eigenbasis hA hB]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => (hterm i j).symm

/-- Finite quantum relative entropy is nonnegative whenever the supports are compatible. -/
theorem relativeEntropyReal_nonneg {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (hs : SupportLE ρ σ) : 0 ≤ relativeEntropyReal ρ σ := by
  obtain ⟨p, q, hsub, he⟩ := exists_pmf_relativeEntropyReal_eq hρ hσ hs
  rw [he]
  exact Cslib.Probability.PMF.sum_mul_log_div_nonneg hsub

@[simp] theorem relativeEntropy_self (ρ : Matrix ι ι ℂ) : relativeEntropy ρ ρ = 0 := by
  rw [relativeEntropy_of_supportLE (SupportLE.refl ρ), relativeEntropyReal, sub_self,
    Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  rfl

/-- Quantum relative entropy is nonnegative, with an infinite value if the support test fails. -/
theorem relativeEntropy_nonneg {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) : 0 ≤ relativeEntropy ρ σ := by
  by_cases h : SupportLE ρ σ
  · rw [relativeEntropy_of_supportLE h]
    exact_mod_cast relativeEntropyReal_nonneg hρ hσ h
  · rw [relativeEntropy_of_not_supportLE h]
    exact le_top

/-- Scaling the reference by a positive constant subtracts the logarithm of that
constant times the source trace. The identity uses only the support of the source. -/
theorem relativeEntropy_smul_right {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) {c : ℝ} (hc : 0 < c) :
    relativeEntropy ρ (c • σ) =
      relativeEntropy ρ σ + ((-(Real.log c * ρ.trace.re) : ℝ) : WithTop ℝ) := by
  have hsupp : SupportLE ρ (c • σ) ↔ SupportLE ρ σ := by
    simp only [SupportLE, smul_mulVec, smul_eq_zero, hc.ne', false_or]
  by_cases hs : SupportLE ρ σ
  · have hfinite : (spectrum ℝ σ).Finite :=
      hσ.spectrum_real_eq_range_eigenvalues.symm ▸ Set.finite_range _
    have hcomp : cfc Real.log (c • σ) = cfc (fun x : ℝ => Real.log (c * x)) σ :=
      (cfc_comp_const_mul c Real.log σ
        ((hfinite.image _).continuousOn Real.log) hσ.isSelfAdjoint).symm
    rw [relativeEntropy_of_supportLE (hsupp.mpr hs), relativeEntropy_of_supportLE hs,
      ← WithTop.coe_add, WithTop.coe_eq_coe]
    simp only [relativeEntropyReal, mul_sub, trace_sub, Complex.sub_re]
    have hρtrace : ρ.trace.re = ∑ i, hρ.eigenvalues i := by
      rw [hρ.trace_eq_sum_eigenvalues, Complex.re_sum]
      exact sum_congr rfl fun i _ => Complex.ofReal_re (hρ.eigenvalues i)
    have htrace : (ρ * cfc (fun x : ℝ => Real.log (c * x)) σ).trace.re =
        (ρ * cfc Real.log σ).trace.re + Real.log c * ρ.trace.re := by
      rw [trace_mul_cfc_re _ _ hρ hσ, trace_mul_cfc_re _ _ hρ hσ,
        hρtrace, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      have hrow := sum_eigenbasis_overlap_row hρ hσ i
      rw [← mul_one (Real.log c * hρ.eigenvalues i), ← hrow, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      by_cases hz : hσ.eigenvalues j = 0
      · have hzero := eigenvalue_mul_overlap_eq_zero_of_supportLE hρ hσ hs i j hz
        simp only [hz, mul_zero, Real.log_zero, zero_mul, zero_add]
        rw [mul_assoc, hzero, mul_zero]
      · rw [Real.log_mul hc.ne' hz]
        ring
    rw [hcomp, htrace]
    ring
  · rw [relativeEntropy_of_not_supportLE hs,
      relativeEntropy_of_not_supportLE (fun h => hs (hsupp.mp h))]
    simp

end Cslib.Quantum
