/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Orthogonalization
public import CslibFrontier.Foundations.Quantum.Naimark

/-!
# Orthogonalization of measurements

A measurement whose effects are almost idempotent in a state is close to a projective measurement
in that state, with no loss in the dimension: for a measurement `M` on `ℂ^ι` and any state `φ` on
the matrix algebra there is a projective measurement `P` on `ℂ^ι` with

`∑_a ‖M_a - P_a‖²_φ ≤ 9 (1 - φ(∑_a M_a²))`

(`Cslib.Quantum.Measurement.exists_isProjective_sum_norm_sub_sq_le`). This is
[de la Salle, Theorem 1.2][delaSalle2022] (arXiv:2103.14126v2) for the finite von Neumann algebra
`M_ι(ℂ)`. Since `φ` is an arbitrary state, `P` stays on the factor `M` acts on, which rigidity
arguments for tensor-product strategies need. The orthogonalization lemma of Kempe, Kobayashi,
Matsumoto, Toner and Vidick, and its quantitative versions, have error polynomial in `ε`; de la
Salle's is linear.

The proof follows §3 of the paper, with its two lemmas made explicit in finite dimension:

* **Selection** (Lemma 3.1). Diagonalize each effect, `M_a = U_a diag(λ_a) U_aᴴ`, and select
  `|ι|` of the pairs `(a, k)`: the ones of largest weight `λ_{a,k} φ(U_a e_k e_kᴴ U_aᴴ)`. The
  projections `q_a` onto the selected eigenvectors commute with `M_a`, have total rank `|ι|`, and
  satisfy `φ(∑_a M_a²) ≤ φ(∑_a q_a M_a)`: the eigenvalues form a fractional selection of total
  mass `|ι|`, and the largest weights beat every such selection
  (`Cslib.exists_card_eq_sum_mul_le`). This replaces the paper's Krein–Milman argument.
* **Polar decomposition** (Lemma 3.2). The rows `√λ_{a,k} (U_a e_k)ᴴ` of the selected pairs form a
  square matrix `y` with `yᴴ y = ∑_a q_a M_a`. Its polar decomposition `y = R |y|`, with `R`
  unitary (`Cslib.Quantum.exists_polar`), gives the projective measurement
  `P_a = Rᴴ T_a R`, where `T_a` projects onto the selected pairs with outcome `a`, and
  `|y| P_a |y| = q_a M_a`.
* **Estimate.** `Cslib.Quantum.Measurement.sum_norm_sub_sq_le_of_dilation` turns these data into
  the bound, in any star-ordered algebra.

## Main results

* `Cslib.exists_card_eq_sum_mul_le`: the `d` largest weights beat every fractional selection of
  mass `d`.
* `Cslib.Quantum.exists_polar`: polar decomposition of a square matrix.
* `Cslib.Quantum.Measurement.exists_isProjective_sum_norm_sub_sq_le`,
  `Cslib.Quantum.Measurement.exists_isProjective_sum_norm_sub_sq_le_of_le`: orthogonalization.

## References

* [M. de la Salle, *Orthogonalization of positive operator valued measures*][delaSalle2022]
-/

@[expose] public section

open Matrix Finset
open scoped MatrixOrder ComplexOrder

namespace Cslib


/-- The `d` largest weights beat every fractional selection of total mass `d`. -/
theorem exists_card_eq_sum_mul_le {N : Type*} [Fintype N] (w c : N → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) {d : ℕ} (hd : ∑ i, c i = d) :
    ∃ S : Finset N, S.card = d ∧ ∑ i, w i * c i ≤ ∑ i ∈ S, w i := by
  classical
  have hdN : d ≤ Fintype.card N := by
    have : (d : ℝ) ≤ Fintype.card N := by
      rw [← hd]
      calc ∑ i, c i ≤ ∑ _i : N, (1 : ℝ) := sum_le_sum fun i _ => hc1 i
        _ = Fintype.card N := by simp
    exact_mod_cast this
  have hne : (powersetCard d (univ : Finset N)).Nonempty :=
    powersetCard_nonempty.mpr (by simpa using hdN)
  obtain ⟨S, hS, hmax⟩ := exists_max_image _ (fun S => ∑ i ∈ S, w i) hne
  have hcard : S.card = d := (mem_powersetCard.mp hS).2
  refine ⟨S, hcard, ?_⟩
  -- Exchange: every weight outside `S` is at most every weight inside.
  have hex : ∀ s ∈ S, ∀ t ∉ S, w t ≤ w s := by
    intro s hs t ht
    by_contra hlt
    rw [not_le] at hlt
    have hmem : insert t (S.erase s) ∈ powersetCard d (univ : Finset N) := by
      refine mem_powersetCard.mpr ⟨subset_univ _, ?_⟩
      rw [card_insert_of_notMem (fun h => ht (mem_of_mem_erase h)), card_erase_of_mem hs, hcard]
      have : 0 < d := hcard ▸ card_pos.mpr ⟨s, hs⟩
      omega
    have := hmax _ hmem
    rw [sum_insert (fun h => ht (mem_of_mem_erase h)), ← add_sum_erase S w hs] at this
    linarith
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · -- `d = 0`, so all `c i = 0`.
    subst hS0
    have hd0 : d = 0 := by simpa using hcard.symm
    have hc : ∀ i, c i = 0 := fun i =>
      (sum_eq_zero_iff_of_nonneg fun i _ => hc0 i).mp (by rw [hd, hd0]; simp) i (mem_univ i)
    simp [hc]
  · set τ := S.inf' hSne w
    have hin : ∀ s ∈ S, τ ≤ w s := fun s hs => inf'_le _ hs
    have hout : ∀ t ∉ S, w t ≤ τ := fun t ht => (le_inf'_iff _ _).mpr fun s hs => hex s hs t ht
    have hsplit : ∑ i, w i * c i = ∑ i ∈ S, w i * c i + ∑ i ∈ univ \ S, w i * c i := by
      rw [add_comm, sum_sdiff (subset_univ S)]
    have hcsplit : ∑ i ∈ S, c i + ∑ i ∈ univ \ S, c i = d := by
      rw [add_comm, sum_sdiff (subset_univ S), hd]
    have h₁ : ∑ i ∈ univ \ S, w i * c i ≤ ∑ i ∈ univ \ S, τ * c i :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hout i (mem_sdiff.mp hi).2) (hc0 i)
    have h₂ : ∑ i ∈ S, τ * (1 - c i) ≤ ∑ i ∈ S, w i * (1 - c i) :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hin i hi) (sub_nonneg.mpr (hc1 i))
    have h₃ : ∑ i ∈ S, (1 - c i) = d - ∑ i ∈ S, c i := by
      rw [sum_sub_distrib]; simp [hcard]
    rw [← mul_sum] at h₁ h₂
    rw [h₃] at h₂
    have h₄ : ∑ i ∈ S, w i * (1 - c i) = ∑ i ∈ S, w i - ∑ i ∈ S, w i * c i := by
      rw [← sum_sub_distrib]; simp [mul_sub]
    rw [h₄] at h₂
    have : ∑ i ∈ univ \ S, c i = d - ∑ i ∈ S, c i := by linarith
    rw [this] at h₁
    linarith

end Cslib

namespace Cslib.Quantum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary diagonalization of a Hermitian matrix, with `Uᴴ` on the right. -/
theorem exists_unitary_eq_diagonal {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * diagonal (fun k => (hA.eigenvalues k : ℂ)) * Uᴴ := by
  refine ⟨hA.eigenvectorUnitary, ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]


/-- **Polar decomposition** of a square matrix `y : m × n`, `|m| = |n|`: a unitary `R` and
`h = |y| ≥ 0` with `h² = yᴴ y` and `y = R h`; if `yᴴ y ≤ 1` then `h ≤ 1`. -/
theorem exists_polar {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (y : Matrix m n ℂ) (hmn : Fintype.card m = Fintype.card n) :
    ∃ (R : Matrix m n ℂ) (h : Matrix n n ℂ), Rᴴ * R = 1 ∧ R * Rᴴ = 1 ∧ h.PosSemidef ∧
      h * h = yᴴ * y ∧ y = R * h ∧ (yᴴ * y ≤ 1 → h ≤ 1) := by
  classical
  set B := yᴴ * y
  have hB : B.PosSemidef := posSemidef_conjTranspose_mul_self y
  set μ := hB.1.eigenvalues
  have hμ0 : ∀ k, 0 ≤ μ k := hB.eigenvalues_nonneg
  obtain ⟨U, hU1, hU2, hBU⟩ := exists_unitary_eq_diagonal hB.1
  set s : n → ℝ := fun k => √(μ k)
  have hss : ∀ k, s k * s k = μ k := fun k => Real.mul_self_sqrt (hμ0 k)
  set Y := y * U
  -- Columns of `Y` are orthogonal with squared norms `μ`.
  have hYY : Yᴴ * Y = diagonal (fun k => (μ k : ℂ)) := by
    have : Yᴴ * Y = Uᴴ * B * U := by
      simp only [Y, conjTranspose_mul, Matrix.mul_assoc, B]
    rw [this, hBU]
    simp only [← Matrix.mul_assoc, hU1, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
  have hcol : ∀ k l, ∑ i, star (Y i k) * Y i l = if k = l then (μ k : ℂ) else 0 := fun k l => by
    have := congrFun (congrFun hYY k) l
    simpa [Matrix.mul_apply, diagonal_apply] using this
  have hY0 : ∀ k, μ k = 0 → ∀ i, Y i k = 0 := fun k hk i => by
    have h0 : ∑ i, star (Y i k) * Y i k = 0 := by
      rw [hcol, ite_eq_left rfl, hk, Complex.ofReal_zero]
    have hn : ∀ i, star (Y i k) * Y i k = ((‖Y i k‖ ^ 2 : ℝ) : ℂ) := fun i => by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [hn] at h0
    rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h0
    have := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖Y i k‖).mp h0 i (mem_univ i)
    simpa using this
  -- The normalized nonzero columns form an isometry.
  let P := {k : n // μ k ≠ 0}
  let W : Matrix m P ℂ := Matrix.of fun i k => Y i k.1 / (s k.1 : ℂ)
  have hs0 : ∀ k : P, (s k.1 : ℂ) ≠ 0 := fun k => by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr (lt_of_le_of_ne (hμ0 k.1) (Ne.symm k.2))).ne'
  have hW : Wᴴ * W = 1 := by
    ext k l
    simp only [Matrix.mul_apply, conjTranspose_apply, W, Matrix.of_apply, Matrix.one_apply]
    have : ∀ i, star (Y i k.1 / (s k.1 : ℂ)) * (Y i l.1 / (s l.1 : ℂ)) =
        (star (Y i k.1) * Y i l.1) / ((s k.1 : ℂ) * (s l.1 : ℂ)) := fun i => by
      rw [star_div₀, Complex.star_def, Complex.conj_ofReal]; ring
    simp only [this, ← sum_div, hcol]
    by_cases hkl : k = l
    · subst hkl
      rw [ite_eq_left rfl, ite_eq_left rfl, ← Complex.ofReal_mul, hss, div_self]
      exact_mod_cast k.2
    · rw [ite_eq_right (fun h => absurd (Subtype.ext h) hkl), ite_eq_right (absurd · hkl), zero_div]
  -- Extend to a unitary and reindex.
  let σ : n ≃ m := Fintype.equivOfCardEq hmn.symm
  obtain ⟨U', hU', hU'W⟩ := exists_unitary_extension W hW
    (j := fun k : P => σ k.1) (fun a b hab => Subtype.ext (σ.injective hab))
  have hU'1 : U'ᴴ * U' = 1 := by
    rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff'.mp hU')
  have hU'2 : U' * U'ᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff.mp hU')
  set R' : Matrix m n ℂ := U'.submatrix id σ
  have hR'1 : R'ᴴ * R' = 1 := by
    ext k l
    have := congrFun (congrFun hU'1 (σ k)) (σ l)
    simpa [Matrix.mul_apply, R', Matrix.one_apply, σ.injective.eq_iff] using this
  have hR'2 : R' * R'ᴴ = 1 := by
    ext i i'
    have := congrFun (congrFun hU'2 i) i'
    simp only [Matrix.mul_apply, conjTranspose_apply, R', submatrix_apply, id] at this ⊢
    rw [← this]
    exact σ.sum_comp (fun j => U' i j * star (U' i' j))
  have hR'Y : R' * diagonal (fun k => (s k : ℂ)) = Y := by
    ext i k
    rw [mul_diagonal]
    by_cases hk : μ k = 0
    · rw [hY0 k hk i]
      simp [s, hk]
    · have h1 := hU'W i ⟨k, hk⟩
      simp only [R', submatrix_apply, id, W, Matrix.of_apply] at h1 ⊢
      rw [h1, div_mul_cancel₀ _ (hs0 ⟨k, hk⟩)]
  set h := U * diagonal (fun k => (s k : ℂ)) * Uᴴ
  refine ⟨R' * Uᴴ, h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc R'ᴴ,
      hR'1, Matrix.one_mul, hU2]
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ,
      hU1, Matrix.one_mul, hR'2]
  · exact (posSemidef_diagonal_iff.mpr fun k =>
      Complex.zero_le_real.mpr (Real.sqrt_nonneg _)).mul_mul_conjTranspose_same U
  · have : h * h = U * diagonal (fun k => (μ k : ℂ)) * Uᴴ := by
      simp only [h, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU1, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
        diagonal_mul_diagonal]
      congr 3
      ext k
      rw [← Complex.ofReal_mul, hss]
    rw [this, hBU]
  · simp only [h, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc R', hU1, Matrix.mul_one, hR'Y, Matrix.mul_assoc, hU2, Matrix.mul_one]
  · intro hB1
    have hd : (1 - diagonal (fun k => (μ k : ℂ))).PosSemidef := by
      have := (Matrix.le_iff.mp hB1).conjTranspose_mul_mul_same U
      rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU1, hBU, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hU1, Matrix.one_mul, Matrix.mul_assoc, hU1, Matrix.mul_one] at this
    have hμ1 : ∀ k, μ k ≤ 1 := fun k => by
      have := hd.diag_nonneg (i := k)
      rw [Matrix.sub_apply, one_apply_eq, diagonal_apply_eq] at this
      have h' : ((1 - μ k : ℝ) : ℂ) ≥ 0 := by push_cast; exact this
      have := Complex.zero_le_real.mp h'
      linarith
    rw [Matrix.le_iff]
    have : 1 - h = U * diagonal (fun k => ((1 - s k : ℝ) : ℂ)) * Uᴴ := by
      have e : diagonal (fun k => ((1 - s k : ℝ) : ℂ)) = 1 - diagonal (fun k => (s k : ℂ)) := by
        ext i j; by_cases hij : i = j <;> simp [hij]
      rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]
    rw [this]
    refine (posSemidef_diagonal_iff.mpr fun k =>
      Complex.zero_le_real.mpr ?_).mul_mul_conjTranspose_same U
    have := Real.sqrt_le_one.mpr (hμ1 k)
    simp only [s]
    linarith

/-- `U diag(f) Uᴴ` for a real vector `f`. -/
private noncomputable def conjDiag (U : Matrix ι ι ℂ) (f : ι → ℝ) : Matrix ι ι ℂ :=
  U * diagonal (fun k => (f k : ℂ)) * Uᴴ

variable {U : Matrix ι ι ℂ}

private theorem conjDiag_mul (hU : Uᴴ * U = 1) (f g : ι → ℝ) :
    conjDiag U f * conjDiag U g = conjDiag U (f * g) := by
  simp only [conjDiag, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
    diagonal_mul_diagonal]
  congr 3
  ext k
  simp

private theorem conjDiag_sub (f g : ι → ℝ) : conjDiag U (f - g) = conjDiag U f - conjDiag U g := by
  simp only [conjDiag, ← Matrix.mul_sub, ← Matrix.sub_mul, diagonal_sub]
  congr 3
  ext k
  simp

private theorem conjDiag_one (hU : U * Uᴴ = 1) : conjDiag U 1 = 1 := by
  simp [conjDiag, hU]

private theorem conjTranspose_conjDiag (f : ι → ℝ) : (conjDiag U f)ᴴ = conjDiag U f := by
  have : star (fun k => (f k : ℂ)) = fun k => (f k : ℂ) := by
    ext k; simp
  simp only [conjDiag, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc, this]

private theorem posSemidef_conjDiag {f : ι → ℝ} (hf : ∀ k, 0 ≤ f k) : (conjDiag U f).PosSemidef :=
  (posSemidef_diagonal_iff.mpr fun k =>
    Complex.zero_le_real.mpr (hf k)).mul_mul_conjTranspose_same U

private theorem conjDiag_eq_sum (f : ι → ℝ) :
    conjDiag U f = ∑ k, (f k : ℂ) • conjDiag U (Pi.single k 1) := by
  have : diagonal (fun k => (f k : ℂ)) =
      ∑ k, (f k : ℂ) • diagonal (fun j => (((Pi.single k (1 : ℝ) : ι → ℝ) j : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [diagonal_apply_eq, Matrix.sum_apply, Matrix.smul_apply, Pi.single_apply,
        smul_eq_mul]
      rw [sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    · simp [Matrix.sum_apply, hij]
  simp only [conjDiag, this, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

private theorem trace_conjDiag (hU : Uᴴ * U = 1) (f : ι → ℝ) :
    (conjDiag U f).trace = ∑ k, (f k : ℂ) := by
  rw [conjDiag, trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, trace_diagonal]


/-- A real-diagonal matrix bounded by `1` has diagonal entries at most `1`. -/
private theorem le_one_of_conjDiag_le_one (hU : Uᴴ * U = 1) {f : ι → ℝ}
    (h : conjDiag U f ≤ 1) (k : ι) : f k ≤ 1 := by
  have hd := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same U
  have e : Uᴴ * (1 - conjDiag U f) * U = 1 - diagonal (fun k => (f k : ℂ)) := by
    simp only [conjDiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU, ← Matrix.mul_assoc,
      Matrix.one_mul]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [e] at hd
  have := hd.diag_nonneg (i := k)
  rw [Matrix.sub_apply, one_apply_eq, diagonal_apply_eq] at this
  have h' : ((1 - f k : ℝ) : ℂ) ≥ 0 := by push_cast; exact this
  linarith [Complex.zero_le_real.mp h']

private theorem conjDiag_apply (f : ι → ℝ) (j j' : ι) :
    conjDiag U f j j' = ∑ k, U j k * (f k : ℂ) * star (U j' k) := by
  simp [conjDiag, Matrix.mul_apply, diagonal_apply]

/-- The state of `U diag(f) Uᴴ` is linear in `f`. -/
private theorem re_apply_conjDiag (φ : AlgState (Matrix ι ι ℂ)) (f : ι → ℝ) :
    (φ (conjDiag U f)).re = ∑ k, f k * (φ (conjDiag U (Pi.single k 1))).re := by
  conv_lhs => rw [conjDiag_eq_sum]
  rw [map_sum, Complex.re_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]

end Cslib.Quantum

namespace Cslib.Quantum.Measurement

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- **Orthogonalization of measurements** [de la Salle, §1, Theorem 1.2][delaSalle2022]: every
measurement `M` on `ℂ^ι` is close to a projective measurement `P` on `ℂ^ι` in any state `φ`:
`∑_a ‖M_a - P_a‖²_φ ≤ 9 (1 - φ(∑_a M_a²))`. -/
theorem exists_isProjective_sum_norm_sub_sq_le (φ : AlgState (Matrix ι ι ℂ))
    (M : Measurement α (Matrix ι ι ℂ)) :
    ∃ P : Measurement α (Matrix ι ι ℂ), P.IsProjective ∧
      ∑ a, φ.norm (M.effect a - P.effect a) ^ 2 ≤
        9 * (1 - ∑ a, (φ (M.effect a * M.effect a)).re) := by
  classical
  have hpsd : ∀ a, (M.effect a).PosSemidef := fun a => nonneg_iff_posSemidef.mp (M.nonneg a)
  choose U hU1 hU2 hUd using fun a => exists_unitary_eq_diagonal (hpsd a).1
  set lam : α → ι → ℝ := fun a => (hpsd a).1.eigenvalues
  have hM : ∀ a, M.effect a = conjDiag (U a) (lam a) := hUd
  have hl0 : ∀ a k, 0 ≤ lam a k := fun a => (hpsd a).eigenvalues_nonneg
  have hl1 : ∀ a k, lam a k ≤ 1 := fun a =>
    le_one_of_conjDiag_le_one (hU1 a) (hM a ▸ M.effect_le_one a)
  -- The eigenvalues of all effects sum to the dimension.
  have hsum : ∑ p : α × ι, lam p.1 p.2 = Fintype.card ι := by
    have h := congrArg (fun A : Matrix ι ι ℂ => A.trace) M.sum_effect
    simp only [trace_sum, hM, trace_conjDiag (hU1 _), trace_one] at h
    rw [Fintype.sum_prod_type]
    exact_mod_cast h
  -- Select the `|ι|` largest weights.
  set w : α × ι → ℝ := fun p => lam p.1 p.2 * (φ (conjDiag (U p.1) (Pi.single p.2 1))).re
  obtain ⟨S, hS, hSw⟩ := exists_card_eq_sum_mul_le w (fun p => lam p.1 p.2)
    (fun p => hl0 _ _) (fun p => hl1 _ _) hsum
  set sel : α → ι → ℝ := fun a k => if (a, k) ∈ S then 1 else 0
  set q : α → Matrix ι ι ℂ := fun a => conjDiag (U a) (sel a)
  have hqM : ∀ a, q a * M.effect a = conjDiag (U a) (sel a * lam a) := fun a => by
    rw [hM, conjDiag_mul (hU1 a)]
  -- The selection beats the measurement: `φ(∑_a M_a²) ≤ φ(∑_a q_a M_a)`.
  have hsel : ∑ a, (φ (M.effect a * M.effect a)).re ≤ (φ (∑ a, q a * M.effect a)).re := by
    have e1 : ∑ a, (φ (M.effect a * M.effect a)).re = ∑ p : α × ι, w p * lam p.1 p.2 := by
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ => ?_
      rw [hM, conjDiag_mul (hU1 a), re_apply_conjDiag]
      refine sum_congr rfl fun k _ => ?_
      simp only [w, Pi.mul_apply]
      ring
    have e2 : (φ (∑ a, q a * M.effect a)).re = ∑ p ∈ S, w p := by
      rw [← Finset.filter_univ_mem S, Finset.sum_filter, Fintype.sum_prod_type, map_sum,
        Complex.re_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [hqM, re_apply_conjDiag]
      refine sum_congr rfl fun k _ => ?_
      simp only [w, sel, Pi.mul_apply]
      split_ifs <;> ring
    rw [e1, e2]
    exact hSw
  -- The square matrix `y` with rows `√λ_{a,k} e_{a,k}ᴴ` over the selection.
  let y : Matrix S ι ℂ := Matrix.of fun s j => (√(lam s.1.1 s.1.2) : ℂ) * star (U s.1.1 j s.1.2)
  have hyT : ∀ t : α → ℝ, yᴴ * diagonal (fun s : S => (t s.1.1 : ℂ)) * y =
      ∑ a, (t a : ℂ) • (q a * M.effect a) := fun t => by
    ext j j'
    simp only [Matrix.mul_apply, conjTranspose_apply, diagonal_apply, y, Matrix.of_apply,
      Matrix.sum_apply, Matrix.smul_apply, hqM, conjDiag_apply, smul_eq_mul, mul_sum]
    have hsq : ∀ s : S, star ((√(lam s.1.1 s.1.2) : ℂ) * star (U s.1.1 j s.1.2)) *
        (√(lam s.1.1 s.1.2) : ℂ) = (lam s.1.1 s.1.2 : ℂ) * U s.1.1 j s.1.2 := fun s => by
      have e : (√(lam s.1.1 s.1.2) : ℂ) * (√(lam s.1.1 s.1.2) : ℂ) = lam s.1.1 s.1.2 := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hl0 _ _)]
      rw [star_mul', star_star, Complex.star_def, Complex.conj_ofReal]
      linear_combination (U s.1.1 j s.1.2) * e
    simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    let F : α × ι → ℂ := fun p =>
      (t p.1 : ℂ) * ((lam p.1 p.2 : ℂ) * U p.1 j p.2) * star (U p.1 j' p.2)
    have hl : ∀ x : S, star ((√(lam x.1.1 x.1.2) : ℂ) * star (U x.1.1 j x.1.2)) * (t x.1.1 : ℂ) *
        ((√(lam x.1.1 x.1.2) : ℂ) * star (U x.1.1 j' x.1.2)) = F x.1 := fun x => by
      simp only [F]
      rw [← hsq x]
      ring
    rw [sum_congr rfl fun x _ => hl x, Finset.sum_coe_sort S F, ← Finset.filter_univ_mem S,
      Finset.sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => sum_congr rfl fun k _ => ?_
    simp only [F, sel, Pi.mul_apply]
    split_ifs <;> push_cast <;> ring
  have hyy : yᴴ * y = ∑ a, q a * M.effect a := by
    have := hyT 1
    simp only [Pi.one_apply, Complex.ofReal_one, one_smul] at this
    rw [← this, show diagonal (fun _ : S => (1 : ℂ)) = 1 from rfl, Matrix.mul_one]
  -- Indicator of the outcome `a` on the selection.
  let T : α → Matrix S S ℂ := fun a =>
    diagonal fun s : S => (((fun a' : α => if a' = a then (1 : ℝ) else 0) s.1.1 : ℝ) : ℂ)
  have hyTa : ∀ a, yᴴ * T a * y = q a * M.effect a := fun a => by
    refine (hyT (fun a' => if a' = a then (1 : ℝ) else 0)).trans ?_
    rw [sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hTT : ∀ a, T a * T a = T a := fun a => by
    simp only [T, diagonal_mul_diagonal]
    congr 1
    ext s
    split_ifs <;> simp
  have hTsum : ∑ a, T a = 1 := by
    ext s s'
    rw [Matrix.sum_apply]
    by_cases hss : s = s'
    · subst hss
      simp only [T, diagonal_apply_eq, one_apply_eq]
      rw [sum_eq_single s.1.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    · simp only [T, diagonal_apply_ne _ hss, one_apply_ne hss, sum_const_zero]
  have hTh : ∀ a, (T a)ᴴ = T a := fun a => by
    simp only [T, diagonal_conjTranspose]
    congr 1
    ext s
    simp
  -- Polar decomposition `y = R h`.
  have hcard : Fintype.card S = Fintype.card ι := by rw [Fintype.card_coe, hS]
  obtain ⟨R, h, hR1, hR2, hh0, hhh, hyR, hle⟩ := exists_polar y hcard
  have hqMle : yᴴ * y ≤ 1 := by
    rw [hyy, Matrix.le_iff, ← M.sum_effect, ← sum_sub_distrib]
    refine posSemidef_sum _ fun a _ => ?_
    rw [hqM, hM, ← conjDiag_sub]
    refine posSemidef_conjDiag fun k => ?_
    simp only [sel, Pi.sub_apply, Pi.mul_apply]
    split_ifs <;> simp [hl0 a k]
  -- The projective measurement `p_a = Rᴴ T_a R`.
  let P : Measurement α (Matrix ι ι ℂ) :=
    { effect := fun a => Rᴴ * T a * R
      nonneg := fun a => nonneg_iff_posSemidef.mpr
        ((posSemidef_diagonal_iff.mpr fun s => by
          dsimp only
          split_ifs <;> simp).conjTranspose_mul_mul_same R)
      sum_effect := by
        rw [← Matrix.sum_mul, ← Matrix.mul_sum, hTsum, Matrix.mul_one, hR1] }
  have hP : P.IsProjective := fun a => by
    change Rᴴ * T a * R * (Rᴴ * T a * R) = Rᴴ * T a * R
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R Rᴴ, hR2, Matrix.one_mul, ← Matrix.mul_assoc (T a) (T a), hTT]
  have hhs : hᴴ = h := hh0.1
  have hp : ∀ a, h * P.effect a * h = q a * M.effect a := fun a => by
    change h * (Rᴴ * T a * R) * h = q a * M.effect a
    rw [← hyTa, hyR, conjTranspose_mul, hhs]
    simp only [Matrix.mul_assoc]
  refine ⟨P, hP, sum_norm_sub_sq_le_of_dilation φ M P hP q (fun a => ?_) (fun a => ?_)
    (fun a => ?_) (nonneg_iff_posSemidef.mpr hh0) (hle hqMle) (by rw [hhh, hyy]) hp hsel⟩
  · change conjDiag (U a) (sel a) * conjDiag (U a) (sel a) = conjDiag (U a) (sel a)
    rw [conjDiag_mul (hU1 a)]
    congr 1
    ext k
    simp only [sel, Pi.mul_apply]
    split_ifs <;> simp
  · rw [IsSelfAdjoint, star_eq_conjTranspose]
    exact conjTranspose_conjDiag _
  · change conjDiag (U a) (sel a) * M.effect a = M.effect a * conjDiag (U a) (sel a)
    rw [hM, conjDiag_mul (hU1 a), conjDiag_mul (hU1 a), mul_comm]

/-- **Orthogonalization of measurements**, with the defect as a hypothesis: if
`φ(∑_a M_a²) ≥ 1 - ε`, then `M` is `9ε`-close to a projective measurement. -/
theorem exists_isProjective_sum_norm_sub_sq_le_of_le (φ : AlgState (Matrix ι ι ℂ))
    (M : Measurement α (Matrix ι ι ℂ)) {ε : ℝ}
    (hε : 1 - ε ≤ ∑ a, (φ (M.effect a * M.effect a)).re) :
    ∃ P : Measurement α (Matrix ι ι ℂ), P.IsProjective ∧
      ∑ a, φ.norm (M.effect a - P.effect a) ^ 2 ≤ 9 * ε := by
  obtain ⟨P, hP, h⟩ := exists_isProjective_sum_norm_sub_sq_le φ M
  exact ⟨P, hP, h.trans (by linarith)⟩

end Cslib.Quantum.Measurement
