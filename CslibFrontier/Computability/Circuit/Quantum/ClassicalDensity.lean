/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Classical
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Isometry
public import CslibFrontier.Foundations.Quantum.POVM.Density
import CslibFrontier.Computability.Circuit.Quantum.Parallel

/-!
# Classical reversible circuits on joint density matrices

A classical circuit permutes both indices of an arbitrary density matrix by its inverse basis
permutation. Tensoring its action with the identity retains the complete reference register,
including off-diagonal correlations. Basis measurement therefore pushes the original joint
distribution forward by the classical permutation.

## Main results

* `Cslib.Quantum.Circuit.densityConj_ofCodes_kronecker_apply`: exact joint matrix entries after a
  classical circuit, without positivity, normalization or product-state hypotheses.
* `Cslib.Quantum.Circuit.measureDensity_basis_ofCodes`: basis readout follows the classical
  permutation while retaining the reference coordinate.

These are original bridges between the existing circuit and density-matrix semantics.
-/

public section

namespace Cslib.Quantum.Circuit

open Matrix Finset GateCode
open scoped Kronecker

variable {m : ℕ} {codes : List GateCode}

private theorem matrix_ofCodes_apply (h : IsClassical m codes)
    (y x : Fin m → Bool) :
    (matrix (ofCodes m codes) : Matrix _ _ ℂ) y x =
      if classicalUnrun codes y = x then 1 else 0 := by
  rw [← eval_ket_apply]
  simpa only [ket_apply] using eval_ofCodes_apply h (ket x) y

/-- A classical circuit permutes the active indices of every joint matrix and leaves both
reference indices unchanged. In particular, it preserves reference entanglement. -/
theorem densityConj_ofCodes_kronecker_apply (h : IsClassical m codes)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Matrix ((Fin m → Bool) × κ) ((Fin m → Bool) × κ) ℂ)
    (p q : (Fin m → Bool) × κ) :
    densityConj
        ((matrix (ofCodes m codes) : Matrix _ _ ℂ) ⊗ₖ
          (1 : Matrix κ κ ℂ)) ρ p q =
      ρ (classicalUnrun codes p.1, p.2) (classicalUnrun codes q.1, q.2) := by
  simp [densityConj_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, matrix_ofCodes_apply h, Fintype.sum_prod_type,
    apply_ite (starRingEnd ℂ)]

/-- Basis readout after a classical circuit is the pushforward by its basis permutation. The
input may be mixed and entangled with an arbitrary finite reference register. -/
theorem measureDensity_basis_ofCodes (h : IsClassical m codes)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Matrix ((Fin m → Bool) × κ) ((Fin m → Bool) × κ) ℂ)
    (hρ : IsDensityMatrix ρ) :
    POVM.basis.measureDensity
        (densityConj
          ((matrix (ofCodes m codes) : Matrix _ _ ℂ) ⊗ₖ
            (1 : Matrix κ κ ℂ)) ρ)
        (hρ.densityConj_kronecker (UnitaryGroup.star_mul_self (matrix (ofCodes m codes)))) =
      (POVM.basis.measureDensity ρ hρ).map
        (fun p => (classicalRun codes p.1, p.2)) := by
  ext p
  have hpre (q : (Fin m → Bool) × κ) :
      p = (classicalRun codes q.1, q.2) ↔ q = (classicalUnrun codes p.1, p.2) := by
    constructor
    · intro hp
      rw [hp]
      simp [classicalUnrun_classicalRun h]
    · rintro rfl
      simp [classicalRun_classicalUnrun h]
  simp [POVM.measureDensity_apply, POVM.densityProb_basis,
    densityConj_ofCodes_kronecker_apply h, PMF.map_apply, tsum_fintype, hpre]

end Cslib.Quantum.Circuit
