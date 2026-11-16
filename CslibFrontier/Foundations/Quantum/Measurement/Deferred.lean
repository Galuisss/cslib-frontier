/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Measurement.Classical

/-!
# Deferred computational-basis readout

`coherentRecord f` copies the classical label `f i` of a computational-basis index `i` into a
fresh record register while retaining `i`.  Discarding that record after conjugation gives exactly
the sum of the existing subnormalized classical branches.  The input index may itself contain an
arbitrary reference register, so the identity applies without a product-state assumption.

To keep a classical copy of the readout, record the label twice and discard one copy.  The second
main identity gives the resulting block-diagonal joint state of the retained label and input.

This is the finite-dimensional deferred-measurement identity for a classical readout.  It is
original formalization infrastructure.

## Main definitions

* `Cslib.Quantum.coherentRecord`: the rectangular matrix that coherently records a classical
  label in a fresh register.

## Main results

* `Cslib.Quantum.partialTraceLeft_densityConj_coherentRecord`: discarding the coherent record is
  exactly the sum of the corresponding classical density branches.
* `Cslib.Quantum.partialTraceLeft_densityConj_coherentRecord_twice`: recording twice and
  discarding one copy retains the other as a classical branch label.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped ComplexOrder Kronecker

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]

/-- Coherently record the classical label `f i` in a fresh register while retaining the basis
index `i`.  Thus column `i` is the basis vector `(f i, i)`. -/
@[expose] def coherentRecord (f : ι → A) : Matrix (A × ι) ι ℂ :=
  fun p i => if p = (f i, i) then 1 else 0

/-- The coherent classical-record matrix has orthonormal columns. -/
theorem coherentRecord_isometry [Fintype A] (f : ι → A) :
    (coherentRecord f)ᴴ * coherentRecord f = 1 := by
  classical
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.mul_apply, coherentRecord, Matrix.one_apply, h, eq_comm]

/-- Conjugation by the coherent record embeds matrix entries at the corresponding pair of
recorded labels. -/
theorem densityConj_coherentRecord_apply (f : ι → A) (ρ : Matrix ι ι ℂ)
    (y z : A) (i j : ι) :
    densityConj (coherentRecord f) ρ (y, i) (z, j) =
      if y = f i ∧ z = f j then ρ i j else 0 := by
  classical
  rw [densityConj_apply, Matrix.mul_apply,
    Fintype.sum_eq_single j (fun x hx => by
      simp [coherentRecord, conjTranspose_apply, Ne.symm hx]),
    Matrix.mul_apply,
    Fintype.sum_eq_single i (fun x hx => by
      simp [coherentRecord, Ne.symm hx])]
  by_cases hy : y = f i <;> by_cases hz : z = f j <;>
    simp [coherentRecord, conjTranspose_apply, hy, hz]

/-- **Deferred classical readout.** Conjugate by the coherent-record isometry and discard only
the fresh record.  The retained state is exactly the sum of the existing subnormalized branches.
Taking `ι` to be `system × reference` and `f` to ignore the reference gives the arbitrary-reference
form used by interactive quantum reductions. -/
theorem partialTraceLeft_densityConj_coherentRecord [Fintype A]
    (f : ι → A) (ρ : Matrix ι ι ℂ) :
    partialTraceLeft (densityConj (coherentRecord f) ρ) =
      ∑ y, classicalDensityBranch f y ρ := by
  classical
  ext i j
  by_cases h : f i = f j <;>
    simp [partialTraceLeft_apply, densityConj_coherentRecord_apply, Matrix.sum_apply,
      classicalDensityBranch_apply, h, eq_comm]

private theorem classicalDensityBranch_coherentRecord [Fintype A] (f : ι → A)
    (y : A) (ρ : Matrix ι ι ℂ) :
    classicalDensityBranch (Prod.fst : A × ι → A) y
        (densityConj (coherentRecord f) ρ) =
      pureState (ket y) ⊗ₖ classicalDensityBranch f y ρ := by
  classical
  ext ⟨z, i⟩ ⟨w, j⟩
  simp only [classicalDensityBranch_apply, densityConj_coherentRecord_apply,
    pureState_apply, ket_apply, kroneckerMap_apply]
  split_ifs <;> simp_all

/-- **Deferred classical readout with a retained label.** Record the label twice, discard the
first copy, and retain the second together with the original input.  The result is the joint
block-diagonal state whose `y` block is the existing subnormalized classical branch. -/
theorem partialTraceLeft_densityConj_coherentRecord_twice [Fintype A] (f : ι → A)
    (ρ : Matrix ι ι ℂ) :
    partialTraceLeft
        (densityConj
          (coherentRecord (Prod.fst : A × ι → A) * coherentRecord f) ρ) =
      ∑ y, (pureState (ket y) ⊗ₖ classicalDensityBranch f y ρ) := by
  rw [densityConj_mul, partialTraceLeft_densityConj_coherentRecord]
  simp_rw [classicalDensityBranch_coherentRecord]

end Cslib.Quantum
