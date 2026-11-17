/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Measurement.Classical
public import Mathlib.Data.Matrix.Block

/-!
# Deferred computational-basis readout

`coherentRecord f` copies the classical label `f i` of a computational-basis index `i` into a
fresh record register while retaining `i`.  Discarding that record after conjugation gives exactly
the sum of the existing subnormalized classical branches.  The input index may itself contain an
arbitrary reference register, so the identity applies without a product-state assumption.

To keep a classical copy of the readout, record the label twice and discard one copy.  The second
main identity gives the resulting block-diagonal joint state of the retained label and input.
A controlled continuation may then use the retained full label while leaving it available for a
later observation; its exact branchwise evolution is the final identity below.

This is the finite-dimensional deferred-measurement identity for a classical readout.  It is
original formalization infrastructure.

## Main definitions

* `Cslib.Quantum.coherentRecord`: the rectangular matrix that coherently records a classical
  label in a fresh register.
* `Cslib.Quantum.coherentEnvironmentRecord`: replace a hidden classical register by its
  reversible environment, record a complete label and retain an arbitrary reference.

## Main results

* `Cslib.Quantum.coherentRecord_kronecker_one_reassociate`: extending a coherent record by the
  identity on an arbitrary reference is the coherent record that ignores that reference.
* `Cslib.Quantum.partialTraceLeft_densityConj_coherentRecord`: discarding the coherent record is
  exactly the sum of the corresponding classical density branches.
* `Cslib.Quantum.partialTraceLeft_densityConj_coherentRecord_twice`: recording twice and
  discarding one copy retains the other as a classical branch label.
* `Cslib.Quantum.partialTraceLeft_densityConj_controlled_coherentRecord_twice`: the retained
  full label controls a branch-dependent continuation and remains in the joint output.
* `Cslib.Quantum.partialTraceLeft_densityConj_coherentEnvironmentRecord`: replacing a hidden
  register by an injective environment and tracing that environment gives the full-label
  classical branches with the hidden register discarded.
* `Cslib.Quantum.partialTraceLeft_densityConj_controlled_coherentEnvironmentRecord`: replacing a
  hidden register by an injective environment leaves the recorded label and a continuation on
  the remaining factor.
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

/-- Replace a hidden classical basis register by its reversible environment, record a complete
classical label, and retain a separate reference register. Unlike `coherentRecord`, this matrix
does not retain the hidden input as an additional output factor. -/
@[expose] def coherentEnvironmentRecord {H R S B : Type*}
    [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (env : H → S) (f : H → B) : Matrix (S × (B × R)) (H × R) ℂ :=
  fun p i => if p = (env i.1, (f i.1, i.2)) then 1 else 0

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

omit [Fintype ι] in
/-- Extending a coherent record by the identity on an arbitrary reference and reassociating the
output is exactly the coherent record whose label ignores that reference.  This is the shared
reference-lifting equality used by physical deferred-measurement clients. -/
theorem coherentRecord_kronecker_one_reassociate {Reference : Type*}
    [DecidableEq Reference] (f : ι → A) :
    ((coherentRecord f ⊗ₖ (1 : Matrix Reference Reference ℂ)).submatrix
      (Equiv.prodAssoc A ι Reference).symm id) =
      coherentRecord (f ∘ Prod.fst) := by
  ext ⟨label, indexOut, referenceOut⟩ ⟨indexIn, referenceIn⟩
  simp only [Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply,
    kroneckerMap_apply, Matrix.one_apply, coherentRecord, Function.comp_apply]
  by_cases hreference : referenceOut = referenceIn <;>
    simp [hreference]

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

omit [DecidableEq ι] in
/-- A block-diagonal continuation selected by a retained classical label evolves exactly that
label's matrix block.  `Matrix.blockDiagonal` uses the active-register-first convention, so the
two `Prod.swap` reindexings expose the label as the first factor. -/
theorem densityConj_blockDiagonal_swap_kronecker {ι' : Type*} [Fintype A]
    (V : A → Matrix ι' ι ℂ) (y : A) (ρ : Matrix ι ι ℂ) :
    densityConj
        ((Matrix.blockDiagonal V).submatrix Prod.swap Prod.swap)
        (pureState (ket y) ⊗ₖ ρ) =
      pureState (ket y) ⊗ₖ densityConj (V y) ρ := by
  classical
  ext ⟨z, i⟩ ⟨w, j⟩
  simp [densityConj_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, pureState_apply, ket_apply, kroneckerMap_apply]
  split_ifs <;> simp_all

/-- Replacing an injectively encoded hidden basis register by its environment and tracing that
environment gives the classical full-label branches, with the hidden register itself discarded.
The reference may be entangled with the hidden register; no product-state or normalization
hypothesis is used. -/
theorem partialTraceLeft_densityConj_coherentEnvironmentRecord
    {H R S B : Type*} [Fintype H] [Fintype R] [Fintype S] [Fintype B]
    [DecidableEq H] [DecidableEq R] [DecidableEq S] [DecidableEq B]
    (env : H → S) (f : H → B)
    (henv : Function.Injective env) (ρ : Matrix (H × R) (H × R) ℂ) :
    partialTraceLeft (densityConj (coherentEnvironmentRecord env f) ρ) =
      ∑ y, pureState (ket y) ⊗ₖ
        partialTraceLeft (classicalDensityBranch (f ∘ Prod.fst) y ρ) := by
  classical
  ext ⟨y, r⟩ ⟨z, q⟩
  have hsum :
      if y = z then
        (∑ x : H, if z = f x then ρ (x, r) (x, q) else 0) =
          ∑ i : S, ∑ x : H,
            if i = env x then
              if z = f x then
                ∑ x' : H,
                  if i = env x' then
                    if y = f x' then ρ (x', r) (x, q) else 0
                  else 0
              else 0
            else 0
      else
        0 = ∑ i : S, ∑ x : H,
          if i = env x then
            if z = f x then
              ∑ x' : H,
                if i = env x' then
                  if y = f x' then ρ (x', r) (x, q) else 0
                else 0
            else 0
          else 0 := by
    by_cases hyz : y = z
    · simp only [hyz, ite_true]
      subst z
      conv_rhs =>
        rw [Finset.sum_comm (s := (Finset.univ : Finset S))
          (t := (Finset.univ : Finset H))]
      simp only [henv.eq_iff, Fintype.sum_ite_eq, Fintype.sum_ite_eq']
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : y = f x
      · simp only [hx, ite_true]
      · simp only [hx, ite_false]
    · simp only [hyz, ite_false]
      conv_rhs =>
        rw [Finset.sum_comm (s := (Finset.univ : Finset S))
          (t := (Finset.univ : Finset H))]
      simp only [henv.eq_iff, Fintype.sum_ite_eq, Fintype.sum_ite_eq']
      rw [eq_comm]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hzx : z = f x
      · have hyf : y ≠ f x := fun hyf => hyz (hyf.trans hzx.symm)
        simp only [hzx, hyf, ↓reduceIte]
      · simp only [hzx, ↓reduceIte]
  simpa [partialTraceLeft_apply, densityConj_apply, Matrix.mul_apply,
    coherentEnvironmentRecord, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, pureState_apply, ket_apply, classicalDensityBranch_apply,
    ite_and, eq_comm, apply_ite, ite_mul, one_mul, mul_one, zero_mul, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero] using hsum

/-- **Deferred full-label readout followed by a controlled continuation.** Record the complete
label twice, discard one orthogonal copy, and apply the label-selected rectangular map to the
retained input.  The retained label remains classical and correlated with the complete evolved
branch.  For an inaccessible reference `R`, instantiate `V y` as `W y ⊗ 1_R`; the generic
statement permits arbitrary `V y` and does not itself enforce that `R` is untouched.  No
product-state or normalization hypothesis is used. -/
theorem partialTraceLeft_densityConj_controlled_coherentRecord_twice {ι' : Type*}
    [Fintype A] (f : ι → A) (V : A → Matrix ι' ι ℂ)
    (ρ : Matrix ι ι ℂ) :
    partialTraceLeft
        (densityConj
          (((1 : Matrix A A ℂ) ⊗ₖ
              (Matrix.blockDiagonal V).submatrix Prod.swap Prod.swap) *
            (coherentRecord (Prod.fst : A × ι → A) * coherentRecord f)) ρ) =
      ∑ y, (pureState (ket y) ⊗ₖ
        densityConj (V y) (classicalDensityBranch f y ρ)) := by
  rw [densityConj_mul, partialTraceLeft_densityConj_one_kronecker,
    partialTraceLeft_densityConj_coherentRecord_twice, map_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [densityConj_blockDiagonal_swap_kronecker]

/-- **A reversible environment may replace the hidden label register.** The environment
distinguishes the hidden branches. After discarding it, a label-controlled continuation acts on
the remaining factor; the hidden register is not duplicated in the output. For an inaccessible
subfactor `External`, instantiate `R` as `Active × External` and `V y` as `W y ⊗ 1_External`.
This is the deferred-measurement form for an actual reversible service followed by a protected
classical reply record. -/
theorem partialTraceLeft_densityConj_controlled_coherentEnvironmentRecord
    {H R S B ι' : Type*} [Fintype H] [Fintype R] [Fintype S] [Fintype B]
    [DecidableEq H] [DecidableEq R] [DecidableEq S] [DecidableEq B]
    (env : H → S) (f : H → B)
    (henv : Function.Injective env) (V : B → Matrix ι' R ℂ)
    (ρ : Matrix (H × R) (H × R) ℂ) :
    partialTraceLeft
        (densityConj
          (((1 : Matrix S S ℂ) ⊗ₖ
              (Matrix.blockDiagonal V).submatrix Prod.swap Prod.swap) *
            coherentEnvironmentRecord env f) ρ) =
      ∑ y, pureState (ket y) ⊗ₖ
        densityConj (V y)
          (partialTraceLeft (classicalDensityBranch (f ∘ Prod.fst) y ρ)) := by
  rw [densityConj_mul, partialTraceLeft_densityConj_one_kronecker,
    partialTraceLeft_densityConj_coherentEnvironmentRecord env f henv, map_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [densityConj_blockDiagonal_swap_kronecker]

end Cslib.Quantum
