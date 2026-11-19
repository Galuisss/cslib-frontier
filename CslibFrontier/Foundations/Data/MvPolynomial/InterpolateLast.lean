/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial interpolation across coordinate slices

View a polynomial in `m + 1` variables as a univariate polynomial in the last variable
with coefficients in the first `m` variables. The ordinary Lagrange basis then interpolates
polynomial-valued data. The construction controls the degree in the interpolation variable
and preserves common degree bounds in all other variables.

## Main definitions

* `MvPolynomial.lastVariableEquiv`: view the last variable as the univariate variable.
* `MvPolynomial.specializeLast`: assign a scalar to the last variable.
* `MvPolynomial.interpolateLast`: interpolate a family of lower-dimensional polynomials.

## Main results

* `MvPolynomial.specializeLast_interpolateLast`: the interpolant recovers the given slices.
* `MvPolynomial.degreeOf_last_interpolateLast_le`: the last degree is at most the node count
  minus one.
* `MvPolynomial.degreeOf_castSucc_interpolateLast_le`: the other individual degree bounds
  are inherited from the input slices.
* `MvPolynomial.eq_of_specializeLast_eq`: enough slices uniquely determine the polynomial.
-/

public section

namespace MvPolynomial

open Finset

variable {R : Type*} {m : ℕ} [CommSemiring R]

/-- Isolate the last variable of a multivariate polynomial. -/
noncomputable def lastVariableEquiv (R : Type*) [CommSemiring R] (m : ℕ) :
    MvPolynomial (Fin (m + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin m) R) :=
  (renameEquiv R finSuccEquivLast).trans (optionEquivLeft R (Fin m))

/-- Substitute a scalar for the last variable, keeping all the preceding variables. -/
noncomputable def specializeLast (x : R) :
    MvPolynomial (Fin (m + 1)) R →+* MvPolynomial (Fin m) R :=
  (Polynomial.evalRingHom (C x)).comp (lastVariableEquiv R m).toRingHom

@[simp] theorem specializeLast_X_last (x : R) :
    specializeLast x (X (Fin.last m)) = C x := by
  unfold specializeLast lastVariableEquiv
  simp [finSuccEquivLast_last]

@[simp] theorem specializeLast_X_castSucc (x : R) (i : Fin m) :
    specializeLast x (X i.castSucc) = X i := by
  unfold specializeLast lastVariableEquiv
  simp [finSuccEquivLast_castSucc]

/-- Specialization corresponds to evaluating on the last-coordinate slice. -/
theorem eval_specializeLast (x : R) (u : Fin m → R) (p : MvPolynomial (Fin (m + 1)) R) :
    eval u (specializeLast x p) = eval (Fin.snoc u x) p := by
  unfold specializeLast lastVariableEquiv
  change eval u (Polynomial.eval (C x) (optionEquivLeft R _ (rename finSuccEquivLast p))) = _
  rw [← Polynomial.eval₂_id, Polynomial.hom_eval₂, RingHom.comp_id, eval_C,
    ← Polynomial.eval_map, ← optionEquivLeft_elim_eval, eval_rename]
  congr 1
  apply congrArg (fun v : Fin (m + 1) → R => eval v)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [finSuccEquivLast_last]
  · simp [finSuccEquivLast_castSucc]

theorem natDegree_lastVariableEquiv (p : MvPolynomial (Fin (m + 1)) R) :
    (lastVariableEquiv R m p).natDegree = p.degreeOf (Fin.last m) := by
  unfold lastVariableEquiv
  change (optionEquivLeft R _ (rename finSuccEquivLast p)).natDegree = _
  rw [natDegree_optionEquivLeft, ← finSuccEquivLast_last,
    degreeOf_rename_of_injective finSuccEquivLast.injective]

/-- A prefix variable has degree at most `d` exactly when it has that bound in each
coefficient of the polynomial in the last variable. -/
theorem degreeOf_castSucc_le_iff (i : Fin m) (p : MvPolynomial (Fin (m + 1)) R)
    (d : ℕ) :
    p.degreeOf i.castSucc ≤ d ↔ ∀ k, ((lastVariableEquiv R m p).coeff k).degreeOf i ≤ d := by
  unfold lastVariableEquiv
  change p.degreeOf i.castSucc ≤ d ↔
    ∀ k, ((optionEquivLeft R _ (rename finSuccEquivLast p)).coeff k).degreeOf i ≤ d
  rw [← degreeOf_rename_of_injective finSuccEquivLast.injective i.castSucc,
    finSuccEquivLast_castSucc]
  simp only [degreeOf_le_iff, mem_support_coeff_optionEquivLeft]
  constructor
  · intro h k s hs
    simpa using h (s.optionElim k) hs
  · intro h s hs
    exact h (s none) s.some (by simpa using hs)

/-- Specializing the last variable preserves each bound on the prefix variables. -/
theorem degreeOf_specializeLast_le (x : R) (p : MvPolynomial (Fin (m + 1)) R) (i : Fin m) :
    (specializeLast x p).degreeOf i ≤ p.degreeOf i.castSucc := by
  have h := (degreeOf_castSucc_le_iff i p _).mp le_rfl
  unfold specializeLast
  change (Polynomial.eval (C x) (lastVariableEquiv R m p)).degreeOf i ≤ _
  rw [Polynomial.eval_eq_sum_range]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [← map_pow (C : R →+* MvPolynomial (Fin m) R) x j, degreeOf_C, add_zero]
  exact h j

section Field

variable {F ι : Type*} [Field F] [DecidableEq ι]

/-- Interpolate polynomials given on the distinct slices indexed by `s`. -/
noncomputable def interpolateLast (s : Finset ι) (x : ι → F)
    (g : ι → MvPolynomial (Fin m) F) : MvPolynomial (Fin (m + 1)) F :=
  (lastVariableEquiv F m).symm <| ∑ j ∈ s,
    Polynomial.C (g j) * (Lagrange.basis s x j).map C

/-- The interpolated polynomial specializes to the requested polynomial at each node. -/
theorem specializeLast_interpolateLast {s : Finset ι} {x : ι → F}
    (hx : Set.InjOn x s) (g : ι → MvPolynomial (Fin m) F) {j : ι} (hj : j ∈ s) :
    specializeLast (x j) (interpolateLast s x g) = g j := by
  unfold specializeLast interpolateLast
  change Polynomial.eval (C (x j)) (lastVariableEquiv F m ((lastVariableEquiv F m).symm _)) = _
  rw [AlgEquiv.apply_symm_apply, Polynomial.eval_finsetSum]
  rw [sum_eq_single_of_mem j hj]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Lagrange.eval_basis_self hx hj, map_one, mul_one]
  · intro i hi hij
    rw [Polynomial.eval_mul, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Lagrange.eval_basis_of_ne hij hj, map_zero, mul_zero]

/-- Interpolating over `s` puts degree at most `s.card - 1` in the last variable. -/
theorem degreeOf_last_interpolateLast_le {s : Finset ι} {x : ι → F}
    (hx : Set.InjOn x s) (g : ι → MvPolynomial (Fin m) F) :
    (interpolateLast s x g).degreeOf (Fin.last m) ≤ s.card - 1 := by
  rw [← natDegree_lastVariableEquiv, interpolateLast, AlgEquiv.apply_symm_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add,
    Polynomial.natDegree_map_eq_of_injective (C_injective (Fin m) F),
    Lagrange.natDegree_basis hx hj]

/-- Interpolation does not increase any of the degrees in the prefix variables. -/
theorem degreeOf_castSucc_interpolateLast_le (s : Finset ι) (x : ι → F)
    (g : ι → MvPolynomial (Fin m) F) (i : Fin m) {d : ℕ}
    (h : ∀ j ∈ s, (g j).degreeOf i ≤ d) :
    (interpolateLast s x g).degreeOf i.castSucc ≤ d := by
  rw [degreeOf_castSucc_le_iff]
  intro k
  unfold interpolateLast
  rw [AlgEquiv.apply_symm_apply, Polynomial.finsetSum_coeff]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun j hj => ?_)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  exact (degreeOf_mul_le _ _ _).trans (by simpa using h j hj)

omit [DecidableEq ι] in
/-- Two polynomials of last degree strictly below the number of distinct slices coincide
if their specializations coincide on those slices. -/
theorem eq_of_specializeLast_eq {s : Finset ι} {x : ι → F} (hx : Set.InjOn x s)
    {p q : MvPolynomial (Fin (m + 1)) F}
    (hp : p.degreeOf (Fin.last m) < s.card) (hq : q.degreeOf (Fin.last m) < s.card)
    (h : ∀ j ∈ s, specializeLast (x j) p = specializeLast (x j) q) : p = q := by
  classical
  apply (lastVariableEquiv F m).injective
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (ι := s)
    _ _ (f := fun j => C (x j))
    (fun i j hij => Subtype.ext (hx i.prop j.prop (C_injective (Fin m) F hij)))
  · exact fun j => h j j.prop
  · rw [Fintype.card_coe, natDegree_lastVariableEquiv, natDegree_lastVariableEquiv]
    exact max_lt hp hq

end Field

end MvPolynomial
