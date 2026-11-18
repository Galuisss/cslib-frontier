/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitment
public import CslibFrontier.Crypto.Computational.SIS.Polynomial
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.HashFamily.MatrixKernel
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum.Prime
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Evaluation coordinates for the ML-DSA matrix

The 256 distinct roots of `X^256 + 1` over the FIPS 204 field split the negacyclic coefficient
algebra into 256 copies of that field. Evaluation commutes with each module matrix product.
The kernel of a square coefficient matrix is therefore the product of the finite-field kernels
in the 256 coordinates, as used in [BarbosaEtAl2023, Appendix A.1].
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Polynomial Finset
open scoped BigOperators

private abbrev F := ZMod 8380417

private instance : Fact (Nat.Prime 8380417) := ⟨by norm_num1⟩

private def nodes (i : Fin 256) : F := 1753 ^ (2 * i.val + 1)

private theorem nodes_root (i : Fin 256) : nodes i ^ 256 = -1 := by
  have h : (1753 : F) ^ 256 = -1 := by decide +kernel
  rw [nodes, ← pow_mul, Nat.mul_comm, pow_mul, h, pow_add, pow_mul]
  norm_num

private theorem nodes_injective : Function.Injective nodes := by
  have h : orderOf (1753 : F) = 2 ^ (8 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 8) (by decide +kernel) (by decide +kernel)
  intro i j hij
  have eq := pow_injOn_Iio_orderOf (x := (1753 : F))
    (show 2 * i.val + 1 < orderOf (1753 : F) by rw [h]; lia)
    (show 2 * j.val + 1 < orderOf (1753 : F) by rw [h]; lia) hij
  apply Fin.ext
  lia

private noncomputable def evalHom :
    AdjoinRoot ((X : F[X]) ^ 256 + 1) →ₐ[F] (Fin 256 → F) :=
  AlgHom.pi fun i => AdjoinRoot.liftAlgHom _ (AlgHom.id F F) (nodes i) (by
    simp [nodes_root])

private theorem evalHom_surjective : Function.Surjective evalHom := by
  intro v
  refine ⟨AdjoinRoot.mk _ (Lagrange.interpolate Finset.univ nodes v), ?_⟩
  funext i
  change Polynomial.eval (nodes i) (Lagrange.interpolate Finset.univ nodes v) = v i
  exact Lagrange.eval_interpolate_at_node v nodes_injective.injOn (Finset.mem_univ i)

/-- Evaluation at the 256 odd powers of 1753, the primitive 512th root specified by FIPS 204.
The index orders the roots by exponent. -/
noncomputable def splitPolynomial : Negacyclic (ZMod 8380417) 256 ≃ₐ[ZMod 8380417] Poly :=
  let h := negacyclicEquiv (R := F) (n := 256) (by decide)
  let f := evalHom.comp h.toAlgHom
  AlgEquiv.ofBijective f <| (Fintype.bijective_iff_surjective_and_card f).2
    ⟨evalHom_surjective.comp h.surjective, Fintype.card_congr Negacyclic.coeffsEquiv⟩

private noncomputable def splitVector (m : ℕ) :
    (Fin m → Poly) ≃ (Fin 256 → Fin m → F) :=
  (Equiv.piCongrRight fun _ => Negacyclic.coeffsEquiv.symm.trans splitPolynomial.toEquiv).trans
    (Equiv.piComm _)

/-- The field matrix obtained by evaluating every coefficient polynomial at the same root. -/
noncomputable def matrixBlock {k ℓ : ℕ} (A : Matrix (Fin k) (Fin ℓ) Poly) (r : Fin 256) :
    Matrix (Fin k) (Fin ℓ) (ZMod 8380417) :=
  fun i j => splitPolynomial (Negacyclic.ofCoeffs (A i j)) r

private theorem splitVector_mul {k ℓ : ℕ} (A : Matrix (Fin k) (Fin ℓ) Poly)
    (y : Fin ℓ → Poly) (r : Fin 256) :
    splitVector k (moduleSISMap A y) r = (matrixBlock A r).mulVec (splitVector ℓ y r) := by
  funext i
  change splitPolynomial (Negacyclic.ofCoeffs (moduleSISMap A y i)) r = _
  change splitPolynomial (Negacyclic.ofCoeffs (innerPoly (A i) y)) r = _
  rw [Negacyclic.ofCoeffs_innerPoly]
  simp only [_root_.dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
  rfl

/-- The actual coefficient kernel is equivalent to independently choosing a kernel vector for
each evaluation coordinate. This includes singular and zero matrices. -/
noncomputable def splitMatrixKernel {k ℓ : ℕ} (A : Matrix (Fin k) (Fin ℓ) Poly) :
    { y : Fin ℓ → Poly // moduleSISMap A y = 0 } ≃
      { v : Fin 256 → Fin ℓ → ZMod 8380417 // ∀ r, (matrixBlock A r).mulVec (v r) = 0 } := by
  let e := splitVector ℓ
  have hz (x : Fin k → Poly) : splitVector k x = 0 ↔ x = 0 := by
    have hzero : splitVector k 0 = 0 := by
      funext r j
      exact congrFun (map_zero splitPolynomial) r
    rw [← hzero, Equiv.apply_eq_iff_eq]
  have hh (y : Fin ℓ → Poly) : moduleSISMap A y = 0 ↔
      ∀ r, (matrixBlock A r).mulVec (e y r) = 0 := by
    rw [← hz, funext_iff]
    simp only [splitVector_mul, Pi.zero_apply, e]
  exact e.subtypeEquiv hh

private noncomputable def blocksEquiv (k ℓ : ℕ) :
    Matrix (Fin k) (Fin ℓ) Poly ≃ (Fin 256 → Matrix (Fin k) (Fin ℓ) F) :=
  let e := Negacyclic.coeffsEquiv.symm.trans splitPolynomial.toEquiv
  { toFun := matrixBlock
    invFun := fun B i j => e.symm fun r => B r i j
    left_inv := fun A => by
      funext i j
      exact e.symm_apply_apply (A i j)
    right_inv := fun B => by
      funext r i j
      exact congrFun (e.apply_symm_apply fun r => B r i j) r }

private theorem expect_firstRows {k ℓ : ℕ} (h : ℓ ≤ k)
    (g : Matrix (Fin ℓ) (Fin ℓ) Poly → ℝ) :
    (𝔼 A : Matrix (Fin k) (Fin ℓ) Poly, g (A.submatrix (Fin.castLE h) id)) = 𝔼 B, g B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fintype.expect_comp_fst (β := Fin m → Fin ℓ → Poly) g]
  exact Fintype.expect_equiv (Fin.appendEquiv (α := Fin ℓ → Poly) ℓ m).symm _ _ fun _ => rfl

private theorem mean_sqrt_blockKernel_lt (ℓ : ℕ) :
    (𝔼 D : Fin 256 → Matrix (Fin ℓ) (Fin ℓ) F,
      Real.sqrt (Nat.card {v : Fin 256 → Fin ℓ → F // ∀ r, (D r).mulVec (v r) = 0})) <
      11 / 10 := by
  apply lt_of_le_of_lt (Cslib.Probability.expect_sqrt_card_joint_kernel_le 256)
  rw [ZMod.card]
  have root : (2800 : ℝ) ≤ Real.sqrt 8380417 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  calc
    _ ≤ (1 + (2801 : ℝ)⁻¹) ^ 256 := by
      gcongr
      norm_num1
      linarith
    _ < 11 / 10 := by norm_num

private theorem mean_sqrt_squareKernel_lt (ℓ : ℕ) :
    (𝔼 B : Matrix (Fin ℓ) (Fin ℓ) Poly,
      Real.sqrt (Nat.card {y : Fin ℓ → Poly // moduleSISMap B y = 0})) < 11 / 10 := by
  let J (D : Fin 256 → Matrix (Fin ℓ) (Fin ℓ) F) :=
    Real.sqrt (Nat.card {v : Fin 256 → Fin ℓ → F // ∀ r, (D r).mulVec (v r) = 0})
  refine lt_of_eq_of_lt (b := 𝔼 D, J D) ?_ (mean_sqrt_blockKernel_lt ℓ)
  apply Fintype.expect_equiv (blocksEquiv ℓ ℓ)
  intro B
  apply congrArg (fun k : ℕ => Real.sqrt (k : ℝ))
  exact Nat.card_congr (splitMatrixKernel B)

/-- Over a uniform FIPS coefficient matrix, the mean square root of the top submatrix's kernel
size is below `11/10` at all three levels. Evaluation gives 256 independent uniform field
matrices and preserves the entire kernel, including its size at singular matrices. -/
theorem mean_sqrt_commitmentKernelSize_lt (s : Level) :
    (𝔼 A : PublicMatrix s, Real.sqrt (commitmentKernelSize s A)) < 11 / 10 := by
  let K (B : Matrix (Fin s.params.ℓ) (Fin s.params.ℓ) Poly) :=
    Real.sqrt (Nat.card {y : Fin s.params.ℓ → Poly // moduleSISMap B y = 0})
  have hdim : s.params.ℓ ≤ s.params.k := by cases s <;> decide
  change (𝔼 A : PublicMatrix s, K (A.submatrix (Fin.castLE hdim) id)) < _
  exact lt_of_eq_of_lt (expect_firstRows hdim K) (mean_sqrt_squareKernel_lt s.params.ℓ)

/-- The distinguishing advantage for one fresh ideal signing commitment after `T` coherent
queries. The right-hand side is numerical at every FIPS 204 level. -/
theorem abs_commitmentRefreshProbability_sub_le_fips (s : Level) (extra : Finset (List Bool))
    {W κ : Type*} [Fintype W] [Fintype κ] (T : ℕ) (U ψ readout post accept)
    (hψ : ∀ A, ‖ψ A‖ = 1) :
    |commitmentRefreshProbability s extra true (W := W) (κ := κ) T U ψ readout post accept -
      commitmentRefreshProbability s extra false T U ψ readout post accept| ≤
      2 * T * ((11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits)) := by
  apply (abs_commitmentRefreshProbability_sub_le_kernel s extra T U ψ readout post accept hψ).trans
  gcongr
  exact (mean_sqrt_commitmentKernelSize_lt s).le

end Cslib.Crypto.MLDSA.FIPS204
