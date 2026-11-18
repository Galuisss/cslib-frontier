/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import CslibFrontier.Foundations.Data.BitString.Binary
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.OrderOfElement

/-!
# The inverse NTT in ML-DSA matrix expansion

[FIPS 204][NISTFIPS204], §2.5, equation (2.1), orders the odd powers of 1753 by reversing
eight bits. Polynomial evaluation in this order inverts `fromNTT`, the coefficient conversion
used by `Xofs.expandA` after rejection sampling. Consequently an entire matrix of uniform NTT
entries remains uniform after this conversion.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

private abbrev F := ZMod 8380417

private instance : Fact (Nat.Prime 8380417) := ⟨by norm_num1⟩

private theorem orderOf_zeta : orderOf (1753 : F) = 512 :=
  orderOf_eq_prime_pow (p := 2) (n := 8) (by decide +kernel) (by decide +kernel)

/-- The odd roots of `X^256 + 1` in exponent order, before the bit reversal in equation (2.1). -/
def nttNode (i : Fin 256) : ZMod 8380417 := 1753 ^ (2 * i.val + 1)

theorem nttNode_pow (i : Fin 256) : nttNode i ^ 256 = -1 := by
  have h : (1753 : F) ^ 256 = -1 := by decide +kernel
  rw [nttNode, ← pow_mul, Nat.mul_comm, pow_mul, h, pow_add, pow_mul]
  norm_num

theorem nttNode_injective : Function.Injective nttNode := by
  intro i j hij
  have h := pow_injOn_Iio_orderOf (x := (1753 : F))
    (show 2 * i.val + 1 < orderOf (1753 : F) by rw [orderOf_zeta]; lia)
    (show 2 * j.val + 1 < orderOf (1753 : F) by rw [orderOf_zeta]; lia) hij
  apply Fin.ext
  lia

private def bitRev (i : Fin 256) : Fin 256 :=
  ⟨BitString.lsbValue (BitString.lowBits 8 i.val).reverse, by
    simpa using BitString.lsbValue_lt (BitString.lowBits 8 i.val).reverse⟩

private theorem bitRev_involutive : Function.Involutive bitRev := by
  intro i
  apply Fin.ext
  have h := BitString.lowBits_lsbValue (BitString.lowBits 8 i.val).reverse
  simp only [List.length_reverse, BitString.length_lowBits] at h
  change BitString.lsbValue (BitString.lowBits 8
    (BitString.lsbValue (BitString.lowBits 8 i.val).reverse)).reverse = i.val
  rw [h, List.reverse_reverse]
  exact BitString.lsbValue_lowBits i.isLt

/-- The direct forward NTT of equation (2.1), evaluating the coefficient polynomial at each
bit-reversed odd power of 1753. -/
def toNTT (coeffs : Poly) : Poly := fun i => ∑ j, coeffs j * nttNode (bitRev i) ^ j.val

private theorem fromNTT_get (v : Poly) (j : Fin 256) :
    (fromNTT v).get j = 8347681 * ∑ i, v i * ((nttNode (bitRev i))⁻¹) ^ j.val := by
  unfold fromNTT
  simp only [Vector.get_ofFn]
  apply congrArg (fun x : F => 8347681 * x)
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : F => v i * x)
  change (1753 : F) ^ ((511 - 2 * (bitRev i).val) * j.val % 512) = _
  rw [← orderOf_zeta, pow_mod_orderOf, pow_mul]
  apply congrArg (fun x : F => x ^ j.val)
  apply eq_inv_of_mul_eq_one_left
  rw [nttNode, ← pow_add]
  have h : 511 - 2 * (bitRev i).val + (2 * (bitRev i).val + 1) = 512 := by
    have := (bitRev i).isLt
    lia
  rw [h, ← orderOf_zeta, pow_orderOf_eq_one]

private theorem sum_node_ratio (k i : Fin 256) :
    ∑ j : Fin 256, (nttNode (bitRev k) / nttNode (bitRev i)) ^ j.val =
      if i = k then 256 else 0 := by
  have hi : nttNode (bitRev i) ≠ 0 := by
    intro h
    simpa [h] using nttNode_pow (bitRev i)
  split_ifs with hik
  · subst k
    simp [div_self hi]
  · have hne : nttNode (bitRev k) / nttNode (bitRev i) ≠ 1 := by
      intro h
      exact hik (bitRev_involutive.injective (nttNode_injective ((div_eq_one_iff_eq hi).mp h))).symm
    rw [Fin.sum_univ_eq_sum_range]
    apply (mul_eq_zero.mp _).resolve_right (sub_ne_zero.mpr hne)
    rw [geom_sum_mul, div_pow, nttNode_pow, nttNode_pow]
    norm_num

/-- Evaluating a converted polynomial in the FIPS order recovers all its input NTT values. -/
theorem toNTT_fromNTT : Function.LeftInverse toNTT (fun v => (fromNTT v).get) := by
  intro v
  funext k
  simp only [toNTT, fromNTT_get, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_pow, ← div_eq_inv_mul, ← Finset.mul_sum, sum_node_ratio]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [mul_left_comm, show (8347681 : F) * 256 = 1 by decide +kernel, mul_one]

/-- NTT coordinates and coefficient coordinates are equivalent by the two explicit transforms.
The forward direction is the actual inverse transform called for each entry of `Xofs.expandA`. -/
@[expose] def fromNTTEquiv : Poly ≃ Poly where
  toFun v := (fromNTT v).get
  invFun := toNTT
  left_inv := toNTT_fromNTT
  right_inv := toNTT_fromNTT.rightInverse_of_card_le le_rfl

/-- The equivalence applies the exact coefficient conversion used inside `Xofs.expandA`. -/
theorem fromNTTEquiv_apply (v : Poly) : fromNTTEquiv v = (fromNTT v).get := by
  rw [← fromNTTEquiv.toFun_as_coe]
  rfl

/-- Entrywise application of the FIPS matrix expansion's inverse NTT transports a uniform
NTT matrix to a uniform coefficient matrix, including the joint law of all its entries. -/
theorem uniformOfFintype_map_fromNTT (s : Level) :
    (PMF.uniformOfFintype (PublicMatrix s)).map (fun A i j => (fromNTT (A i j)).get) =
      PMF.uniformOfFintype (PublicMatrix s) := by
  let e : PublicMatrix s ≃ PublicMatrix s := fromNTTEquiv.mapMatrix
  have he (A : PublicMatrix s) : e A = fun i j => (fromNTT (A i j)).get := by
    apply Matrix.ext
    intro i j
    rw [show e A = A.map fromNTTEquiv by exact Equiv.mapMatrix_apply .., Matrix.map_apply]
    exact fromNTTEquiv_apply (A i j)
  rw [← funext he]
  exact Probability.PMF.uniformOfFintype_map_equiv e

end Cslib.Crypto.MLDSA.FIPS204
