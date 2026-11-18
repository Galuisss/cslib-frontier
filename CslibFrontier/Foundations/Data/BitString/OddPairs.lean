/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Hadamard
public import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Averages over the odd pairs of bit strings

Rigidity arguments for Pauli operators average over the pairs `(a, b)` of bit strings with
`a · b = 1`, the *odd* pairs, on which `X(a)` and `Z(b)` anticommute. The **masked average**
`oddExpect f = E_{a,b} [a · b = 1] f(a, b)` (`Cslib.BitString.oddExpect`) averages `f` over all
pairs with the even pairs set to `0`; for `n ≥ 1` bits it is `(1 - 2⁻ⁿ) / 2` times the conditional
average over the odd pairs. It is monotone and linear on the odd pairs
(`Cslib.BitString.oddExpect_mono`, `Cslib.BitString.oddExpect_add`,
`Cslib.BitString.oddExpect_const_mul`).

A nonzero `a` has `a · c = 1` for exactly half of the `c`, so a bound holding for every such `c`
holds for twice the masked average over `c`: if `g ≤ h(c)` whenever `a · c = 1`, then
`g ≤ 2 E_c [a · c = 1] h(c)` (`Cslib.BitString.le_two_mul_expect_ite_of_forall`). This turns
pointwise estimates through an auxiliary odd string `c` into averaged ones.

## Main definitions

* `Cslib.BitString.oddExpect`: the masked average over the odd pairs.

## Main results

* `Cslib.BitString.le_two_mul_expect_ite_of_forall`: a bound over the strings `c` with `a · c = 1`
  bounds twice the masked average.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonzero bit string `a` gives a bound `g ≤ h(c)` for every `c` with `a · c = 1`, the half of
the strings with odd inner product; then `g ≤ 2 E_c [a · c = 1] h(c)`. -/
theorem le_two_mul_expect_ite_of_forall {a : ι → Bool} (ha : a ≠ 0) {g : ℝ}
    {h : (ι → Bool) → ℝ} (hg : ∀ c, a ⬝ᵥ c = true → g ≤ h c) :
    g ≤ 2 * 𝔼 c, if a ⬝ᵥ c = true then h c else 0 := by
  set S := (univ : Finset (ι → Bool)).filter fun c => a ⬝ᵥ c = true
  have hcard : 2 * (S.card : ℝ) = Fintype.card (ι → Bool) := by
    have hc := two_mul_card_dotProduct_eq_true_add a
    simp only [ha, ↓reduceIte, add_zero] at hc
    rw [Fintype.card_fun, Fintype.card_bool]
    exact_mod_cast hc
  have hN : (0 : ℝ) < Fintype.card (ι → Bool) := by exact_mod_cast Fintype.card_pos
  have hsum : (S.card : ℝ) * g ≤ ∑ c, if a ⬝ᵥ c = true then h c else 0 := by
    rw [← sum_filter, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun c hc => hg c (mem_filter.mp hc).2
  rw [Fintype.expect_eq_sum_div_card, mul_div_assoc', le_div_iff₀ hN, ← hcard]
  linarith

/-- The **masked average over the odd pairs**: `E_{a,b} [a · b = 1] f(a, b)`. -/
noncomputable def oddExpect (f : (ι → Bool) → (ι → Bool) → ℝ) : ℝ :=
  𝔼 a, 𝔼 b, if a ⬝ᵥ b = true then f a b else 0

theorem oddExpect_def (f : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect f = 𝔼 a, 𝔼 b, if a ⬝ᵥ b = true then f a b else 0 := by
  unfold oddExpect; rfl

variable {f g : (ι → Bool) → (ι → Bool) → ℝ}

theorem oddExpect_mono (h : ∀ a b, a ⬝ᵥ b = true → f a b ≤ g a b) :
    oddExpect f ≤ oddExpect g := by
  rw [oddExpect_def, oddExpect_def]
  exact expect_le_expect fun a _ => expect_le_expect fun b _ => by
    split_ifs with hab
    · exact h a b hab
    · exact le_rfl

theorem oddExpect_nonneg (h : ∀ a b, a ⬝ᵥ b = true → 0 ≤ f a b) : 0 ≤ oddExpect f := by
  have h0 := oddExpect_mono (f := fun _ _ => 0) h
  rwa [oddExpect_def (fun _ _ => 0), show (𝔼 a : ι → Bool, 𝔼 b : ι → Bool,
    if a ⬝ᵥ b = true then (0 : ℝ) else 0) = 0 by simp] at h0

theorem oddExpect_add (f g : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect (fun a b => f a b + g a b) = oddExpect f + oddExpect g := by
  simp only [oddExpect_def, ← expect_add_distrib]
  refine expect_congr rfl fun a _ => expect_congr rfl fun b _ => ?_
  split_ifs <;> ring

theorem oddExpect_const_mul (r : ℝ) (f : (ι → Bool) → (ι → Bool) → ℝ) :
    oddExpect (fun a b => r * f a b) = r * oddExpect f := by
  simp only [oddExpect_def, mul_expect]
  refine expect_congr rfl fun a _ => expect_congr rfl fun b _ => ?_
  split_ifs <;> ring

end Cslib.BitString
