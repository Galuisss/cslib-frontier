/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Counting in logarithmic space

`SharpL` counts actual accepting branches of a logspace counting machine. Branches that
halt early are counted once, and distinct transition occurrences may lead to the same
configuration. The nondeterministic view is used only to bound workspace.

`GapL` takes differences of two such counts. `UL`, `LogFewNL`, `LogFew`, `ParityL`,
`ModkL`, `ModL`, `PL`, and `SPL` restrict or test these counts and differences.

## References

* [Complexity Zoo, symbols](https://complexityzoo.net/Complexity_Zoo:Symbols#sharpl)
* [Complexity Zoo, logarithmic-space fewness](https://complexityzoo.net/Complexity_Zoo:L#logfew)
* [Complexity Zoo, modular logarithmic space](https://complexityzoo.net/Complexity_Zoo:M#modl)
* [E. Allender and M. Ogihara, *Relationships Among PL, #L, and the Determinant*]
  (https://archive.numdam.org/item/ITA_1996__30_1_1_0/)
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type}

/-- The accepting branch counts of logspace machines. One finite machine stays within logarithmic
workspace on every prefix and halts on every branch. The sufficient clock may depend on the
instance, since the terminal count is stable after all branches halt. -/
def SharpL (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapeCTM k Bool State) (c : ℕ),
    ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
      ∃ t, M.HaltsWithin t (Cfg.init M.initial (enc a)) ∧
        f a = M.acceptCount t (Cfg.init M.initial (enc a))}

/-- Integer-valued differences of two `SharpL` functions. -/
def GapL (enc : α ↪ List Bool) : Set (α → ℤ) :=
  {g | ∃ f₁ ∈ SharpL enc, ∃ f₂ ∈ SharpL enc, ∀ a, g a = f₁ a - f₂ a}

/-- Unambiguous logarithmic space. There is one accepting branch on members and none on
nonmembers. -/
def UL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, (∀ a, f a ≤ 1) ∧ ∀ a, a ∈ A ↔ 0 < f a}

/-- FewP with logarithmic workspace. The number of accepting branches has a polynomial bound. -/
def LogFewNL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, ∃ p : Polynomial ℕ,
    (∀ a, f a ≤ p.eval (enc a).length) ∧ ∀ a, a ∈ A ↔ 0 < f a}

/-- Test a polynomially bounded logspace accepting count by a deterministic logspace predicate
on the instance paired with the binary count. -/
def LogFew (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, ∃ p : Polynomial ℕ,
    (∀ a, f a ≤ p.eval (enc a).length) ∧
    ∃ R : α × ℕ → Bool, ComputableInLogSpace R (encPair enc encNat) encBool ∧
      ∀ a, a ∈ A ↔ R (a, f a) = true}

/-- Parity logarithmic space, using an odd accepting branch count on members. -/
def ParityL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, ∀ a, a ∈ A ↔ Odd (f a)}

/-- Fixed-modulus logspace counting. For `m ≥ 2`, membership is nonzero residue modulo `m`.
The class at an invalid modulus is empty. -/
def ModkL (m : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | 2 ≤ m ∧ ∃ f ∈ SharpL enc, ∀ a, a ∈ A ↔ f a % m ≠ 0}

/-- Variable-modulus logspace counting. The modulus is the length of a unary string output in
deterministic logarithmic space and must be a power of a prime. Membership
uses zero residue of a `GapL` function. -/
def ModL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ GapL enc, ∃ g : α → List Bool, ComputableInLogSpace g enc encBits ∧
    ∀ a, (∃ p e : ℕ, Nat.Prime p ∧ g a = List.replicate (p ^ e) false) ∧
      (a ∈ A ↔ f a % (g a).length = 0)}

/-- Unbounded-error probabilistic logarithmic space in its equivalent positive-gap
characterization [Allender and Ogihara, Theorem 1]
(https://archive.numdam.org/item/ITA_1996__30_1_1_0/). -/
def PL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ GapL enc, ∀ a, a ∈ A ↔ 0 < f a}

/-- Stoic probabilistic logspace, whose indicator is a `GapL` function. -/
def SPL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ GapL enc, (∀ a, f a = 0 ∨ f a = 1) ∧ ∀ a, a ∈ A ↔ f a = 1}

/-- Unambiguous machines satisfy the fewness bound with the constant polynomial one. -/
theorem UL_subset_LogFewNL {enc : α ↪ List Bool} : UL enc ⊆ LogFewNL enc := by
  rintro A ⟨f, hf, hle, hA⟩
  exact ⟨f, hf, 1, fun a => by simpa using hle a, hA⟩

end Cslib.Complexity
