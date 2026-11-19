/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BQP

/-!
# BQP with classical advice

These are Karp–Lipton advice classes [Karp, Lipton][KarpLipton1980]. The decider receives
a framed advice word followed by the input, with time polynomial in the complete encoded
length. Membership in the decider's language has bounded error on every pair, including
pairs with incorrect advice. Only the advice used to recover the original language needs to
depend on input length alone.

## Main definitions

* `BQPWithAdvice`: bounded-error quantum polynomial time with a specified advice length.
* `BQPLog`, `BQPPoly`: logarithmic and polynomial-length advice.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Bounded-error quantum polynomial time with an arbitrary advice string of exactly
`length n` bits at input length `n`. The decider has bounded error on every advice/input pair. -/
def BQPWithAdvice (length : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ advice : ℕ → List Bool, (∀ n, (advice n).length = length n) ∧
    ∃ A ∈ BQP (encPair encBits encBits), ∀ x, x ∈ L ↔ (advice x.length, x) ∈ A}

/-- BQP with logarithmic-length Karp–Lipton advice. -/
def BQPLog : Set (Set (List Bool)) :=
  {L | ∃ c : ℕ, L ∈ BQPWithAdvice (fun n => c * (Nat.log 2 n + 1))}

/-- BQP with polynomial-length Karp–Lipton advice. -/
def BQPPoly : Set (Set (List Bool)) :=
  {L | ∃ p : Polynomial ℕ, L ∈ BQPWithAdvice p.eval}


end Cslib.Complexity
