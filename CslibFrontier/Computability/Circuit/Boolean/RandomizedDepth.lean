/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses

/-!
# Randomized polylogarithmic-depth circuits

These are the one-sided randomized counterparts of the nonuniform `NC` levels. A circuit
at input length `n` receives the input bits followed by independent fair random bits.
[Mulmuley, Vazirani and Vazirani][MulmuleyVaziraniVazirani1987]

## Main definitions

* `Cslib.Circuits.Boolean.RNCLevel`: one-sided error with a fixed polylogarithmic depth exponent.
* `Cslib.Circuits.Boolean.RNC`: the union of the levels.
* `Cslib.Circuits.Boolean.RNC1`: the logarithmic depth level.
-/

public section

namespace Cslib.Circuits.Boolean

/-- Languages decided by a nonuniform family of polynomial-size, bounded-fan-in circuits
of depth `O((log n) ^ i)`. Members are accepted on at least half of the random strings.
Nonmembers are rejected on every random string. -/
def RNCLevel (i : ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (s r : ℕ → ℕ), PolynomiallyBounded s ∧ PolynomiallyBounded r ∧
    ∀ n, ∃ C : Circuit signature (n + r n) 1,
      C.depth ≤ c * (Nat.log 2 n + 1) ^ i ∧ C.size ≤ s n ∧
      ∀ x : Fin n → Bool,
        let accepts (coins : Fin (r n) → Bool) := C.eval interpretation (Fin.append x coins) 0
        (L.slice n x = true →
          2 ^ r n ≤ 2 * (Finset.univ.filter fun coins => accepts coins = true).card) ∧
        (L.slice n x = false → ∀ coins, accepts coins = false)}

/-- The languages in some randomized polylogarithmic-depth level. -/
def RNC : Set (Language Bool) := ⋃ i, RNCLevel i

/-- The first randomized NC level, with logarithmic depth. -/
def RNC1 : Set (Language Bool) := RNCLevel 1

end Cslib.Circuits.Boolean
