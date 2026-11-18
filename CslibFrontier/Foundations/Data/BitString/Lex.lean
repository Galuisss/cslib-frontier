/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Data.List.Lex
import Mathlib.Data.List.OfFn

/-!
# Lexicographic order on fixed-width bit strings

`Cslib.BitString.lexSwap` tells a caller whether to swap two strings to put them in
lexicographic order. It can also be used to permute data associated with the coordinates.
-/

public section

namespace Cslib.BitString

/-- Whether lexicographic sorting interchanges `a` and `b`. Ties preserve input order. -/
@[expose] def lexSwap {n : ℕ} (a b : Fin n → Bool) : Bool :=
  decide (List.ofFn b < List.ofFn a)

/-- Reversing distinct inputs reverses the sorting decision. -/
theorem lexSwap_reverse {n : ℕ} {a b : Fin n → Bool} (h : a ≠ b) :
    lexSwap b a = !(lexSwap a b) := by
  have hn : List.ofFn a ≠ List.ofFn b := fun he => h (List.ofFn_injective he)
  rcases lt_or_gt_of_ne hn with hab | hba
  · simp [lexSwap, hab, not_lt_of_ge hab.le]
  · simp [lexSwap, hba, not_lt_of_ge hba.le]

end Cslib.BitString
