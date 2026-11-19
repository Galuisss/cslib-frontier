/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.PPT

/-!
# Probabilistic polynomial-time functions

`Cslib.Complexity.FBPP` is the function analogue of `BPP`. It uses a single output function
and requires bounded error on each input under one uniform polynomial clock.
-/

public section

namespace Cslib.Complexity

open Cslib.Probability

/-- The functions computed by a strict probabilistic polynomial-time algorithm that outputs the
correct value on each input with probability at least two thirds. -/
def FBPP {α β : Type} (enc : α ↪ List Bool) (out : β ↪ List Bool) : Set (α → β) :=
  {f | ∃ program : α → ProbComp β, IsPPTOn enc out program ∧
    ∀ a, 2 / 3 ≤ ProbComp.eval (program a) (f a)}

end Cslib.Complexity
