/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ArityOccurrence

/-! The shared declared-port accessor retains a nullary row, repeated argument names,
and a large binary name. Successor transport uses the same original constraint position. -/

public section

namespace CslibFrontierTests.CSPArityOccurrence

open Cslib.Logic.PL Cslib.Complexity.CSP

/-- Relation names are their arities; the first row has no argument occurrences. -/
def body : CSP ℕ ℕ := [⟨0, []⟩, ⟨3, [2 ^ 250, 7, 7]⟩]

private theorem width : body.WellFormed id := by
  simp [Cslib.Logic.PL.CSP.WellFormed, body]

example : (arityOccurrence body width ⟨1, by decide⟩ (0 : Fin 3)).var = 2 ^ 250 := rfl

example : (argumentSuccessor (arityOccurrence body width ⟨1, by decide⟩
    (2 : Fin 3))).var = 2 ^ 250 := by
  rw [argumentSuccessor_arityOccurrence]
  rfl

-- The repeated name does not identify its two actual scope positions.
example : arityOccurrence body width ⟨1, by decide⟩ (1 : Fin 3) ≠
    arityOccurrence body width ⟨1, by decide⟩ (2 : Fin 3) := by decide +kernel

example : (arityOccurrence body width ⟨1, by decide⟩ (1 : Fin 3)).var =
    (arityOccurrence body width ⟨1, by decide⟩ (2 : Fin 3)).var := rfl

end CslibFrontierTests.CSPArityOccurrence
