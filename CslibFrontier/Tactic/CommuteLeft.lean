/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Group.Commute.Basic
public meta import Lean.Elab.Tactic.Simp

/-!
# Moving commuting factors to the left

Rigidity arguments move an operator of one player past operators of the other, which it commutes
with, many times in each chain of approximations: `X a * Z c * Z' d = Z' d * (X a * Z c)` when
`Z' d` commutes with `X a` and `Z c`. `commute_left [h₁, …, hₖ]` proves such equalities. Each
`hᵢ` states `Commute x y`, possibly quantified (`hXZ : ∀ a b, Commute (X a) (Z' b)`), and lets the
factors `y` move to the left of the factors `x`. The tactic instantiates each hypothesis with one
placeholder per binder and calls `simp only` with associativity and the instances of
`Commute.left_comm` and `Commute.eq`, so both sides reach the same normal form: products
associated to the right, with each `y` in front of the `x`s it commutes with.

The direction comes from the hypotheses: `Commute x y` moves `y` left, never `x`, so the rewriting
terminates. Do not pass both `Commute x y` and `Commute y x` for the same families, which would let
the factors swap back and forth.

## Main definitions

* `commute_left [h₁, …]`: prove an equation of products up to the given commutations.
-/

public meta section

namespace Cslib.Tactic.CommuteLeft

open Lean Meta Elab Tactic

/-- `commute_left [h₁, …, hₖ]` proves an equation of products in a monoid up to associativity and
the commutations `hᵢ : ∀ …, Commute x y`, by moving each `y` to the left of each `x`. -/
syntax (name := commuteLeft) "commute_left " "[" term,* "]" : tactic

/-- Elaborates `commute_left`. -/
@[tactic commuteLeft]
def evalCommuteLeft : Tactic := fun stx => do
  let hs : Syntax.TSepArray `term "," := ⟨stx[2].getArgs⟩
  let mut lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for h in hs.getElems do
    let e ← elabTerm h none
    let n ← forallTelescopeReducing (← inferType e) fun xs _ => pure xs.size
    let holes : Array (TSyntax `term) ← (List.replicate n ()).toArray.mapM fun _ => `(_)
    let app ← if n = 0 then pure h else `($h $holes*)
    lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| ($app).left_comm))
    lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| ($app).eq))
  evalTactic (← `(tactic| simp only [mul_assoc, $lemmas,*]))

end Cslib.Tactic.CommuteLeft
