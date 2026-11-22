/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Declared-variable CSP instances

This module packages constraint satisfaction instances with an explicit variable-index upper bound
`numVars` as `DeclaredCSP Rel` and defines its canonical multi-tape encoding `encDeclaredCSP`:
`numVars` is encoded in unary (`encUnary`) so variable-indexed recursion and allocation scale in the
declared universe size, while `formula` uses the framed binary-variable CSP encoding
`encCSP encRel encNat`.

## Main definitions

* `Cslib.Complexity.DeclaredCSP`: structure pairing `numVars : ℕ` and `formula : CSP Rel ℕ`.
* `Cslib.Complexity.encDeclaredCSP`: canonical bit encoding via `encUnary` and
  `encCSP encRel encNat`.
* `Cslib.Complexity.DeclaredCSP.WellFormed`, `Cslib.Complexity.DeclaredCSP.wellFormed`:
  propositional and executable checks that all occurring variables lie below `numVars`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL
open Turing.MultiTapeTM

/-- A constraint satisfaction problem instance equipped with an explicit upper bound `numVars` on
its declared variable indices (`0, …, numVars - 1`). -/
structure DeclaredCSP (Rel : Type) where
  /-- Number of declared variables (`0, …, numVars - 1`). -/
  numVars : ℕ
  /-- The CSP formula over natural-number variable labels. -/
  formula : CSP Rel ℕ
  deriving Repr

section EncDeclaredCSP

variable {Rel : Type}

/-- Canonical bit encoding of `DeclaredCSP`: unary variable bound `encUnary` followed by the
framed binary-variable CSP encoding `encCSP encRel encNat`. -/
enc_structure encDeclaredCSP (encRel : Rel ↪ List Bool) : DeclaredCSP Rel where
  numVars : encUnary,
  formula : (encCSP encRel encNat)

end EncDeclaredCSP

attribute [fun_prop]
  encDeclaredCSP_numVars_polyTime
  encDeclaredCSP_formula_polyTime
  encDeclaredCSP_mk_polyTime

namespace DeclaredCSP

variable {Rel : Type}

/-- Every variable occurring in `x.formula` lies in `{0, …, x.numVars - 1}`. -/
@[expose] def WellFormed (x : DeclaredCSP Rel) : Prop :=
  ∀ v ∈ x.formula.vars, v < x.numVars

/-- Executable Boolean check for `WellFormed`. -/
@[expose] def wellFormed (x : DeclaredCSP Rel) : Bool :=
  x.formula.vars.all fun v => decide (v < x.numVars)

end DeclaredCSP
end Cslib.Complexity
