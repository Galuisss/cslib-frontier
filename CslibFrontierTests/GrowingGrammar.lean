/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Foundations.Computability.GrowingGrammar

open Cslib

private def emptyGrammar : GrowingGrammar Bool where
  NT := Unit
  finiteNT := inferInstance
  initial := ()
  rules := [⟨[Symbol.nonterminal ()], []⟩]
  hasNonterminal := by
    intro d hd
    obtain rfl := List.mem_singleton.mp hd
    exact ⟨(), List.mem_cons_self⟩
  initial_notMem := by
    intro d hd
    obtain rfl := List.mem_singleton.mp hd
    exact List.not_mem_nil
  grows := by
    intro d hd hne
    obtain rfl := List.mem_singleton.mp hd
    exact (hne rfl).elim

/-- The rule from the start symbol to the empty word is permitted. -/
public theorem gcsl_contains_emptyWordLanguage : ∃ L ∈ GCSL Bool, [] ∈ L := by
  refine ⟨emptyGrammar.language, ⟨emptyGrammar, rfl⟩, ?_⟩
  exact Relation.ReflTransGen.single ⟨[], _, [], List.mem_cons_self, rfl, rfl⟩
