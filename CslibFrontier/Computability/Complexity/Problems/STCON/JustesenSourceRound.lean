/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenRoundCallback.Resource
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Retained

/-!
# Retained Justesen source round

One source round retains the initialized subdivision and the source-loop endpoints. Its
tagged edge and membership callbacks use the original input and the current round registers.

## Main definitions

* `Cslib.Complexity.STCON.justesenRetainedSourceRound`: the fixed round with tagged callbacks.
* `Cslib.Complexity.STCON.justesenRetainedSourceRoundEntry`: initialize it from loop registers.
* `Cslib.Complexity.STCON.justesenRetainedSourceRoundReply`: read its optional round update.

## Main results

* `Cslib.Complexity.STCON.justesenRetainedSourceRoundEntry_inSpace`: linear workspace for entry.
* `Cslib.Complexity.STCON.justesenRetainedSourceRound_parts_inSpace`: linear workspace for
  query, transition, halt and reply on the encoded round state.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.DoubleCounting
open _root_.Turing _root_.Turing.DoubleCounting _root_.Turing.NondeterministicQueryMachine
open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

/-- The round retains the same source context as its enclosing loop. -/
abbrev JustesenRetainedSourceRoundState :=
  JustesenSourceContext × SourceRound.MachineState JustesenRoundCallbackState

/-- Frame the retained context and the existing tagged round state. -/
@[expose] def encJustesenRetainedSourceRoundState :
    JustesenRetainedSourceRoundState ↪ List Bool :=
  encPair encJustesenSourceContext
    (SourceRound.encMachineState JustesenRoundCallbackState encJustesenRoundCallbackState)

/-- Use each entry's original subdivision when starting either tagged callback. -/
@[expose] noncomputable def justesenRetainedSourceRound {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r : SourceRoundLoop.Registers JustesenSourceContext) :
    NondeterministicQueryMachine JustesenRetainedSourceRoundState :=
  SourceRoundLoop.retainedRound JustesenSourceContext.size JustesenSourceContext.sourceID
    (justesenRoundCallback ntm c) (fun ctx => justesenRoundCallbackStart ctx.adjacency)
    justesenRoundCallbackReply r

/-- Re-enter the round at the current source-loop registers. -/
@[expose] def justesenRetainedSourceRoundEntry
    (r : SourceRoundLoop.Registers JustesenSourceContext) : JustesenRetainedSourceRoundState :=
  SourceRoundLoop.retainedRoundEntry JustesenSourceContext.size JustesenSourceContext.sourceID r

/-- Read a completed update, with a tie distinct from callback rejection. -/
@[expose] def justesenRetainedSourceRoundReply
    (q : JustesenRetainedSourceRoundState) : Option RoundUpdate :=
  SourceRound.answer q.2

/-- The round entry is computable in linear workspace in the encoded loop registers. -/
theorem justesenRetainedSourceRoundEntry_inSpace :
    let E := SourceRoundLoop.encRegisters encJustesenSourceContext
    ComputableInSpace justesenRetainedSourceRoundEntry E encJustesenRetainedSourceRoundState
      (fun r => (E r).length) := by
  have hctx := budget_id (enc := encJustesenSourceContext) (.refl _)
  exact SourceRoundLoop.retainedRoundEntry_inSpace JustesenSourceContext.size
    JustesenSourceContext.sourceID encJustesenSourceContext encJustesenRoundCallbackState
    (encJustesenSourceContext_size_budget hctx) (encJustesenSourceContext_sourceID_budget hctx)

/-- The retained round inherits scalar operations and its context-dependent transition. -/
theorem justesenRetainedSourceRound_parts_inSpace {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r : SourceRoundLoop.Registers JustesenSourceContext) :
    let M := justesenRetainedSourceRound ntm c r
    let E := encJustesenRetainedSourceRoundState
    let encStep := encPair E encReadChoice
    ComputableInSpace M.query E encNat (fun q => (E q).length) ∧
      ComputableInSpace M.next encStep E (fun p => (encStep p).length) ∧
      ComputableInSpace M.halted E encBool (fun q => (E q).length) ∧
      ComputableInSpace justesenRetainedSourceRoundReply E (encOption encRoundUpdate)
        (fun q => (E q).length) := by
  intro M E encStep
  let C := encJustesenRoundCallbackState
  let N := justesenRoundCallback ntm c
  let ctx :=
    SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r
  let start := justesenRoundCallbackStart r.context.adjacency
  obtain ⟨hq, hn, hh, hf⟩ := justesenRoundCallback_parts_inSpace ntm c
  have hsnd := snd encJustesenSourceContext (SourceRound.encMachineState _ C)
  have hadj := encJustesenSourceContext_adjacency_budget
    (fst encJustesenSourceContext SourceRound.encState)
  have hentry := budget_comp_linear justesenRoundCallbackStart_inSpace
    (budget_prod hadj (snd encJustesenSourceContext SourceRound.encState))
  have hquery := budget_comp_linear
    (SourceRound.machine_query_inSpace C ctx N start justesenRoundCallbackReply hq) hsnd
  have hnext := SourceRoundLoop.retainedRound_next_inSpace JustesenSourceContext.size
    JustesenSourceContext.sourceID N (fun k => justesenRoundCallbackStart k.adjacency)
    justesenRoundCallbackReply r encJustesenSourceContext C hentry hf hh hn
  have hhalt := budget_comp_linear
    (SourceRound.machine_halted_inSpace C ctx N start justesenRoundCallbackReply) hsnd
  have hreply := budget_comp_linear (SourceRound.answer_inSpace C) hsnd
  exact ⟨hquery, hnext, hhalt, hreply⟩

end Cslib.Complexity.STCON
