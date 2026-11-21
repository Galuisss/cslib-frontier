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
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRound_correct`: a successful
  round at exact totals returns the next tally and the tie flag.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.DoubleCounting
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

/-- The retained round consumes exactly the selectors of the corresponding scalar replay. -/
theorem justesenRetainedSourceRound_firstHalting_iff_replayScan
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r : SourceRoundLoop.Registers JustesenSourceContext) (w bits : List Bool)
    (update : RoundUpdate) :
    let M := justesenRetainedSourceRound ntm c r
    let ctx :=
      SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r
    M.FirstHalting w bits M.init ∧ justesenRetainedSourceRoundReply (M.run w bits) = some update ↔
      SourceRound.replayScan ctx (justesenRoundCallback ntm c)
        (justesenRoundCallbackStart r.context.adjacency) justesenRoundCallbackReply w bits =
          some (update, []) := by
  intro M ctx
  let N := justesenRoundCallback ntm c
  let start := fun ctx : JustesenSourceContext => justesenRoundCallbackStart ctx.adjacency
  change (SourceRoundLoop.retainedRound _ _ N start justesenRoundCallbackReply r).FirstHalting
      w bits (SourceRoundLoop.retainedRoundEntry JustesenSourceContext.size
        JustesenSourceContext.sourceID r) ∧ _ ↔ _
  rw [SourceRoundLoop.retainedRound_firstHalting]
  have hrun := SourceRoundLoop.retainedRound_run JustesenSourceContext.size
    JustesenSourceContext.sourceID N start justesenRoundCallbackReply r w bits
  change _ ∧ justesenRetainedSourceRoundReply
    ((SourceRoundLoop.retainedRound _ _ N start justesenRoundCallbackReply r).run w bits) =
      some update ↔ _
  rw [hrun]
  exact SourceRound.firstHalting_iff_replayScan ctx N (start r.context)
    justesenRoundCallbackReply w bits update

/-- At exact totals with a unique passing transcript, every successful retained round returns
the next tally and reports whether the next transcript is unique. -/
theorem configurationJustesenRetainedSourceRound_correct
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
      (fuel radius : ℕ),
      let edge := fun u v => configurationJustesenSubdivisionAdjacent ntm c w seed u v = true
      (∃! transcript, Passes edge source radius transcript) →
      let context : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      let r : SourceRoundLoop.Registers JustesenSourceContext :=
        ⟨context, fuel, radius, expected edge source radius⟩
      let M := justesenRetainedSourceRound ntm c r
      ∀ (bits : List Bool) (update : RoundUpdate), M.FirstHalting w bits M.init →
        justesenRetainedSourceRoundReply (M.run w bits) = some update →
        update.tally = expected edge source (radius + 1) ∧
          (update.bad = false ↔ ∃! transcript, Passes edge source (radius + 1) transcript) := by
  intro I n seed source target fuel radius edge hpass context r M bits update hfirst hreply
  have hscan := (justesenRetainedSourceRound_firstHalting_iff_replayScan ntm c r w bits update).mp
    ⟨hfirst, hreply⟩
  let adj := configurationJustesenSubdivisionContext ntm c w seed.val
  let ctx : SourceRound.Context := ⟨n, source.val, radius, expected edge source radius⟩
  have hsize : context.size = n :=
    configurationJustesenSourceContext_size ntm c w seed.val source.val target.val
  have hctx :
      SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r =
        ctx := by
    simp only [SourceRoundLoop.roundContext, r, hsize, ctx]
    rfl
  rw [hctx] at hscan
  refine SourceRound.replayScan_correct ctx source edge (justesenRoundCallback ntm c)
    (justesenRoundCallbackStart adj) justesenRoundCallbackReply w rfl hpass ?_ ?_ hscan
  · intro u v call hit rest hcall
    have h := configurationJustesenRoundCallback_readReply_correct ntm c w seed source radius
      (.edge u.val v.val) ⟨u.isLt, v.isLt⟩ call hit rest hcall
    change hit = configurationJustesenSubdivisionAdjacent ntm c w seed u v at h
    rw [h]
  · intro v call hit rest hcall
    exact (configurationJustesenRoundCallback_readReply_correct ntm c w seed source radius
      (.member v.val) v.isLt call hit rest hcall).trans mem_round.symm

end Cslib.Complexity.STCON
