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
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRoundClock`: a common selector clock.

## Main results

* `Cslib.Complexity.STCON.justesenRetainedSourceRoundEntry_inSpace`: linear workspace for entry.
* `Cslib.Complexity.STCON.justesenRetainedSourceRound_parts_inSpace`: linear workspace for
  query, transition, halt and reply on the encoded round state.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRound_bounds`: the clock and
  uniform state envelope hold at every admissible round entry.
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

open Cslib.Code.JustesenFamily

variable {k : ℕ} {State : Type} [Fintype State]

/-- Use the same fixed round machine with any new retained context and scalar registers. -/
theorem justesenRetainedSourceRound_withInit
    (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r next : SourceRoundLoop.Registers JustesenSourceContext) :
    (justesenRetainedSourceRound ntm c r).withInit (justesenRetainedSourceRoundEntry next) =
      justesenRetainedSourceRound ntm c next :=
  SourceRoundLoop.retainedRound_withInit JustesenSourceContext.size JustesenSourceContext.sourceID
    (justesenRoundCallback ntm c) (fun ctx => justesenRoundCallbackStart ctx.adjacency)
    justesenRoundCallbackReply r next

/-- Charge round routing and the common tagged callback clock on the original input. -/
noncomputable def configurationJustesenRetainedSourceRoundClock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  SourceRound.roundClock
    (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    (configurationJustesenRoundCallbackClock ntm c w)

/-- The retained round's common selector clock is polynomial in the original word length. -/
theorem configurationJustesenRetainedSourceRoundClock_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenRetainedSourceRoundClock ntm c) := by
  have hn := configurationSubdivisionVertexCount_polyBounded ntm c
  have ht := configurationJustesenRoundCallbackClock_polyBounded ntm c
  exact (((hn.add (.const 1)).mul (((PolyBounded.const 2).mul hn).add (.const 1))).mul
    (ht.add (.const 2))).add (ht.add (.const 1))

/-- For an initialized subdivision, every admissible round entry shares a selector clock and
an encoded-state envelope. The latter charges the retained context and the scalar round at
the maximum radius and tally allowed by the loop limit. -/
theorem configurationJustesenRetainedSourceRound_bounds
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
        (limit : ℕ), limit ≤ n →
        let context : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        ∀ r, SourceRoundLoop.Admissible context context.size limit r →
          let M := justesenRetainedSourceRound ntm c r
          let D := C * (Nat.log2 w.length + 1)
          M.HaltsWithin w (configurationJustesenRetainedSourceRoundClock ntm c w) ∧
            ∀ bits, (encJustesenRetainedSourceRoundState (M.run w bits)).length ≤
              2 * (encJustesenSourceContext context).length + 1 +
                SourceRound.roundStateBound
                  ⟨n, source.val, limit, ⟨1 + limit * n, n * limit * limit⟩⟩ D := by
  obtain ⟨C, hcallback⟩ := configurationJustesenRoundCallback_bounds ntm c
  refine ⟨C, fun w => ?_⟩
  intro I n seed source target limit hlimit context r hr M D
  have hsize : context.size = n :=
    configurationJustesenSourceContext_size ntm c w seed.val source.val target.val
  obtain ⟨_, hrad, hcount, hsum⟩ := SourceRoundLoop.admissible_caps hr
  rw [hsize] at hcount hsum
  have hcount' := hcount.trans (Nat.add_le_add_left (Nat.mul_le_mul_right n hlimit) 1)
  have hsum' := hsum.trans (Nat.mul_le_mul (Nat.mul_le_mul_left n hlimit) hlimit)
  let N := justesenRoundCallback ntm c
  let start := fun k : JustesenSourceContext => justesenRoundCallbackStart k.adjacency
  let clock := configurationJustesenRoundCallbackClock ntm c w
  have hcall (req : SourceRound.Request) (hv : req.InRange r.context.size) :
      let entry := start r.context
        (SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r)
        req
      N.HaltsFrom w entry clock ∧
        ∀ bits, (encJustesenRoundCallbackState (N.replay w bits entry)).length ≤ D := by
    simp only [SourceRoundLoop.roundContext, hr.1, hsize] at hv ⊢
    exact hcallback w seed source r.radius r.tally (hrad.trans hlimit) hcount' hsum' req hv
  have hhalt := SourceRoundLoop.retainedRound_haltsWithin JustesenSourceContext.size
    JustesenSourceContext.sourceID N start justesenRoundCallbackReply r w clock
    (fun req hv => (hcall req hv).1)
  refine ⟨?_, fun bits => ?_⟩
  · simpa only [M, justesenRetainedSourceRound, N, start, clock, n,
      configurationJustesenRetainedSourceRoundClock, hr.1, hsize] using hhalt
  · have hlen := SourceRoundLoop.retainedRound_length_run_le JustesenSourceContext.size
      JustesenSourceContext.sourceID N start justesenRoundCallbackReply r encJustesenSourceContext
      encJustesenRoundCallbackState w bits D (fun req hv => (hcall req hv).2)
    refine hlen.trans ?_
    have hscalar := SourceRoundLoop.roundStateBound_le JustesenSourceContext.size
      JustesenSourceContext.sourceID context limit r hr D
    simpa only [SourceRoundLoop.retainedRoundStateBound, hr.1, hsize] using
      Nat.add_le_add_left hscalar (2 * (encJustesenSourceContext context).length + 1)

end Cslib.Complexity.STCON
