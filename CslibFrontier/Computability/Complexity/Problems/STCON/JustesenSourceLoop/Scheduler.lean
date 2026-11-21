/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceContext.Scheduler
public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceLoop
public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler.Machine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Retain

/-!
# Justesen source loop for scheduler requests

The seed scheduler can start the retained source loop directly from a scan request and the
prepared field context. The entry uses the subdivision's vertex count as fuel and shares the
workspace budget of the request and field producers. A single scheduler machine carries the
prepared field in its state and uses it to start each scan on the original input.

## Main definitions

* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest`: enter the concrete source loop.
* `Cslib.Complexity.STCON.justesenSeedScheduler`: the scheduler with a retained field.
* `Cslib.Complexity.STCON.configurationJustesenSeedSchedulerEntry`: its entry for an original word.

## Main results

* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest_budget`: the full-fuel entry
  uses the shared workspace budget.
* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest_eq`: the scheduler and original-word
  initializers agree at any requested source.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_replay`: re-entering the fixed
  scheduler agrees with the scheduler initialized for the original word.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily
open _root_.Turing _root_.Turing.DoubleCounting
open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

/-- Enter the concrete retained round or terminate immediately at zero fuel. -/
@[expose] def justesenSourceLoopEntryOfRequest (request : SeedScanRequest) (field : FieldContext) :
    JustesenSourceLoopState :=
  SourceRoundLoop.enterRound justesenRetainedSourceRoundEntry
    (justesenSourceRegistersOfRequest request field)

/-- The callback entry uses the shared workspace budget of the request and field producers. -/
theorem justesenSourceLoopEntryOfRequest_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {request : α → SeedScanRequest} {field : α → FieldContext}
    (hrequest : ComputableInSpace request enc encSeedScanRequest S)
    (hfield : ComputableInSpace field enc encFieldContext S) :
    ComputableInSpace (fun a => justesenSourceLoopEntryOfRequest (request a) (field a))
      enc encJustesenSourceLoopState S :=
  budget_comp_linear
    (SourceRoundLoop.enterRound_inSpace encJustesenSourceContext encJustesenRetainedSourceRoundState
      (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)
      justesenRetainedSourceRoundEntry justesenRetainedSourceRoundEntry_inSpace)
    (justesenSourceRegistersOfRequest_budget hrequest hfield)

/-- The scheduler's concrete entry agrees with the original-word initializer at any source. -/
theorem justesenSourceLoopEntryOfRequest_eq {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (rank source : ℕ) :
    let setup := configurationSeedSearchSetup ntm c w
    justesenSourceLoopEntryOfRequest ⟨setup, rank, source⟩ (configurationFieldContext ntm c w) =
      (justesenSourceLoop ntm c
        ⟨configurationJustesenSubdivisionContext ntm c w rank, source, setup.targetID⟩
        setup.parameters.search.subdivision.vertexCount).init :=
  congrArg (SourceRoundLoop.enterRound justesenRetainedSourceRoundEntry)
    (justesenSourceRegistersOfRequest_eq ntm c w rank source)

/-- The concrete scheduler's scanner uses the source loop's fixed transitions. -/
noncomputable def justesenSeedSchedulerScan {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    NondeterministicQueryMachine JustesenSourceLoopState :=
  justesenSourceLoop ntm c ⟨configurationJustesenSubdivisionContext ntm c [] 0, 0, 0⟩ 0

/-- Run the scheduler for a given setup and prepared field, re-entering the source loop
at the request-specific state for each scan. -/
noncomputable def justesenSeedSchedulerFor {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (setup : SeedSearchSetup) (field : FieldContext) :
    NondeterministicQueryMachine (SeedSchedulerMachine.State JustesenSourceLoopState) :=
  SeedSchedulerMachine.machine setup (justesenSeedSchedulerScan ntm c)
    (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply

/-- The scheduler retains the prepared field alongside its existing state. -/
abbrev JustesenSeedSchedulerState :=
  FieldContext × SeedSchedulerMachine.State JustesenSourceLoopState

/-- Frame the retained field before the scheduler state. -/
def encJustesenSeedSchedulerState : JustesenSeedSchedulerState ↪ List Bool :=
  encPair encFieldContext (SeedSchedulerMachine.encState encJustesenSourceLoopState)

/-- One query machine for every prepared field and setup. Re-entry supplies the data for
the actual input word. -/
noncomputable def justesenSeedScheduler {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    NondeterministicQueryMachine JustesenSeedSchedulerState :=
  NondeterministicQueryMachine.retain (Equiv.refl _)
    (justesenSeedSchedulerFor ntm c (configurationSeedSearchSetup ntm c []))
    (configurationFieldContext ntm c [])

/-- Enter candidate zero with the setup and retained field computed on the original word. -/
noncomputable def configurationJustesenSeedSchedulerEntry {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    JustesenSeedSchedulerState :=
  let field := configurationFieldContext ntm c w
  (field, (justesenSeedSchedulerFor ntm c (configurationSeedSearchSetup ntm c w) field).init)

/-- Every selector replay from an original-word entry retains the field and agrees with
the scheduler initialized directly for that word, including rejected replays. -/
theorem configurationJustesenSeedScheduler_replay {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w bits : List Bool) :
    let field := configurationFieldContext ntm c w
    (justesenSeedScheduler ntm c).replay w bits
      (configurationJustesenSeedSchedulerEntry ntm c w) =
      (field, (justesenSeedSchedulerFor ntm c (configurationSeedSearchSetup ntm c w) field).run
        w bits) := by
  intro field
  let empty := configurationSeedSearchSetup ntm c []
  let setup := configurationSeedSearchSetup ntm c w
  let family := justesenSeedSchedulerFor ntm c empty
  let entered := justesenSeedSchedulerFor ntm c setup field
  let e := Equiv.refl JustesenSeedSchedulerState
  change (NondeterministicQueryMachine.retain e family (configurationFieldContext ntm c [])).replay
    w bits (e.symm (field, entered.init)) = (field, entered.run w bits)
  rw [NondeterministicQueryMachine.replay_retain]
  have hentry : (family field).withInit entered.init = entered :=
    SeedSchedulerMachine.machine_withInit empty setup (justesenSeedSchedulerScan ntm c)
      (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply
  exact congrArg (fun M : NondeterministicQueryMachine _ => (field, M.run w bits)) hentry

end Cslib.Complexity.STCON
