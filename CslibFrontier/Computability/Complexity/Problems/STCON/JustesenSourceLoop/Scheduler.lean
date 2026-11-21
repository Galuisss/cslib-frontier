/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceContext.Scheduler
public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceLoop

/-!
# Justesen source loop for scheduler requests

The seed scheduler can start the retained source loop directly from a scan request and the
prepared field context. The entry uses the subdivision's vertex count as fuel and shares the
workspace budget of the request and field producers.

## Main definitions

* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest`: enter the concrete source loop.

## Main results

* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest_budget`: the full-fuel entry
  uses the shared workspace budget.
* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest_eq`: the scheduler and original-word
  initializers agree at any requested source.
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

end Cslib.Complexity.STCON
