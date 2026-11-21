/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenRoundCallback
public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision.Replay
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Dispatch.Resource
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Linear-space operations of the tagged Justesen callback

The callback uses the existing encodings for the rejecting-choice edge state and retained
membership state, preceded by the dispatch tag. The same read response and selector encoding
is used in both branches.

## Main definitions

* `Cslib.Complexity.STCON.encJustesenRoundCallbackState`: the tagged state encoding.

## Main results

* `Cslib.Complexity.STCON.justesenRoundCallback_parts_inSpace`: the query, transition,
  halt test, and optional Boolean reply consume linear workspace in their encoded requests.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.DoubleCounting _root_.Turing.NondeterministicQueryMachine

/-- Use the existing edge and membership state encodings with a single dispatch tag. -/
@[expose] def encJustesenRoundCallbackState : JustesenRoundCallbackState ↪ List Bool :=
  encSum (encOption encJustesenSubdivisionState)
    (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)

/-- Dispatch preserves the linear-space operation certificates of both callbacks. -/
theorem justesenRoundCallback_parts_inSpace {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let M := justesenRoundCallback ntm c
    let E := encJustesenRoundCallbackState
    let encStep := encPair E encReadChoice
    ComputableInSpace M.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace M.next encStep E (fun p => (encStep p).length) ∧
      ComputableInSpace M.halted E encBool (fun s => (E s).length) ∧
      ComputableInSpace justesenRoundCallbackReply E (encOption encBool)
        (fun s => (E s).length) := by
  intro M E encStep
  obtain ⟨heq, hen, heh, her⟩ := justesenWeightedSubdivisionChoice_parts_inSpace ntm
  obtain ⟨hmq, hmn, hmh, hmr⟩ := justesenSourceMembershipMachine_parts_inSpace ntm c
  have hnext := dispatch_next_inSpace (justesenWeightedSubdivisionCallback ntm).withRejectingChoice
    (justesenSourceMembershipMachine ntm c) _ _ hen hmn
  exact ⟨sumElim heq hmq, hnext, sumElim heh hmh, sumElim her hmr⟩

end Cslib.Complexity.STCON
