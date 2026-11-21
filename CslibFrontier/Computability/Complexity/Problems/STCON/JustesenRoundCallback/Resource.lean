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
* `Cslib.Complexity.STCON.justesenRoundCallbackStart_inSpace`: enter the requested callback
  from retained adjacency and the encoded source-round state.
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

private theorem memberStart_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {adjacency : α → JustesenSubdivisionContext} {ctx : α → SourceRound.Context}
    {target : α → ℕ} (hadj : ComputableInSpace adjacency enc encJustesenSubdivisionContext S)
    (hctx : ComputableInSpace ctx enc SourceRound.encContext S)
    (htarget : ComputableInSpace target enc encNat S) :
    ComputableInSpace
      (fun a => justesenRoundCallbackStart (adjacency a) (ctx a) (.member (target a)))
      enc encJustesenRoundCallbackState S :=
  budget_comp_linear (of_inO (ComputableInO.inr _ _))
    (justesenRoundMembershipStart_budget hadj hctx htarget)

/-- Enter either requested callback using linear workspace in the retained adjacency and
scalar round state. The request is read from the existing round state encoding. -/
theorem justesenRoundCallbackStart_inSpace :
    let E := encPair encJustesenSubdivisionContext SourceRound.encState
    ComputableInSpace (fun p : JustesenSubdivisionContext × SourceRound.State =>
      justesenRoundCallbackStart p.1 p.2.context (SourceRound.request p.2))
      E encJustesenRoundCallbackState (fun p => (E p).length) := by
  intro E
  let P := encPair E Predecessor.encState
  have hadj := fst encJustesenSubdivisionContext SourceRound.encState
  have hstate := snd encJustesenSubdivisionContext SourceRound.encState
  have houter := memberStart_budget hadj (SourceRound.encState_context_budget hstate)
    (SourceRound.encState_cursor_budget hstate)
  have hpair := fst E Predecessor.encState
  have hpred := snd E Predecessor.encState
  have hadj' := budget_comp_linear hadj hpair
  have hstate' := budget_comp_linear hstate hpair
  have hctx := SourceRound.encState_context_budget hstate'
  have hcursor := Predecessor.encState_cursor_budget hpred
  have htarget := SourceRound.encState_cursor_budget hstate'
  have hphase := Predecessor.encState_memberPhase_budget hpred
  have hmember := memberStart_budget hadj' hctx hcursor
  have hedgeState := budget_comp_linear justesenSubdivisionEdgeStart_inSpace
    (budget_prod hadj' (budget_prod hcursor htarget))
  have hedge : ComputableInSpace
      (fun p : (JustesenSubdivisionContext × SourceRound.State) × Predecessor.State =>
        justesenRoundCallbackStart p.1.1 p.1.2.context (.edge p.2.cursor p.1.2.cursor))
      P encJustesenRoundCallbackState (fun p => (P p).length) :=
    budget_comp_linear (of_inO (ComputableInO.inl _ _)) (budget_optionSome hedgeState)
  have hoptional := budget_prod (budget_id (enc := E) (.refl _))
    (SourceRound.encState_predecessor_budget hstate)
  refine (budget_comp_linear (optionElimSnd houter (budget_ite hphase hmember hedge))
    hoptional).of_enc_eq ?_
  rintro ⟨adjacency, q⟩
  cases hp : q.predecessor with
  | none => simp only [hp, SourceRound.request, Option.elim_none]
  | some p =>
    cases hphase : p.memberPhase <;> simp only [hp, hphase, SourceRound.request,
      Option.elim_some, Bool.false_eq_true, ite_false, ite_true]

end Cslib.Complexity.STCON
