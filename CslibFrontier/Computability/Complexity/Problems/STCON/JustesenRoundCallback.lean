/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceContext
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Dispatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.DeterministicCall

/-!
# Tagged callback for a Justesen source round

A source round requests either adjacency between two vertices or membership of one candidate.
The request selects the entry tag. Both alternatives use the supplied initialized subdivision
context and read the original input.

## Main definitions

* `Cslib.Complexity.STCON.justesenRoundCallback`: dispatch to the edge or membership machine.
* `Cslib.Complexity.STCON.justesenRoundCallbackStart`: initialize the requested alternative.
* `Cslib.Complexity.STCON.justesenRoundCallbackReply`: decode the optional Boolean reply.

## Main results

* `Cslib.Complexity.STCON.justesenRoundCallback_readReply`: the selected callback consumes
  exactly its own selectors, preserves its verdict, and returns the same suffix.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.DoubleCounting _root_.Turing.QueryMachine.Subdivision
open _root_.Turing.NondeterministicQueryMachine

variable {k : ℕ} {State : Type} [Fintype State]

/-- The tagged callback state keeps rejection distinct from either Boolean verdict. -/
abbrev JustesenRoundCallbackState :=
  Option JustesenSubdivisionState ⊕
    MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState

/-- Run the requested adjacency or membership callback on the original input. -/
@[expose] noncomputable def justesenRoundCallback (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    NondeterministicQueryMachine JustesenRoundCallbackState :=
  (justesenWeightedSubdivisionCallback ntm).withRejectingChoice.dispatch
    (justesenSourceMembershipMachine ntm c)

/-- The round request determines the callback tag and the queried vertex IDs. -/
@[expose] def justesenRoundCallbackStart (adjacency : JustesenSubdivisionContext)
    (ctx : SourceRound.Context) : SourceRound.Request → JustesenRoundCallbackState
  | .edge u v => .inl (some (justesenSubdivisionEdgeStart (adjacency, u, v)))
  | .member v => .inr (justesenRoundMembershipStart adjacency ctx v)

/-- Read the optional Boolean reply from the selected callback. -/
@[expose] def justesenRoundCallbackReply : JustesenRoundCallbackState → Option Bool :=
  Sum.elim (Option.map callbackVerdict) MembershipTally.retainedReply

/-- A request's tagged reply parser agrees with the corresponding direct parser. -/
theorem justesenRoundCallback_readReply
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (adjacency : JustesenSubdivisionContext)
    (ctx : SourceRound.Context) (request : SourceRound.Request) (input bits : List Bool) :
    (justesenRoundCallback ntm c).readReply justesenRoundCallbackReply input
      (justesenRoundCallbackStart adjacency ctx request) bits =
      match request with
      | .edge u v => (justesenWeightedSubdivisionCallback ntm).withRejectingChoice.readReply
          (Option.map callbackVerdict) input
          (some (justesenSubdivisionEdgeStart (adjacency, u, v))) bits
      | .member v => (justesenSourceMembershipMachine ntm c).readReply
          MembershipTally.retainedReply input
          (justesenRoundMembershipStart adjacency ctx v) bits := by
  cases request <;> apply Option.ext <;> rintro ⟨hit, suffix⟩ <;>
    simp only [justesenRoundCallbackStart, justesenRoundCallback, readReply_iff,
      firstHalting_dispatch_inl, firstHalting_dispatch_inr, replay_dispatch,
      Sum.map_inl, Sum.map_inr, justesenRoundCallbackReply, Sum.elim_inl, Sum.elim_inr]

end Cslib.Complexity.STCON
