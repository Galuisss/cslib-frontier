/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.BoundedWalk.Runtime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Membership tallies with a runtime bounded walk

A tally can call a bounded-walk machine whose transition rules read the dimension from the
walk state. Each call enters at the tally's dimension, source, candidate and radius. This
allows different tally queries to use the same walk on the original input. A retained-context
tally also loads the adjacency context from its own entry state.

## Main definitions

* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk`: the existing membership tally
  using a walk with runtime dimensions.
* `Turing.DoubleCounting.MembershipTally.retainedMachine`: one machine with a re-entrant
  adjacency context.

## Main results

* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_firstHalting_iff`: a successful
  first-halt selector list describes exactly one successful typed scan with the same reply.
* `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_haltsWithin` and
  `Turing.DoubleCounting.MembershipTally.withRuntimeWalk_length_run_le`: the common selector
  clock and encoded-state bound for all branches starting from a valid source.
* `Turing.DoubleCounting.MembershipTally.retainedMachine_replay`: every selector prefix agrees
  with the tally for the retained adjacency context.
-/

public section

namespace Turing.DoubleCounting.MembershipTally

open Cslib.DoubleCounting MultiTapeTM
open Turing.DoubleCounting.BoundedWalk

variable {κ τ : Type} (edge : QueryMachine τ) (start : κ → ℕ → ℕ → τ)
  (verdict : τ → Bool) (clock : ℕ)

private def enterRuntimeWalk (context : κ) (r : Registers) : Runtime.State κ τ :=
  if h : r.context.source < r.context.size ∧ r.cursor < r.context.size then
    Runtime.entry edge start verdict clock context
      ⟨⟨r.context.source, h.1⟩, ⟨r.cursor, h.2⟩, r.context.radius⟩
  else ⟨context, 1, Nat.zero_lt_one, .done none⟩

variable (initialWalk : Runtime.State κ τ) (context : κ)

/-- Run a membership tally with the supplied runtime walk. The walk enters at each valid
candidate with the tally's dimension and supplied adjacency context. An invalid walk entry
rejects. -/
def withRuntimeWalk (ctx : Context) : NondeterministicQueryMachine (State (Runtime.State κ τ)) :=
  machine ctx (Runtime.machine edge start verdict clock initialWalk)
    (enterRuntimeWalk edge start verdict clock context) Runtime.remainingFuel

/-- Re-enter the tally at new query parameters using the same runtime walk and adjacency context. -/
theorem withRuntimeWalk_withInit (ctx newContext : Context) :
    (withRuntimeWalk edge start verdict clock initialWalk context ctx).withInit
      (initial newContext) =
    withRuntimeWalk edge start verdict clock initialWalk context newContext := by
  unfold withRuntimeWalk NondeterministicQueryMachine.withInit
  rfl

/-- A successful first halt has exactly the selectors of a unique successful typed scan
and preserves its membership bit. The walk's original entry can have a different dimension
and adjacency context. -/
theorem withRuntimeWalk_firstHalting_iff {N : ℕ} (input : List Bool)
    (adjacent : Fin N → Fin N → Bool) (source target : Fin N) (radius : ℕ)
    (expected : Tally)
    (hclock : ∀ u v : Fin N,
      edge.halted (edge.runFrom input (start context u.val v.val) clock) = true)
    (hedge : ∀ u v : Fin N,
      verdict (edge.runFrom input (start context u.val v.val) clock) = adjacent u v)
    (bits : List Bool) (hit : Bool) :
    let M := withRuntimeWalk edge start verdict clock initialWalk context
      ⟨N, source.val, target.val, radius, expected⟩
    M.FirstHalting input bits M.init ∧ reply (M.run input bits) = some hit ↔
      ∃! branch, bits = selectors (BoundedWalk.selectors clock) branch ∧
        Scan.run adjacent source target radius expected branch = some hit := by
  unfold withRuntimeWalk
  refine firstHalting_iff_scan _ _ _ input adjacent source target radius expected
    (BoundedWalk.selectors clock) (BoundedWalk.eq_of_selectors_prefix clock) ?_ bits hit
  intro v acc ws left
  simpa only [enterRuntimeWalk, source.isLt, v.isLt, and_self, dite_true] using
    Runtime.firstHalting_remainingFuel_iff edge start verdict clock initialWalk context
      ⟨source, v, radius⟩ input adjacent hclock hedge ws left

private theorem runtimeWalk_withInit {ctx : Context} (r : Registers) (hr : r.context = ctx)
    (hsource : ctx.source < ctx.size) (hcursor : r.cursor < ctx.size) :
    let entry := Runtime.entry edge start verdict clock context
      ⟨⟨ctx.source, hsource⟩, ⟨r.cursor, hcursor⟩, ctx.radius⟩
    (Runtime.machine edge start verdict clock initialWalk).withInit
      (enterRuntimeWalk edge start verdict clock context r) =
    Runtime.machine edge start verdict clock entry := by
  cases hr
  simp only [Runtime.machine_withInit, enterRuntimeWalk, dite_eq_left (And.intro hsource hcursor)]

/-- The common selector clock charges the walk, entry and return for each candidate. -/
@[expose] def runtimeWalkClock (clock : ℕ) (ctx : Context) : ℕ :=
  ctx.size * (ctx.radius * (ctx.size.size + clock + 3) + (ctx.size.size + 2) + 2) + 1

/-- Charge the candidate scan and its calls, including all rejecting selector lists. -/
theorem withRuntimeWalk_haltsWithin (ctx : Context) (hsource : ctx.source < ctx.size)
    (input : List Bool) :
    (withRuntimeWalk edge start verdict clock initialWalk context ctx).HaltsWithin input
      (runtimeWalkClock clock ctx) := by
  apply haltsWithin
  intro r hr _ hcursor
  rw [runtimeWalk_withInit edge start verdict clock initialWalk context r hr hsource hcursor]
  exact Runtime.haltsWithin edge start verdict clock context
    ⟨⟨ctx.source, hsource⟩, ⟨r.cursor, hcursor⟩, ctx.radius⟩ input

/-- Add the framed adjacency context and runtime dimension to the fixed-dimension tally bound. -/
@[expose] def runtimeWalkStateBound (clock : ℕ) (ctx : Context)
    (contextLength calleeBound : ℕ) : ℕ :=
  stateBound ctx (Runtime.stateBound ctx.size ctx.radius clock contextLength calleeBound)

/-- Bound the encoded tally state on every selector prefix, including while a walk retains
the adjacency context and a suspended callback state. -/
theorem withRuntimeWalk_length_run_le (encK : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    (ctx : Context) (hsource : ctx.source < ctx.size) (input : List Bool) (calleeBound : ℕ)
    (hcallee : ∀ u v : Fin ctx.size, ∀ t ≤ clock,
      (encCallee (edge.runFrom input (start context u.val v.val) t)).length ≤ calleeBound)
    (bits : List Bool) :
    (encState (Runtime.encState encK encCallee)
      ((withRuntimeWalk edge start verdict clock initialWalk context ctx).run input bits)).length ≤
      runtimeWalkStateBound clock ctx (encK context).length calleeBound := by
  unfold runtimeWalkStateBound
  apply length_replay_le
  intro r hr _ hcursor choices
  rw [← NondeterministicQueryMachine.run_withInit,
    runtimeWalk_withInit edge start verdict clock initialWalk context r hr hsource hcursor]
  exact Runtime.length_run_le edge start verdict clock context
    ⟨⟨ctx.source, hsource⟩, ⟨r.cursor, hcursor⟩, ctx.radius⟩ input choices
    encK encCallee calleeBound hcallee

/-- A tally phase together with the adjacency context used at each walk entry. -/
structure RetainedState (κ τ : Type) where
  /-- The context passed to each adjacency call, such as the initialized seed and field. -/
  walkContext : κ
  /-- The existing tally state, including a suspended runtime walk when present. -/
  tally : State (Runtime.State κ τ)

/-- Frame the adjacency context before the existing encoded tally state. -/
enc_structure encRetainedState (encK : κ ↪ List Bool) (encCallee : τ ↪ List Bool) :
    RetainedState κ τ where
  walkContext : encK, tally : (encState (Runtime.encState encK encCallee))

/-- Enter the tally with the supplied adjacency context and query parameters. -/
def retainedInitial (walkContext : κ) (ctx : Context) : RetainedState κ τ :=
  ⟨walkContext, initial ctx⟩

/-- Decode the terminal membership reply from the retained tally. -/
def retainedReply (s : RetainedState κ τ) : Option Bool := reply s.tally

/-- Run the existing tally with the adjacency context taken from its state. -/
def retainedMachine (ctx : Context) : NondeterministicQueryMachine (RetainedState κ τ) :=
  let tallyFor k := withRuntimeWalk edge start verdict clock initialWalk k ctx
  { init := retainedInitial context ctx
    query := fun s => (tallyFor s.walkContext).query s.tally
    next := fun (s, answer, choice) =>
      { s with tally := (tallyFor s.walkContext).next (s.tally, answer, choice) }
    halted := fun s => (tallyFor s.walkContext).halted s.tally
    accept := fun s => (tallyFor s.walkContext).accept s.tally }

/-- Changing both the adjacency context and the query at entry preserves the transitions. -/
theorem retainedMachine_withInit (ctx newCtx : Context) (newContext : κ) :
    (retainedMachine edge start verdict clock initialWalk context ctx).withInit
      (retainedInitial newContext newCtx) =
    retainedMachine edge start verdict clock initialWalk newContext newCtx := by
  unfold retainedMachine withRuntimeWalk NondeterministicQueryMachine.withInit
  rfl

private theorem retainedMachine_step (ctx : Context) (input : List Bool)
    (s : RetainedState κ τ) (choice : Bool) :
    (retainedMachine edge start verdict clock initialWalk context ctx).step input s choice =
      ⟨s.walkContext,
        (withRuntimeWalk edge start verdict clock initialWalk s.walkContext ctx).step
          input s.tally choice⟩ := by
  rcases s with ⟨k, t⟩
  by_cases h : (withRuntimeWalk edge start verdict clock initialWalk k ctx).halted t = true <;>
    simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, retainedMachine, h]

/-- Replay preserves the retained context and forwards exactly the same selectors and input. -/
theorem retainedMachine_replay (ctx : Context) (input bits : List Bool) (s : RetainedState κ τ) :
    (retainedMachine edge start verdict clock initialWalk context ctx).replay input bits s =
      ⟨s.walkContext,
        (withRuntimeWalk edge start verdict clock initialWalk s.walkContext ctx).replay
          input bits s.tally⟩ := by
  induction bits generalizing s with
  | nil =>
    cases s
    rfl
  | cons choice choices ih =>
    simp only [NondeterministicQueryMachine.replay_cons, retainedMachine_step, ih]

/-- The first-halting selectors and reply agree with the tally at the retained adjacency context. -/
theorem retainedMachine_firstHalting_reply_iff (ctx : Context) (input bits : List Bool)
    (hit : Bool) :
    let M := retainedMachine edge start verdict clock initialWalk context ctx
    let T := withRuntimeWalk edge start verdict clock initialWalk context ctx
    M.FirstHalting input bits M.init ∧ retainedReply (M.run input bits) = some hit ↔
      T.FirstHalting input bits T.init ∧ reply (T.run input bits) = some hit := by
  dsimp only [NondeterministicQueryMachine.FirstHalting, NondeterministicQueryMachine.run]
  simp only [retainedMachine_replay, retainedReply]
  rfl

/-- The retained tally has the same all-branch selector clock. -/
theorem retainedMachine_haltsWithin (ctx : Context) (hsource : ctx.source < ctx.size)
    (input : List Bool) :
    (retainedMachine edge start verdict clock initialWalk context ctx).HaltsWithin input
      (runtimeWalkClock clock ctx) := by
  intro bits hlen
  rw [NondeterministicQueryMachine.run, retainedMachine_replay]
  change (withRuntimeWalk edge start verdict clock initialWalk context ctx).halted
    ((withRuntimeWalk edge start verdict clock initialWalk context ctx).run input bits) = true
  exact withRuntimeWalk_haltsWithin edge start verdict clock initialWalk context ctx hsource
    input bits hlen

/-- The encoded state bound adds the context frame to the existing runtime tally envelope. -/
def retainedStateBound (clock : ℕ) (ctx : Context)
    (contextLength calleeBound : ℕ) : ℕ :=
  2 * contextLength + 1 + runtimeWalkStateBound clock ctx contextLength calleeBound

/-- The encoded-state bound covers every retained tally state, including suspended walks. -/
theorem retainedMachine_length_run_le (encK : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    (ctx : Context) (hsource : ctx.source < ctx.size) (input : List Bool) (calleeBound : ℕ)
    (hcallee : ∀ u v : Fin ctx.size, ∀ t ≤ clock,
      (encCallee (edge.runFrom input (start context u.val v.val) t)).length ≤ calleeBound)
    (bits : List Bool) :
    (encRetainedState encK encCallee
      ((retainedMachine edge start verdict clock initialWalk context ctx).run input bits)).length ≤
      retainedStateBound clock ctx (encK context).length calleeBound := by
  have h := withRuntimeWalk_length_run_le edge start verdict clock initialWalk context
    encK encCallee ctx hsource input calleeBound hcallee bits
  rw [NondeterministicQueryMachine.run, retainedMachine_replay]
  let tally := withRuntimeWalk edge start verdict clock initialWalk context ctx
  change (encRetainedState encK encCallee ⟨context, tally.run input bits⟩).length ≤ _
  simp only [encRetainedState_apply, encRetainedStateFields, length_encPair, retainedStateBound]
  exact Nat.add_le_add_left h (2 * (encK context).length + 1)

end Turing.DoubleCounting.MembershipTally
