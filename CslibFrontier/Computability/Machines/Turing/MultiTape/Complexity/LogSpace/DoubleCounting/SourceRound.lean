/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.Predecessor
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Scalar controller for one double-counting round

The outer cursor requests membership before testing incoming edges. A negative membership
reply starts the predecessor loop for that vertex. The outer cursor advances only after a
positive membership reply or a completed predecessor count. A rejected request terminates
the round, distinct from a completed round that encountered a tie.
-/

public section

namespace Turing.DoubleCounting.SourceRound

open Cslib.DoubleCounting MultiTapeTM

/-- Immutable arguments for a round of membership and adjacency calls. -/
structure Context where
  /-- Number of vertices. -/
  size : ℕ
  /-- Source for membership requests. -/
  source : ℕ
  /-- Radius used for every membership request in this round. -/
  radius : ℕ
  /-- Tally supplied to membership requests throughout this round. -/
  expected : Tally

/-- The current round prefix and any active predecessor loop. -/
structure State where
  /-- Original callback arguments. -/
  context : Context
  /-- Number of completed vertices. -/
  cursor : ℕ
  /-- Updated tally and tie flag for the completed prefix. -/
  update : RoundUpdate
  /-- Present while testing the incoming edges of the current vertex. -/
  predecessor : Option Predecessor.State
  /-- A callback rejected. -/
  rejected : Bool

/-- Binary graph size, source, radius and expected tally. -/
enc_structure encContext : Context where
  size : encNat, source : encNat, radius : encNat, expected : encTally

/-- The current encoded tally and its tie bit. -/
enc_structure encUpdate : RoundUpdate where
  tally : encTally, bad : encBool

/-- Binary outer cursor and tally, with the active predecessor loop if present. -/
enc_structure encState : State where
  context : encContext, cursor : encNat, update : encUpdate,
  predecessor : (encOption Predecessor.encState), rejected : encBool

/-- Arguments of the currently requested same-input callback. -/
inductive Request where
  /-- Test the directed edge from one vertex to another. -/
  | edge (source target : ℕ)
  /-- Test membership in the original round for this vertex. -/
  | member (vertex : ℕ)

/-- Start with the supplied tally and no completed vertices. -/
@[expose] def initial (ctx : Context) : State :=
  ⟨ctx, 0, ⟨ctx.expected, false⟩, none, false⟩

/-- Rejection and completion of the outer cursor stop the controller. -/
@[expose] def halted (q : State) : Bool :=
  q.rejected || decide (q.context.size ≤ q.cursor)

/-- Dispatch the outer membership test or the current predecessor request. -/
@[expose] def request (q : State) : Request :=
  match q.predecessor with
  | none => .member q.cursor
  | some p => if p.memberPhase then .member p.cursor else .edge p.cursor q.cursor

/-- Consume one result from the selected callback. The active predecessor loop uses its
landed reply handler, and every finished count contributes through `RoundUpdate.addVertex`. -/
@[expose] def advance (q : State) (reply : Option Bool) : State :=
  let nextVertex (update : RoundUpdate) : State :=
    { q with cursor := q.cursor + 1, update := update, predecessor := none }
  match reply with
  | none => { q with rejected := true }
  | some hit =>
    match q.predecessor with
    | none =>
      if hit then nextVertex q.update
      else
        { q with predecessor := some (Predecessor.initial
            ⟨q.context.size, q.context.source, q.cursor, q.context.radius, q.context.expected⟩) }
    | some p =>
      let next := Predecessor.advance p (some hit)
      if Predecessor.halted next then
        nextVertex (q.update.addVertex q.context.radius next.count)
      else { q with predecessor := some next }

/-- The original callback arguments are unchanged by any reply. -/
theorem advance_context (q : State) (reply : Option Bool) :
    (advance q reply).context = q.context := by
  cases reply with
  | none => rfl
  | some hit =>
    cases hp : q.predecessor with
    | none => cases hit <;> simp [advance, hp]
    | some p =>
      simp only [advance, hp]
      split <;> rfl

/-- The cursor never exceeds the number of vertices, including after a rejected reply. -/
theorem advance_cursor_le {q : State} (hlive : halted q = false) (reply : Option Bool) :
    (advance q reply).cursor ≤ q.context.size := by
  have hlt : q.cursor < q.context.size := by
    simp only [halted, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hlive
    exact hlive.2
  cases reply with
  | none => exact hlt.le
  | some hit =>
    cases hp : q.predecessor with
    | none =>
      cases hit
      · simpa only [advance, hp, Bool.false_eq_true, ite_false] using hlt.le
      · simpa only [advance, hp, ite_true] using Nat.succ_le_of_lt hlt
    | some p =>
      simp only [advance, hp]
      split
      · exact hlt
      · exact hlt.le

/-- A completed round retains its tie flag. A rejected round has no update. -/
@[expose] def result (q : State) : Option RoundUpdate :=
  if q.rejected then none else some q.update

/-- The controller retains its scalar registers while a callback reads the same input. -/
structure MachineState (τ : Type) where
  /-- Active or suspended controller. -/
  controller : State
  /-- Callback state while a request is pending. -/
  callee : Option τ

/-- The framed controller and, during a call, the entire encoded callee state. -/
enc_structure encMachineState (τ : Type) (encT : τ ↪ List Bool) : MachineState τ where
  controller : encState, callee : (encOption encT)

/-- A bound on the entire round machine state, including the suspended caller and live callee. -/
theorem length_encMachineState_le {τ : Type} (encT : τ ↪ List Bool)
    (q : MachineState τ) (C D : ℕ) (hc : (encState q.controller).length ≤ C)
    (ht : ∀ t ∈ q.callee, (encT t).length ≤ D) :
    (encMachineState τ encT q).length ≤ 2 * C + D + 2 := by
  rw [encMachineState_apply]
  simp only [encMachineStateFields, length_encPair]
  cases hcall : q.callee with
  | none =>
    rw [encOption_none]
    simp only [List.length_nil]
    omega
  | some t =>
    have hlen := ht t (by simp [hcall])
    rw [encOption_some]
    simp only [List.length_cons]
    omega

/-- Enter the fixed round transition machine with the supplied radius and tally. -/
@[expose] def entry {τ : Type} (ctx : Context) : MachineState τ :=
  ⟨initial ctx, none⟩

/-- Read the optional update after a completed round. -/
@[expose] def answer {τ : Type} (q : MachineState τ) : Option RoundUpdate :=
  result q.controller

/-- Run calls on the original input. Entering and returning use the false selector.
An active callback receives each choice unchanged until it halts. -/
@[expose] def machine {τ : Type} (ctx : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool) :
    NondeterministicQueryMachine (MachineState τ) where
  init := entry ctx
  query q := q.callee.elim 0 N.query
  next := fun ⟨q, bit, choice⟩ =>
    let reject := ⟨advance q.controller none, none⟩
    match q.callee with
    | none =>
      if choice then reject else
        ⟨q.controller, some (start q.controller.context (request q.controller))⟩
    | some callee =>
      if N.halted callee then
        if choice then reject else ⟨advance q.controller (finish callee), none⟩
      else ⟨q.controller, some (N.next (callee, bit, choice))⟩
  halted q := halted q.controller
  accept q := !q.controller.rejected

/-- Changing the round context changes only the entry state. -/
theorem machine_withInit {τ : Type} (ctx next : Context) (N : NondeterministicQueryMachine τ)
    (start : Context → Request → τ) (finish : τ → Option Bool) :
    (machine ctx N start finish).withInit (entry next) = machine next N start finish :=
  rfl

private theorem replay_callee {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ) (finish : τ → Option Bool)
    (input : List Bool) (q : State) (hq : halted q = false) (bits : List Bool) (s : τ)
    (hlive : ∀ i < bits.length, N.halted (N.replay input (bits.take i) s) = false) :
    (machine ctx N start finish).replay input bits ⟨q, some s⟩ =
      ⟨q, some (N.replay input bits s)⟩ := by
  induction bits generalizing s with
  | nil => rfl
  | cons bit bits ih =>
    have hs : N.halted s = false := hlive 0 (by simp)
    simp only [NondeterministicQueryMachine.replay_cons]
    have hstep : (machine ctx N start finish).step input ⟨q, some s⟩ bit =
        ⟨q, some (N.step input s bit)⟩ := by
      simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, machine, hq, hs]
    rw [hstep]
    apply ih
    intro i hi
    simpa only [List.take_succ_cons, NondeterministicQueryMachine.replay_cons] using
      hlive (i + 1) (Nat.succ_lt_succ hi)

/-- Replay a first-halting callback on the original input. One false selector enters the
call and one returns. The final reply may be negative or may reject. -/
theorem replay_request {τ : Type} (ctx : Context)
    (N : NondeterministicQueryMachine τ) (start : Context → Request → τ) (finish : τ → Option Bool)
    (input : List Bool) (q : State) (hq : halted q = false) (bits : List Bool)
    (hcall : N.FirstHalting input bits (start q.context (request q))) :
    (machine ctx N start finish).replay input (false :: bits ++ [false]) ⟨q, none⟩ =
      ⟨advance q (finish (N.replay input bits (start q.context (request q)))), none⟩ := by
  rw [List.cons_append, NondeterministicQueryMachine.replay_cons]
  have henter : (machine ctx N start finish).step input ⟨q, none⟩ false =
      ⟨q, some (start q.context (request q))⟩ := by
    simp [NondeterministicQueryMachine.step, machine, hq]
  rw [henter, NondeterministicQueryMachine.replay_append, replay_callee _ _ _ _ _ q hq _ _ hcall.2]
  simp [NondeterministicQueryMachine.replay_cons, NondeterministicQueryMachine.step, machine,
    hq, hcall.1]

end Turing.DoubleCounting.SourceRound
