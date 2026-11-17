/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the tm_step tactic)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step

/-!
# Steps and equalities of configurations with `tm_step`

One test for each way `tm_step` reads a goal: the step of a running and of a halted machine, each
split of the index of the work tapes, a machine without work tapes, a move of the input head, a
configuration with oracle channels, the goals it leaves, and its two errors.
-/

public section

namespace CslibFrontierTests.TMStep

open Turing

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Writes `true` on its only tape, moves that head right, and halts. -/
def mark : MultiTapeTM 1 Bool Unit :=
  .ofTr () fun _ _ _ => ⟨0, fun _ => (some (some true), 1), none, none⟩

-- A step from a running configuration: the state is found by `rfl`, the table is unfolded, and
-- the index in `Fin 1` is replaced by `0`.
example (ws : Fin 1 → List Bool) (out : List Bool) :
    mark.step (wordsCfg input (some ()) ws out) =
      ⟨none, 1, fun _ => Function.update (tapeOfList (ws 0)) 0 (some true), fun _ => 1, out⟩ := by
  tm_step [mark]

-- A step from a halted configuration changes nothing.
example (tm : MultiTapeTM k Bool State) (c : Cfg k Bool State input) (hc : c.state = none) :
    tm.step c = c := by
  tm_step [hc]

-- `Function.update`: the index is compared with the updated one.
example (j : Fin k) (c : Cfg k Bool State input) (q : State) :
    (⟨0, Function.update (fun _ => (none, 0)) j (some (some true), 1), none, some q⟩ :
        Action k Bool State).apply c =
      ⟨some q, c.inputPos,
        Function.update c.workTapes j (Function.update (c.workTapes j) (c.workTapePos j) true),
        Function.update c.workTapePos j (c.workTapePos j + 1), c.output⟩ := by
  tm_step

-- `Fin.lastCases` and `Fin.addCases`: the index is split with the same eliminators.
example (c : Cfg (k + 2 + 1) Bool State input) :
    (⟨0, Fin.lastCases (none, 1) (Fin.addCases (fun _ => (none, 0)) fun _ => (none, -1)), none,
        c.state⟩ : Action (k + 2 + 1) Bool State).apply c =
      ⟨c.state, c.inputPos, c.workTapes,
        Fin.lastCases (c.workTapePos (Fin.last _) + 1) (Fin.addCases
          (fun i => c.workTapePos (Fin.castAdd 2 i).castSucc)
          fun i => c.workTapePos (Fin.natAdd k i).castSucc - 1), c.output⟩ := by
  tm_step

-- A numeral number of tapes: one case for each tape.
example (c : Cfg 2 Bool State input) :
    (⟨0, ![(none, 1), (none, -1)], none, c.state⟩ : Action 2 Bool State).apply c =
      ⟨c.state, c.inputPos, c.workTapes, ![c.workTapePos 0 + 1, c.workTapePos 1 - 1],
        c.output⟩ := by
  tm_step

-- `if`: the condition on the index is split on.
example (j : Fin k) (c : Cfg k Bool State input) :
    (⟨0, fun i => if i = j then (none, 1) else (none, 0), none, c.state⟩ :
        Action k Bool State).apply c =
      ⟨c.state, c.inputPos, c.workTapes,
        fun i => if i = j then c.workTapePos i + 1 else c.workTapePos i, c.output⟩ := by
  tm_step

-- No work tapes, and a move of the input head away from the right end, compared as integers.
example (c : Cfg 0 Bool State input) (n : ℕ) (hn : n < input.length + 1)
    (hc : c.inputPos = ⟨n, by omega⟩) :
    (⟨1, Fin.elim0, none, c.state⟩ : Action 0 Bool State).apply c =
      ⟨c.state, ⟨n + 1, by omega⟩, Fin.elim0, Fin.elim0, c.output⟩ := by
  tm_step [hc]

-- A configuration with oracle channels: the tapes and the channels are compared.
example (c : Cfg k Bool State input) (q : State) :
    (⟨c, fun _ => {}⟩ : MultiTapeMachine.Config k Bool State Empty input).step
        ⟨0, fun _ => (none, 0), none, some q⟩ Empty.elim Empty.elim =
      ⟨c.withState (some q), fun _ => {}⟩ := by
  tm_step [MultiTapeMachine.Config.step]

-- What `simp` does not close is left as a goal, with the hypothesis of its case in context.
example (j : Fin k) (c : Cfg k Bool State input) (pos : Fin k → ℤ)
    (hj : c.workTapePos j + 1 = pos j) (hpos : ∀ i, ¬i = j → c.workTapePos i = pos i) :
    (⟨0, Function.update (fun _ => (none, 0)) j (none, 1), none, c.state⟩ :
        Action k Bool State).apply c =
      ⟨c.state, c.inputPos, c.workTapes, pos, c.output⟩ := by
  tm_step
  · exact hj
  · exact hpos _ ‹_›

-- A field is split into at most eight cases.
/--
error: tm_step: comparing the two sides of one field takes more than 8 cases of its index.
Prove that field apart, or give fewer definitions to unfold.
-/
#guard_msgs (whitespace := lax) in
example (c : Cfg 9 Bool State input) :
    (⟨0, fun _ => (none, 1), none, c.state⟩ : Action 9 Bool State).apply c =
      ⟨c.state, c.inputPos, c.workTapes, fun i => 1 + c.workTapePos i, c.output⟩ := by
  tm_step

-- The goal has to be an equality of configurations.
/--
error: tm_step: the goal is not an equality of configurations
  a = b
-/
#guard_msgs in
example (a b : ℕ) : a = b := by
  tm_step

end CslibFrontierTests.TMStep
