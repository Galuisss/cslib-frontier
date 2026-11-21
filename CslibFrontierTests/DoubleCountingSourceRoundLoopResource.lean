/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Replay

/-! A concrete single-round machine composed with the multi-round source loop. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingSourceRoundLoopResource

open Turing MultiTapeTM ComputableInSpace
open Turing.DoubleCounting
open Turing.DoubleCounting.SourceRoundLoop

private def callback : NondeterministicQueryMachine Unit where
  init := ()
  query := fun _ => 0
  next := fun _ => ()
  halted := fun _ => true
  accept := fun _ => true

private def oneVertex (_ : Unit) : ℕ := 1

private def source (_ : Unit) : ℕ := 0

private def entry (_ : Turing.DoubleCounting.SourceRound.Context)
    (_ : Turing.DoubleCounting.SourceRound.Request) : Unit := ()

private def memberEntry (_ : Registers Unit) : Unit := ()

private def scan :=
  withSourceRound oneVertex source callback entry (fun _ => some true) () 1
    callback memberEntry (fun _ => some false)

example : ComputableInSpace
    (fun r => Turing.DoubleCounting.SourceRound.entry (roundContext oneVertex source r))
    (encRegisters encUnit) (Turing.DoubleCounting.SourceRound.encMachineState Unit encUnit)
    (fun r => (encRegisters encUnit r).length) :=
  roundEntry_inSpace oneVertex source encUnit encUnit
    (budget_const 1 (.refl _)) (budget_const 0 (.refl _))

-- The first call counts no new vertex, and the final membership call returns a valid negative.
example : (scan.run [] [false, false, false, false]) = .inr (some (.decided false)) := rfl

-- Enter a different register state and leave two bits for the enclosing loop.
example :
    let initial : Registers Unit := ⟨(), 3, 2, ⟨0, 0⟩⟩
    let r := start () 1
    let round := SourceRound.machine (roundContext oneVertex source initial) callback entry
      (fun _ => some true)
    let run := round.readReply SourceRound.answer [] (SourceRound.entry
      (roundContext oneVertex source r))
    run [false, false, false, true, false] = some (⟨⟨1, 0⟩, false⟩, [true, false]) ∧
      run [false, false, true, true, false] = none := by
  dsimp only
  constructor
  · apply (readSourceRoundReply_iff oneVertex source callback entry (fun _ => some true)
      _ _ [] _ _ _).mpr
    refine ⟨[false, false], rfl, (SourceRound.firstHalting_iff_replayScan _ callback entry
      (fun _ => some true) [] [false, false] _).mp ⟨?_, rfl⟩⟩
    exact NondeterministicQueryMachine.firstHalting_append_singleton _ [] [false] false rfl rfl
  · rfl

-- The same concrete machine has the composed clock on every branch and every input.
example (input : List Bool) : scan.HaltsWithin input 15 := by
  simpa only [scan, oneVertex, SourceRound.roundClock] using
    withSourceRound_haltsWithin oneVertex source callback entry (fun _ => some true) () 1
      callback memberEntry (fun _ => some false) input 0 0
      (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

-- The bound includes the actual suspended single-round state and the outer registers.
example (input choices : List Bool) :
    (encState encUnit (SourceRound.encMachineState Unit encUnit)
      encUnit (scan.run input choices)).length ≤
      2 * registerStateBound encUnit () (oneVertex ()) 1 +
        max (SourceRound.roundStateBound ⟨oneVertex (), source (), 1,
          ⟨1 + 1 * oneVertex (), oneVertex () * 1 * 1⟩⟩ 0) 0 + (encNat 1).length + 4 :=
  withSourceRound_length_run_le oneVertex source callback entry (fun _ => some true) () 1
    encUnit encUnit encUnit callback memberEntry (fun _ => some false) input 0 0
    (fun _ _ _ _ _ => Nat.zero_le 0) (fun _ _ _ => Nat.zero_le 0) choices

end CslibFrontierTests.DoubleCountingSourceRoundLoopResource
