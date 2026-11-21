/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Resource

/-! A concrete single-round machine composed with the multi-round source loop. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingSourceRoundLoopResource

open Turing MultiTapeTM ComputableInSpace
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

-- The same concrete machine has the composed clock on every branch and every input.
example (input : List Bool) : scan.HaltsWithin input 15 := by
  simpa only [scan, oneVertex, roundClock] using
    withSourceRound_haltsWithin oneVertex source callback entry (fun _ => some true) () 1
      callback memberEntry (fun _ => some false) input 0 0
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

-- The bound includes the actual suspended single-round state and the outer registers.
example (input choices : List Bool) :
    (encState encUnit (Turing.DoubleCounting.SourceRound.encMachineState Unit encUnit)
      encUnit (scan.run input choices)).length ≤
      2 * registerStateBound encUnit () 1 1 + roundStateBound ⟨1, 0, 1, ⟨2, 1⟩⟩ 0 +
        (encNat 1).length + 4 := by
  simpa only [scan, oneVertex, source, Nat.one_mul, Nat.mul_one, max_zero] using
    withSourceRound_length_run_le oneVertex source callback entry (fun _ => some true) () 1
      encUnit encUnit encUnit callback memberEntry (fun _ => some false) input 0 0
      (fun _ _ _ _ => Nat.zero_le 0) (fun _ _ _ => Nat.zero_le 0) choices

end CslibFrontierTests.DoubleCountingSourceRoundLoopResource
