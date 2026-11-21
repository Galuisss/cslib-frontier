/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally

/-! Checks for the membership tally's passing negative answer and rejecting terminal check. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingMembershipTally

open Turing Turing.DoubleCounting.MembershipTally

private def unusedWalk : NondeterministicQueryMachine Unit where
  init := ()
  query := fun _ => 0
  next := fun _ => ()
  halted := fun _ => true
  accept := fun _ => true

private def run (count : ℕ) :=
  (machine ⟨1, 0, 0, 0, ⟨count, 0⟩⟩ unusedWalk (fun _ => ()) (fun _ => some 0)).run []

-- Skipping the only vertex is a successful negative answer when the expected tally is empty.
example : run 0 [false, false] = .inr (.inr (some false)) := rfl

example :
    let ctx : Context := ⟨1, 0, 0, 0, ⟨0, 0⟩⟩
    let M := machine ctx unusedWalk (fun _ => ()) (fun _ => some 0)
    M.FirstHalting [] [false, false] M.init :=
  (firstHalting_finish ⟨1, 0, 0, 0, ⟨0, 0⟩⟩ unusedWalk (fun _ => ()) (fun _ => some 0)
    [] [false] Cslib.DoubleCounting.Scan.Result.zero false rfl rfl).1

-- The same choices reject when the expected count is one.
example : run 1 [false, false] = .inr (.inr none) := rfl

-- A selected walk returns through one deterministic boundary step.
example : run 1 [true, false, false] = .inr (.inr (some true)) := rfl

end CslibFrontierTests.DoubleCountingMembershipTally
