/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally

/-! Checks for the source loop’s tie, stabilization, and callback rejection. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingSourceRoundLoop

open Cslib.DoubleCounting Turing Turing.DoubleCounting.SourceRoundLoop

private def done : NondeterministicQueryMachine Unit where
  init := ()
  query := fun _ => 0
  next := fun _ => ()
  halted := fun _ => true
  accept := fun _ => true

private def round : NondeterministicQueryMachine (Registers Unit) where
  init := start () 0
  query := fun _ => 0
  next := fun (r, _, _) => r
  halted := fun _ => true
  accept := fun _ => true

private def runWith (answer : Registers Unit → Option RoundUpdate) (choices : List Bool) :
    Option ControllerVerdict :=
  reply ((machine (start () 2) round id answer done (fun _ => ()) (fun _ => some false)).run []
    choices)

-- A tied round reports the next radius, and no final membership call is made.
example : runWith (fun _ => some ⟨⟨1, 0⟩, true⟩) [false] = some (.bad 1) := rfl

-- A growing round is followed by a stable round and the final membership query.
example : runWith (fun _ => some ⟨⟨2, 1⟩, false⟩) [false, false, false] =
    some (.decided false) := rfl

-- A rejected round never produces a source verdict.
example : runWith (fun _ => none) [false] = none := rfl

-- A true selector at a deterministic return rejects, even after a successful round.
example : runWith (fun _ => some ⟨⟨1, 0⟩, true⟩) [true] = none := rfl

private def growingRound (_ : Registers Unit) : Option RoundUpdate := some ⟨⟨2, 1⟩, false⟩

/-- Both complete outer selector returns and membership input are represented in exact replay. -/
example :
    replayRounds round id growingRound done (fun _ => ()) (fun _ => some false)
      [] (start () 2) [false, false, false] = some (some (.decided false), []) := by
  apply (firstHalting_iff_replayRounds (start () 2) round id growingRound done
    (fun _ => ()) (fun _ => some false) [] _ _).mp
  refine ⟨?_, rfl⟩
  exact NondeterministicQueryMachine.firstHalting_append_singleton _ [] [false, false] false
    rfl rfl

private def stableRound (r : Registers Unit) : Option RoundUpdate := some ⟨r.tally, false⟩

open Turing.DoubleCounting in
private def tallyInit (r : Registers Unit) : MembershipTally.State Unit :=
  MembershipTally.initial ⟨2, 0, 1, r.radius, r.tally⟩

open Turing.DoubleCounting in
private def tally : NondeterministicQueryMachine (MembershipTally.State Unit) :=
  MembershipTally.machine ⟨2, 0, 1, 0, ⟨1, 0⟩⟩ done (fun _ => ()) (fun _ => some 0)

open Turing.DoubleCounting in
-- The stable round enters the existing tally and reads a passing negative via its reply decoder.
example :
    reply ((machine (start () 1) round id stableRound tally tallyInit
        MembershipTally.reply).run [] [false, true, false, false, false, false]) =
      some (.decided false) := rfl

example (input : List Bool) :
    (machine (start () 2) round id growingRound done (fun _ => ())
      (fun _ => some false)).HaltsWithin input 3 :=
  haltsWithin (start () 2) round id growingRound done (fun _ => ()) (fun _ => some false) input
    (fun _ => True) trivial (fun _ _ _ _ _ _ _ => trivial)
    0 0 (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

end CslibFrontierTests.DoubleCountingSourceRoundLoop
