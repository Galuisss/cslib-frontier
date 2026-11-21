/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRound

/-! Checked scalar traces for the source controller's tie and rejection results. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingSourceRound

open Turing Turing.DoubleCounting.SourceRound

private def context : Context := ⟨3, 0, 0, ⟨2, 0⟩⟩

private def reply : NondeterministicQueryMachine (Option Bool) where
  init := none
  query _ := 0
  next p := p.1
  halted _ := true
  accept := Option.isSome

private def start (_ : Context) : Request → Option Bool
  | .edge u v => some (decide (u < 2 ∧ v = 2))
  | .member u => some (decide (u < 2))

private def tieRound := machine context reply start id

-- The first two vertices are already in the round. Both reach the third vertex.
example :
    let q := tieRound.run [] (List.replicate 16 false)
    tieRound.halted q = true ∧ (answer q).map (·.bad) = some true ∧
      (answer q).map (·.tally.count) = some 3 := by decide +kernel

private def rejectRound := machine context reply
  (fun ctx request => match request with
    | .edge .. => none
    | .member _ => start ctx request) id

-- A missing reply on the first edge call rejects the round.
example :
    let q := rejectRound.run [] (List.replicate 8 false)
    rejectRound.halted q = true ∧ (answer q).isNone = true := by decide +kernel

private inductive CallbackState where
  | pending (request : Request)
  | finished (reply : Option Bool)

private def readReply (request : Request) (bit : Option Bool) : Option Bool :=
  match request with
  | .edge u v => bit.map fun b => b && decide (u < 2 ∧ v = 2)
  | .member u => some (decide (u < 2))

private def callback : NondeterministicQueryMachine CallbackState where
  init := .finished none
  query _ := 0
  next := fun
    | (.pending request, bit, _) => .finished (readReply request bit)
    | (.finished result, _, _) => .finished result
  halted := fun
    | .pending _ => false
    | .finished _ => true
  accept _ := true

private def finish : CallbackState → Option Bool
  | .pending _ => none
  | .finished result => result

private def round := machine context callback (fun _ => .pending) finish

/-- Reading an edge bit on the original input distinguishes a tie from a missing reply. -/
example :
    let tied := round.run [true] (List.replicate 24 false)
    let rejected := round.run [] (List.replicate 12 false)
    round.halted tied = true ∧ (answer tied).map (·.bad) = some true ∧
      round.halted rejected = true ∧ (answer rejected).isNone = true := by
  decide +kernel

end CslibFrontierTests.DoubleCountingSourceRound
