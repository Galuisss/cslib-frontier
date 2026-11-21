/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Resource
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay

/-!
# Typed round replies in the native source loop

A successful return from the re-entered round machine consumes a complete typed round trace
and the false return selector. The rest of the selector list is available to the source loop.

## Main results

* `readSourceRoundReply_iff` characterizes the complete typed prefix and exact suffix.
-/

public section

namespace Turing.DoubleCounting.SourceRoundLoop

open Cslib.DoubleCounting NondeterministicQueryMachine

/-- The loop's round parser consumes a complete typed round replay and the false return selector,
leaving the suffix for the next round or the final membership callback. -/
theorem readSourceRoundReply_iff {κ τ : Type} (size source : κ → ℕ)
    (callee : NondeterministicQueryMachine τ)
    (calleeStart : SourceRound.Context → SourceRound.Request → τ)
    (calleeReply : τ → Option Bool) (initial r : Registers κ)
    (input bits : List Bool) (update : RoundUpdate) (suffix : List Bool) :
    let round := SourceRound.machine (roundContext size source initial) callee calleeStart
      calleeReply
    round.readReply SourceRound.answer input (SourceRound.entry (roundContext size source r))
      bits = some (update, suffix) ↔
      ∃ roundBits, bits = roundBits ++ false :: suffix ∧
        SourceRound.replayScan (roundContext size source r) callee calleeStart calleeReply input
          roundBits = some (update, []) := by
  dsimp only
  rw [readReply_iff]
  refine exists_congr fun roundBits => and_congr_right' ?_
  have hscan := SourceRound.firstHalting_iff_replayScan (roundContext size source r)
    callee calleeStart calleeReply input roundBits update
  rw [← SourceRound.machine_withInit (roundContext size source initial),
    firstHalting_withInit, run_withInit] at hscan
  exact hscan

end Turing.DoubleCounting.SourceRoundLoop
