/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceRound

/-!
# Justesen source loop

The source loop retains the initialized subdivision. It runs the tagged round until it
stabilizes, rejects, exhausts its fuel or finds a tie. On stabilization it calls the
membership tally at the designated target.

## Main definitions

* `Cslib.Complexity.STCON.justesenSourceLoop`: the fixed round and final membership loop.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoopClock`: a uniform selector clock.

## Main results

* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_haltsWithin_clock`: every
  branch at a valid initialized entry halts within the common polynomial clock.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily
open _root_.Turing _root_.Turing.DoubleCounting _root_.Turing.NondeterministicQueryMachine
open _root_.Turing.MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State]

/-- Run the concrete retained round and final membership callback on the original input. -/
@[expose] noncomputable def justesenSourceLoop
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (context : JustesenSourceContext) (limit : ℕ) :
    NondeterministicQueryMachine
      (SourceRoundLoop.State JustesenSourceContext JustesenRetainedSourceRoundState
        (MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState)) :=
  let initial := SourceRoundLoop.start context limit
  SourceRoundLoop.machine initial (justesenRetainedSourceRound ntm c initial)
    justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply
    (justesenSourceMembershipMachine ntm c) justesenSourceMembershipStart
    MembershipTally.retainedReply

/-- Charge at most one round per vertex and one final tally, including the return selectors. -/
noncomputable def configurationJustesenSourceLoopClock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
  n * (configurationJustesenRetainedSourceRoundClock ntm c w + 1) +
    configurationJustesenMembershipTallyClock ntm c w + 1

/-- The source-loop clock is polynomial in the length of the original input. -/
theorem configurationJustesenSourceLoopClock_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenSourceLoopClock ntm c) :=
  (((configurationSubdivisionVertexCount_polyBounded ntm c).mul
    ((configurationJustesenRetainedSourceRoundClock_polyBounded ntm c).add (.const 1))).add
    (configurationJustesenMembershipTallyClock_polyBounded ntm c)).add (.const 1)

/-- Every source-loop branch halts within the common clock, including rejection and limits
smaller than the subdivision size. -/
theorem configurationJustesenSourceLoop_haltsWithin_clock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
      (limit : ℕ), limit ≤ n →
      let context : JustesenSourceContext :=
        ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
      (justesenSourceLoop ntm c context limit).HaltsWithin w
        (configurationJustesenSourceLoopClock ntm c w) := by
  intro I n seed source target limit hlimit context
  obtain ⟨_, hround⟩ := configurationJustesenRetainedSourceRound_bounds ntm c
  obtain ⟨_, hmember⟩ := justesenSourceMembership_bounds ntm c
  let initial := SourceRoundLoop.start context limit
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  let roundClock := configurationJustesenRetainedSourceRoundClock ntm c w
  let memberClock := configurationJustesenMembershipTallyClock ntm c w
  have hclosed := SourceRoundLoop.retainedRound_admissible_closed JustesenSourceContext.size
    JustesenSourceContext.sourceID (justesenRoundCallback ntm c)
    (fun ctx => justesenRoundCallbackStart ctx.adjacency) justesenRoundCallbackReply context limit w
  have hrun := SourceRoundLoop.haltsWithin initial round justesenRetainedSourceRoundEntry
    justesenRetainedSourceRoundReply member justesenSourceMembershipStart
    MembershipTally.retainedReply w _
    (SourceRoundLoop.start_admissible context context.size limit) hclosed roundClock memberClock
    (fun r hr => by
      rw [justesenRetainedSourceRound_withInit]
      exact (hround w seed source target limit hlimit r hr).1)
    (fun r hr => (hmember w seed source target limit hlimit r hr).1)
  refine HaltsWithin.mono (justesenSourceLoop ntm c context limit) w hrun ?_
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right (roundClock + 1) hlimit) memberClock) 1

end Cslib.Complexity.STCON
