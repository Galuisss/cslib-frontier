/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceRound
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.PolyClock
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.HaltingTime

/-!
# Justesen source loop

The source loop retains the initialized subdivision. It runs the tagged round until it
stabilizes, rejects, exhausts its fuel or finds a tie. On stabilization it calls the
membership tally at the designated target.

## Main definitions

* `Cslib.Complexity.STCON.justesenSourceLoop`: the fixed round and final membership loop.
* `Cslib.Complexity.STCON.encJustesenSourceLoopState`: the existing framed loop encoding.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoopClock`: a uniform selector clock.

## Main results

* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_haltsWithin_clock`: every
  branch at a valid initialized entry halts within the common polynomial clock.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_length_run_le_log`: every
  encoded prefix state, including rejection, has logarithmic length.
* `Cslib.Complexity.STCON.configurationJustesenSourceLoop_exists_routines`: compile the
  loop on the original encoded input with logarithmic workspace and polynomial time.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily
open _root_.Turing _root_.Turing.DoubleCounting _root_.Turing.NondeterministicQueryMachine
open _root_.Turing.MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State]

/-- The concrete round and final tally use the existing loop state sum. -/
abbrev JustesenSourceLoopState :=
  SourceRoundLoop.State JustesenSourceContext JustesenRetainedSourceRoundState
    (MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState)

/-- Frame the suspended loop registers and the active round or membership state. -/
@[expose] def encJustesenSourceLoopState : JustesenSourceLoopState ↪ List Bool :=
  SourceRoundLoop.encState encJustesenSourceContext encJustesenRetainedSourceRoundState
    (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)

/-- Run the concrete retained round and final membership callback on the original input. -/
@[expose] noncomputable def justesenSourceLoop
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (context : JustesenSourceContext) (limit : ℕ) :
    NondeterministicQueryMachine JustesenSourceLoopState :=
  let initial := SourceRoundLoop.start context limit
  SourceRoundLoop.machine initial (justesenRetainedSourceRound ntm c initial)
    justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply
    (justesenSourceMembershipMachine ntm c) justesenSourceMembershipStart
    MembershipTally.retainedReply

/-- Re-entry changes the retained context and loop limit of the fixed source-loop machine. -/
theorem justesenSourceLoop_withInit (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (context next : JustesenSourceContext) (limit nextLimit : ℕ) :
    (justesenSourceLoop ntm c context limit).withInit
      (justesenSourceLoop ntm c next nextLimit).init =
      justesenSourceLoop ntm c next nextLimit :=
  SourceRoundLoop.machine_withInit _ _ _ justesenRetainedSourceRoundEntry
    justesenRetainedSourceRoundReply _ justesenSourceMembershipStart MembershipTally.retainedReply

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

private theorem justesenSourceLoop_closed
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (context : JustesenSourceContext)
    (limit : ℕ) (w : List Bool) :
    SourceRoundLoop.Closed (justesenRetainedSourceRound ntm c (SourceRoundLoop.start context limit))
      justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply w
      (SourceRoundLoop.Admissible context context.size limit) :=
  SourceRoundLoop.retainedRound_admissible_closed JustesenSourceContext.size
    JustesenSourceContext.sourceID (justesenRoundCallback ntm c)
    (fun ctx => justesenRoundCallbackStart ctx.adjacency) justesenRoundCallbackReply context limit w

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
  have hclosed := justesenSourceLoop_closed ntm c context limit w
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

/-- At valid initialized entries, every prefix of the concrete source loop has logarithmic
encoded length. The bound includes the retained registers and either suspended call. -/
theorem configurationJustesenSourceLoop_length_run_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
        (limit : ℕ), limit ≤ n →
        let context : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        let M := justesenSourceLoop ntm c context limit
        ∀ bits, (encJustesenSourceLoopState (M.run w bits)).length ≤
          C * (Nat.log2 w.length + 1) := by
  obtain ⟨A, hround⟩ := configurationJustesenRetainedSourceRound_bounds ntm c
  obtain ⟨B, henvelope⟩ := configurationJustesenRetainedSourceRound_envelopes_le_log ntm c
  obtain ⟨D, hmember⟩ := justesenSourceMembership_bounds ntm c
  obtain ⟨E, hsize⟩ := length_configurationSubdivisionVertexCount_le_log ntm c
  refine ⟨3 * B + A + D + E + 4, fun w => ?_⟩
  intro I n seed source target limit hlimit context M bits
  let b := Nat.log2 w.length + 1
  let initial := SourceRoundLoop.start context limit
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  have hctx : context.size = n :=
    configurationJustesenSourceContext_size ntm c w seed.val source.val target.val
  obtain ⟨hreg, hroundSize⟩ := henvelope w seed source target limit hlimit
  have hlength := SourceRoundLoop.length_run_le initial round justesenRetainedSourceRoundEntry
    justesenRetainedSourceRoundReply member justesenSourceMembershipStart
    MembershipTally.retainedReply w encJustesenSourceContext encJustesenRetainedSourceRoundState
    (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)
    _ (SourceRoundLoop.start_admissible context context.size limit)
    (justesenSourceLoop_closed ntm c context limit w) (B * b) (B * b + A * b) (D * b)
    (fun r hr => by
      have h := SourceRoundLoop.length_encRegisters_le encJustesenSourceContext hr
      rw [hctx] at h
      exact h.trans hreg)
    (fun r hr choices => by
      rw [← run_withInit, justesenRetainedSourceRound_withInit]
      exact ((hround w seed source target limit hlimit r hr).2 choices).trans
        (hroundSize (A * b)))
    (fun r hr => (hmember w seed source target limit hlimit r hr).2) bits
  refine hlength.trans ?_
  simp only [initial, SourceRoundLoop.start, Nat.add_zero, Nat.add_mul, Nat.mul_assoc]
  have hfuel : (encNat limit).length ≤ E * b :=
    (length_encNat_mono hlimit).trans (hsize w)
  have hb : 1 ≤ b := Nat.succ_le_succ (Nat.zero_le _)
  change 2 * (B * b) + max (B * b + A * b) (D * b) + (encNat limit).length + 4 ≤
    3 * (B * b) + A * b + D * b + E * b + 4 * b
  omega

/-- Compile one native source loop from a producer of valid initial registers. The fixed
machine runs on the original encoded input, with a logarithmic workspace bound and a
polynomial native time bound. -/
theorem configurationJustesenSourceLoop_exists_routines
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {α : Type} {enc : α ↪ List Bool}
    (contextOf : α → JustesenSourceContext) (limitOf : α → ℕ)
    (hregisters : ComputableInSpace (fun a => SourceRoundLoop.start (contextOf a) (limitOf a))
      enc (SourceRoundLoop.encRegisters encJustesenSourceContext)
      (fun a => Nat.log2 (enc a).length + 1))
    (hvalid : ∀ a,
      let w := enc a
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∃ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
        contextOf a =
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩ ∧
        limitOf a ≤ n) :
    let baseline : JustesenSourceContext :=
      ⟨configurationJustesenSubdivisionContext ntm c [] 0, 0, 0⟩
    let M := justesenSourceLoop ntm c baseline 0
    let entry := fun a => (justesenSourceLoop ntm c (contextOf a) (limitOf a)).init
    ∃ R : Routines M entry enc (fun a => Nat.log2 (enc a).length + 1),
      ∃ L d, ∀ a, R.machine.RunsInSpace (enc a) (L * (Nat.log2 (enc a).length + 1)) ∧
        R.machine.RunsInTime (enc a) (polyClock d (enc a).length) := by
  intro baseline M entry
  let initial := SourceRoundLoop.start baseline 0
  let round := justesenRetainedSourceRound ntm c initial
  let member := justesenSourceMembershipMachine ntm c
  let encMember := MembershipTally.encRetainedState encJustesenSubdivisionContext
    encJustesenSubdivisionState
  obtain ⟨hrq, hrn, hrh, hrr⟩ := justesenRetainedSourceRound_parts_inSpace ntm c initial
  obtain ⟨hmq, hmn, hmh, hmr⟩ := justesenSourceMembershipMachine_parts_inSpace ntm c
  obtain ⟨C, hspace⟩ := configurationJustesenSourceLoop_length_run_le_log ntm c
  have hstates : ∀ a bits, (encJustesenSourceLoopState
      ((justesenSourceLoop ntm c (contextOf a) (limitOf a)).run (enc a) bits)).length ≤
        C * (Nat.log2 (enc a).length + 1) := by
    intro a bits
    obtain ⟨seed, source, target, hctx, hlimit⟩ := hvalid a
    rw [hctx]
    exact hspace (enc a) seed source target (limitOf a) hlimit bits
  obtain ⟨R⟩ : Nonempty (Routines M entry enc (fun a => Nat.log2 (enc a).length + 1)) :=
    SourceRoundLoop.exists_routines encJustesenSourceContext encJustesenRetainedSourceRoundState
      encMember initial round justesenRetainedSourceRoundEntry justesenRetainedSourceRoundReply
      member justesenSourceMembershipStart MembershipTally.retainedReply enc _
      (fun a => SourceRoundLoop.start (contextOf a) (limitOf a)) hregisters (fun _ => le_rfl)
      justesenRetainedSourceRoundEntry_inSpace justesenSourceMembershipStart_inSpace hrr hmr
      hrq hmq hrh hmh hrn hmn ⟨C, hstates⟩
  let L := R.k * (2 * R.c + 1)
  have hnativeSpace (a : α) :
      R.machine.RunsInSpace (enc a) (L * (Nat.log2 (enc a).length + 1)) := by
    apply (R.runsInSpace a).mono
    dsimp only [L]
    rw [Nat.mul_assoc R.k, Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc 2 R.c]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) _)
  let : Finite R.SI := R.finiteI
  let : ∀ b, Finite (R.SP b) := R.finiteP
  let : Finite R.SF := R.finiteF
  obtain ⟨d, hd⟩ := R.machine.exists_runsInTime_polynomial_of_runsInSpace_log L
  refine ⟨R, L, d, fun a => ⟨hnativeSpace a, ?_⟩⟩
  obtain ⟨seed, source, target, hctx, hlimit⟩ := hvalid a
  have hhalt : (M.withInit (entry a)).HaltsWithin (enc a)
      (configurationJustesenSourceLoopClock ntm c (enc a)) := by
    dsimp only [M, entry]
    rw [justesenSourceLoop_withInit, hctx]
    exact configurationJustesenSourceLoop_haltsWithin_clock ntm c (enc a)
      seed source target (limitOf a) hlimit
  obtain ⟨_, htime⟩ := R.exists_runsInTime a hhalt
  exact hd (hnativeSpace a) htime

end Cslib.Complexity.STCON
