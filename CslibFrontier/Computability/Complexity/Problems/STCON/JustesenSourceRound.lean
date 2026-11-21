/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenRoundCallback.Resource
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Retained
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Retained Justesen source round

One source round retains the initialized subdivision and the source-loop endpoints. Its
tagged edge and membership callbacks use the original input and the current round registers.

## Main definitions

* `Cslib.Complexity.STCON.justesenRetainedSourceRound`: the fixed round with tagged callbacks.
* `Cslib.Complexity.STCON.justesenRetainedSourceRoundEntry`: initialize it from loop registers.
* `Cslib.Complexity.STCON.justesenRetainedSourceRoundReply`: read its optional round update.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRoundClock`: a common selector clock.

## Main results

* `Cslib.Complexity.STCON.justesenRetainedSourceRoundEntry_inSpace`: linear workspace for entry.
* `Cslib.Complexity.STCON.justesenRetainedSourceRound_parts_inSpace`: linear workspace for
  query, transition, halt and reply on the encoded round state.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRound_bounds`: the clock and
  uniform state envelope hold at every admissible round entry.
* `Cslib.Complexity.STCON.configurationJustesenRetainedSourceRound_envelopes_le_log`:
  the round and loop register envelopes are logarithmic apart from the charged callback.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.DoubleCounting
open _root_.Turing _root_.Turing.DoubleCounting _root_.Turing.NondeterministicQueryMachine
open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

/-- The round retains the same source context as its enclosing loop. -/
abbrev JustesenRetainedSourceRoundState :=
  JustesenSourceContext × SourceRound.MachineState JustesenRoundCallbackState

/-- Frame the retained context and the existing tagged round state. -/
@[expose] def encJustesenRetainedSourceRoundState :
    JustesenRetainedSourceRoundState ↪ List Bool :=
  encPair encJustesenSourceContext
    (SourceRound.encMachineState JustesenRoundCallbackState encJustesenRoundCallbackState)

/-- Use each entry's original subdivision when starting either tagged callback. -/
@[expose] noncomputable def justesenRetainedSourceRound {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r : SourceRoundLoop.Registers JustesenSourceContext) :
    NondeterministicQueryMachine JustesenRetainedSourceRoundState :=
  SourceRoundLoop.retainedRound JustesenSourceContext.size JustesenSourceContext.sourceID
    (justesenRoundCallback ntm c) (fun ctx => justesenRoundCallbackStart ctx.adjacency)
    justesenRoundCallbackReply r

/-- Re-enter the round at the current source-loop registers. -/
@[expose] def justesenRetainedSourceRoundEntry
    (r : SourceRoundLoop.Registers JustesenSourceContext) : JustesenRetainedSourceRoundState :=
  SourceRoundLoop.retainedRoundEntry JustesenSourceContext.size JustesenSourceContext.sourceID r

/-- Read a completed update, with a tie distinct from callback rejection. -/
@[expose] def justesenRetainedSourceRoundReply
    (q : JustesenRetainedSourceRoundState) : Option RoundUpdate :=
  SourceRound.answer q.2

/-- The round entry is computable in linear workspace in the encoded loop registers. -/
theorem justesenRetainedSourceRoundEntry_inSpace :
    let E := SourceRoundLoop.encRegisters encJustesenSourceContext
    ComputableInSpace justesenRetainedSourceRoundEntry E encJustesenRetainedSourceRoundState
      (fun r => (E r).length) := by
  have hctx := budget_id (enc := encJustesenSourceContext) (.refl _)
  exact SourceRoundLoop.retainedRoundEntry_inSpace JustesenSourceContext.size
    JustesenSourceContext.sourceID encJustesenSourceContext encJustesenRoundCallbackState
    (encJustesenSourceContext_size_budget hctx) (encJustesenSourceContext_sourceID_budget hctx)

/-- The retained round inherits scalar operations and its context-dependent transition. -/
theorem justesenRetainedSourceRound_parts_inSpace {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r : SourceRoundLoop.Registers JustesenSourceContext) :
    let M := justesenRetainedSourceRound ntm c r
    let E := encJustesenRetainedSourceRoundState
    let encStep := encPair E encReadChoice
    ComputableInSpace M.query E encNat (fun q => (E q).length) ∧
      ComputableInSpace M.next encStep E (fun p => (encStep p).length) ∧
      ComputableInSpace M.halted E encBool (fun q => (E q).length) ∧
      ComputableInSpace justesenRetainedSourceRoundReply E (encOption encRoundUpdate)
        (fun q => (E q).length) := by
  intro M E encStep
  let C := encJustesenRoundCallbackState
  let N := justesenRoundCallback ntm c
  let ctx :=
    SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r
  let start := justesenRoundCallbackStart r.context.adjacency
  obtain ⟨hq, hn, hh, hf⟩ := justesenRoundCallback_parts_inSpace ntm c
  have hsnd := snd encJustesenSourceContext (SourceRound.encMachineState _ C)
  have hadj := encJustesenSourceContext_adjacency_budget
    (fst encJustesenSourceContext SourceRound.encState)
  have hentry := budget_comp_linear justesenRoundCallbackStart_inSpace
    (budget_prod hadj (snd encJustesenSourceContext SourceRound.encState))
  have hquery := budget_comp_linear
    (SourceRound.machine_query_inSpace C ctx N start justesenRoundCallbackReply hq) hsnd
  have hnext := SourceRoundLoop.retainedRound_next_inSpace JustesenSourceContext.size
    JustesenSourceContext.sourceID N (fun k => justesenRoundCallbackStart k.adjacency)
    justesenRoundCallbackReply r encJustesenSourceContext C hentry hf hh hn
  have hhalt := budget_comp_linear
    (SourceRound.machine_halted_inSpace C ctx N start justesenRoundCallbackReply) hsnd
  have hreply := budget_comp_linear (SourceRound.answer_inSpace C) hsnd
  exact ⟨hquery, hnext, hhalt, hreply⟩

open Cslib.Code.JustesenFamily

variable {k : ℕ} {State : Type} [Fintype State]

/-- Use the same fixed round machine with any new retained context and scalar registers. -/
theorem justesenRetainedSourceRound_withInit
    (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (r next : SourceRoundLoop.Registers JustesenSourceContext) :
    (justesenRetainedSourceRound ntm c r).withInit (justesenRetainedSourceRoundEntry next) =
      justesenRetainedSourceRound ntm c next :=
  SourceRoundLoop.retainedRound_withInit JustesenSourceContext.size JustesenSourceContext.sourceID
    (justesenRoundCallback ntm c) (fun ctx => justesenRoundCallbackStart ctx.adjacency)
    justesenRoundCallbackReply r next

/-- Charge round routing and the common tagged callback clock on the original input. -/
noncomputable def configurationJustesenRetainedSourceRoundClock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  SourceRound.roundClock
    (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    (configurationJustesenRoundCallbackClock ntm c w)

/-- The retained round's common selector clock is polynomial in the original word length. -/
theorem configurationJustesenRetainedSourceRoundClock_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenRetainedSourceRoundClock ntm c) := by
  have hn := configurationSubdivisionVertexCount_polyBounded ntm c
  have ht := configurationJustesenRoundCallbackClock_polyBounded ntm c
  exact (((hn.add (.const 1)).mul (((PolyBounded.const 2).mul hn).add (.const 1))).mul
    (ht.add (.const 2))).add (ht.add (.const 1))

/-- For an initialized subdivision, every admissible round entry shares a selector clock and
an encoded-state envelope. The latter charges the retained context and the scalar round at
the maximum radius and tally allowed by the loop limit. -/
theorem configurationJustesenRetainedSourceRound_bounds
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
        (limit : ℕ), limit ≤ n →
        let context : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        ∀ r, SourceRoundLoop.Admissible context context.size limit r →
          let M := justesenRetainedSourceRound ntm c r
          let D := C * (Nat.log2 w.length + 1)
          M.HaltsWithin w (configurationJustesenRetainedSourceRoundClock ntm c w) ∧
            ∀ bits, (encJustesenRetainedSourceRoundState (M.run w bits)).length ≤
              2 * (encJustesenSourceContext context).length + 1 +
                SourceRound.roundStateBound
                  ⟨n, source.val, limit, ⟨1 + limit * n, n * limit * limit⟩⟩ D := by
  obtain ⟨C, hcallback⟩ := configurationJustesenRoundCallback_bounds ntm c
  refine ⟨C, fun w => ?_⟩
  intro I n seed source target limit hlimit context r hr M D
  have hsize : context.size = n :=
    configurationJustesenSourceContext_size ntm c w seed.val source.val target.val
  obtain ⟨_, hrad, hcount, hsum⟩ := SourceRoundLoop.admissible_caps hr
  rw [hsize] at hcount hsum
  have hcount' := hcount.trans (Nat.add_le_add_left (Nat.mul_le_mul_right n hlimit) 1)
  have hsum' := hsum.trans (Nat.mul_le_mul (Nat.mul_le_mul_left n hlimit) hlimit)
  let N := justesenRoundCallback ntm c
  let start := fun k : JustesenSourceContext => justesenRoundCallbackStart k.adjacency
  let clock := configurationJustesenRoundCallbackClock ntm c w
  have hcall (req : SourceRound.Request) (hv : req.InRange r.context.size) :
      let entry := start r.context
        (SourceRoundLoop.roundContext JustesenSourceContext.size JustesenSourceContext.sourceID r)
        req
      N.HaltsFrom w entry clock ∧
        ∀ bits, (encJustesenRoundCallbackState (N.replay w bits entry)).length ≤ D := by
    simp only [SourceRoundLoop.roundContext, hr.1, hsize] at hv ⊢
    exact hcallback w seed source r.radius r.tally (hrad.trans hlimit) hcount' hsum' req hv
  have hhalt := SourceRoundLoop.retainedRound_haltsWithin JustesenSourceContext.size
    JustesenSourceContext.sourceID N start justesenRoundCallbackReply r w clock
    (fun req hv => (hcall req hv).1)
  refine ⟨?_, fun bits => ?_⟩
  · simpa only [M, justesenRetainedSourceRound, N, start, clock, n,
      configurationJustesenRetainedSourceRoundClock, hr.1, hsize] using hhalt
  · have hlen := SourceRoundLoop.retainedRound_length_run_le JustesenSourceContext.size
      JustesenSourceContext.sourceID N start justesenRoundCallbackReply r encJustesenSourceContext
      encJustesenRoundCallbackState w bits D (fun req hv => (hcall req hv).2)
    refine hlen.trans ?_
    have hscalar := SourceRoundLoop.roundStateBound_le JustesenSourceContext.size
      JustesenSourceContext.sourceID context limit r hr D
    simpa only [SourceRoundLoop.retainedRoundStateBound, hr.1, hsize] using
      Nat.add_le_add_left hscalar (2 * (encJustesenSourceContext context).length + 1)

/-- The round and register envelopes are logarithmic in the input length, with a separate
charge for the suspended callback's encoded state. -/
theorem configurationJustesenRetainedSourceRound_envelopes_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n)
        (limit : ℕ), limit ≤ n →
        let context : JustesenSourceContext :=
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
        let budget := C * (Nat.log2 w.length + 1)
        SourceRoundLoop.registerStateBound encJustesenSourceContext context n limit ≤ budget ∧
          ∀ D, 2 * (encJustesenSourceContext context).length + 1 +
            SourceRound.roundStateBound ⟨n, source.val, limit, ⟨1 + limit * n, n * limit * limit⟩⟩
              D ≤ budget + D := by
  obtain ⟨A, hA⟩ := length_configurationJustesenSourceContext_le_log ntm c
  obtain ⟨B, hB⟩ := length_configurationSubdivisionVertexCount_le_log ntm c
  refine ⟨2 * A + 432 * B + 369, fun w => ?_⟩
  intro I n seed source target limit hl context budget
  let b := Nat.log2 w.length + 1
  let width := (encNat n).length
  have hctx : (encJustesenSourceContext context).length ≤ A * b := hA w seed source target
  have hn : width ≤ B * b := hB w
  have hs : (encNat source.val).length ≤ width := length_encNat_mono source.isLt.le
  have hk : (encNat limit).length ≤ width := length_encNat_mono hl
  have hone : (encNat 1).length = 1 := rfl
  have hcount : (encNat (1 + limit * n)).length ≤ 2 * width + 2 := by
    have hmul := length_encNat_mul_le limit n
    have hadd := length_encNat_add_le_add 1 (limit * n)
    dsimp only [width] at hk ⊢
    omega
  have hsum : (encNat (n * limit * limit)).length ≤ 3 * width := by
    have hmul := length_encNat_mul_le n limit
    have hmul' := length_encNat_mul_le (n * limit) limit
    dsimp only [width] at hk ⊢
    omega
  have hreg : SourceRoundLoop.registerStateBound encJustesenSourceContext context n limit ≤
      2 * (encJustesenSourceContext context).length + 11 * width + 8 := by
    rw [SourceRoundLoop.registerStateBound]
    omega
  let round : SourceRound.Context := ⟨n, source.val, limit, ⟨1 + limit * n, n * limit * limit⟩⟩
  have hround : (SourceRound.encContext round).length ≤ 13 * width + 8 := by
    simp only [round, SourceRound.encContext_apply, SourceRound.encContextFields,
      encTally_apply, encTallyFields, length_encPair]
    dsimp only [width] at hs hk hcount hsum ⊢
    omega
  let count := 1 + limit * n + n
  let total := n * limit * limit + n * (limit + 1)
  let V := max count total
  have hcountWidth : (encNat count).length ≤ 3 * width + 3 := by
    have hadd := length_encNat_add_le_add (1 + limit * n) n
    dsimp only [width, count] at hcount ⊢
    omega
  have htotalWidth : (encNat total).length ≤ 5 * width + 3 := by
    have hadd := length_encNat_add_le_add limit 1
    have hmul := length_encNat_mul_le n (limit + 1)
    have htotal := length_encNat_add_le_add (n * limit * limit) (n * (limit + 1))
    dsimp only [width, total] at hk hsum ⊢
    omega
  have hV : (encNat V).length ≤ 5 * width + 3 := by
    rcases le_total count total with h | h
    · simpa only [V, max_eq_right h] using htotalWidth
    · dsimp only [V]
      rw [max_eq_left h]
      omega
  have hlogN : Nat.log2 n ≤ width := by
    change Nat.log2 n ≤ (encNat n).length
    rw [length_encNat_eq_size]
    exact Nat.log2_le_size n
  have hlogV : Nat.log2 (V * V) ≤ 10 * width + 6 := by
    have hlog := Nat.log2_le_size (V * V)
    rw [← length_encNat_eq_size] at hlog
    have hmul := length_encNat_mul_le V V
    omega
  have hscalar (D : ℕ) : SourceRound.roundStateBound round D ≤ 432 * width + 368 + D := by
    change 2 * (6 * (SourceRound.encContext round).length + 18 * (Nat.log2 n + 1) +
      12 * (Nat.log2 (V * V) + 1) + 33) + D + 2 ≤ _
    omega
  have hb : 1 ≤ b := Nat.succ_le_succ (Nat.zero_le _)
  have hbudget : budget = 2 * (A * b) + 432 * (B * b) + 369 * b := by
    simp only [budget, b, Nat.add_mul, Nat.mul_assoc]
  refine ⟨hreg.trans ?_, fun D => ?_⟩
  · omega
  · have hstate := hscalar D
    change 2 * (encJustesenSourceContext context).length + 1 +
      SourceRound.roundStateBound round D ≤ budget + D
    omega

end Cslib.Complexity.STCON
