/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally.Runtime
import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenBoundedWalk
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Justesen subdivision membership tally

The retained tally reads the original word. It supplies the same initialized Justesen context
to every bounded walk, so the typed scan uses the subdivision adjacency for the chosen rank.

## Main results

* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_firstHalting_iff`: exact
  first-halting selector and membership-reply correspondence for the weighted tally.
* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_length_run_le_log`:
  logarithmic encoded length on every prefix of a bounded tally query.
* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_haltsWithin_clock`:
  a common polynomial selector clock for those queries.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.DoubleCounting
open _root_.Turing _root_.Turing.MultiTapeTM
open _root_.Turing.DoubleCounting _root_.Turing.QueryMachine.Subdivision

variable {k : ℕ} {State : Type} [Fintype State]

private noncomputable def tallyWalkInitial (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    BoundedWalk.Runtime.State JustesenSubdivisionContext JustesenSubdivisionState :=
  ⟨configurationJustesenSubdivisionContext ntm c [] 0, 1, Nat.zero_lt_one, .done none⟩

/-- The membership tally for the initialized Justesen-weighted subdivision of the original
input. Its adjacency calls use the common clock three. -/
noncomputable def configurationJustesenMembershipTally (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) (rank : ℕ) (params : MembershipTally.Context) :
    NondeterministicQueryMachine
      (MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState) :=
  MembershipTally.retainedMachine (justesenWeightedSubdivisionCallback ntm)
    (fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)) callbackVerdict 3
    (tallyWalkInitial ntm c) (configurationJustesenSubdivisionContext ntm c w rank) params

/-- Changing the original word, rank, and query parameters changes only the tally entry. -/
theorem configurationJustesenMembershipTally_withInit (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w w' : List Bool) (rank rank' : ℕ) (params params' : MembershipTally.Context) :
    (configurationJustesenMembershipTally ntm c w rank params).withInit
      (MembershipTally.retainedInitial (configurationJustesenSubdivisionContext ntm c w' rank')
        params') =
    configurationJustesenMembershipTally ntm c w' rank' params' :=
  MembershipTally.retainedMachine_withInit (justesenWeightedSubdivisionCallback ntm)
    (fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)) callbackVerdict 3
    (tallyWalkInitial ntm c) (configurationJustesenSubdivisionContext ntm c w rank)
    params params' (configurationJustesenSubdivisionContext ntm c w' rank')

/-- At a valid seed and endpoints, a successful tally uses the selectors of exactly one
passing typed scan and preserves its membership reply. -/
theorem configurationJustesenMembershipTally_firstHalting_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ) (expected : Tally) (bits : List Bool) (hit : Bool),
      let M := configurationJustesenMembershipTally ntm c w seed.val
        ⟨size.vertexCount, source.val, target.val, radius, expected⟩
      M.FirstHalting w bits M.init ∧ MembershipTally.retainedReply (M.run w bits) = some hit ↔
        ∃! branch, bits = MembershipTally.selectors (BoundedWalk.selectors 3) branch ∧
          Scan.run (configurationJustesenSubdivisionAdjacent ntm c w seed)
            source target radius expected branch = some hit := by
  intro I size seed source target radius expected bits hit M
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
  let initial := tallyWalkInitial ntm c
  have hcall := configurationJustesenSubdivisionEdge_halts_and_agrees ntm c w seed
  exact (MembershipTally.retainedMachine_firstHalting_reply_iff edge start callbackVerdict 3
    initial ctx ⟨size.vertexCount, source.val, target.val, radius, expected⟩ w bits hit).trans
    (MembershipTally.withRuntimeWalk_firstHalting_iff edge start callbackVerdict 3 initial ctx
      w (configurationJustesenSubdivisionAdjacent ntm c w seed) source target radius expected
      (fun u v => (hcall u v).1) (fun u v => (hcall u v).2) bits hit)

/-- The tally envelope is logarithmic apart from the charged adjacency callback state. -/
theorem configurationJustesenMembershipTally_stateBound_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
        (radius : ℕ) (expected : Tally) (calleeBound : ℕ),
        radius ≤ size.vertexCount →
        expected.count ≤ size.vertexCount →
        expected.lengthSum ≤ size.vertexCount * size.vertexCount →
        let params : MembershipTally.Context :=
          ⟨size.vertexCount, source.val, target.val, radius, expected⟩
        let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
        MembershipTally.retainedStateBound 3 params
          (encJustesenSubdivisionContext ctx).length calleeBound ≤
          C * (Nat.log2 w.length + 1) + calleeBound := by
  obtain ⟨W, hwalk⟩ := configurationJustesenBoundedWalk_stateBound_le_log ntm c
  obtain ⟨D, hcontext⟩ := length_configurationJustesenSubdivisionContext_le_log ntm c
  obtain ⟨P, hvertices⟩ := length_configurationSubdivisionVertexCount_le_log ntm c
  refine ⟨2 * D + 68 * P + W + 52, fun w => ?_⟩
  intro I size seed source target radius expected calleeBound hr hc hs params ctx
  let n := size.vertexCount
  let b := Nat.log2 w.length + 1
  have hn : (encNat n).length ≤ P * b := hvertices w
  have hctx : (encJustesenSubdivisionContext ctx).length ≤ D * b :=
    hcontext w seed.val seed.isLt
  have hW : BoundedWalk.Runtime.stateBound n radius 3
      (encJustesenSubdivisionContext ctx).length calleeBound ≤ W * b + calleeBound :=
    hwalk w seed radius calleeBound hr
  have hsource := length_encNat_mono source.isLt.le
  have htarget := length_encNat_mono target.isLt.le
  have hradius := length_encNat_mono hr
  have hcount := length_encNat_mono hc
  have hsum := (length_encNat_mono hs).trans (length_encNat_mul_le n n)
  have hparams : (MembershipTally.encContext params).length ≤ 12 * (encNat n).length + 5 := by
    simp only [params, MembershipTally.encContext_apply, MembershipTally.encContextFields,
      encTally_apply, encTallyFields, length_encPair]
    dsimp only [n] at hsum ⊢
    omega
  have hlogN : Nat.log2 n ≤ (encNat n).length := by
    rw [length_encNat_eq_size]
    exact Nat.log2_le_size _
  have hlogSum : Nat.log2 (n * radius) ≤ 2 * (encNat n).length := by
    have hlen := length_encNat_mul_le n radius
    have hlog : Nat.log2 (n * radius) ≤ (encNat (n * radius)).length := by
      rw [length_encNat_eq_size]
      exact Nat.log2_le_size _
    dsimp only [n] at hlen hlog ⊢
    omega
  have hb : 1 ≤ b := Nat.succ_le_succ (Nat.zero_le _)
  change MembershipTally.retainedStateBound 3 params
    (encJustesenSubdivisionContext ctx).length calleeBound ≤ _ * b + _
  simp only [MembershipTally.retainedStateBound, MembershipTally.runtimeWalkStateBound,
    MembershipTally.stateBound, Nat.add_mul, Nat.mul_assoc]
  change 2 * (encJustesenSubdivisionContext ctx).length + 1 +
    (4 * (MembershipTally.encContext params).length + 12 * (Nat.log2 n + 1) +
      4 * (Nat.log2 (n * radius) + 1) +
      BoundedWalk.Runtime.stateBound n radius 3
        (encJustesenSubdivisionContext ctx).length calleeBound + 15) ≤ _
  dsimp only [n] at hn hW hparams hlogN hlogSum ⊢
  omega

/-- Every prefix of an initialized tally fits the uniform logarithmic encoded-state bound. -/
theorem configurationJustesenMembershipTally_length_run_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
        (radius : ℕ) (expected : Tally),
        radius ≤ size.vertexCount →
        expected.count ≤ size.vertexCount →
        expected.lengthSum ≤ size.vertexCount * size.vertexCount →
        let params : MembershipTally.Context :=
          ⟨size.vertexCount, source.val, target.val, radius, expected⟩
        let M := configurationJustesenMembershipTally ntm c w seed.val params
        ∀ bits, (MembershipTally.encRetainedState encJustesenSubdivisionContext
          encJustesenSubdivisionState (M.run w bits)).length ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨A, hcall⟩ := configurationJustesenSubdivisionEdge_contract ntm c
  obtain ⟨C, hbound⟩ := configurationJustesenMembershipTally_stateBound_le_log ntm c
  refine ⟨C + A, fun w => ?_⟩
  intro I size seed source target radius expected hr hc hs params M bits
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
  let b := Nat.log2 w.length + 1
  have hcallee (u v : Fin size.vertexCount) (t : ℕ) (ht : t ≤ 3) :
      (encJustesenSubdivisionState (edge.runFrom w (start ctx u.val v.val) t)).length ≤ A * b :=
    (hcall w seed u v).2.2.2 t ht
  have hrun := MembershipTally.retainedMachine_length_run_le edge start callbackVerdict 3
    (tallyWalkInitial ntm c) ctx encJustesenSubdivisionContext encJustesenSubdivisionState
    params source.isLt w (A * b) hcallee bits
  refine hrun.trans ?_
  simpa only [b, Nat.add_mul] using hbound w seed source target radius expected (A * b) hr hc hs

/-- Charge one bounded walk and its entry and return at each candidate, then the final check. -/
noncomputable def configurationJustesenMembershipTallyClock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
  n * (configurationJustesenBoundedWalkClock ntm c w + 2) + 1

/-- The common tally selector clock is polynomial in the length of the original input. -/
theorem configurationJustesenMembershipTallyClock_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenMembershipTallyClock ntm c) :=
  ((configurationSubdivisionVertexCount_polyBounded ntm c).mul
      ((configurationJustesenBoundedWalkClock_polyBounded ntm c).add (.const 2))).add (.const 1)

/-- The clock covers all tally branches uniformly over valid seed and endpoint IDs
and radii at most the subdivision vertex count. -/
theorem configurationJustesenMembershipTally_haltsWithin_clock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ) (expected : Tally), radius ≤ size.vertexCount →
      let params : MembershipTally.Context :=
        ⟨size.vertexCount, source.val, target.val, radius, expected⟩
      (configurationJustesenMembershipTally ntm c w seed.val params).HaltsWithin w
        (configurationJustesenMembershipTallyClock ntm c w) := by
  intro I size seed source target radius expected hr params
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
  have h := MembershipTally.retainedMachine_haltsWithin edge start callbackVerdict 3
    (tallyWalkInitial ntm c) ctx params source.isLt w
  refine NondeterministicQueryMachine.HaltsWithin.mono _ _ h ?_
  simp only [MembershipTally.runtimeWalkClock, params, configurationJustesenMembershipTallyClock,
    configurationJustesenBoundedWalkClock, Nat.add_assoc, Nat.reduceAdd]
  gcongr

end Cslib.Complexity.STCON
