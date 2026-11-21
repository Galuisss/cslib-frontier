/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally.Runtime

/-!
# Justesen subdivision membership tally

The retained tally reads the original word. It supplies the same initialized Justesen context
to every bounded walk, so the typed scan uses the subdivision adjacency for the chosen rank.

## Main results

* `Cslib.Complexity.STCON.configurationJustesenMembershipTally_firstHalting_iff`: exact
  first-halting selector and membership-reply correspondence for the weighted tally.
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

end Cslib.Complexity.STCON
