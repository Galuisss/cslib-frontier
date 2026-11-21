/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenMembershipTally

/-! Re-enter the Justesen tally at a variable seed and check replay and encoded length. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONJustesenTally

open Cslib.Code.JustesenFamily Cslib.Complexity.STCON Cslib.DoubleCounting
open Turing Turing.MultiTapeTM Turing.DoubleCounting

example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin size.vertexCount)
      (radius : ℕ) (expected : Tally) (branch : Scan.Branch size.vertexCount),
      Scan.run (configurationJustesenSubdivisionAdjacent ntm c w seed)
          source target radius expected branch = some false →
      let params : MembershipTally.Context :=
        ⟨size.vertexCount, source.val, target.val, radius, expected⟩
      let base := configurationJustesenMembershipTally ntm c [] 0 params
      let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
      let M := base.withInit (MembershipTally.retainedInitial ctx params)
      let bits := MembershipTally.selectors (BoundedWalk.selectors 3) branch
      M.FirstHalting w bits M.init ∧ MembershipTally.retainedReply (M.run w bits) = some false := by
  intro I size seed source target radius expected branch hscan params base ctx M bits
  dsimp only [M, base, ctx]
  rw [configurationJustesenMembershipTally_withInit]
  exact (configurationJustesenMembershipTally_firstHalting_iff ntm c w seed source target
    radius expected bits false).mpr
    ⟨branch, ⟨rfl, hscan⟩, fun other h =>
      MembershipTally.selectors_injective _ (BoundedWalk.eq_of_selectors_prefix 3) h.1.symm⟩

/-- A common polynomial clock and logarithmic state bound apply after re-entry at
the radius and tally limits. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenMembershipTallyClock ntm c) ∧
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source target : Fin n),
        let params : MembershipTally.Context := ⟨n, source.val, target.val, n, ⟨n, n * n⟩⟩
        let base := configurationJustesenMembershipTally ntm c [] 0 params
        let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
        let M := base.withInit (MembershipTally.retainedInitial ctx params)
        M.HaltsWithin w (configurationJustesenMembershipTallyClock ntm c w) ∧
          ∀ bits, (MembershipTally.encRetainedState encJustesenSubdivisionContext
            encJustesenSubdivisionState (M.run w bits)).length ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, h⟩ := configurationJustesenMembershipTally_length_run_le_log ntm c
  refine ⟨configurationJustesenMembershipTallyClock_polyBounded ntm c, C, fun w => ?_⟩
  intro I n seed source target params base ctx M
  dsimp only [M, base, ctx]
  rw [configurationJustesenMembershipTally_withInit]
  exact ⟨configurationJustesenMembershipTally_haltsWithin_clock ntm c w
    seed source target n ⟨n, n * n⟩ le_rfl,
    h w seed source target n ⟨n, n * n⟩ le_rfl le_rfl le_rfl⟩

end CslibFrontierTests.STCONJustesenTally
