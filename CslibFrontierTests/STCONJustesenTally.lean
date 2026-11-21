/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenMembershipTally

/-! Re-enter the Justesen tally at a variable seed and replay a passing negative scan. -/

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

end CslibFrontierTests.STCONJustesenTally
