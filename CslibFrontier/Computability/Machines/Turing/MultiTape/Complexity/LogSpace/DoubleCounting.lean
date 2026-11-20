/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Native terminal test for double counting

The comparison used by `Cslib.DoubleCounting.Passes` takes two binary tally records and uses
workspace linear in their encoded length. In a scan on `N` vertices with walk lengths bounded
by `k`, the count is at most `N` and the sum is at most `N * k`. The comparison can therefore
operate on short registers, independently of the walks that contributed to them.
-/

public section

namespace Turing.DoubleCounting

open Cslib.DoubleCounting MultiTapeTM ComputableInSpace

/-- Binary count (framed), followed by binary length sum. -/
enc_structure encTally : Tally where count : encNat, lengthSum : encNat

/-- The actual tally (framed), followed by the expected tally. -/
abbrev encTallies := encPair encTally encTally

/-- The terminal test uses linear work space in the size of the two binary tallies. -/
theorem matches_inSpace :
    ComputableInSpace (fun p : Tally × Tally => p.1.matches p.2)
      encTallies encBool (fun p => (encTallies p).length) := by
  have actual := fst encTally encTally
  have expected := snd encTally encTally
  have countCheck := budget_natEq (encTally_count_budget actual) (encTally_count_budget expected)
  have lengthCheck := budget_natEq
    (encTally_lengthSum_budget actual) (encTally_lengthSum_budget expected)
  exact (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod countCheck lengthCheck)).of_enc_eq fun _ => rfl

end Turing.DoubleCounting
