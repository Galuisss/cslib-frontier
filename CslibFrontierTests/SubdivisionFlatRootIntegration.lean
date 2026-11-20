/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.DoubleCounting.SeedSearch.OriginalRoots
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.FlatQuery

/-! Checked agreement between the ordered source enumeration and flat adjacency requests. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SubdivisionFlatRootIntegration

open Cslib.Reachability.Hoza Cslib.LayeredDigraph.Subdivision Turing.QueryMachine.Subdivision

private def rectangularIndex (h w bound : ℕ) :
    Vertex (Fin (h + 1) × Fin w) bound ≃ Fin (((h + 1) * w) * (bound + 1)) :=
  ((equivProd _ bound).trans (finProdFinEquiv.prodCongr (Equiv.refl _))).trans finProdFinEquiv

-- The entire search source list has exactly the native root IDs in original-label order.
example (h w bound : ℕ) :
    (originalRootIDs (rectangularIndex h w bound)).map Fin.val =
      List.ofFn (fun i : Fin ((h + 1) * w) => rootID i.val bound) := by
  simp [originalRootIDs, rectangularIndex, rootID, List.map_ofFn, Function.comp_def,
    Nat.mod_add_div]

-- The same index decodes directly to the callback's labels and offsets.
example {h w : ℕ} (bound : ℕ) (ctx : Bool) (a b : Vertex (Fin (h + 1) × Fin w) bound) :
    decodeFlatQuery
      ⟨ctx, bound, (rectangularIndex h w bound a).val, (rectangularIndex h w bound b).val⟩ =
      ⟨ctx, (finProdFinEquiv a.vertex).val, (finProdFinEquiv b.vertex).val,
        a.offset.val, b.offset.val⟩ := by
  have hi (v : Vertex (Fin (h + 1) × Fin w) bound) :
      rectangularIndex h w bound v = flatIndex ((h + 1) * w) bound
        ⟨finProdFinEquiv v.vertex, v.offset⟩ := by
    simp [rectangularIndex, flatIndex]
  rw [hi a, hi b]
  exact decodeFlatQuery_flatIndex ctx bound _ _

end CslibFrontierTests.SubdivisionFlatRootIntegration
