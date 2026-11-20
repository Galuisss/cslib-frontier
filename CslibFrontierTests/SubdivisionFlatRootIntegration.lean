/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.DoubleCounting.SeedSearch.OriginalRoots
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.FlatQuery
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.HozaSize

/-! Checked agreement between the ordered source enumeration and flat adjacency requests. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SubdivisionFlatRootIntegration

open Cslib.Reachability.Hoza Cslib.LayeredDigraph.Subdivision Turing.QueryMachine.Subdivision

private def labelEquiv (w h : ℕ) : (Fin (h + 1) × Fin w) ≃
    Fin (subdivisionSize w h).originalCount :=
  finProdFinEquiv.trans (finCongr (by simp [subdivisionSize, Nat.mul_comm]))

private abbrev relabel (w h : ℕ) :
    Vertex (Fin (h + 1) × Fin w) (subdivisionSize w h).chainBound ≃
      Vertex (Fin (subdivisionSize w h).originalCount) (subdivisionSize w h).chainBound :=
  ((equivProd _ _).trans ((labelEquiv w h).prodCongr (Equiv.refl _))).trans (equivProd _ _).symm

private theorem relabel_apply {w h : ℕ}
    (v : Vertex (Fin (h + 1) × Fin w) (subdivisionSize w h).chainBound) :
    relabel w h v = ⟨labelEquiv w h v.vertex, v.offset⟩ := by
  apply (equivProd _ _).injective
  simp

private def sizeIndex (w h : ℕ) :
    Vertex (Fin (h + 1) × Fin w) (subdivisionSize w h).chainBound ≃
      Fin (subdivisionSize w h).vertexCount :=
  let p := subdivisionSize w h
  ((relabel w h).trans (flatIndex p.originalCount p.chainBound)).trans (finCongr rfl)

private theorem sizeIndex_val {w h : ℕ}
    (v : Vertex (Fin (h + 1) × Fin w) (subdivisionSize w h).chainBound) :
    (sizeIndex w h v).val =
      (flatIndex (subdivisionSize w h).originalCount (subdivisionSize w h).chainBound
        ⟨labelEquiv w h v.vertex, v.offset⟩).val := by
  change (flatIndex _ _ (relabel w h v)).val = _
  rw [relabel_apply]

-- The native root ID list has the same ordering and values as the search's original sources.
example (w h : ℕ) :
    (originalRootIDs (sizeIndex w h)).map Fin.val =
      List.ofFn (fun i : Fin ((h + 1) * w) => rootID i.val (subdivisionSize w h).chainBound) := by
  simp only [originalRootIDs, List.map_ofFn]
  congr 1
  funext i
  change (sizeIndex w h (root _ (finProdFinEquiv.symm i))).val = _
  rw [sizeIndex_val, ← rootID_eq_flatIndex]
  change rootID (finProdFinEquiv (finProdFinEquiv.symm i)).val _ = _
  rw [Equiv.apply_symm_apply]

-- The same numbering has the returned size and decodes both endpoints of the callback query.
example {w h : ℕ} (ctx : Bool)
    (a b : Vertex (Fin (h + 1) × Fin w) (subdivisionSize w h).chainBound) :
    decodeFlatQuery
      ⟨ctx, (subdivisionSize w h).chainBound, (sizeIndex w h a).val, (sizeIndex w h b).val⟩ =
      ⟨ctx, (labelEquiv w h a.vertex).val, (labelEquiv w h b.vertex).val,
        a.offset.val, b.offset.val⟩ := by
  rw [sizeIndex_val a, sizeIndex_val b]
  exact decodeFlatQuery_flatIndex ctx _ _ _

end CslibFrontierTests.SubdivisionFlatRootIntegration
