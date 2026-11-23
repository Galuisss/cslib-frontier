/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.RowLabels
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.OriginCount
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.RowBandwidth
import Mathlib.Tactic.Ring

/-!
# Bandwidth of the actual row-ordered planarization

Each row receives original source vertices, bounded cap gadgets, and bounded crossover gadgets.
The same actual vertex-row function gives both the row budget and the endpoint distance bound.
A supplied row-sorted order is retained in the resulting bandwidth certificate.

## Main definitions

* `Planar.Embedding.rowBudget`: source, cap, and crossing contributions to one row.
* `Planar.Embedding.rowBandwidthCertificate`: certify the supplied actual order.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding
open Diagram

/-- Vertex capacity contributed by source vertices, edge caps, and actual wire crossings. -/
@[expose] def rowBudget (sources edges labels : ℕ) : ℕ := sources + 16 * edges + 1144 * labels ^ 2

section Layout
variable {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (vertexRow : Fin vs.length → ℕ) (srcRow : Port (Fin m) → ℕ) (ownerRow : Fin m → ℕ)
    (hxs : (Sources.vertexLabels vs).Pairwise (fun a b => srcRow a ≤ srcRow b))
    (hys : (Sinks.pairLabels (List.finRange m)).Pairwise
      (fun a b => ownerRow a.edge ≤ ownerRow b.edge))
    (hrow : ∀ a ∈ Sources.vertexLabels vs,
      ownerRow a.edge ≤ srcRow a ∧ srcRow a ≤ ownerRow a.edge + 1)
    (A E B : ℕ) (hA : ∀ r, Nat.card {i // vertexRow i = r} ≤ A)
    (hE : ∀ r, Nat.card {e // ownerRow e = r} ≤ E)
    (hB : ∀ r, ((Sources.vertexLabels vs).filter (fun a => ownerRow a.edge == r)).length ≤ B)

include hxs hys hrow hA hE hB in
/-- The actual planarized vertex rows have a uniform capacity determined by the source data. -/
theorem planeVertexRow_card_le (r : ℕ) :
    Nat.card {v : (planeDiagram vs hw).Vtx Prim.interp //
      planeVertexRow vs hw vertexRow ownerRow v = r} ≤ rowBudget A E B := by
  let row : VertexOrigin vs.length m (swapCount (routing vs (color vs) hw).diagram) → ℕ
    | .vertex i => vertexRow i
    | .cap e => ownerRow e
    | .crossing i => crossingRow vs (color vs) hw (fun p => ownerRow p.edge) i
  have h := planeVertexOrigin_row_fiber_le vs hw row r
  have hx : Nat.card {i // crossingRow vs (color vs) hw (fun p => ownerRow p.edge) i = r} ≤
      4 * B ^ 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      crossingRow_card_le vs (color vs) hw srcRow (fun p => ownerRow p.edge) hxs hys hrow B hB r
  change Nat.card {v : (planeDiagram vs hw).Vtx Prim.interp //
    planeVertexRow vs hw vertexRow ownerRow v = r} ≤
      Nat.card {i // vertexRow i = r} + 16 * Nat.card {e // ownerRow e = r} +
        286 * Nat.card {i // crossingRow vs (color vs) hw (fun p => ownerRow p.edge) i = r} at h
  calc
    _ ≤ _ := h
    _ ≤ A + 16 * E + 286 * (4 * B ^ 2) :=
      Nat.add_le_add (Nat.add_le_add (hA r) (Nat.mul_le_mul_left 16 (hE r)))
        (Nat.mul_le_mul_left 286 hx)
    _ = rowBudget A E B := by unfold rowBudget; ring

variable (hports : ∀ i p, p ∈ (vs.get i).ports →
    vertexRow i ≤ ownerRow p.port.edge + 1 ∧ ownerRow p.port.edge ≤ vertexRow i + 1)

/-- The supplied order of actual output vertices has bandwidth below three consecutive rows. -/
@[expose] def rowBandwidthCertificate {n : ℕ}
    (order : (planeDiagram vs hw).Vtx Prim.interp ≃ Fin n)
    (hs : Monotone (fun i => planeVertexRow vs hw vertexRow ownerRow (order.symm i))) :
    ConstraintGraph.BandwidthCertificate ((planeDiagram vs hw).graph Prim.interp)
      (3 * rowBudget A E B - 1) :=
  ConstraintGraph.BandwidthCertificate.ofRowOrder _ order (planeVertexRow vs hw vertexRow ownerRow)
    (planeVertexRow_card_le vs hw vertexRow srcRow ownerRow hxs hys hrow A E B hA hE hB) hs
    (planeVertexRow_edge_bounds vs hw vertexRow srcRow ownerRow hxs hys hrow hports)

end Layout
end Cslib.Complexity.NCL.Planar.Embedding
