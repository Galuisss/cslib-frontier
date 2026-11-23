/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Vertices
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Size of the complete selector-network implementation

Each original vertex contributes a linear budget in its number of input ports. Private wires
belong to one component, while selector and relation edges remain shared.

## Main results

* `SelectorNetwork.AndOr.card_targetVertex_le`: total standard vertex bound.
* `SelectorNetwork.AndOr.card_private_le`: total private-wire bound.
-/

public section

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr

open Diagram
open scoped BigOperators

variable {U C R : Type*} [DecidableEq U] [DecidableEq C]
variable (N : SelectorNetwork U C R) (A : RowSection N)
variable [Fintype U] [Fintype C] [Fintype R]

/-- Total standard vertices are bounded by the sum of the local linear budgets. -/
theorem card_targetVertex_le : Fintype.card (TargetVertex N A) ≤
    ∑ v, (64 + 22 * (cell N A v).top.length) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_le_sum
  intro v _
  have h := Fintype.card_congr (vertexEquiv Prim.interp (cell N A v).diagram)
  simp only [Fintype.card_fin] at h
  exact h.le.trans ((cell N A v).size_le).1

/-- Private wires are bounded by the same sum of local budgets. -/
theorem card_private_le : Fintype.card (Private N A) ≤
    ∑ v, (64 + 22 * (cell N A v).top.length) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_le_sum
  intro v _
  have h := Diagram.Replacement.card_inner (cell N A v).openSim
  have hn := ((cell N A v).size_le).2
  omega

/-- The complete graph retains its shared edges and adds linearly many private wires. -/
theorem card_targetEdge_le : Fintype.card (Edge C R ⊕ Private N A) ≤
    Fintype.card (Edge C R) + ∑ v, (64 + 22 * (cell N A v).top.length) := by
  rw [Fintype.card_sum]
  exact Nat.add_le_add_left (card_private_le N A) _

end Cslib.Complexity.NCL.SelectorNetwork.AndOr
