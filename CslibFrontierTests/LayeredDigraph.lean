/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Combinatorics.Digraph.Layered.MinIsolation

/-! A diamond with two distinct paths of different internal weights. -/

namespace CslibFrontierTests.LayeredDigraph

open Cslib

private def diamondLayer (v : Fin 4) : ℕ :=
  if v = 0 then 0 else if v = 3 then 2 else 1

private def diamond : LayeredDigraph (Fin 4) where
  Adj a b := diamondLayer b = diamondLayer a + 1
  layer := diamondLayer
  layer_adj h := h

private theorem adj_of_layer {a b : Fin 4} (h : diamondLayer b = diamondLayer a + 1) :
    diamond.Adj a b := h

private def viaOne : diamond.Path 0 3 :=
  (LayeredDigraph.Path.ofAdj (G := diamond) (b := 1) (adj_of_layer (by decide))).comp
    (LayeredDigraph.Path.ofAdj (G := diamond) (adj_of_layer (by decide)))

private def viaTwo : diamond.Path 0 3 :=
  (LayeredDigraph.Path.ofAdj (G := diamond) (b := 2) (adj_of_layer (by decide))).comp
    (LayeredDigraph.Path.ofAdj (G := diamond) (adj_of_layer (by decide)))

example : viaOne ∈ diamond.pathsThrough 0 3 1 ∧ viaOne ∉ diamond.pathsThrough 0 3 2 := by
  change (1 : Fin 4) ∈ [1] ∧ (2 : Fin 4) ∉ [1]
  decide

example : viaOne.internalWeight Fin.val < viaTwo.internalWeight Fin.val := by
  change 1 < (2 : ℕ)
  decide

example : ∃! v, v ∈ viaTwo.vertices ∧ diamond.layer v = 1 :=
  viaTwo.existsUnique_vertex (by decide) (by decide)

example : IsMinOn (LayeredDigraph.Path.internalWeight Fin.val)
    (diamond.pathsThrough 0 3 1) viaOne := by
  unfold viaOne
  rw [LayeredDigraph.isMinOn_pathsThrough_comp_iff _ _ _
    (by decide : diamond.layer 0 < diamond.layer 1)
    (by decide : diamond.layer 1 < diamond.layer 3)]
  constructor <;> rw [isMinOn_univ_iff] <;> intro q
  · rw [LayeredDigraph.Path.eq_of_layer_le_succ
      (by decide : diamond.layer 1 ≤ diamond.layer 0 + 1) q _]
  · rw [LayeredDigraph.Path.eq_of_layer_le_succ
      (by decide : diamond.layer 3 ≤ diamond.layer 1 + 1) q _]

example : ¬diamond.Adj 0 3 := by
  change ¬diamondLayer 3 = diamondLayer 0 + 1
  decide

end CslibFrontierTests.LayeredDigraph
