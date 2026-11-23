/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.PortGraph
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.AndOrBandwidth
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Standard AND/OR networks for word reconfiguration

Each position uses the zero symbol as its final row port. The complete network implements
canonical word configurations exactly and has a constant implementation budget per source
vertex when the alphabet is fixed.

## Main definitions

* `HWord.AndOr.graph`: the standard network of a fixed compatibility graph.
* `HWord.AndOr.orientation`: the physical encoding of a word.

## Main results

* `HWord.AndOr.reachable_orientation_iff`: exact word reconfiguration.
* `HWord.AndOr.card_vertices_le`: linear vertex bound at fixed alphabet size.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner
  Cslib.Complexity.NCL.Diagram.instDecidableEqInner

namespace Cslib.Complexity.NCL.HWord.AndOr

open SelectorNetwork
open scoped BigOperators

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Symbol zero is the final port of every row OR tree. -/
@[expose] def rowSection : RowSection (PortGraph.network H n) where
  character i := (i, ⟨0, hq⟩)
  row_character i := PortGraph.network_row H (i, ⟨0, hq⟩)

/-- The standard vertices of the word network. -/
abbrev TargetVertex := SelectorNetwork.AndOr.TargetVertex (PortGraph.network H n) (rowSection H hq)

/-- Shared selector/relation edges and fresh private implementation wires. -/
abbrev TargetEdge := Edge (Fin n × Fin q) (RelationSite q n) ⊕
  SelectorNetwork.AndOr.Private (PortGraph.network H n) (rowSection H hq)

/-- The actual finite standard AND/OR network implementing the word constraints. -/
@[expose] def graph : ConstraintGraph (TargetVertex (n := n) H hq) (TargetEdge (n := n) H hq) :=
  SelectorNetwork.AndOr.graph (PortGraph.network H n) (rowSection H hq)

/-- Canonical physical configurations of a word. -/
@[expose] def orientation (w : Fin n → Fin q) : TargetEdge (n := n) H hq → Bool :=
  (SelectorNetwork.AndOr.simulation (PortGraph.network H n) (rowSection H hq)).enc
    ((PortGraph.network H n).encode (oneHot w))

/-- The encoded physical state is legal exactly when the word is compatible. -/
theorem legal_orientation_iff (w : Fin n → Fin q) :
    (graph H hq).Legal (orientation H hq w) ↔ Legal H w :=
  (SelectorNetwork.AndOr.simulation (PortGraph.network H n) (rowSection H hq)).legal_enc_iff.trans
    (PortGraph.legal_oneHot_iff H w)

/-- Canonical physical states preserve and reflect all word-reconfiguration paths. -/
theorem reachable_orientation_iff (s t : Fin n → Fin q) :
    (graph H hq).Reachable (orientation H hq s) (orientation H hq t) ↔ Reachable H s t :=
  ((SelectorNetwork.AndOr.simulation (PortGraph.network H n)
    (rowSection H hq)).reachable_enc_iff).trans (PortGraph.reachable_oneHot_iff H s t)

/-- Every word-network vertex is standard AND or OR. -/
theorem isAndOr : (graph (n := n) H hq).IsAndOr :=
  SelectorNetwork.AndOr.isAndOr _ _

/-- Word-network implementations have no self-loops. -/
theorem loopFree : (graph (n := n) H hq).LoopFree :=
  SelectorNetwork.AndOr.loopFree _ _

/-- Every implementation edge has exactly two opposite ports with the same weight. -/
theorem wellFormed : (graph (n := n) H hq).WellFormed :=
  SelectorNetwork.AndOr.wellFormed _ _

private theorem rowInputs_length_le (i : Fin n) :
    (SelectorNetwork.AndOr.rowInputs (PortGraph.network H n) (rowSection H hq) i).length ≤ q := by
  let xs := SelectorNetwork.AndOr.rowInputs (PortGraph.network H n) (rowSection H hq) i
  have hn : xs.Nodup := (PortGraph.network H n).characters_nodup.filter _
  have hinj : Set.InjOn Prod.snd (↑xs.toFinset : Set (Fin n × Fin q)) := by
    intro c hc d hd hcd
    have hc' := (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hc)).2).1
    have hd' := (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hd)).2).1
    rw [PortGraph.network_row] at hc' hd'
    exact Prod.ext (hc'.trans hd'.symm) hcd
  change xs.length ≤ q
  rw [← List.toFinset_card_of_nodup hn, ← Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_univ _).trans_eq (by simp)

/-- Every local implementation has at most `3q` inputs. -/
theorem input_arity_le (v : Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    (SelectorNetwork.AndOr.cell (PortGraph.network H n)
      (rowSection H hq) v).top.length ≤ 3 * q := by
  rcases v with i | (c | r)
  · change (Gadgets.OrTree.bundle _).length ≤ _
    rw [Gadgets.OrTree.length_bundle]
    exact (rowInputs_length_le H hq i).trans (by omega)
  · change (Gadgets.OrTree.bundle _).length ≤ _
    rw [Gadgets.OrTree.length_bundle]
    have hc := PortGraph.selectorWeight_le H c
    change ((PortGraph.network H n).incident c).length + 1 ≤ 3 * q + 1 at hc
    omega
  · exact Nat.zero_le _

/-- Shared slots zero and one plus every private creation slot fit in one fixed local interval. -/
theorem slot_budget_le (v : Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
    (SelectorNetwork.AndOr.cell (PortGraph.network H n) (rowSection H hq) v).top.length +
      (SelectorNetwork.AndOr.cell (PortGraph.network H n) (rowSection H hq) v).diagram.innerCount +
        2 ≤ 66 + 69 * q := by
  have h := ((SelectorNetwork.AndOr.cell (PortGraph.network H n) (rowSection H hq) v).size_le).2
  have ha := input_arity_le H hq v
  omega

private theorem budget_le :
    (∑ v, (64 + 22 * (SelectorNetwork.AndOr.cell (PortGraph.network H n)
      (rowSection H hq) v).top.length)) ≤ n * ((1 + (q + q * q)) * (64 + 66 * q)) := by
  calc
    _ ≤ ∑ _v : Vert (Fin n) (Fin n × Fin q) (RelationSite q n), (64 + 66 * q) := by
      apply Finset.sum_le_sum
      intro v _
      have h := input_arity_le H hq v
      omega
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change Fintype.card (Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) * _ = _
      rw [PortGraph.card_vertices, Nat.mul_assoc]

/-- The standard vertex count is linear in word length for each fixed alphabet. -/
theorem card_vertices_le : Fintype.card (TargetVertex (n := n) H hq) ≤
    n * ((1 + (q + q * q)) * (64 + 66 * q)) :=
  (SelectorNetwork.AndOr.card_targetVertex_le _ _).trans (budget_le H hq)

/-- The number of private implementation wires is linear in word length. -/
theorem card_private_le :
    Fintype.card (SelectorNetwork.AndOr.Private (PortGraph.network H n) (rowSection H hq)) ≤
      n * ((1 + (q + q * q)) * (64 + 66 * q)) :=
  (SelectorNetwork.AndOr.card_private_le _ _).trans (budget_le H hq)

/-- The complete edge count, including all shared and private wires, is linear in word length. -/
theorem card_edges_le : Fintype.card (TargetEdge (n := n) H hq) ≤
    n * (q + 2 * (q * q) + (1 + (q + q * q)) * (64 + 66 * q)) := by
  have hr : Fintype.card (RelationSite q n) = n * (q * q) := by
    have h := PortGraph.card_vertices (q := q) (n := n)
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Nat.mul_add, Nat.mul_one] at h
    omega
  rw [Fintype.card_sum]
  change Fintype.card (Edge (Fin n × Fin q) (RelationSite q n)) +
    Fintype.card (SelectorNetwork.AndOr.Private (PortGraph.network H n) (rowSection H hq)) ≤ _
  calc
    _ ≤ Fintype.card (Edge (Fin n × Fin q) (RelationSite q n)) +
        n * ((1 + (q + q * q)) * (64 + 66 * q)) := Nat.add_le_add_left (card_private_le H hq) _
    _ = _ := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hr]
      ring

/-- A fixed alphabet gives a bandwidth bound independent of word length. -/
noncomputable def bandwidthCertificate : ConstraintGraph.BandwidthCertificate
    (graph (n := n) H hq) ((64 + 66 * q) * (2 * (1 + (q + q * q))) - 1) := by
  have hbudget (v : Vert (Fin n) (Fin n × Fin q) (RelationSite q n)) :
      64 + 22 * (SelectorNetwork.AndOr.cell (PortGraph.network H n)
        (rowSection H hq) v).top.length ≤ 64 + 66 * q := by
    have h := input_arity_le H hq v
    omega
  have h := SelectorNetwork.AndOr.bandwidthCertificate (PortGraph.network H n)
    (rowSection H hq) (PortGraph.bandwidthCertificate H) hbudget
  have heq : 2 * (1 + (q + q * q)) - 1 + 1 = 2 * (1 + (q + q * q)) := by omega
  simpa only [heq, graph] using h

end Cslib.Complexity.NCL.HWord.AndOr
