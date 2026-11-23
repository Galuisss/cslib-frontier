/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Clause
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# Selector constraints for word reconfiguration

At each position, a positive clause selects a nonempty set of symbols. Negative binary clauses
forbid incompatible selections at consecutive positions. A selector is shared by its row clause
and all incident compatibility clauses. These are the Boolean constraints underlying the
character and relation gadgets in the proof of [VanDerZanden2015, Theorem 6].

## Main definitions

* `HWord.RelationSite`: a position and an ordered symbol pair.
* `HWord.graph`: row and compatibility clauses, using the common constraint-graph semantics.
* `HWord.oneHot`: the unique-selection encoding of a word.

## Main results

* `HWord.legal_graph_iff`: graph legality means nonempty, pairwise compatible selections.
* `HWord.reachable_oneHot_iff`: word reconfiguration is equivalent to selector reconfiguration.

## References

* [T. C. van der Zanden, *Parameterized Complexity of Graph Constraint Logic*]
  [VanDerZanden2015], Theorem 6, pp. 286–289.
-/

public section

namespace Cslib.Complexity.NCL.HWord

/-- A possible forbidden pair at one position and its successor. -/
@[ext] structure RelationSite (q n : ℕ) where
  /-- The position of the first symbol. -/
  position : Fin n
  /-- The selected symbol at this position. -/
  first : Fin q
  /-- The selected symbol at the next position. -/
  second : Fin q
  deriving DecidableEq, Fintype

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj]

/-- Row clauses require a selection; forbidden-pair clauses exclude incompatible neighbours. -/
@[expose] def graph (n : ℕ) :
    ConstraintGraph (Fin n ⊕ RelationSite q n) (Fin n × Fin q)
  | .inl i => Vertex.clause ((List.finRange q).map fun a => ⟨(i, a), true⟩)
  | .inr c =>
    if h : c.position.val + 1 < n then
      if H.Adj c.first c.second then ⟨[], 0⟩ else
        Vertex.clause [⟨(c.position, c.first), false⟩,
          ⟨(⟨c.position.val + 1, h⟩, c.second), false⟩]
    else ⟨[], 0⟩

/-- Selected symbols form nonempty sets with full compatibility between neighbouring sets. -/
structure SelectionLegal (s : Fin n × Fin q → Bool) : Prop where
  /-- At least one symbol is selected at every position. -/
  nonempty : ∀ i, ∃ a, s (i, a) = true
  /-- Every selected pair at consecutive positions is compatible. -/
  compatible : ∀ i j, i.val + 1 = j.val →
    ∀ a b, s (i, a) = true → s (j, b) = true → H.Adj a b

/-- A selector configuration includes the symbol of the word at every position. -/
@[expose] def Encodes (s : Fin n × Fin q → Bool) (w : Fin n → Fin q) : Prop :=
  ∀ i, s (i, w i) = true

/-- Select exactly the word's symbol at each position. -/
@[expose] def oneHot (w : Fin n → Fin q) (e : Fin n × Fin q) : Bool :=
  decide (w e.1 = e.2)

/-- Selector clauses recognize exactly nonempty, mutually compatible symbol sets. -/
theorem legal_graph_iff (s : Fin n × Fin q → Bool) :
    (graph H n).Legal s ↔ SelectionLegal H s := by
  constructor
  · intro hs
    constructor
    · intro i
      simpa [graph, Vertex.sat_clause_iff, Port.In] using hs (.inl i)
    · intro i j hij a b ha hb
      by_contra hab
      have hi : i.val + 1 < n := hij ▸ j.isLt
      have hj : (⟨i.val + 1, hi⟩ : Fin n) = j := Fin.ext hij
      have hc := hs (.inr ⟨i, a, b⟩)
      simp [graph, hi, hab, Vertex.sat_clause_iff, Port.In, hj, ha, hb] at hc
  · intro hs v
    cases v with
    | inl i =>
      obtain ⟨a, ha⟩ := hs.nonempty i
      exact Vertex.sat_clause (List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩) ha
    | inr c =>
      simp only [graph]
      split_ifs with hi hab
      · simp [Vertex.Sat, Vertex.inflow]
      · rw [Vertex.sat_clause_iff]
        by_cases ha : s (c.position, c.first) = true
        · have hb : s (⟨c.position.val + 1, hi⟩, c.second) = false := by
            apply Bool.eq_false_iff.mpr
            intro hb
            exact hab (hs.compatible _ _ rfl _ _ ha hb)
          exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hb⟩
        · exact ⟨_, List.mem_cons_self, Bool.eq_false_iff.mpr ha⟩
      · simp [Vertex.Sat, Vertex.inflow]

private theorem legal_encoded {s : Fin n × Fin q → Bool} {w : Fin n → Fin q}
    (hs : (graph H n).Legal s) (hw : Encodes s w) : Legal H w :=
  fun i j hij => ((legal_graph_iff H s).mp hs).compatible i j hij _ _ (hw i) (hw j)

/-- Unique selections are legal exactly when the encoded word is compatible. -/
theorem legal_oneHot_iff (w : Fin n → Fin q) :
    (graph H n).Legal (oneHot w) ↔ Legal H w := by
  constructor
  · exact fun h => legal_encoded H h (fun i => by simp [oneHot])
  · intro hw
    apply (legal_graph_iff H _).mpr
    constructor
    · exact fun i => ⟨w i, by simp [oneHot]⟩
    · intro i j hij a b ha hb
      have ha' : w i = a := of_decide_eq_true ha
      have hb' : w j = b := of_decide_eq_true hb
      exact ha' ▸ hb' ▸ hw i j hij

private theorem decode_reachable {s t : Fin n × Fin q → Bool}
    (hr : (graph H n).Reachable s t)
    (w : Fin n → Fin q) (hw : Encodes s w) :
    ∃ v, Reachable H w v ∧ Encodes t v := by
  induction hr with
  | refl => exact ⟨w, .refl, hw⟩
  | @tail t u hr hm ih =>
    obtain ⟨v, hv, htv⟩ := ih
    obtain ⟨ht, hu, e, rfl⟩ := hm
    obtain ⟨b, hb⟩ := ((legal_graph_iff H _).mp hu).nonempty e.1
    let v' := Function.update v e.1 b
    have huv : Encodes (reverse t e) v' := by
      intro j
      by_cases hj : j = e.1
      · subst j
        simpa only [v', Function.update_self] using hb
      · have hje : (j, v' j) ≠ e := fun h => hj (congrArg Prod.fst h)
        rw [reverse_of_ne t hje]
        simpa only [v', Function.update_of_ne hj] using htv j
    refine ⟨v', hv.trans (reachable_of_eq_off (legal_encoded H ht htv)
      (legal_encoded H hu huv) e.1 ?_), huv⟩
    intro j hj
    exact (Function.update_of_ne hj b v).symm

private def union (s t : Fin n → Fin q) (e : Fin n × Fin q) : Bool :=
  decide (s e.1 = e.2 ∨ t e.1 = e.2)

private theorem legal_union {s t : Fin n → Fin q} (hs : Legal H s) (ht : Legal H t)
    (i : Fin n) (heq : ∀ j, j ≠ i → s j = t j) :
    (graph H n).Legal (union s t) := by
  apply (legal_graph_iff H _).mpr
  constructor
  · exact fun j => ⟨s j, by simp [union]⟩
  · intro j k hjk a b ha hb
    have ha' : s j = a ∨ t j = a := of_decide_eq_true ha
    have hb' : s k = b ∨ t k = b := of_decide_eq_true hb
    by_cases hj : j = i
    · have hk : k ≠ i := by intro hk; subst j k; omega
      have hbk : s k = b := hb'.elim id (fun h => (heq k hk).trans h)
      rcases ha' with haj | haj
      · exact haj ▸ hbk ▸ hs j k hjk
      · exact haj ▸ ((heq k hk).symm.trans hbk) ▸ ht j k hjk
    · have haj : t j = a := ha'.elim (fun h => (heq j hj).symm.trans h) id
      rcases hb' with hbk | hbk
      · exact ((heq j hj).trans haj) ▸ hbk ▸ hs j k hjk
      · exact haj ▸ hbk ▸ ht j k hjk

private theorem reverse_oneHot {s t : Fin n → Fin q} (i : Fin n)
    (hne : s i ≠ t i) (heq : ∀ j, j ≠ i → s j = t j) :
    reverse (oneHot s) (i, t i) = union s t := by
  funext ⟨j, a⟩
  by_cases hj : j = i
  · subst j
    by_cases ha : a = t i
    · subst a
      simp [reverse, oneHot, union, hne]
    · simp [reverse, oneHot, union, ha, Ne.symm ha]
  · simp [reverse, oneHot, union, hj, heq j hj]

private theorem lift_step {s t : Fin n → Fin q} (hst : Step H s t) :
    (graph H n).Reachable (oneHot s) (oneHot t) := by
  obtain ⟨hs, ht, i, hne, heq⟩ := hst
  have hu := legal_union H hs ht i heq
  have hfirst : (graph H n).Step (oneHot s) (union s t) :=
    ⟨(legal_oneHot_iff H s).mpr hs, hu, (i, t i), (reverse_oneHot i hne heq).symm⟩
  have hur : union t s = union s t := by funext e; simp only [union, or_comm]
  have hlast : (graph H n).Step (oneHot t) (union s t) := by
    refine ⟨(legal_oneHot_iff H t).mpr ht, hu, (i, s i), ?_⟩
    rw [reverse_oneHot i hne.symm (fun j hj => (heq j hj).symm), hur]
  exact (Relation.ReflTransGen.single hfirst).tail hlast.symm

/-- Single-symbol word paths correspond exactly to selector paths between unique selections. -/
theorem reachable_oneHot_iff {s t : Fin n → Fin q} :
    (graph H n).Reachable (oneHot s) (oneHot t) ↔ Reachable H s t := by
  constructor
  · intro hr
    obtain ⟨v, hv, htv⟩ := decode_reachable H hr s
      (fun i => by simp [oneHot])
    have hvt : v = t := funext fun i => (of_decide_eq_true (htv i)).symm
    exact hvt ▸ hv
  · intro hr
    induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact ih.trans (lift_step H hm)

end Cslib.Complexity.NCL.HWord
