/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.ConstraintGraph
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Bandwidth
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Fixed bandwidth of selector constraints

Order each row clause together with the relation clauses whose first position is that row.
Each block contains `1 + q * q` vertices and every selector occurs only in its own block and
the preceding block. Thus the span bound depends only on the fixed alphabet size `q`.

## Main results

* `HWord.bandwidthCertificate`: an explicit order with span at most `2 * (1 + q * q) - 1`.

## References

* The row-block argument is the intermediate constraint version of the locality argument in
  [VanDerZanden2015, Theorem 6, p. 289].
-/

public section

namespace Cslib.Complexity.NCL.HWord

variable {q n : ℕ}

private def row : Fin n ⊕ RelationSite q n → Fin n
  | .inl i => i
  | .inr c => c.position

private def rowTag : (Fin n ⊕ RelationSite q n) ≃
    Fin n × (Fin 1 ⊕ (Fin q × Fin q)) where
  toFun
    | .inl i => (i, .inl 0)
    | .inr c => (c.position, .inr (c.first, c.second))
  invFun
    | (i, .inl _) => .inl i
    | (i, .inr (a, b)) => .inr ⟨i, a, b⟩
  left_inv v := by cases v <;> rfl
  right_inv v := by
    rcases v with ⟨i, j | ⟨a, b⟩⟩
    · cases Fin.eq_zero j
      rfl
    · rfl

private def blocks : (Fin n ⊕ RelationSite q n) ≃ Fin n × Fin (1 + q * q) :=
  rowTag.trans (Equiv.prodCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv))

variable (H : Digraph (Fin q)) [DecidableRel H.Adj]

private theorem port_rows (v : Fin n ⊕ RelationSite q n)
    (p : WeightedPort (Fin n × Fin q)) (hp : p ∈ (graph H n v).ports) :
    (row v).val ≤ p.port.edge.1.val ∧ p.port.edge.1.val ≤ (row v).val + 1 := by
  cases v with
  | inl i =>
    simp only [graph, Vertex.clause, List.map_map, Function.comp_def] at hp
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
    simp [row]
  | inr c =>
    simp only [graph] at hp
    split_ifs at hp with hi hab
    · simp at hp
    · simp only [Vertex.clause, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [row]
    · simp at hp

/-- The selector graph has a word-length-independent bandwidth bound. -/
def bandwidthCertificate :
    ConstraintGraph.BandwidthCertificate (graph H n) (2 * (1 + q * q) - 1) :=
  ConstraintGraph.BandwidthCertificate.ofBlocks (graph H n) blocks (by
    intro u v p hp r hr he
    have hup := port_rows H u p hp
    have hvr := port_rows H v r hr
    have he' := congrArg (fun e => e.1.val) he
    have hrow (v : Fin n ⊕ RelationSite q n) : (blocks v).1 = row v := by cases v <;> rfl
    simp only [hrow, Nat.dist]
    omega)

end Cslib.Complexity.NCL.HWord
