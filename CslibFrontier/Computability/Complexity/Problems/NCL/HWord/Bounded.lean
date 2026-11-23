/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Rows
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.RowBandwidth
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.RowOrder
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CompileBandwidth
import Mathlib.Data.List.GetD

/-!
# Constant bandwidth of the actual H-word planarization

The row array reads each actual primitive vertex in compiled list order. Stable row sorting
therefore supplies an explicit vertex order for the existing planar word. All capacity bounds
depend only on the fixed alphabet, independently of the word length.

## Main definitions

* `HWord.Planarized.layoutBound`: a fixed bandwidth bound depending only on the alphabet.
* `HWord.Planarized.layoutCertificate`: bandwidth of the actual diagram.
-/

public section

namespace Cslib.Complexity.NCL.HWord.Planarized
open Diagram

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Actual primitive vertex rows, read in the emitted diagram's vertex-list order. -/
private def rowArray : List ℕ :=
  List.ofFn fun i : Fin ((diagram (n := n) H hq).vertexList Prim.interp).length =>
    Planar.Embedding.planeVertexRow (vertices H hq) (vertices_wellFormed H hq)
      (vertexRow H hq) (ownerRow H hq) ((vertexEquiv Prim.interp (diagram (n := n) H hq)).symm i)

/-- A uniform bandwidth bound for this fixed alphabet's actual planar implementations. -/
@[expose] def layoutBound (q : ℕ) : ℕ :=
  let K := 1 + (q + q * q)
  3 * Planar.Embedding.rowBudget (K * (64 + 66 * q)) (K * (66 + 69 * q))
    (2 * (K * (66 + 69 * q))) - 1

/-- The actual emitted vertices sorted by their row array. -/
private def layoutOrder : (diagram (n := n) H hq).Vtx Prim.interp ≃
    Fin (rowArray (n := n) H hq).length :=
  ((vertexEquiv Prim.interp (diagram (n := n) H hq)).trans (finCongr List.length_ofFn.symm)).trans
    (ConstraintGraph.RowOrder.equiv (rowArray (n := n) H hq))

private theorem getD_rowArray (v : (diagram (n := n) H hq).Vtx Prim.interp) :
    (rowArray (n := n) H hq).getD ((vertexEquiv Prim.interp (diagram (n := n) H hq)) v).val 0 =
      Planar.Embedding.planeVertexRow (vertices H hq) (vertices_wellFormed H hq)
        (vertexRow H hq) (ownerRow H hq) v := by
  unfold rowArray
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using
    ((vertexEquiv Prim.interp (diagram (n := n) H hq)) v).isLt)]
  simp only [List.getElem_ofFn]
  change Planar.Embedding.planeVertexRow _ _ _ _
    ((vertexEquiv Prim.interp (diagram (n := n) H hq)).symm
      ((vertexEquiv Prim.interp (diagram (n := n) H hq)) v)) = _
  rw [Equiv.symm_apply_apply]

private theorem monotone_layoutOrder : Monotone (fun i =>
    Planar.Embedding.planeVertexRow (vertices (n := n) H hq) (vertices_wellFormed H hq)
      (vertexRow H hq) (ownerRow H hq) ((layoutOrder (n := n) H hq).symm i)) := by
  have hrow (i : Fin (rowArray (n := n) H hq).length) :
      Planar.Embedding.planeVertexRow (vertices H hq) (vertices_wellFormed H hq)
        (vertexRow H hq) (ownerRow H hq) ((layoutOrder (n := n) H hq).symm i) =
      (rowArray (n := n) H hq).getD
        ((ConstraintGraph.RowOrder.equiv (rowArray (n := n) H hq)).symm i).val 0 := by
    calc
      _ = (rowArray (n := n) H hq).getD
          ((vertexEquiv Prim.interp (diagram (n := n) H hq))
            ((layoutOrder (n := n) H hq).symm i)).val 0 :=
        (getD_rowArray (n := n) H hq _).symm
      _ = _ := by
        apply congrArg (fun k => (rowArray (n := n) H hq).getD k 0)
        change ((vertexEquiv Prim.interp (diagram (n := n) H hq))
          ((vertexEquiv Prim.interp (diagram (n := n) H hq)).symm
            (Fin.cast (show (rowArray (n := n) H hq).length =
              ((diagram (n := n) H hq).vertexList Prim.interp).length from List.length_ofFn)
              ((ConstraintGraph.RowOrder.equiv (rowArray (n := n) H hq)).symm i)))).val = _
        rw [Equiv.apply_symm_apply]
        rfl
  intro i j hij
  exact (hrow i).trans_le
    ((ConstraintGraph.RowOrder.monotone_row_symm (rowArray (n := n) H hq) hij).trans_eq
      (hrow j).symm)

/-- The actual emitted graph has the fixed bandwidth under its computed row order. -/
def layoutCertificate :
    ConstraintGraph.BandwidthCertificate ((diagram (n := n) H hq).graph Prim.interp)
      (layoutBound q) :=
  Planar.Embedding.rowBandwidthCertificate (vertices H hq) (vertices_wellFormed H hq)
    (vertexRow H hq) (portRow H hq) (ownerRow H hq)
    (vertexLabels_pairwise H hq) (pairLabels_pairwise H hq)
    (fun p _ => portRow_bounds H hq p)
    _ _ _
    (fun r => by simpa only [Nat.card_eq_fintype_card] using vertexRow_card_le H hq r)
    (fun r => by simpa only [Nat.card_eq_fintype_card] using ownerRow_card_le H hq r)
    (incidenceRow_length_le H hq)
    (vertexRow_port_bounds H hq) (layoutOrder (n := n) H hq)
    (by exact monotone_layoutOrder (n := n) H hq)

end Cslib.Complexity.NCL.HWord.Planarized
