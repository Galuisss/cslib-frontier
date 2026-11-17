/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Polygonal
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.CardinalOrder
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs

/-!
# Actual end-segment germs and executed integer neighbours

The outgoing germ of the converted polygonal route is exactly the vector from the original
displayed vertex to the neighbour read by the native cardinal-successor computation.
Both ends of every indexed edge use the same shared route normalization. No chosen rotation
or geometric rank provider occurs in the statement.

This is original representation transport.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Orthogonal OrthogonalDrawing

/-- The proof-side polygonal conversion and the native endpoint-neighbour lookup read
exactly the same actual segment vector, including independently reversed input routes. -/
theorem IsPlanarOrthogonalDrawing.germ_polygonalDrawing
    {G : Graph} {d : OrthogonalDrawing} (hd : IsPlanarOrthogonalDrawing G d) (a : Dart G) :
    hd.polygonalDrawing.germ a = complexPoint (exitNeighbor G d a.index) -
      complexPoint (drawingPosition G d a.vertex) := by
  rcases a with ⟨e, side⟩
  let r := (sourceRoute G d e).reverse
  have hlen : 2 ≤ r.length := by
    simpa only [r, List.length_reverse] using sourceRoute_length_ge_two hd e.isLt
  cases side
  · have he := hd.polygonalDrawing.endpoint_eq e false
    change complexPoint r[0] = complexPoint (drawingPosition G d (Dart.vertex (e, false))) at he
    change complexPoint r[1] - complexPoint r[0] = _
    apply congrArg₂ (· - ·) _ he
    apply congrArg complexPoint
    have hdiv : (2 * e.val) / 2 = e.val := by omega
    have hmod : (2 * e.val) % 2 = 0 := by omega
    simp only [exitNeighbor, Dart.index, Bool.toNat_false, Nat.add_zero, hdiv, hmod, ↓reduceIte]
    exact (List.getD_eq_getElem r (0, 0) (by omega : 1 < r.length)).symm
  · have he := hd.polygonalDrawing.endpoint_eq e true
    change complexPoint r[r.length - 2 + 1] =
      complexPoint (drawingPosition G d (Dart.vertex (e, true))) at he
    change complexPoint r[r.length - 2] - complexPoint r[r.length - 2 + 1] = _
    apply congrArg₂ (· - ·) _ he
    apply congrArg complexPoint
    have hdiv : (2 * e.val + 1) / 2 = e.val := by omega
    have hmod : (2 * e.val + 1) % 2 = 1 := by omega
    simp only [exitNeighbor, Dart.index, Bool.toNat_true, hdiv, hmod,
      Nat.one_ne_zero, ↓reduceIte]
    exact (List.getD_eq_getElem r (0, 0) (by omega : r.length - 2 < r.length)).symm

end Cslib.Complexity.Graph
