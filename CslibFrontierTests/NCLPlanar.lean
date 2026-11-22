/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Hardness
import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.PlanarDrawing

/-! Axiom guards for the plane-word decision problems and their complexity bounds. -/

open Cslib.Complexity.NCL

/-- info: 'Cslib.Complexity.NCL.Word.computableInPolyTime_checkPlane' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Word.computableInPolyTime_checkPlane

/-- info: 'Cslib.Complexity.NCL.Word.computableInPolyTime_wellTyped' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Word.computableInPolyTime_wellTyped

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCL_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCL_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdge_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdge_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdgeToEdge_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlanarAndOrNCL' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTimeReducible_TQBFCNF_PlanarAndOrNCL

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCL_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCL_pspaceHard

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCL_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCL_pspaceComplete

/-- info: 'Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdge

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdge_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdge_pspaceHard

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdge_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdge_pspaceComplete

/-- info: 'Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdgeToEdge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdgeToEdge

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdgeToEdge_pspaceHard

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdgeToEdge_pspaceComplete

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCL.reduce_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCL.reduce_spec

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCL.pspaceHard_of_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCL.pspaceHard_of_inv

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdge.reduce_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdge.reduce_spec

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdge.pspaceHard_of_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdge.pspaceHard_of_inv

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge.reduce_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdgeToEdge.reduce_spec

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge.pspaceHard_of_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdgeToEdge.pspaceHard_of_inv


/-- info: 'Cslib.Complexity.NCL.Word.planarOrthogonalDrawing_compile' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Word.planarOrthogonalDrawing_compile

-- Semantic correctness and the drawing refer to the same serialized reduction output.
example (x : Cslib.Complexity.PrenexCNF) :
    (PlanarAndOrNCL.reduce x ∈ PlanarAndOrNCL ↔ x ∈ Cslib.Complexity.TQBFCNF) ∧
    ∃ D : GridDrawing.Closed (Word.compile (PlanarAndOrNCL.reduce x).word).graph,
      Cslib.Complexity.Graph.IsPlanarOrthogonalDrawing D.incidenceGraph D.orthogonalDrawing := by
  have h := (PlanarAndOrNCL.reduce_spec x).1
  exact ⟨PlanarAndOrNCL.reduce_mem_iff x, Word.planarOrthogonalDrawing_compile h.1 h.2.1⟩
