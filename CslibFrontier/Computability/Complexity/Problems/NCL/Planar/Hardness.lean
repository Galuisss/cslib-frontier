/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Reduction
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PSPACE

/-!
# Plane AND/OR NCL is PSPACE-complete

The planar source emitter runs in polynomial time and preserves all three reachability questions.
Combine it with upstream alternating prenex-CNF hardness and the plane-word space upper bounds
[HearnDemaine2005, Theorem 9].

## Main results

* `Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlanarAndOrNCL` and its edge variants:
  the three source reductions.
* `Cslib.Complexity.NCL.PlanarAndOrNCL_pspaceComplete`,
  `Cslib.Complexity.NCL.PlanarAndOrNCLEdge_pspaceComplete`,
  `Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge_pspaceComplete`: the completeness theorems.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 9]
-/

public section

namespace Cslib.Complexity.NCL

/-- Alternating prenex CNF reduces to fixed-target plane AND/OR NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_PlanarAndOrNCL :
    PolyTimeReducible encPrenexCNF encPlanarAndOrNCL TQBFCNF PlanarAndOrNCL :=
  ⟨PlanarAndOrNCL.reduce, PlanarAndOrNCL.computableInPolyTime_reduce,
    fun x => (PlanarAndOrNCL.reduce_mem_iff x).symm⟩

/-- Fixed-target plane AND/OR NCL is PSPACE-hard. -/
theorem PlanarAndOrNCL_pspaceHard : PSPACEHard encPlanarAndOrNCL PlanarAndOrNCL :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_PlanarAndOrNCL

/-- Fixed-target plane AND/OR NCL is PSPACE-complete. -/
theorem PlanarAndOrNCL_pspaceComplete : PSPACEComplete encPlanarAndOrNCL PlanarAndOrNCL :=
  ⟨PlanarAndOrNCL_mem_PSPACE, PlanarAndOrNCL_pspaceHard⟩

/-- Alternating prenex CNF reduces to configuration-to-edge plane AND/OR NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdge :
    PolyTimeReducible encPrenexCNF encPlanarAndOrNCLEdge TQBFCNF PlanarAndOrNCLEdge :=
  ⟨PlanarAndOrNCLEdge.reduce, PlanarAndOrNCLEdge.computableInPolyTime_reduce,
    fun x => (PlanarAndOrNCLEdge.reduce_mem_iff x).symm⟩

/-- Configuration-to-edge plane AND/OR NCL is PSPACE-hard. -/
theorem PlanarAndOrNCLEdge_pspaceHard : PSPACEHard encPlanarAndOrNCLEdge PlanarAndOrNCLEdge :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdge

/-- Configuration-to-edge plane AND/OR NCL is PSPACE-complete. -/
theorem PlanarAndOrNCLEdge_pspaceComplete :
    PSPACEComplete encPlanarAndOrNCLEdge PlanarAndOrNCLEdge :=
  ⟨PlanarAndOrNCLEdge_mem_PSPACE, PlanarAndOrNCLEdge_pspaceHard⟩

/-- Alternating prenex CNF reduces to directional plane AND/OR NCL in polynomial time. -/
theorem polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdgeToEdge :
    PolyTimeReducible encPrenexCNF encPlanarAndOrNCLEdgeToEdge TQBFCNF PlanarAndOrNCLEdgeToEdge :=
  ⟨PlanarAndOrNCLEdgeToEdge.reduce, PlanarAndOrNCLEdgeToEdge.computableInPolyTime_reduce,
    fun x => (PlanarAndOrNCLEdgeToEdge.reduce_mem_iff x).symm⟩

/-- Directional edge-to-edge plane AND/OR NCL is PSPACE-hard. -/
theorem PlanarAndOrNCLEdgeToEdge_pspaceHard :
    PSPACEHard encPlanarAndOrNCLEdgeToEdge PlanarAndOrNCLEdgeToEdge :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdgeToEdge

/-- Directional edge-to-edge plane AND/OR NCL is PSPACE-complete. -/
theorem PlanarAndOrNCLEdgeToEdge_pspaceComplete :
    PSPACEComplete encPlanarAndOrNCLEdgeToEdge PlanarAndOrNCLEdgeToEdge :=
  ⟨PlanarAndOrNCLEdgeToEdge_mem_PSPACE, PlanarAndOrNCLEdgeToEdge_pspaceHard⟩

end Cslib.Complexity.NCL
