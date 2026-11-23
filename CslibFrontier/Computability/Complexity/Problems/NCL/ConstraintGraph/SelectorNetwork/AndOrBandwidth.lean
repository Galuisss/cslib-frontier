/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.AndOrSize

/-!
# Bandwidth of selector-network compilation

Place each implementation in a block of a fixed budget after its source vertex. Private wires
stay inside their block, and shared wires inherit the source span. Removing unused block slots
gives an exact order of the resulting graph.

## Main results

* `SelectorNetwork.AndOr.bandwidthCertificate`: bounded-size replacements preserve constant
  bandwidth.
-/

public section

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr

open Diagram

variable {U C R : Type*} [DecidableEq U] [DecidableEq C] [DecidableEq R]
variable (N : SelectorNetwork U C R) (A : RowSection N)
variable [Fintype U] [Fintype C] [Fintype R]

/-- A source order and a common local budget give an exact order of the complete standard graph. -/
noncomputable def bandwidthCertificate {bound budget : ℕ}
    (B : ConstraintGraph.BandwidthCertificate N.graph bound)
    (hbudget : ∀ v, 64 + 22 * (cell N A v).top.length ≤ budget) :
    ConstraintGraph.BandwidthCertificate (graph N A) (budget * (bound + 1) - 1) := by
  let number (v : Vert U C R) : (cell N A v).diagram.Vtx Prim.interp → Fin budget :=
    fun w => (vertexEquiv Prim.interp (cell N A v).diagram w).castLE
      (((cell N A v).size_le).1.trans (hbudget v))
  have hnumber (v : Vert U C R) : Function.Injective (number v) :=
    (Fin.castLE_injective _).comp (vertexEquiv Prim.interp (cell N A v).diagram).injective
  let slots (u : TargetVertex N A) : Fin B.size × Fin budget := (B.order u.1, number u.1 u.2)
  have hslots : Function.Injective slots := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ h
    have hv : v = v' := B.order.injective (congrArg Prod.fst h)
    subst v'
    have hw : w = w' := hnumber v (congrArg Prod.snd h)
    subst w'
    rfl
  let index : TargetVertex N A → Fin (B.size * budget) := finProdFinEquiv ∘ slots
  apply ConstraintGraph.BandwidthCertificate.ofInjection (graph N A) index
    (finProdFinEquiv.injective.comp hslots)
  intro u v p hp r hr he
  have hrows := origin_span N A B u v p hp r hr he
  have huv : (B.order u.1).val ≤ (B.order v.1).val + bound := by
    simp only [Nat.dist] at hrows
    omega
  have hvu : (B.order v.1).val ≤ (B.order u.1).val + bound := by
    simp only [Nat.dist] at hrows
    omega
  have hmuv := Nat.mul_le_mul_left budget huv
  have hmvu := Nat.mul_le_mul_left budget hvu
  have hu := (number u.1 u.2).isLt
  have hv := (number v.1 v.2).isLt
  change Nat.dist ((number u.1 u.2).val + budget * (B.order u.1).val)
    ((number v.1 v.2).val + budget * (B.order v.1).val) ≤ _
  simp only [Nat.dist, Nat.mul_add, Nat.mul_one] at *
  omega

end Cslib.Complexity.NCL.SelectorNetwork.AndOr
