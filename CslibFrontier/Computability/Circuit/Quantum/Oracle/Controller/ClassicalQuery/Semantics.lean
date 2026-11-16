/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.ClassicalQuery
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.BlockCopy.Deferred

/-!
# Physical semantics of the classical-query controller

The classical-query controller copies its Hadamard challenge bit into the first wire of the
protected reply record.  After splitting out that fresh target wire, the actual CNOT block is the
existing `coherentRecord` isometry.  The equality below includes an arbitrary finite reference
factor and therefore does not assume a product input or quantum advice.

This is the first physical boundary in the controller correspondence.  Dephasing the complete
hidden-bit-and-ciphertext label, running the ciphertext-only second stage, and identifying the
final comparison measurement with the native success experiment remain separate obligations.

## Main results

* `Cslib.Quantum.ClassicalQueryLayout.Compatible.ofPhaseCodes_compileClassicalQuery`: the
  erased compiled circuit is the exact sequence of its three embedded component circuits and
  physical boundary blocks.
* `Cslib.Quantum.ClassicalQueryLayout.matrix_copyHidden_zeroTarget_withReference`: the actual
  protected-hidden-bit copy is a coherent record while retaining every other wire and reference.
* `Cslib.Quantum.ClassicalQueryLayout.partialTraceLeft_copyRequest_zeroTarget_withReference`:
  discarding the actual copied request gives exactly the sum of request density branches,
  including an arbitrary inaccessible reference.

## References

This register correspondence is original formalization infrastructure for the B2 reduction in
[HQC2026], Theorem 6.3, pp. 61--64.
-/

public section

namespace Cslib.Quantum.ClassicalQueryLayout

open Matrix Circuit GateCode
open scoped Kronecker

/-- The erased compiled controller is exactly the sequence of its three component circuits,
embedded at the physical register placements declared by the layout, and its concrete boundary
blocks.  This factorization is the semantic entry point for the full reply/readout proof. -/
theorem Compatible.ofPhaseCodes_compileClassicalQuery {layout : ClassicalQueryLayout}
    (h : layout.Compatible) :
    Circuit.ofPhaseCodes layout.width
        (compileClassicalQuery layout).instructions.zeroOraclePhaseCodes =
      Circuit.ofCodes layout.width
          (blockCopyCodes 0 layout.serviceBase layout.fullInputWidth) ++
      Circuit.ofCodes layout.width
          (blockCopyCodes 0 layout.secondBase
            (2 * layout.input.securityParameter + 1)) ++
      (Circuit.ofPhaseCodes layout.first.width
        layout.first.instructions.zeroOraclePhaseCodes).mapWires layout.firstEmbedding ++
      Circuit.ofCodes layout.width
          (blockCopyCodes 0 layout.requestBase layout.first.outputWidth) ++
      Circuit.ofCodes layout.width (hadamardCodes layout.hiddenWire 1) ++
      Circuit.ofCodes layout.width
          (blockCopyCodes layout.hiddenWire layout.replyBase 1) ++
      (Circuit.ofPhaseCodes layout.service.width
        layout.service.instructions.zeroOraclePhaseCodes).mapWires layout.serviceEmbedding ++
      Circuit.ofCodes layout.width
          (blockCopyCodes layout.serviceBase (layout.replyBase + 1)
            layout.ciphertextWidth) ++
      Circuit.ofCodes layout.width
          (blockCopyCodes (layout.replyBase + 1)
            (layout.secondBase + (2 * layout.input.securityParameter + 1))
            layout.ciphertextWidth) ++
      (Circuit.ofPhaseCodes layout.second.width
        layout.second.instructions.zeroOraclePhaseCodes).mapWires layout.secondEmbedding ++
      Circuit.ofCodes layout.width (prefixSwapCodes layout.secondBase 1) ++
      Circuit.ofCodes layout.width (compareBits layout.replyBase 0) := by
  have hfirst := Circuit.ofPhaseCodes_map_relabel layout.firstEmbedding layout.firstWire
    (fun _ => rfl)
    (OracleCircuit.wellFormed_zeroOraclePhaseCodes h.first_wellFormed.instructions)
  have hservice := Circuit.ofPhaseCodes_map_relabel layout.serviceEmbedding layout.serviceWire
    (fun _ => rfl)
    (OracleCircuit.wellFormed_zeroOraclePhaseCodes h.service_wellFormed.instructions)
  have hsecond := Circuit.ofPhaseCodes_map_relabel layout.secondEmbedding layout.secondWire
    (fun _ => rfl)
    (OracleCircuit.wellFormed_zeroOraclePhaseCodes h.second_wellFormed.instructions)
  simp only [OracleCircuit.zeroOraclePhaseCodes] at hfirst hservice hsecond
  have ofPhaseCodes_append (left right : List PhaseGateCode) :
      Circuit.ofPhaseCodes layout.width (left ++ right) =
        Circuit.ofPhaseCodes layout.width left ++ Circuit.ofPhaseCodes layout.width right :=
    List.filterMap_append
  simp only [compileClassicalQuery, OracleCircuit.zeroOraclePhaseCodes,
    List.filterMap_append, List.filterMap_map, Function.comp_apply, List.filterMap_eq_map',
    ofPhaseCodes_append, Circuit.ofPhaseCodes_map, hfirst, hservice, hsecond]

/-- The controller's physical hidden-bit copy, restricted to a zero protected target, is exactly
a coherent record.  Reassociation exposes the copied bit as the first factor while retaining all
other controller wires and an arbitrary inaccessible reference. -/
theorem matrix_copyHidden_zeroTarget_withReference (layout : ClassicalQueryLayout)
    {Reference : Type*} [DecidableEq Reference] :
    let htarget : layout.replyBase + 1 ≤ layout.width := by
      simp only [width, secondBase]
      omega
    let hsource : layout.hiddenWire + 1 ≤ layout.width := by
      simp only [width, secondBase, replyBase, serviceBase]
      omega
    let targetEmbedding := blockEmb layout.replyBase htarget
    let Rest := {j : Fin layout.width // ¬ ∃ i, targetEmbedding i = j}
    let sourceLabel : (Rest → Bool) → Fin 1 → Bool :=
      fun rest i =>
        (splitEquiv targetEmbedding).symm (fun _ => false, rest)
          ⟨layout.hiddenWire + i, by omega⟩
    let reassociate : (((Fin 1 → Bool) × (Rest → Bool)) × Reference) ≃
        ((Fin 1 → Bool) × ((Rest → Bool) × Reference)) :=
      Equiv.prodAssoc _ _ _
    let copyMatrix :=
      (Circuit.matrix (Circuit.ofCodes layout.width
        (blockCopyCodes layout.hiddenWire layout.replyBase 1)) : Matrix _ _ ℂ).submatrix
        (fun p => (splitEquiv targetEmbedding).symm p)
        (fun rest => (splitEquiv targetEmbedding).symm (fun _ => false, rest))
    let physical := (copyMatrix ⊗ₖ
      (1 : Matrix Reference Reference ℂ)).submatrix reassociate.symm id
    physical =
      coherentRecord (fun p : (Rest → Bool) × Reference => sourceLabel p.1) := by
  classical
  dsimp only
  let htarget : layout.replyBase + 1 ≤ layout.width := by
    simp only [width, secondBase]
    omega
  let hsource : layout.hiddenWire + 1 ≤ layout.width := by
    simp only [width, secondBase, replyBase, serviceBase]
    omega
  let targetEmbedding := blockEmb layout.replyBase htarget
  let Rest := {j : Fin layout.width // ¬ ∃ i, targetEmbedding i = j}
  let sourceLabel : (Rest → Bool) → Fin 1 → Bool :=
    fun rest i =>
      (splitEquiv targetEmbedding).symm (fun _ => false, rest)
        ⟨layout.hiddenWire + i, by omega⟩
  let reassociate : (((Fin 1 → Bool) × (Rest → Bool)) × Reference) ≃
      ((Fin 1 → Bool) × ((Rest → Bool) × Reference)) :=
    Equiv.prodAssoc _ _ _
  have hcopy := Circuit.matrix_blockCopyCodes_zeroTarget
    (source := layout.hiddenWire) (target := layout.replyBase) (count := 1)
    (width := layout.width) (by
      left
      simp only [replyBase, serviceBase]
      omega) hsource htarget
  rw [hcopy]
  exact coherentRecord_kronecker_one_reassociate
    (Reference := Reference) (A := Fin 1 → Bool) sourceLabel

/-- Copying the first-stage output into the controller's fresh request register and discarding
that register gives exactly computational-basis readout of the request.  The original first-stage
register and an arbitrary inaccessible reference remain in every subnormalized branch.  This is
the physical density-matrix boundary used before the request-controlled service continuation. -/
theorem partialTraceLeft_copyRequest_zeroTarget_withReference
    {layout : ClassicalQueryLayout} (h : layout.Compatible)
    {Reference : Type*} [Fintype Reference] [DecidableEq Reference]
    (ρ :
      let htarget : layout.requestBase + layout.first.outputWidth ≤ layout.width := by
        simp only [requestBase, width, secondBase, replyBase, serviceBase, hiddenWire]
        omega
      let targetEmbedding := blockEmb layout.requestBase htarget
      let Rest := {j : Fin layout.width // ¬ ∃ i, targetEmbedding i = j}
      Matrix ((Rest → Bool) × Reference) ((Rest → Bool) × Reference) ℂ) :
    let htarget : layout.requestBase + layout.first.outputWidth ≤ layout.width := by
      simp only [requestBase, width, secondBase, replyBase, serviceBase, hiddenWire]
      omega
    let targetEmbedding := blockEmb layout.requestBase htarget
    let Rest := {j : Fin layout.width // ¬ ∃ i, targetEmbedding i = j}
    let sourceLabel : (Rest → Bool) → Fin layout.first.outputWidth → Bool :=
      fun rest i =>
        (splitEquiv targetEmbedding).symm (fun _ => false, rest) ⟨i, by omega⟩
    let requestLabel : ((Rest → Bool) × Reference) →
        (Fin layout.first.outputWidth → Bool) :=
      fun p => sourceLabel p.1
    let reassociate :
        (((Fin layout.first.outputWidth → Bool) × (Rest → Bool)) × Reference) ≃
          ((Fin layout.first.outputWidth → Bool) × ((Rest → Bool) × Reference)) :=
      Equiv.prodAssoc _ _ _
    let copyMatrix :=
      (Circuit.matrix (Circuit.ofCodes layout.width
        (blockCopyCodes 0 layout.requestBase layout.first.outputWidth)) : Matrix _ _ ℂ).submatrix
        (fun p => (splitEquiv targetEmbedding).symm p)
        (fun rest => (splitEquiv targetEmbedding).symm (fun _ => false, rest))
    let physical := (copyMatrix ⊗ₖ
      (1 : Matrix Reference Reference ℂ)).submatrix reassociate.symm id
    partialTraceLeft (densityConj physical ρ) =
      ∑ request, classicalDensityBranch requestLabel request ρ := by
  classical
  dsimp only
  have hinput := h.first_wellFormed.input_le
  rw [h.first_quantumInputWidth, Nat.add_zero] at hinput
  have houtput := h.first_output_le
  have hsourceFirst : layout.first.outputWidth ≤ layout.first.width :=
    houtput.trans hinput
  let hsource : layout.first.outputWidth ≤ layout.width := by
    simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
      ClassicalQueryLayout.replyBase, ClassicalQueryLayout.serviceBase,
      ClassicalQueryLayout.hiddenWire, ClassicalQueryLayout.requestBase]
    omega
  let htarget : layout.requestBase + layout.first.outputWidth ≤ layout.width := by
    simp only [requestBase, width, secondBase, replyBase, serviceBase, hiddenWire]
    omega
  let targetEmbedding := blockEmb layout.requestBase htarget
  let Rest := {j : Fin layout.width // ¬ ∃ i, targetEmbedding i = j}
  let sourceLabel : (Rest → Bool) → Fin layout.first.outputWidth → Bool :=
    fun rest i =>
      (splitEquiv targetEmbedding).symm (fun _ => false, rest) ⟨i, by omega⟩
  let requestLabel : ((Rest → Bool) × Reference) →
      (Fin layout.first.outputWidth → Bool) :=
    fun p => sourceLabel p.1
  let reassociate :
      (((Fin layout.first.outputWidth → Bool) × (Rest → Bool)) × Reference) ≃
        ((Fin layout.first.outputWidth → Bool) × ((Rest → Bool) × Reference)) :=
    Equiv.prodAssoc _ _ _
  let copyMatrix :=
    (Circuit.matrix (Circuit.ofCodes layout.width
      (blockCopyCodes 0 layout.requestBase layout.first.outputWidth)) : Matrix _ _ ℂ).submatrix
      (fun p => (splitEquiv targetEmbedding).symm p)
      (fun rest => (splitEquiv targetEmbedding).symm (fun _ => false, rest))
  let physical := (copyMatrix ⊗ₖ
    (1 : Matrix Reference Reference ℂ)).submatrix reassociate.symm id
  have hdisjoint : layout.first.outputWidth ≤ layout.requestBase := by
    simp only [requestBase]
    omega
  have hcopy := Circuit.matrix_blockCopyCodes_zeroTarget
    (source := 0) (target := layout.requestBase) (count := layout.first.outputWidth)
    (width := layout.width) (Or.inl (by simpa only [Nat.zero_add] using hdisjoint))
    (by simpa only [Nat.zero_add] using hsource) htarget
  have hphysical : physical = coherentRecord requestLabel := by
    dsimp only [physical, copyMatrix]
    rw [hcopy]
    rw [coherentRecord_kronecker_one_reassociate
      (Reference := Reference) (A := Fin layout.first.outputWidth → Bool)]
    apply congrArg coherentRecord
    funext p i
    simp only [requestLabel, sourceLabel, targetEmbedding, Function.comp_apply, Nat.zero_add]
  change partialTraceLeft (densityConj physical ρ) = _
  rw [hphysical, partialTraceLeft_densityConj_coherentRecord]

end Cslib.Quantum.ClassicalQueryLayout
