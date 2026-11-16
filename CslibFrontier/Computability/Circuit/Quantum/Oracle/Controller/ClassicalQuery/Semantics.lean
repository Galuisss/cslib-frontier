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

* `Cslib.Quantum.ClassicalQueryLayout.matrix_copyHidden_zeroTarget_withReference`: the actual
  protected-hidden-bit copy is a coherent record while retaining every other wire and reference.

## References

This register correspondence is original formalization infrastructure for the B2 reduction in
[HQC2026], Theorem 6.3, pp. 61--64.
-/

public section

namespace Cslib.Quantum.ClassicalQueryLayout

open Matrix Circuit GateCode
open scoped Kronecker

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
  ext ⟨label, restOut, referenceOut⟩ ⟨restIn, referenceIn⟩
  simp only [Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply,
    kroneckerMap_apply, Matrix.one_apply, coherentRecord]
  by_cases hreference : referenceOut = referenceIn <;>
    simp [hreference]

end Cslib.Quantum.ClassicalQueryLayout
