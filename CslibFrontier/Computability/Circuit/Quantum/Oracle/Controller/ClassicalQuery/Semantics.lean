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
* `Cslib.Quantum.ClassicalQueryLayout.eval_requestHidden_embedState`: the actual request copy,
  Hadamard seed and protected-bit copy preserve the complete first-stage superposition.
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

/-- The actual fresh Hadamard seed and protected CNOT record produce equal-amplitude branches
with the same bit in both wires. This intermediate prefix identity retains all other wires. -/
private theorem eval_prepareHidden_ket (layout : ClassicalQueryLayout)
    (x : Fin layout.width → Bool)
    (hhidden : readBit x layout.hiddenWire = false)
    (hreply : readBit x layout.replyBase = false) :
    let hsource : layout.hiddenWire + 1 ≤ layout.width := by
      simp only [width, secondBase, replyBase, serviceBase]
      omega
    let htarget : layout.replyBase < layout.width := by
      simp only [width, secondBase]
      omega
    Circuit.eval (Circuit.ofCodes layout.width
        (hadamardCodes layout.hiddenWire 1 ++
          blockCopyCodes layout.hiddenWire layout.replyBase 1)) (ket x) =
      ∑ bit : Fin 1 → Bool, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        ket (Function.update (glue (blockEmb layout.hiddenWire hsource) bit x)
          ⟨layout.replyBase, htarget⟩ (bit 0)) := by
  classical
  dsimp only
  have hsource : layout.hiddenWire + 1 ≤ layout.width := by
    simp only [width, secondBase, replyBase, serviceBase]
    omega
  have htarget : layout.replyBase + 1 ≤ layout.width := by
    simp only [width, secondBase]
    omega
  have hdisjoint : layout.hiddenWire + 1 ≤ layout.replyBase := by
    simp only [replyBase, serviceBase]
    omega
  have hhiddenlt : layout.hiddenWire < layout.width := by omega
  have hreplylt : layout.replyBase < layout.width := by omega
  have hemb : blockEmb layout.hiddenWire hsource (0 : Fin 1) =
      ⟨layout.hiddenWire, hhiddenlt⟩ := by
    apply Fin.ext
    simp only [blockEmb_apply_val, Fin.val_zero, Nat.zero_add]
  have hzero : ∀ i : Fin 1, x (blockEmb layout.hiddenWire hsource i) = false := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [hemb]
    rwa [readBit_of_lt x hhiddenlt] at hhidden
  have hclass := isClassical_blockCopyCodes (Or.inl hdisjoint) hsource htarget
  rw [Circuit.ofCodes_append, Circuit.eval_append,
    eval_hadamardCodes_ket hsource x hzero]
  simp only [pow_one, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro bit _
  rw [Circuit.eval_ofCodes_ket hclass]
  congr 2
  let y := glue (blockEmb layout.hiddenWire hsource) bit x
  have hysource : readBit y layout.hiddenWire = bit 0 := by
    rw [readBit_of_lt _ hhiddenlt]
    dsimp only [y]
    rw [← hemb]
    exact glue_apply_emb _ _ _ _
  have hytarget : y ⟨layout.replyBase, hreplylt⟩ = false := by
    dsimp only [y]
    rw [glue_of_not _ _ _ (fun i heq => by
      have hv := congrArg Fin.val heq
      simp only [blockEmb_apply_val] at hv
      omega)]
    rwa [readBit_of_lt x hreplylt] at hreply
  change classicalRun (blockCopyCodes layout.hiddenWire layout.replyBase 1) y = _
  simp only [classicalRun, blockCopyCodes, List.range_one, List.map_cons, List.map_nil,
    Nat.add_zero, List.foldl_cons, List.foldl_nil, classicalStep, dite_eq_left hreplylt,
    List.all_cons, List.all_nil, Bool.and_true, hytarget, hysource, Bool.false_xor]
  rfl


/-- The actual request copy and hidden-bit preparation preserve the complete first-stage
superposition. Each basis branch records its request and gets the same fresh bit in the service
seed and protected reply wire. The arbitrary state need not be normalized or classical. -/
theorem eval_requestHidden_embedState (layout : ClassicalQueryLayout)
    (houtput : layout.first.outputWidth ≤ layout.firstInputWidth)
    (hfirstInput : layout.firstInputWidth ≤ layout.first.width)
    (x : Fin layout.width → Bool)
    (hrequest : ∀ i < layout.first.outputWidth,
      readBit x (layout.requestBase + i) = false)
    (hhidden : readBit x layout.hiddenWire = false)
    (hreply : readBit x layout.replyBase = false)
    (ψ : Qubits layout.first.width) :
    let hrequestEnd : layout.requestBase + layout.first.outputWidth ≤ layout.width := by
      simp only [width, secondBase, replyBase, serviceBase, hiddenWire]
      omega
    let hhiddenEnd : layout.hiddenWire + 1 ≤ layout.width := by
      simp only [width, secondBase, replyBase, serviceBase]
      omega
    let hreplyEnd : layout.replyBase < layout.width := by
      simp only [width, secondBase]
      omega
    Circuit.eval (Circuit.ofCodes layout.width
      (blockCopyCodes 0 layout.requestBase layout.first.outputWidth ++
        (hadamardCodes layout.hiddenWire 1 ++
          blockCopyCodes layout.hiddenWire layout.replyBase 1)))
        (embedState layout.firstEmbedding x ψ) =
      ∑ z : Fin layout.first.width → Bool, ψ.ofLp z •
        ∑ bit : Fin 1 → Bool, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          ket (Function.update
            (glue (blockEmb layout.hiddenWire hhiddenEnd) bit
              (glue (blockEmb layout.requestBase hrequestEnd)
                (fun i => z ⟨i, lt_of_lt_of_le i.isLt (houtput.trans hfirstInput)⟩)
                (glue layout.firstEmbedding z x)))
            ⟨layout.replyBase, hreplyEnd⟩ (bit 0)) := by
  classical
  dsimp only
  have hrequestEnd : layout.requestBase + layout.first.outputWidth ≤ layout.width := by
    simp only [width, secondBase, replyBase, serviceBase, hiddenWire]
    omega
  have hfirstWidth : layout.first.width ≤ layout.width := by
    simp only [width, secondBase, replyBase, serviceBase, hiddenWire, requestBase]
    omega
  have hsource : 0 + layout.first.outputWidth ≤ layout.width := by omega
  have hdisjoint : 0 + layout.first.outputWidth ≤ layout.requestBase ∨
      layout.requestBase + layout.first.outputWidth ≤ 0 := by
    left
    simp only [requestBase]
    omega
  have hclass := isClassical_blockCopyCodes hdisjoint hsource hrequestEnd
  have hfresh (z : Fin layout.first.width → Bool) (q : Fin layout.width)
      (hq : layout.requestBase ≤ q) : glue layout.firstEmbedding z x q = x q := by
    apply glue_of_not
    intro i heq
    have hrange := firstWire_lt_requestBase layout i.isLt
    have hv := congrArg Fin.val heq
    change layout.firstWire i = q.val at hv
    omega
  rw [embedState_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul]
  congr 1
  let y := glue layout.firstEmbedding z x
  have hyzero : ∀ i : Fin layout.first.outputWidth,
      y (blockEmb layout.requestBase hrequestEnd i) = false := by
    intro i
    change glue layout.firstEmbedding z x (blockEmb layout.requestBase hrequestEnd i) = _
    rw [hfresh z _ (by simp only [blockEmb_apply_val]; omega)]
    have hi : (blockEmb layout.requestBase hrequestEnd i : ℕ) =
        layout.requestBase + i := by simp only [blockEmb_apply_val, Nat.add_comm]
    have hz := hrequest i i.isLt
    rw [← hi, readBit_fin] at hz
    exact hz
  have hread (i : Fin layout.first.outputWidth) :
      readBit y (0 + i) = z ⟨i, lt_of_lt_of_le i.isLt (houtput.trans hfirstInput)⟩ := by
    simp only [Nat.zero_add]
    rw [readBit_of_lt _ (show i.val < layout.width from lt_of_lt_of_le i.isLt (by omega))]
    have hemb : layout.firstEmbedding
        ⟨i, lt_of_lt_of_le i.isLt (houtput.trans hfirstInput)⟩ =
          (⟨i, lt_of_lt_of_le i.isLt (by omega)⟩ : Fin layout.width) := by
      apply Fin.ext
      change layout.firstWire i = i
      exact ite_eq_left (lt_of_lt_of_le i.isLt houtput)
    dsimp only [y]
    rw [← hemb, glue_apply_emb]
  let recorded := glue (blockEmb layout.requestBase hrequestEnd)
    (fun i => z ⟨i, lt_of_lt_of_le i.isLt (houtput.trans hfirstInput)⟩) y
  have hcopy : classicalRun (blockCopyCodes 0 layout.requestBase layout.first.outputWidth) y =
      recorded := by
    rw [classicalRun_blockCopyCodes_zeroTarget hdisjoint hsource hrequestEnd y hyzero]
    simp only [hread, recorded]
  have hrecordFresh (q : Fin layout.width) (hq : layout.hiddenWire ≤ q) :
      recorded q = x q := by
    dsimp only [recorded]
    rw [glue_of_not _ _ _ (fun i heq => by
      have hv := congrArg Fin.val heq
      simp only [blockEmb_apply_val] at hv
      simp only [hiddenWire] at hq
      omega)]
    exact hfresh z q (by simp only [hiddenWire] at hq; omega)
  have hh : readBit recorded layout.hiddenWire = false := by
    have hlt : layout.hiddenWire < layout.width := by
      simp only [width, secondBase, replyBase, serviceBase]
      omega
    rw [readBit_of_lt _ hlt, hrecordFresh _ (le_refl _)]
    rwa [readBit_of_lt _ hlt] at hhidden
  have hr : readBit recorded layout.replyBase = false := by
    have hlt : layout.replyBase < layout.width := by
      simp only [width, secondBase]
      omega
    rw [readBit_of_lt _ hlt, hrecordFresh _ (by simp only [replyBase, serviceBase]; omega)]
    rwa [readBit_of_lt _ hlt] at hreply
  rw [Circuit.ofCodes_append, Circuit.eval_append, Circuit.eval_ofCodes_ket hclass, hcopy,
    eval_prepareHidden_ket layout recorded hh hr]

end Cslib.Quantum.ClassicalQueryLayout
