/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.ClassicalQuery
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.BlockCopy.Deferred
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Physical semantics of the classical-query controller

The classical-query controller copies its Hadamard challenge bit into the first wire of the
protected reply record.  After splitting out that fresh target wire, the actual CNOT block is the
existing `coherentRecord` isometry.  The equality below includes an arbitrary finite reference
factor and therefore does not assume a product input or quantum advice.

This module also identifies the controller's final comparison measurement with equality of the
second-stage guess and protected hidden bit.  Dephasing the complete hidden-bit-and-ciphertext
label, running the ciphertext-only second stage, and composing these boundaries with the native
success experiment remain separate obligations.

## Main definitions

* `Cslib.Quantum.ClassicalQueryLayout.Compatible.initialPrefixBranch`: the physical basis branch
  retaining the first-stage output, its recorded request, and the matching hidden-bit copies.

## Main results

* `Cslib.Quantum.ClassicalQueryLayout.Compatible.ofPhaseCodes_compileClassicalQuery`: the
  erased compiled circuit is the exact sequence of its three embedded component circuits and
  physical boundary blocks.
* `Cslib.Quantum.ClassicalQueryLayout.Compatible.classicalRun_initialCopies`: the actual input
  copies initialize the canonical first-stage input and retain fresh request/reply registers.
* `Cslib.Quantum.ClassicalQueryLayout.matrix_copyHidden_zeroTarget_withReference`: the actual
  protected-hidden-bit copy is a coherent record while retaining every other wire and reference.
* `Cslib.Quantum.ClassicalQueryLayout.Compatible.eval_initialPrefix`: the actual first six
  blocks run the zero-oracle-erased first stage F on its public input and coherently prepare the
  request and hidden-bit records.
* `Cslib.Quantum.ClassicalQueryLayout.Compatible.initialPrefixBranch_registers`: each branch
  supplies the exact service input, preserves the complete first-stage register, and initializes
  the hidden-bit/zero-ciphertext reply.
* `Cslib.Quantum.ClassicalQueryLayout.eval_requestHidden_embedState`: the actual request copy,
  Hadamard seed and protected-bit copy preserve the complete first-stage superposition.
* `Cslib.Quantum.ClassicalQueryLayout.partialTraceLeft_copyRequest_zeroTarget_withReference`:
  discarding the actual copied request gives exactly the sum of request density branches,
  including an arbitrary inaccessible reference.
* `Cslib.Quantum.ClassicalQueryLayout.measureDensity_finalComparison`: the actual guess
  relocation and hidden-bit comparison measure exactly whether the second-stage guess equals the
  protected hidden bit, for arbitrary mixed states with an external reference.

## References

This register correspondence is original formalization infrastructure for the B2 reduction in
[HQC2026], Theorem 6.3, pp. 61--64.
-/

public section

namespace Cslib.Quantum.ClassicalQueryLayout

open Matrix Circuit GateCode
open Turing.MultiTapeTM
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

/-- The first two physical blocks of the compiled controller save the complete input for the
service and its security header for the second stage.  The sparse first-stage view is exactly the
canonical encoding of the public-key prefix, while the request, hidden-bit and retained-reply
registers remain fresh. -/
theorem Compatible.classicalRun_initialCopies {layout : ClassicalQueryLayout}
    (h : layout.Compatible) (sample : List Bool)
    (hsample : sample.length = layout.input.classicalInputLength) :
    let κ := layout.input.securityParameter
    let encoded := encPair encUnary encBits (κ, sample)
    let initial := inputState layout.width encoded
    let prepared := classicalRun
      (blockCopyCodes 0 layout.secondBase (2 * κ + 1))
      (classicalRun
        (blockCopyCodes 0 layout.serviceBase layout.fullInputWidth) initial)
    prepared ∘ layout.firstEmbedding =
        inputState layout.first.width
          (encPair encUnary encBits (κ, sample.take layout.publicKeyWidth)) ∧
      (∀ i < layout.fullInputWidth, readBit prepared i = encoded.getD i false) ∧
      (∀ i < layout.service.width,
        readBit prepared (layout.serviceBase + i) = encoded.getD i false) ∧
      (∀ i < 2 * κ + 1,
        readBit prepared (layout.secondBase + i) = encoded.getD i false) ∧
      (∀ i < layout.first.outputWidth,
        readBit prepared (layout.requestBase + i) = false) ∧
      readBit prepared layout.hiddenWire = false ∧
      (∀ i < 1 + layout.ciphertextWidth,
        readBit prepared (layout.replyBase + i) = false) := by
  let κ := layout.input.securityParameter
  let encoded := encPair encUnary encBits (κ, sample)
  let firstEncoded := encPair encUnary encBits (κ, sample.take layout.publicKeyWidth)
  let initial := inputState layout.width encoded
  let serviceCopied := classicalRun
    (blockCopyCodes 0 layout.serviceBase layout.fullInputWidth) initial
  let prepared := classicalRun
    (blockCopyCodes 0 layout.secondBase (2 * κ + 1)) serviceCopied
  change prepared ∘ layout.firstEmbedding = inputState layout.first.width firstEncoded ∧
    (∀ i < layout.fullInputWidth, readBit prepared i = encoded.getD i false) ∧
    (∀ i < layout.service.width,
      readBit prepared (layout.serviceBase + i) = encoded.getD i false) ∧
    (∀ i < 2 * κ + 1,
      readBit prepared (layout.secondBase + i) = encoded.getD i false) ∧
    (∀ i < layout.first.outputWidth,
      readBit prepared (layout.requestBase + i) = false) ∧
    readBit prepared layout.hiddenWire = false ∧
    (∀ i < 1 + layout.ciphertextWidth,
      readBit prepared (layout.replyBase + i) = false)
  have hpublicKey := h.publicKey_le
  have hencodedLength : encoded.length = layout.fullInputWidth := by
    simp only [encoded, encPair_apply, encUnary_apply, encBits_apply, List.length_append,
      length_frame, List.length_replicate, fullInputWidth, κ, hsample]
  have hfirstEncodedLength : firstEncoded.length = layout.firstInputWidth := by
    simp only [firstEncoded, encPair_apply, encUnary_apply, encBits_apply, List.length_append,
      length_frame, List.length_replicate, List.length_take, firstInputWidth, κ, hsample]
    rw [Nat.min_eq_left hpublicKey]
  have hfirstWidth : layout.firstInputWidth ≤ layout.first.width := by
    have hinput := h.first_wellFormed.input_le
    rw [h.first_quantumInputWidth, Nat.add_zero] at hinput
    exact hinput
  have hserviceWidth : layout.fullInputWidth ≤ layout.service.width := by
    have hinput := h.service_wellFormed.input_le
    simp only [fullInputWidth]
    omega
  have hsecondHeaderWidth : 2 * κ + 1 ≤ layout.second.width := by
    have hinput := h.second_wellFormed.input_le
    simp only [κ, ciphertextWidth] at hinput ⊢
    omega
  have hinputBeforeRequest : layout.fullInputWidth ≤ layout.requestBase := by
    simp only [firstInputWidth] at hfirstWidth
    simp only [fullInputWidth, requestBase, ciphertextWidth]
    omega
  have hfullBeforeService : layout.fullInputWidth ≤ layout.serviceBase := by
    simp only [serviceBase, hiddenWire]
    omega
  have hfullBeforeSecond : layout.fullInputWidth ≤ layout.secondBase := by
    simp only [secondBase, replyBase, serviceBase]
    omega
  have hheaderBeforeSecond : 2 * κ + 1 ≤ layout.secondBase := by
    simp only [fullInputWidth] at hfullBeforeSecond
    omega
  have hheaderBeforeService : 2 * κ + 1 ≤ layout.serviceBase := by
    simp only [fullInputWidth] at hfullBeforeService
    omega
  have hfullFits : layout.fullInputWidth ≤ layout.width := by
    exact hfullBeforeSecond.trans (by simp only [width]; omega)
  have hserviceTargetFits : layout.serviceBase + layout.fullInputWidth ≤ layout.width := by
    simp only [width, secondBase, replyBase]
    omega
  have hsecondTargetFits : layout.secondBase + (2 * κ + 1) ≤ layout.width := by
    simp only [width]
    omega
  have hencodedFits : encoded.length ≤ layout.width := hencodedLength.le.trans hfullFits
  have hfirstEncodedFits : firstEncoded.length ≤ layout.first.width :=
    hfirstEncodedLength.le.trans hfirstWidth
  have hinitial (q : ℕ) : readBit initial q = encoded.getD q false :=
    readBit_inputState hencodedFits q
  have hserviceTargetBeforeSecond :
      layout.serviceBase + layout.fullInputWidth ≤ layout.secondBase := by
    simp only [secondBase, replyBase]
    omega
  have hglueOff (target count : ℕ) (htarget : target + count ≤ layout.width)
      (z : Fin count → Bool) (x : Fin layout.width → Bool) (q : ℕ)
      (hq : q < target ∨ target + count ≤ q) :
      readBit (glue (blockEmb target htarget) z x) q = readBit x q := by
    apply readBit_glue_of_forall_ne
    intro i heq
    simp only [blockEmb_apply_val] at heq
    rcases hq with hq | hq <;> omega
  have hserviceTargetZero : ∀ i : Fin layout.fullInputWidth,
      initial (blockEmb layout.serviceBase hserviceTargetFits i) = false := by
    intro i
    rw [← readBit_fin initial (blockEmb layout.serviceBase hserviceTargetFits i), hinitial,
      List.getD_eq_default encoded false (by
        rw [hencodedLength]
        simp only [blockEmb_apply_val]
        omega)]
  have hserviceCopiedEq : serviceCopied =
      glue (blockEmb layout.serviceBase hserviceTargetFits)
        (fun i => readBit initial (0 + i)) initial :=
    classicalRun_blockCopyCodes_zeroTarget
      (Or.inl (by simpa only [Nat.zero_add] using hfullBeforeService))
      (by simpa only [Nat.zero_add] using hfullFits) hserviceTargetFits initial
      hserviceTargetZero
  have hserviceOff (q : ℕ)
      (hq : q < layout.serviceBase ∨ layout.serviceBase + layout.fullInputWidth ≤ q) :
      readBit serviceCopied q = readBit initial q := by
    rw [hserviceCopiedEq]
    exact hglueOff layout.serviceBase layout.fullInputWidth hserviceTargetFits _ _ q hq
  have hsecondTargetZero : ∀ i : Fin (2 * κ + 1),
      serviceCopied (blockEmb layout.secondBase hsecondTargetFits i) = false := by
    intro i
    rw [← readBit_fin serviceCopied (blockEmb layout.secondBase hsecondTargetFits i),
      hserviceOff _ (Or.inr (by
        simp only [blockEmb_apply_val]
        omega)), hinitial,
      List.getD_eq_default encoded false (by
        rw [hencodedLength]
        simp only [blockEmb_apply_val]
        omega)]
  have hpreparedEq : prepared =
      glue (blockEmb layout.secondBase hsecondTargetFits)
        (fun i => readBit serviceCopied (0 + i)) serviceCopied :=
    classicalRun_blockCopyCodes_zeroTarget
      (Or.inl (by simpa only [Nat.zero_add] using hheaderBeforeSecond))
      (by simpa only [Nat.zero_add] using hheaderBeforeSecond.trans (by
        simp only [width]
        omega)) hsecondTargetFits serviceCopied hsecondTargetZero
  have hsecondOff (q : ℕ)
      (hq : q < layout.secondBase ∨ layout.secondBase + (2 * κ + 1) ≤ q) :
      readBit prepared q = readBit serviceCopied q := by
    rw [hpreparedEq]
    exact hglueOff layout.secondBase (2 * κ + 1) hsecondTargetFits _ _ q hq
  have hreadOriginal (i : ℕ) (hi : i < layout.fullInputWidth) :
      readBit prepared i = encoded.getD i false := by
    rw [hsecondOff i (Or.inl (hi.trans_le hfullBeforeSecond)),
      hserviceOff i (Or.inl (hi.trans_le hfullBeforeService)), hinitial]
  have hreadService (i : ℕ) (hi : i < layout.service.width) :
      readBit prepared (layout.serviceBase + i) = encoded.getD i false := by
    rw [hsecondOff _ (Or.inl (by simp only [secondBase, replyBase]; omega))]
    by_cases hinput : i < layout.fullInputWidth
    · rw [hserviceCopiedEq]
      let offset : Fin layout.fullInputWidth := ⟨i, hinput⟩
      have hemb : (blockEmb layout.serviceBase hserviceTargetFits offset : ℕ) =
          layout.serviceBase + i := by
        simp only [blockEmb_apply_val, offset, Nat.add_comm]
      rw [← hemb, readBit_fin, glue_apply_emb, Nat.zero_add, hinitial]
    · rw [hserviceOff _ (Or.inr (by omega)), hinitial,
        List.getD_eq_default encoded false (by rw [hencodedLength]; omega),
        List.getD_eq_default encoded false (by rw [hencodedLength]; omega)]
  have hreadSecond (i : ℕ) (hi : i < 2 * κ + 1) :
      readBit prepared (layout.secondBase + i) = encoded.getD i false := by
    rw [hpreparedEq]
    let offset : Fin (2 * κ + 1) := ⟨i, hi⟩
    have hemb : (blockEmb layout.secondBase hsecondTargetFits offset : ℕ) =
        layout.secondBase + i := by
      simp only [blockEmb_apply_val, offset, Nat.add_comm]
    rw [← hemb, readBit_fin, glue_apply_emb, Nat.zero_add,
      hserviceOff i (Or.inl (hi.trans_le hheaderBeforeService)), hinitial]
  have hzero (q : ℕ) (hinput : layout.fullInputWidth ≤ q)
      (hservice : q < layout.serviceBase ∨
        layout.serviceBase + layout.fullInputWidth ≤ q)
      (hsecond : q < layout.secondBase ∨ layout.secondBase + (2 * κ + 1) ≤ q) :
      readBit prepared q = false := by
    rw [hsecondOff q hsecond, hserviceOff q hservice, hinitial,
      List.getD_eq_default encoded false (by rw [hencodedLength]; exact hinput)]
  have hprefix (i : ℕ) (hi : i < layout.firstInputWidth) :
      firstEncoded.getD i false = encoded.getD i false := by
    change
      (frame (encUnary κ) ++ sample.take layout.publicKeyWidth).getD i false =
        (frame (encUnary κ) ++ sample).getD i false
    have hframe : (frame (encUnary κ)).length = 2 * κ + 1 := by
      simp only [encUnary_apply, length_frame, List.length_replicate]
    by_cases hheader : i < 2 * κ + 1
    · rw [List.getD_append _ _ _ _ (hframe.symm ▸ hheader),
        List.getD_append _ _ _ _ (hframe.symm ▸ hheader)]
    · have hoffset : i - (frame (encUnary κ)).length < layout.publicKeyWidth := by
        simp only [firstInputWidth] at hi
        omega
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hoffset]
  constructor
  · funext wire
    simp only [Function.comp_apply]
    rw [← readBit_fin prepared (layout.firstEmbedding wire),
      ← readBit_fin (inputState layout.first.width firstEncoded) wire]
    change readBit prepared (layout.firstWire wire) =
      readBit (inputState layout.first.width firstEncoded) wire
    rw [readBit_inputState hfirstEncodedFits]
    by_cases hwire : (wire : ℕ) < layout.firstInputWidth
    · rw [firstWire, ite_eq_left hwire, hreadOriginal wire (by
          simp only [fullInputWidth, firstInputWidth] at hwire ⊢
          omega)]
      exact (hprefix wire hwire).symm
    · rw [firstWire, ite_eq_right hwire,
        hzero _ (by
          simp only [fullInputWidth, firstInputWidth, ciphertextWidth] at *
          omega) (Or.inl (by
            simp only [serviceBase, hiddenWire, requestBase]
            omega)) (Or.inl (by
              simp only [secondBase, replyBase, serviceBase, hiddenWire, requestBase]
              omega)),
        List.getD_eq_default firstEncoded false (by
          rw [hfirstEncodedLength]
          omega)]
  refine ⟨hreadOriginal, hreadService, hreadSecond, ?_, ?_, ?_⟩
  · intro i hi
    apply hzero
    · exact hinputBeforeRequest.trans (Nat.le_add_right _ _)
    · left
      simp only [serviceBase, hiddenWire]
      omega
    · left
      simp only [secondBase, replyBase, serviceBase, hiddenWire]
      omega
  · apply hzero
    · exact hinputBeforeRequest.trans (by simp only [hiddenWire]; omega)
    · left
      simp only [serviceBase]
      omega
    · left
      simp only [secondBase, replyBase, serviceBase]
      omega
  · intro i hi
    apply hzero
    · exact hinputBeforeRequest.trans (by
        simp only [replyBase, serviceBase, hiddenWire]
        omega)
    · right
      simp only [replyBase]
      omega
    · left
      simp only [secondBase]
      omega

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
  change classicalRun (blockCopyCodes layout.hiddenWire layout.replyBase 1) y =
    Function.update y ⟨layout.replyBase, hreplylt⟩ (bit 0)
  have hembReply : blockEmb layout.replyBase htarget (0 : Fin 1) =
      ⟨layout.replyBase, hreplylt⟩ := by
    apply Fin.ext
    simp only [blockEmb_apply_val, Fin.val_zero, Nat.zero_add]
  have hcopyZero : ∀ i : Fin 1, y (blockEmb layout.replyBase htarget i) = false := by
    intro i
    rw [Subsingleton.elim i 0, hembReply]
    exact hytarget
  rw [classicalRun_blockCopyCodes_zeroTarget (Or.inl hdisjoint) hsource htarget y hcopyZero]
  funext j
  by_cases hj : j = blockEmb layout.replyBase htarget 0
  · subst j
    rw [glue_apply_emb, hembReply, Function.update_self]
    simpa only [Fin.val_zero, Nat.add_zero] using hysource
  · rw [glue_of_not _ _ _ (fun i heq => hj (by
      rw [Subsingleton.elim i 0] at heq
      exact heq.symm)), Function.update_of_ne (by simpa only [hembReply] using hj)]


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


/-- The physical basis branch after the first-stage request is copied and a fresh hidden bit
is supplied to the service and the protected reply. The first-stage basis string is retained in
full; all other wires come from the actual two-copy initializer. -/
@[expose] noncomputable def Compatible.initialPrefixBranch {layout : ClassicalQueryLayout}
    (h : layout.Compatible) (sample : List Bool)
    (z : Fin layout.first.width → Bool) (bit : Fin 1 → Bool) : Fin layout.width → Bool :=
  let hfirstInput : layout.firstInputWidth ≤ layout.first.width := by
    have hi := h.first_wellFormed.input_le
    rw [h.first_quantumInputWidth, Nat.add_zero] at hi
    exact hi
  let hrequestEnd : layout.requestBase + layout.first.outputWidth ≤ layout.width := by
    simp only [width, secondBase, replyBase, serviceBase, hiddenWire]
    omega
  let hhiddenEnd : layout.hiddenWire + 1 ≤ layout.width := by
    simp only [width, secondBase, replyBase, serviceBase]
    omega
  let hreplyEnd : layout.replyBase < layout.width := by
    simp only [width, secondBase]
    omega
  let initial := inputState layout.width
    (encPair encUnary encBits (layout.input.securityParameter, sample))
  let prepared := classicalRun
    (blockCopyCodes 0 layout.secondBase (2 * layout.input.securityParameter + 1))
    (classicalRun (blockCopyCodes 0 layout.serviceBase layout.fullInputWidth) initial)
  Function.update
    (glue (blockEmb layout.hiddenWire hhiddenEnd) bit
      (glue (blockEmb layout.requestBase hrequestEnd)
        (fun i => z ⟨i, lt_of_lt_of_le i.isLt (h.first_output_le.trans hfirstInput)⟩)
        (glue layout.firstEmbedding z prepared)))
    ⟨layout.replyBase, hreplyEnd⟩ (bit 0)


/-- The actual first six controller blocks initialize and run the zero-oracle-erased first stage
F on exactly the public-key prefix, then coherently record its request and prepare matching
hidden bits. Every first-stage basis amplitude is retained; no measurement or dephasing has been
inserted into the circuit. -/
theorem Compatible.eval_initialPrefix {layout : ClassicalQueryLayout}
    (h : layout.Compatible) (sample : List Bool)
    (hsample : sample.length = layout.input.classicalInputLength) :
    let κ := layout.input.securityParameter
    let initial := inputState layout.width (encPair encUnary encBits (κ, sample))
    let firstCircuit := Circuit.ofPhaseCodes layout.first.width
      layout.first.instructions.zeroOraclePhaseCodes
    let ψ := firstCircuit.eval (ket (inputState layout.first.width
      (encPair encUnary encBits (κ, sample.take layout.publicKeyWidth))))
    Circuit.eval
      ((Circuit.ofCodes layout.width (blockCopyCodes 0 layout.serviceBase layout.fullInputWidth) ++
        Circuit.ofCodes layout.width (blockCopyCodes 0 layout.secondBase (2 * κ + 1)) ++
        firstCircuit.mapWires layout.firstEmbedding) ++
        Circuit.ofCodes layout.width
          (blockCopyCodes 0 layout.requestBase layout.first.outputWidth ++
            (hadamardCodes layout.hiddenWire 1 ++
              blockCopyCodes layout.hiddenWire layout.replyBase 1))) (ket initial) =
      ∑ z : Fin layout.first.width → Bool, ψ.ofLp z •
        ∑ bit : Fin 1 → Bool, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          ket (h.initialPrefixBranch sample z bit) := by
  classical
  dsimp only [Compatible.initialPrefixBranch]
  let κ := layout.input.securityParameter
  let initial := inputState layout.width (encPair encUnary encBits (κ, sample))
  let prepared := classicalRun (blockCopyCodes 0 layout.secondBase (2 * κ + 1))
    (classicalRun (blockCopyCodes 0 layout.serviceBase layout.fullInputWidth) initial)
  let firstInput := inputState layout.first.width
    (encPair encUnary encBits (κ, sample.take layout.publicKeyWidth))
  have hfirstInput : layout.firstInputWidth ≤ layout.first.width := by
    have hi := h.first_wellFormed.input_le
    rw [h.first_quantumInputWidth, Nat.add_zero] at hi
    exact hi
  have hserviceWidth : layout.fullInputWidth ≤ layout.service.width := by
    have hi := h.service_wellFormed.input_le
    change layout.fullInputWidth + layout.service.quantumInputWidth ≤ layout.service.width at hi
    omega
  have hsecondWidth : 2 * κ + 1 ≤ layout.second.width := by
    have hi := h.second_wellFormed.input_le
    change 2 * κ + 1 + layout.ciphertextWidth + layout.second.quantumInputWidth ≤
      layout.second.width at hi
    omega
  have hinputBeforeRequest : layout.fullInputWidth ≤ layout.requestBase := by
    have hp := h.publicKey_le
    simp only [fullInputWidth, firstInputWidth, requestBase, ciphertextWidth] at *
    omega
  have hcopyService : IsClassical layout.width
      (blockCopyCodes 0 layout.serviceBase layout.fullInputWidth) := by
    apply isClassical_blockCopyCodes
    · left
      simp only [Nat.zero_add, serviceBase, hiddenWire]
      omega
    · simp only [Nat.zero_add, width, secondBase, replyBase]
      omega
    · simp only [width, secondBase, replyBase]
      omega
  have hcopyHeader : IsClassical layout.width
      (blockCopyCodes 0 layout.secondBase (2 * κ + 1)) := by
    apply isClassical_blockCopyCodes
    · left
      simp only [Nat.zero_add, secondBase, replyBase, serviceBase, hiddenWire,
        fullInputWidth, κ] at *
      omega
    · simp only [Nat.zero_add, width]
      omega
    · simp only [width]
      omega
  have hinitial := h.classicalRun_initialCopies sample hsample
  change prepared ∘ layout.firstEmbedding = firstInput ∧ _ at hinitial
  obtain ⟨hfirst, _, _, _, hrequest, hhidden, hreply⟩ := hinitial
  have hemb : embedState layout.firstEmbedding prepared (ket firstInput) = ket prepared := by
    rw [← hfirst, embedState_ket,
      glue_comp_of_agreeOff (AgreeOff.refl layout.firstEmbedding prepared)]
  rw [Circuit.eval_append, Circuit.eval_append, Circuit.eval_append,
    Circuit.eval_ofCodes_ket hcopyService, Circuit.eval_ofCodes_ket hcopyHeader]
  change Circuit.eval _ (Circuit.eval _ (ket prepared)) = _
  rw [← hemb, Circuit.eval_mapWires_embedState]
  exact eval_requestHidden_embedState layout h.first_output_le hfirstInput prepared hrequest
    hhidden (by simpa only [Nat.add_zero] using hreply 0 (by omega)) _


/-- Each branch of the actual initial prefix supplies the service with the original sample,
recorded request and hidden bit, preserves the full first-stage basis string, and initializes
the protected reply to the same hidden bit followed by zero ciphertext wires. -/
theorem Compatible.initialPrefixBranch_registers {layout : ClassicalQueryLayout}
    (h : layout.Compatible) (sample : List Bool)
    (hsample : sample.length = layout.input.classicalInputLength)
    (z : Fin layout.first.width → Bool) (bit : Fin 1 → Bool) :
    let hfirstInput : layout.firstInputWidth ≤ layout.first.width := by
      have hi := h.first_wellFormed.input_le
      rw [h.first_quantumInputWidth, Nat.add_zero] at hi
      exact hi
    let request : Fin layout.first.outputWidth → Bool :=
      fun i => z ⟨i, lt_of_lt_of_le i.isLt (h.first_output_le.trans hfirstInput)⟩
    let branch := h.initialPrefixBranch sample z bit
    branch ∘ layout.serviceEmbedding = inputState layout.service.width
        (encPair encUnary encBits (layout.input.securityParameter, sample) ++
          List.ofFn request ++ [bit 0]) ∧
      branch ∘ layout.firstEmbedding = z ∧
      (∀ i < 1 + layout.ciphertextWidth,
        readBit branch (layout.replyBase + i) = if i = 0 then bit 0 else false) := by
  classical
  let encoded := encPair encUnary encBits (layout.input.securityParameter, sample)
  let prepared := classicalRun
    (blockCopyCodes 0 layout.secondBase (2 * layout.input.securityParameter + 1))
    (classicalRun (blockCopyCodes 0 layout.serviceBase layout.fullInputWidth)
      (inputState layout.width encoded))
  have hfirstInput : layout.firstInputWidth ≤ layout.first.width := by
    have hi := h.first_wellFormed.input_le
    rw [h.first_quantumInputWidth, Nat.add_zero] at hi
    exact hi
  let request : Fin layout.first.outputWidth → Bool :=
    fun i => z ⟨i, lt_of_lt_of_le i.isLt (h.first_output_le.trans hfirstInput)⟩
  have hr : layout.requestBase + layout.first.outputWidth ≤ layout.width := by
    simp only [width, secondBase, replyBase, serviceBase, hiddenWire]
    omega
  have hh : layout.hiddenWire + 1 ≤ layout.width := by
    simp only [width, secondBase, replyBase, serviceBase]
    omega
  have hb : layout.replyBase < layout.width := by simp only [width, secondBase]; omega
  let firstState := glue layout.firstEmbedding z prepared
  let requested := glue (blockEmb layout.requestBase hr) request firstState
  let seeded := glue (blockEmb layout.hiddenWire hh) bit requested
  let branch := Function.update seeded (⟨layout.replyBase, hb⟩ : Fin layout.width) (bit 0)
  change branch ∘ layout.serviceEmbedding =
      inputState layout.service.width (encoded ++ List.ofFn request ++ [bit 0]) ∧
    branch ∘ layout.firstEmbedding = z ∧ _
  have hencoded : encoded.length = layout.fullInputWidth := by
    simp only [encoded, length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply, hsample, fullInputWidth]
  have hinitial := h.classicalRun_initialCopies sample hsample
  change prepared ∘ layout.firstEmbedding = _ ∧ _ at hinitial
  obtain ⟨_, _, hservice, _, _, _, hreply⟩ := hinitial
  have hfirstOff (q : Fin layout.width) (hq : layout.requestBase ≤ q) :
      firstState q = prepared q := by
    apply glue_of_not
    intro i heq
    have hi := layout.firstWire_lt_requestBase i.isLt
    have heq := congrArg Fin.val heq
    change layout.firstWire i = q.val at heq
    omega
  have hrequestOff (q : Fin layout.width)
      (hq : q.val < layout.requestBase ∨ layout.hiddenWire ≤ q.val) :
      requested q = firstState q := by
    apply glue_of_not
    intro i heq
    have heq := congrArg Fin.val heq
    simp only [blockEmb_apply_val] at heq
    simp only [hiddenWire] at hq
    rcases hq with hq | hq <;> omega
  have hseedOff (q : Fin layout.width) (hq : q.val ≠ layout.hiddenWire) :
      seeded q = requested q := by
    apply glue_of_not
    intro i heq
    have heq := congrArg Fin.val heq
    simp only [blockEmb_apply_val] at heq
    have hi : i.val = 0 := by omega
    omega
  have hbranchOff (q : Fin layout.width) (hq : q.val ≠ layout.replyBase) :
      branch q = seeded q := by
    exact Function.update_of_ne (fun heq => hq (congrArg Fin.val heq)) _ _
  have hservicePhysical (i : Fin layout.service.width)
      (hq : layout.serviceWire i = layout.serviceBase + i) :
      branch (layout.serviceEmbedding i) = encoded.getD i false := by
    have hqVal : (layout.serviceEmbedding i).val = layout.serviceBase + i := hq
    have hbefore := layout.serviceEmbedding_lt_replyBase i
    rw [hbranchOff _ (by change layout.serviceWire i ≠ _; omega),
      hseedOff _ (by rw [hqVal]; simp only [serviceBase]; omega),
      hrequestOff _ (Or.inr (by rw [hqVal]; simp only [serviceBase]; omega)),
      hfirstOff _ (by rw [hqVal]; simp only [serviceBase, hiddenWire]; omega)]
    rw [← readBit_fin prepared (layout.serviceEmbedding i)]
    change readBit prepared (layout.serviceWire i) = _
    rw [hq, hservice i i.isLt]
  constructor
  · funext i
    simp only [Function.comp_apply]
    change branch (layout.serviceEmbedding i) =
      (encoded ++ List.ofFn request ++ [bit 0]).getD i false
    rw [List.append_assoc]
    by_cases hi : i.val < layout.fullInputWidth
    · rw [hservicePhysical i (by simp only [serviceWire, hi, ↓reduceIte]),
        List.getD_append _ _ _ _ (by omega)]
    · rw [List.getD_append_right _ _ _ _ (by omega), hencoded]
      by_cases hreq : i.val - layout.fullInputWidth < layout.first.outputWidth
      · have hq : layout.serviceEmbedding i =
            blockEmb layout.requestBase hr ⟨i.val - layout.fullInputWidth, hreq⟩ := by
          apply Fin.ext
          change layout.serviceWire i = (i.val - layout.fullInputWidth) + layout.requestBase
          simp only [serviceWire, hi, ↓reduceIte]
          rw [ite_eq_left (by omega)]
          omega
        have hqVal : (layout.serviceEmbedding i).val =
            layout.requestBase + (i.val - layout.fullInputWidth) := by
          rw [hq]
          simp only [blockEmb_apply_val, Nat.add_comm]
        rw [hbranchOff _ (by
          have ht := layout.serviceEmbedding_lt_replyBase i
          change layout.serviceWire i ≠ _; omega),
          hseedOff _ (by rw [hqVal]; simp only [hiddenWire]; omega), hq]
        change requested (blockEmb layout.requestBase hr _) = _
        rw [show requested (blockEmb layout.requestBase hr
            ⟨i.val - layout.fullInputWidth, hreq⟩) =
              request ⟨i.val - layout.fullInputWidth, hreq⟩ from glue_apply_emb _ _ _ _,
          List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hreq)]
        exact (List.getD_ofFn_of_lt request hreq false).symm
      · rw [List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using
          (Nat.le_of_not_gt hreq)), List.length_ofFn]
        by_cases heq : i.val - layout.fullInputWidth = layout.first.outputWidth
        · have hq : layout.serviceEmbedding i = blockEmb layout.hiddenWire hh 0 := by
            apply Fin.ext
            simp only [blockEmb_apply_val, Fin.val_zero, Nat.zero_add]
            change layout.serviceWire i = layout.hiddenWire
            simp only [serviceWire, hi, ↓reduceIte, heq, Nat.lt_add_one, hiddenWire]
          rw [hbranchOff _ (by
            have ht := layout.serviceEmbedding_lt_replyBase i
            change layout.serviceWire i ≠ _; omega), hq]
          change seeded (blockEmb layout.hiddenWire hh 0) = _
          rw [show seeded (blockEmb layout.hiddenWire hh 0) = bit 0 from
            glue_apply_emb _ _ _ _, heq, Nat.sub_self]
          rfl
        · rw [hservicePhysical i (by
            simp only [serviceWire, hi, ↓reduceIte]
            rw [ite_eq_right (by omega)]),
            List.getD_eq_default encoded false (by omega),
            List.getD_eq_default [bit 0] false (by simp only [List.length_singleton]; omega)]
  constructor
  · funext i
    simp only [Function.comp_apply]
    have hi := layout.firstWire_lt_requestBase i.isLt
    have hval : (layout.firstEmbedding i).val = layout.firstWire i := rfl
    rw [hbranchOff _ (by rw [hval]; simp only [replyBase, serviceBase, hiddenWire]; omega),
      hseedOff _ (by rw [hval]; simp only [hiddenWire]; omega),
      hrequestOff _ (Or.inl hi)]
    exact glue_apply_emb _ _ _ _
  · intro i hi
    change readBit branch (layout.replyBase + i) = _
    have hfit : layout.replyBase + i < layout.width := by
      simp only [width, secondBase]
      omega
    rw [readBit_of_lt _ hfit]
    by_cases hiz : i = 0
    · subst i
      simp only [Nat.add_zero, branch, Function.update_self, ↓reduceIte]
    · rw [ite_eq_right hiz,
        hbranchOff ⟨layout.replyBase + i, hfit⟩ (by change layout.replyBase + i ≠ _; omega),
        hseedOff _ (by simp only [replyBase, serviceBase]; omega),
        hrequestOff _ (Or.inr (by
          simp only [replyBase, serviceBase]; omega)),
        hfirstOff _ (by simp only [replyBase, serviceBase, hiddenWire]; omega),
        ← readBit_fin prepared ⟨layout.replyBase + i, hfit⟩]
      exact hreply i hi


/-- **The final physical suffix accepts exactly when the second-stage guess equals the protected
hidden bit.**  The actual one-wire prefix swap moves the second-stage output at `secondBase` to
wire zero, and the actual comparison gates replace it by its equality with the retained hidden
bit at `replyBase`.  For every mixed physical state, including one entangled with an arbitrary
finite reference, measuring wire zero after this suffix is therefore exactly the original joint
event `guess = hidden`.

This is the final readout law for a classical-query controller, not a complete game or security
theorem: composing it with the controller prefix, service and controlled second-stage identities
remains separate. -/
theorem measureDensity_finalComparison (layout : ClassicalQueryLayout)
    (hsecondOutput : 1 ≤ layout.second.outputWidth)
    (hsecondOutputFits : layout.second.outputWidth ≤ layout.second.width)
    {Reference : Type*} [Fintype Reference] [DecidableEq Reference]
    (rho : Matrix ((Fin layout.width → Bool) × Reference)
      ((Fin layout.width → Bool) × Reference) ℂ)
    (hrho : IsDensityMatrix rho) :
    let finalCodes :=
      prefixSwapCodes layout.secondBase 1 ++ compareBits layout.replyBase 0
    let finalCircuit := Circuit.ofCodes layout.width finalCodes
    let finalMatrix : Matrix (Fin layout.width → Bool) (Fin layout.width → Bool) ℂ :=
      Circuit.matrix finalCircuit
    (POVM.basis.measureDensity
      (densityConj
        (finalMatrix ⊗ₖ (1 : Matrix Reference Reference ℂ)) rho)
      (hrho.densityConj_kronecker
        (V := finalMatrix)
        (by exact UnitaryGroup.star_mul_self (Circuit.matrix finalCircuit)))).map
        (fun p => readBit p.1 0) =
      (POVM.basis.measureDensity rho hrho).map
        (fun p => readBit p.1 layout.secondBase == readBit p.1 layout.replyBase) := by
  classical
  dsimp only
  let finalCodes :=
    prefixSwapCodes layout.secondBase 1 ++ compareBits layout.replyBase 0
  let finalCircuit := Circuit.ofCodes layout.width finalCodes
  have hsecondWidth : 1 ≤ layout.second.width :=
    hsecondOutput.trans hsecondOutputFits
  have hsourceDisjoint : 1 ≤ layout.secondBase := by
    simp only [ClassicalQueryLayout.secondBase, ClassicalQueryLayout.replyBase,
      ClassicalQueryLayout.serviceBase, ClassicalQueryLayout.hiddenWire]
    omega
  have hsourceFit : layout.secondBase + 1 ≤ layout.width := by
    simp only [ClassicalQueryLayout.width]
    omega
  have hhiddenFit : layout.replyBase < layout.width := by
    simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
    omega
  have hzeroFit : 0 < layout.width := by omega
  have hhiddenZero : layout.replyBase ≠ 0 := by
    simp only [ClassicalQueryLayout.replyBase, ClassicalQueryLayout.serviceBase,
      ClassicalQueryLayout.hiddenWire]
    omega
  have hhiddenSource : layout.replyBase ≠ layout.secondBase := by
    simp only [ClassicalQueryLayout.secondBase]
    omega
  have hclass : IsClassical layout.width finalCodes :=
    IsClassical.append.mpr ⟨
      isClassical_prefixSwapCodes hsourceDisjoint hsourceFit,
      isClassical_compareBits hhiddenZero hhiddenFit hzeroFit⟩
  rw [Circuit.measureDensity_basis_ofCodes hclass rho hrho, PMF.map_comp]
  congr 1
  funext p
  simp only [Function.comp_apply, finalCodes, classicalRun_append]
  rw [readBit_classicalRun_compareBits hzeroFit]
  have hone : prefixSwapCodes layout.secondBase 1 =
      swapWireCodes 0 layout.secondBase := by
    simp [prefixSwapCodes]
  rw [hone,
    readBit_classicalRun_swapWireCodes (by omega) (by omega) (by omega),
    readBit_classicalRun_swapWireCodes_of_ne hhiddenZero hhiddenSource]

end Cslib.Quantum.ClassicalQueryLayout
