/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.HadamardLayer
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.ZeroQuery
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode.Relabel
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.BlockCopy
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Comparison
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling.Prefix
public import CslibFrontier.Computability.Circuit.Quantum.HadamardLayer.NativeCompiler
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Code.NativeCompiler
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.ZeroQuery.NativeCompiler
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.BlockCopy.NativeCompiler
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling.Prefix.NativeCompiler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Comparison
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List

/-!
# A query-free circuit for one classical interaction boundary

`compileClassicalQuery` combines a first native stage, a reversible classical service and a
second native stage into one query-free circuit description. It is specialized to the register
shape used by the HQC 3-DQCSD reduction: the global auxiliary word contains a supplied public-key
prefix followed by the ciphertext mask, and the service emits a ciphertext of the remaining
length. The first stage sees only the public-key prefix. The full sample is copied before that
stage runs, so the service retains the challenge blocks even if the first stage overwrites its
own input wires.

The first-stage request is coherently copied to a discarded record. One Hadamard wire supplies
the hidden bit, which is copied to the retained reply record before the service can modify its
input. The service uses a fresh register, and its ciphertext completes the retained
`(hidden bit, ciphertext)` reply before the original seed and service workspace are discarded.
Only the ciphertext is copied into the second stage's classical input; its quantum input is the
complete saved first-stage register. The second-stage guess is moved to wire zero and compared
with the retained hidden bit by the two-gate equality suffix.

Every component oracle query is erased rather than imposed as a syntactic restriction. The
arbitrary-state zero-oracle theorem justifies that erasure when this construction is used in the
3-DQCSD test, whose supplied oracle is identically zero.

## Main definitions

* `Cslib.Quantum.ClassicalQueryLayout`: the independent security, public-key and component
  description coordinates used by the concrete linker.
* `Cslib.Quantum.encClassicalQueryLayout`: their field-order encoding used by the retained
  compiler.
* `Cslib.Quantum.ClassicalQueryLayout.firstEmbedding`, `serviceEmbedding`, `secondEmbedding`:
  actual component-register placements used by relabelling and semantic composition.
* `Cslib.Quantum.ClassicalQueryLayout.Compatible`: the one shape contract shared by
  well-formedness and the pending semantic theorem.
* `Cslib.Quantum.compileClassicalQuery`: the complete query-free finite description.
* `Cslib.Quantum.compileClassicalQueryCompiler`: its actual retained description compiler.

## Main results

* `Cslib.Quantum.ClassicalQueryLayout.Compatible.wellFormed_compileClassicalQuery`: a compatible
  component triple produces a valid global description.
* `Cslib.Quantum.queryCount_compileClassicalQuery`: the generated description makes no oracle
  calls.
* `Cslib.Quantum.gateCount_compileClassicalQuery`: its exact online elementary-gate count.

The reference-preserving final readout equality is the next semantic obligation for this
construction; the count and compiler theorems here are not a security result.

## References

This construction is original infrastructure for the B2 reduction in [HQC2026], Theorem 6.3,
pp. 61--64.
-/

public section

namespace Cslib.Quantum

open Turing.MultiTapeTM
open Turing.MultiTapeTM.Internal
open Turing.MultiTapeTM.Internal.NativeCompiler

/-- The three generated component descriptions and the two independent external input sizes used
by the concrete classical-query linker. `securityParameter` controls only the standard unary
family header; `publicKeyWidth` is the scheme's actual public-key bit width and is not inferred
from that parameter. -/
structure ClassicalQueryLayout where
  /-- Security parameter and complete 3-DQCSD sample-word length. -/
  input : OracleInputSize
  /-- Actual public-key prefix width in the complete sample word. -/
  publicKeyWidth : ℕ
  /-- First adversary-stage description, specialized to the public-key prefix. -/
  first : OracleCircuitDescription
  /-- Reversible service description, specialized to the complete sample word. -/
  service : OracleCircuitDescription
  /-- Second adversary-stage description, specialized to the ciphertext suffix. -/
  second : OracleCircuitDescription

/-- Standard nested-pair encoding of a classical-query layout, in field order: the oracle input
sizes (security parameter and classical length in unary), the unary public-key width, then the
first-stage, service and second-stage descriptions. Each structure-field boundary uses the
standard outer framing supplied by `encPair`. -/
enc_structure encClassicalQueryLayout : ClassicalQueryLayout where
  input : encOracleInputSize, publicKeyWidth : encUnary,
  first : encOracleCircuitDescription, service : encOracleCircuitDescription,
  second : encOracleCircuitDescription

namespace ClassicalQueryLayout

/-- Width of the ciphertext suffix after the actual public-key prefix is removed. -/
@[expose] def ciphertextWidth (layout : ClassicalQueryLayout) : ℕ :=
  layout.input.classicalInputLength - layout.publicKeyWidth

/-- Complete encoded family-input prefix occupied by the security header and sample word. -/
@[expose] def fullInputWidth (layout : ClassicalQueryLayout) : ℕ :=
  2 * layout.input.securityParameter + 1 + layout.input.classicalInputLength

/-- Encoded first-stage input prefix occupied by the security header and actual public key. -/
@[expose] def firstInputWidth (layout : ClassicalQueryLayout) : ℕ :=
  2 * layout.input.securityParameter + 1 + layout.publicKeyWidth

/-- Encoded second-stage input prefix occupied by the security header and ciphertext. -/
@[expose] def secondInputWidth (layout : ClassicalQueryLayout) : ℕ :=
  2 * layout.input.securityParameter + 1 + layout.ciphertextWidth

/-- First discarded record holding the measured first-stage request. -/
@[expose] def requestBase (layout : ClassicalQueryLayout) : ℕ :=
  layout.first.width + layout.ciphertextWidth

/-- Original Hadamard seed supplied to the reversible service. -/
@[expose] def hiddenWire (layout : ClassicalQueryLayout) : ℕ :=
  layout.requestBase + layout.first.outputWidth

/-- Beginning of the fresh reversible-service register. -/
@[expose] def serviceBase (layout : ClassicalQueryLayout) : ℕ :=
  layout.hiddenWire + 1

/-- Retained full-reply record, with hidden bit first and ciphertext immediately following it. -/
@[expose] def replyBase (layout : ClassicalQueryLayout) : ℕ :=
  layout.serviceBase + layout.service.width

/-- Beginning of the fresh second-stage register. -/
@[expose] def secondBase (layout : ClassicalQueryLayout) : ℕ :=
  layout.replyBase + 1 + layout.ciphertextWidth

/-- Complete active-register width of the linked construction. -/
@[expose] def width (layout : ClassicalQueryLayout) : ℕ :=
  layout.secondBase + layout.second.width

/-- Sparse first-stage embedding: the public prefix is fixed, while every later first-stage wire
skips the hidden challenge-mask suffix. -/
@[expose] def firstWire (layout : ClassicalQueryLayout) (wire : ℕ) : ℕ :=
  if wire < layout.firstInputWidth then wire else wire + layout.ciphertextWidth

/-- Service embedding into its fresh register, with the request and hidden seed supplied through
the service's logical quantum-input interval. -/
@[expose] def serviceWire (layout : ClassicalQueryLayout) (wire : ℕ) : ℕ :=
  if wire < layout.fullInputWidth then layout.serviceBase + wire
  else
    let offset := wire - layout.fullInputWidth
    if offset < layout.first.outputWidth + 1 then layout.requestBase + offset
    else layout.serviceBase + wire

/-- Second-stage embedding: fresh classical input and ancillas surround a noncontiguous view of
the complete saved first-stage register. -/
@[expose] def secondWire (layout : ClassicalQueryLayout) (wire : ℕ) : ℕ :=
  if wire < layout.secondInputWidth then
    layout.secondBase + wire
  else
    let offset := wire - layout.secondInputWidth
    if offset < layout.first.width then layout.firstWire offset
    else layout.secondBase + wire

/-- The sparse first-stage embedding cannot expose any wire of the hidden sample suffix. Images
before the split stay in the public prefix; all later images begin after the complete global input.
This is the register-level reason the choose stage receives only the public key. -/
theorem firstWire_lt_firstInputWidth_or_fullInputWidth_le (layout : ClassicalQueryLayout)
    (hpublic : layout.publicKeyWidth ≤ layout.input.classicalInputLength) (wire : ℕ) :
    layout.firstWire wire < layout.firstInputWidth ∨
      layout.fullInputWidth ≤ layout.firstWire wire := by
  change
    (if wire < 2 * layout.input.securityParameter + 1 + layout.publicKeyWidth then wire
      else wire + (layout.input.classicalInputLength - layout.publicKeyWidth)) <
        2 * layout.input.securityParameter + 1 + layout.publicKeyWidth ∨
    2 * layout.input.securityParameter + 1 + layout.input.classicalInputLength ≤
      (if wire < 2 * layout.input.securityParameter + 1 + layout.publicKeyWidth then wire
        else wire + (layout.input.classicalInputLength - layout.publicKeyWidth))
  by_cases h : wire < 2 * layout.input.securityParameter + 1 + layout.publicKeyWidth
  · simp [h]
  · simp [h]
    omega

/-- The logical hidden-bit quantum input of the service is exactly the original Hadamard wire. -/
theorem serviceWire_hidden (layout : ClassicalQueryLayout) :
    layout.serviceWire (layout.fullInputWidth + layout.first.outputWidth) =
      layout.hiddenWire := by
  simp [serviceWire, fullInputWidth, hiddenWire, requestBase]

/-- No logical wire of the second stage maps into the retained full-reply record. Thus the guess
stage receives the copied ciphertext and saved first-stage register, while the complete reply
remains outside its image. -/
theorem secondWire_ne_replyBlock (layout : ClassicalQueryLayout) (wire : ℕ)
    (replyWire : Fin (1 + layout.ciphertextWidth)) :
    layout.secondWire wire ≠ layout.replyBase + replyWire := by
  by_cases hinput : wire < layout.secondInputWidth
  · rw [secondWire, ite_eq_left hinput]
    simp only [secondBase, replyBase, serviceBase, hiddenWire, requestBase]
    omega
  · by_cases hsaved : wire - layout.secondInputWidth < layout.first.width
    · rw [secondWire, ite_eq_right hinput, ite_eq_left hsaved]
      by_cases hprefix : wire - layout.secondInputWidth < layout.firstInputWidth
      · rw [firstWire, ite_eq_left hprefix]
        simp only [replyBase, serviceBase, hiddenWire, requestBase]
        omega
      · rw [firstWire, ite_eq_right hprefix]
        simp only [replyBase, serviceBase, hiddenWire, requestBase]
        omega
    · rw [secondWire, ite_eq_right hinput, ite_eq_right hsaved]
      simp only [secondBase, replyBase, serviceBase, hiddenWire, requestBase]
      omega

private theorem firstWire_lt_requestBase (layout : ClassicalQueryLayout) {wire : ℕ}
    (hwire : wire < layout.first.width) : layout.firstWire wire < layout.requestBase := by
  by_cases hprefix : wire < layout.firstInputWidth
  · rw [firstWire, ite_eq_left hprefix]
    simp only [requestBase, ciphertextWidth]
    omega
  · rw [firstWire, ite_eq_right hprefix]
    simp only [requestBase]
    omega

/-- Embed the first-stage register into the complete controller register. This is the sparse
placement used by the relabelled first-stage instruction block. -/
@[expose] def firstEmbedding (layout : ClassicalQueryLayout) :
    Fin layout.first.width ↪ Fin layout.width where
  toFun wire := ⟨layout.firstWire wire, by
    have hwire := firstWire_lt_requestBase layout wire.isLt
    simp only [width, secondBase, replyBase, serviceBase, hiddenWire]
    omega⟩
  inj' := fun left right heq => Fin.ext <| by
    have heq := congrArg Fin.val heq
    by_cases hleft : left < layout.firstInputWidth <;>
      by_cases hright : right < layout.firstInputWidth <;>
      simp [firstWire, hleft, hright] at heq <;> omega

/-- Every service-register wire lies strictly before the retained full-reply record. -/
theorem serviceEmbedding_lt_replyBase (layout : ClassicalQueryLayout)
    (wire : Fin layout.service.width) :
    layout.serviceWire wire < layout.replyBase := by
  by_cases hinput : wire < layout.fullInputWidth
  · simp [serviceWire, hinput, replyBase]
  · by_cases hrequest :
        wire - layout.fullInputWidth < layout.first.outputWidth + 1
    · simp [serviceWire, hinput, hrequest, replyBase, serviceBase, hiddenWire]
      omega
    · simp [serviceWire, hinput, hrequest, replyBase]

/-- Embed the service register into the complete controller register, sharing the saved sample,
request and hidden-bit coordinates selected by `serviceWire`. -/
@[expose] def serviceEmbedding (layout : ClassicalQueryLayout) :
    Fin layout.service.width ↪ Fin layout.width where
  toFun wire := ⟨layout.serviceWire wire, by
    have hwire := layout.serviceEmbedding_lt_replyBase wire
    simp only [width, secondBase]
    omega⟩
  inj' := fun left right heq => Fin.ext <| by
    have heq := congrArg Fin.val heq
    by_cases hleftInput : left < layout.fullInputWidth
    · by_cases hrightInput : right < layout.fullInputWidth
      · simp only [serviceWire, hleftInput, hrightInput, ↓reduceIte] at heq
        omega
      · by_cases hrightRequest :
            right - layout.fullInputWidth < layout.first.outputWidth + 1
        · simp only [serviceWire, hleftInput, hrightInput, hrightRequest, ↓reduceIte,
            serviceBase, hiddenWire] at heq
          omega
        · simp only [serviceWire, hleftInput, hrightInput, hrightRequest, ↓reduceIte] at heq
          omega
    · by_cases hleftRequest :
          left - layout.fullInputWidth < layout.first.outputWidth + 1
      · by_cases hrightInput : right < layout.fullInputWidth
        · simp only [serviceWire, hleftInput, hleftRequest, hrightInput, ↓reduceIte,
            serviceBase, hiddenWire] at heq
          omega
        · by_cases hrightRequest :
              right - layout.fullInputWidth < layout.first.outputWidth + 1
          · simp only [serviceWire, hleftInput, hleftRequest, hrightInput, hrightRequest,
              ↓reduceIte] at heq
            omega
          · simp only [serviceWire, hleftInput, hleftRequest, hrightInput, hrightRequest,
              ↓reduceIte, serviceBase, hiddenWire] at heq
            omega
      · by_cases hrightInput : right < layout.fullInputWidth
        · simp only [serviceWire, hleftInput, hleftRequest, hrightInput, ↓reduceIte] at heq
          omega
        · by_cases hrightRequest :
              right - layout.fullInputWidth < layout.first.outputWidth + 1
          · simp only [serviceWire, hleftInput, hleftRequest, hrightInput, hrightRequest,
              ↓reduceIte, serviceBase, hiddenWire] at heq
            omega
          · simp only [serviceWire, hleftInput, hleftRequest, hrightInput, hrightRequest,
              ↓reduceIte] at heq
            omega

/-- Embed the second-stage register into the complete controller register, sharing the saved
first-stage state while keeping the retained reply record outside its image. -/
@[expose] def secondEmbedding (layout : ClassicalQueryLayout) :
    Fin layout.second.width ↪ Fin layout.width :=
  { toFun := fun wire => ⟨layout.secondWire wire, by
      by_cases hinput : wire < layout.secondInputWidth
      · simp [secondWire, hinput, width]
      · by_cases hsaved : wire - layout.secondInputWidth < layout.first.width
        · have hrange := firstWire_lt_requestBase layout hsaved
          simp only [secondWire, hinput, hsaved, ↓reduceIte, width, secondBase, replyBase,
            serviceBase, hiddenWire]
          omega
        · simp only [secondWire, hinput, hsaved, ↓reduceIte, width]
          exact Nat.add_lt_add_left wire.isLt layout.secondBase
          ⟩
    inj' := fun left right heq => Fin.ext <| by
      have heq := congrArg Fin.val heq
      by_cases hleftInput : left < layout.secondInputWidth
      · by_cases hrightInput : right < layout.secondInputWidth
        · simp only [secondWire, hleftInput, hrightInput, ↓reduceIte] at heq
          omega
        · by_cases hrightSaved : right - layout.secondInputWidth < layout.first.width
          · have hrightRange := firstWire_lt_requestBase layout hrightSaved
            simp only [secondWire, hleftInput, hrightInput, hrightSaved, ↓reduceIte,
              secondBase, replyBase, serviceBase, hiddenWire] at heq
            omega
          · simp only [secondWire, hleftInput, hrightInput, hrightSaved, ↓reduceIte] at heq
            omega
      · by_cases hleftSaved : left - layout.secondInputWidth < layout.first.width
        · by_cases hrightInput : right < layout.secondInputWidth
          · have hleftRange := firstWire_lt_requestBase layout hleftSaved
            simp only [secondWire, hleftInput, hleftSaved, hrightInput, ↓reduceIte,
              secondBase, replyBase, serviceBase, hiddenWire] at heq
            omega
          · by_cases hrightSaved : right - layout.secondInputWidth < layout.first.width
            · have hfirstEq :
                  layout.firstWire (left - layout.secondInputWidth) =
                    layout.firstWire (right - layout.secondInputWidth) := by
                simpa only [secondWire, hleftInput, hleftSaved, hrightInput, hrightSaved,
                  ↓reduceIte] using heq
              have hoffset : left - layout.secondInputWidth =
                  right - layout.secondInputWidth := by
                have hembed : layout.firstEmbedding
                    ⟨left - layout.secondInputWidth, hleftSaved⟩ =
                    layout.firstEmbedding
                      ⟨right - layout.secondInputWidth, hrightSaved⟩ := by
                  apply Fin.ext
                  exact hfirstEq
                exact congrArg Fin.val (layout.firstEmbedding.injective hembed)
              omega
            · have hleftRange := firstWire_lt_requestBase layout hleftSaved
              simp only [secondWire, hleftInput, hleftSaved, hrightInput, hrightSaved,
                ↓reduceIte, secondBase, replyBase, serviceBase, hiddenWire] at heq
              omega
        · by_cases hrightInput : right < layout.secondInputWidth
          · simp only [secondWire, hleftInput, hleftSaved, hrightInput, ↓reduceIte] at heq
            omega
          · by_cases hrightSaved : right - layout.secondInputWidth < layout.first.width
            · have hrightRange := firstWire_lt_requestBase layout hrightSaved
              simp only [secondWire, hleftInput, hleftSaved, hrightInput, hrightSaved,
                ↓reduceIte, secondBase, replyBase, serviceBase, hiddenWire] at heq
              omega
            · simp only [secondWire, hleftInput, hleftSaved, hrightInput, hrightSaved,
                ↓reduceIte] at heq
              omega }

/-- Component-shape contract for the concrete classical-query linker. It separates the actual
public-key width from the security header, checks each description at the auxiliary length it
receives, and states exactly which registers cross the two interaction boundaries. -/
structure Compatible (layout : ClassicalQueryLayout) : Prop where
  /-- The public-key prefix is contained in the complete 3-DQCSD sample word. -/
  publicKey_le : layout.publicKeyWidth ≤ layout.input.classicalInputLength
  /-- The first stage is valid on exactly the public-key prefix. -/
  first_wellFormed : layout.first.WellFormed
    ⟨layout.input.securityParameter, layout.publicKeyWidth⟩
  /-- The reversible service is valid on the complete sample word. -/
  service_wellFormed : layout.service.WellFormed layout.input
  /-- The second stage is valid on exactly the ciphertext suffix. -/
  second_wellFormed : layout.second.WellFormed
    ⟨layout.input.securityParameter, layout.ciphertextWidth⟩
  /-- The first stage has no supplied quantum input. -/
  first_quantumInputWidth : layout.first.quantumInputWidth = 0
  /-- Its measured request remains in the public input prefix, so its copied record is contiguous
  and does not touch a hidden challenge-mask wire. -/
  first_output_le : layout.first.outputWidth ≤ layout.firstInputWidth
  /-- The service receives the copied request followed by the hidden bit. -/
  service_quantumInputWidth :
    layout.service.quantumInputWidth = layout.first.outputWidth + 1
  /-- The service returns exactly one ciphertext suffix. -/
  service_outputWidth : layout.service.outputWidth = layout.ciphertextWidth
  /-- The second stage receives the complete saved first-stage register. -/
  second_quantumInputWidth : layout.second.quantumInputWidth = layout.first.width
  /-- The second stage exposes at least its first guess bit. -/
  second_outputWidth : 1 ≤ layout.second.outputWidth

end ClassicalQueryLayout

/-- Compile one HQC-shaped classical interaction boundary into a query-free circuit.

The component descriptions are generated for the same security parameter at the actual
public-key width, the complete sample length and `sampleLength - publicKeyWidth`, respectively.
Shape hypotheses tying their quantum inputs and outputs to the request, service and saved-register
widths are imposed by the well-formed family constructor and semantic theorem, not silently
assumed by this total description function. -/
@[expose] def compileClassicalQuery (layout : ClassicalQueryLayout) : OracleCircuitDescription :=
  let gates : List GateCode → OracleCircuit :=
    fun codes => codes.map fun code => OracleGateCode.gate (false, code)
  let relabel : OracleCircuit → (ℕ → ℕ) → OracleCircuit := fun instructions wireMap =>
    instructions.zeroOraclePhaseCodes.map fun code =>
      OracleGateCode.gate (PhaseGateCode.relabel wireMap code)
  { width := layout.width
    queryWidth := 0
    responseWidth := 0
    quantumInputWidth := 0
    outputWidth := 1
    instructions :=
    gates (GateCode.blockCopyCodes 0
      layout.serviceBase layout.fullInputWidth) ++
    gates (GateCode.blockCopyCodes 0
      layout.secondBase (2 * layout.input.securityParameter + 1)) ++
    relabel layout.first.instructions layout.firstWire ++
    gates (GateCode.blockCopyCodes 0
      layout.requestBase layout.first.outputWidth) ++
    gates (hadamardCodes
      layout.hiddenWire 1) ++
    gates (GateCode.blockCopyCodes
      layout.hiddenWire layout.replyBase 1) ++
    relabel layout.service.instructions layout.serviceWire ++
    gates (GateCode.blockCopyCodes
      layout.serviceBase (layout.replyBase + 1) layout.ciphertextWidth) ++
    gates (GateCode.blockCopyCodes
      (layout.replyBase + 1)
      (layout.secondBase + (2 * layout.input.securityParameter + 1))
      layout.ciphertextWidth) ++
    relabel layout.second.instructions layout.secondWire ++
    gates (GateCode.prefixSwapCodes
      layout.secondBase 1) ++
    gates (GateCode.compareBits layout.replyBase 0) }

private theorem wellFormed_gateInstructions {width : ℕ} {codes : List GateCode}
    (hcodes : ∀ code ∈ codes, code.WellFormed width) :
    ∀ instruction ∈ codes.map (fun code => OracleGateCode.gate (false, code)),
      instruction.WellFormed 0 0 width := by
  intro instruction hinstruction
  obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hinstruction
  simpa only [OracleGateCode.WellFormed, PhaseGateCode.WellFormed] using hcodes code hcode

private theorem wellFormed_zeroOracleRelabel {input : OracleInputSize}
    {description : OracleCircuitDescription} (hdescription : description.WellFormed input)
    {width : ℕ} (embedding : Fin description.width ↪ Fin width) (wireMap : ℕ → ℕ)
    (hwireMap : ∀ wire : Fin description.width, wireMap wire = (embedding wire : ℕ)) :
    ∀ instruction ∈ description.instructions.zeroOraclePhaseCodes.map
        (fun code => OracleGateCode.gate (PhaseGateCode.relabel wireMap code)),
      instruction.WellFormed 0 0 width := by
  intro instruction hinstruction
  obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hinstruction
  apply PhaseGateCode.WellFormed.relabel (e := embedding) (ρ := wireMap) (hρ := hwireMap)
  exact OracleCircuit.wellFormed_zeroOraclePhaseCodes hdescription.instructions code hcode

/-- A compatible component triple produces a valid query-free controller description. This is
the construction's first structural correctness property: every relabelled component gate and
every interaction-boundary gate fits the one global register. -/
theorem ClassicalQueryLayout.Compatible.wellFormed_compileClassicalQuery
    {layout : ClassicalQueryLayout} (h : layout.Compatible) :
    (compileClassicalQuery layout).WellFormed layout.input := by
  have hfirstInput := h.first_wellFormed.input_le
  have hserviceInput := h.service_wellFormed.input_le
  have hsecondInput := h.second_wellFormed.input_le
  change layout.firstInputWidth + layout.first.quantumInputWidth ≤ layout.first.width at hfirstInput
  change layout.fullInputWidth + layout.service.quantumInputWidth ≤
    layout.service.width at hserviceInput
  change 2 * layout.input.securityParameter + 1 + layout.ciphertextWidth +
    layout.second.quantumInputWidth ≤ layout.second.width at hsecondInput
  rw [h.first_quantumInputWidth, Nat.add_zero] at hfirstInput
  rw [h.second_quantumInputWidth] at hsecondInput
  simp only [ClassicalQueryLayout.firstInputWidth] at hfirstInput
  simp only [ClassicalQueryLayout.fullInputWidth] at hserviceInput
  have hpublic := h.publicKey_le
  have hfirstOutput := h.first_output_le
  simp only [ClassicalQueryLayout.firstInputWidth] at hfirstOutput
  have hsecondOne := h.second_outputWidth
  constructor
  · change layout.fullInputWidth ≤ layout.width
    simp only [ClassicalQueryLayout.fullInputWidth, ClassicalQueryLayout.width,
      ClassicalQueryLayout.secondBase, ClassicalQueryLayout.replyBase,
      ClassicalQueryLayout.serviceBase, ClassicalQueryLayout.hiddenWire,
      ClassicalQueryLayout.requestBase, ClassicalQueryLayout.ciphertextWidth] at hfirstInput ⊢
    omega
  · change 0 + 0 ≤ layout.width
    omega
  · change 1 ≤ layout.width
    have hsecondOutput := h.second_wellFormed.output_le
    simp only [ClassicalQueryLayout.width]
    omega
  · intro instruction hinstruction
    have hcopyServiceInput : GateCode.IsClassical layout.width
        (GateCode.blockCopyCodes 0 layout.serviceBase layout.fullInputWidth) := by
      apply GateCode.isClassical_blockCopyCodes
      · left
        simp only [ClassicalQueryLayout.serviceBase, ClassicalQueryLayout.hiddenWire,
          ClassicalQueryLayout.requestBase, ClassicalQueryLayout.fullInputWidth,
          ClassicalQueryLayout.ciphertextWidth]
        omega
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
          ClassicalQueryLayout.replyBase, ClassicalQueryLayout.serviceBase,
          ClassicalQueryLayout.hiddenWire, ClassicalQueryLayout.requestBase,
          ClassicalQueryLayout.fullInputWidth, ClassicalQueryLayout.ciphertextWidth]
        omega
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
          ClassicalQueryLayout.replyBase, ClassicalQueryLayout.fullInputWidth]
        omega
    have hcopySecondHeader : GateCode.IsClassical layout.width
        (GateCode.blockCopyCodes 0 layout.secondBase
          (2 * layout.input.securityParameter + 1)) := by
      apply GateCode.isClassical_blockCopyCodes
      · left
        simp only [ClassicalQueryLayout.secondBase, ClassicalQueryLayout.replyBase,
          ClassicalQueryLayout.serviceBase, ClassicalQueryLayout.hiddenWire,
          ClassicalQueryLayout.requestBase]
        omega
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
        omega
      · simp only [ClassicalQueryLayout.width]
        omega
    have hcopyRequest : GateCode.IsClassical layout.width
        (GateCode.blockCopyCodes 0 layout.requestBase layout.first.outputWidth) := by
      apply GateCode.isClassical_blockCopyCodes
      · left
        simp only [ClassicalQueryLayout.requestBase]
        omega
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
          ClassicalQueryLayout.replyBase, ClassicalQueryLayout.serviceBase,
          ClassicalQueryLayout.hiddenWire, ClassicalQueryLayout.requestBase]
        omega
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
          ClassicalQueryLayout.replyBase, ClassicalQueryLayout.serviceBase,
          ClassicalQueryLayout.hiddenWire]
        omega
    have hhiddenFit : layout.hiddenWire + 1 ≤ layout.width := by
      simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
        ClassicalQueryLayout.replyBase, ClassicalQueryLayout.serviceBase]
      omega
    have hcopyHidden : GateCode.IsClassical layout.width
        (GateCode.blockCopyCodes layout.hiddenWire layout.replyBase 1) := by
      apply GateCode.isClassical_blockCopyCodes
      · left
        simp only [ClassicalQueryLayout.replyBase, ClassicalQueryLayout.serviceBase]
        omega
      · exact hhiddenFit
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
        omega
    have hcopyServiceOutput : GateCode.IsClassical layout.width
        (GateCode.blockCopyCodes layout.serviceBase (layout.replyBase + 1)
          layout.ciphertextWidth) := by
      have hserviceOutput := h.service_wellFormed.output_le
      rw [h.service_outputWidth] at hserviceOutput
      apply GateCode.isClassical_blockCopyCodes
      · left
        simp only [ClassicalQueryLayout.replyBase]
        omega
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
          ClassicalQueryLayout.replyBase]
        omega
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
        omega
    have hcopySecondCiphertext : GateCode.IsClassical layout.width
        (GateCode.blockCopyCodes (layout.replyBase + 1)
          (layout.secondBase + (2 * layout.input.securityParameter + 1))
          layout.ciphertextWidth) := by
      apply GateCode.isClassical_blockCopyCodes
      · left
        simp only [ClassicalQueryLayout.secondBase]
        omega
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
        omega
      · simp only [ClassicalQueryLayout.width]
        omega
    have hmoveGuess : GateCode.IsClassical layout.width
        (GateCode.prefixSwapCodes layout.secondBase 1) := by
      have hsecondOutput := h.second_wellFormed.output_le
      apply GateCode.isClassical_prefixSwapCodes
      · simp only [ClassicalQueryLayout.secondBase, ClassicalQueryLayout.replyBase,
          ClassicalQueryLayout.serviceBase, ClassicalQueryLayout.hiddenWire,
          ClassicalQueryLayout.requestBase]
        omega
      · simp only [ClassicalQueryLayout.width]
        omega
    have hcompare : GateCode.IsClassical layout.width
        (GateCode.compareBits layout.replyBase 0) := by
      have hsecondOutput := h.second_wellFormed.output_le
      apply GateCode.isClassical_compareBits
      · simp only [ClassicalQueryLayout.replyBase, ClassicalQueryLayout.serviceBase,
          ClassicalQueryLayout.hiddenWire, ClassicalQueryLayout.requestBase]
        omega
      · simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
        omega
      · simp only [ClassicalQueryLayout.width]
        omega
    have hfirstRelabel := wellFormed_zeroOracleRelabel h.first_wellFormed
      (firstEmbedding layout) layout.firstWire (fun _ => rfl)
    have hserviceRelabel := wellFormed_zeroOracleRelabel h.service_wellFormed
      (serviceEmbedding layout) layout.serviceWire (fun _ => rfl)
    have hsecondRelabel := wellFormed_zeroOracleRelabel h.second_wellFormed
      (secondEmbedding layout) layout.secondWire (fun _ => rfl)
    change instruction ∈
      (GateCode.blockCopyCodes 0 layout.serviceBase layout.fullInputWidth).map
          (fun code => OracleGateCode.gate (false, code)) ++
      (GateCode.blockCopyCodes 0 layout.secondBase
          (2 * layout.input.securityParameter + 1)).map
          (fun code => OracleGateCode.gate (false, code)) ++
      (layout.first.instructions.zeroOraclePhaseCodes.map fun code =>
          OracleGateCode.gate (PhaseGateCode.relabel layout.firstWire code)) ++
      (GateCode.blockCopyCodes 0 layout.requestBase layout.first.outputWidth).map
          (fun code => OracleGateCode.gate (false, code)) ++
      (hadamardCodes layout.hiddenWire 1).map
          (fun code => OracleGateCode.gate (false, code)) ++
      (GateCode.blockCopyCodes layout.hiddenWire layout.replyBase 1).map
          (fun code => OracleGateCode.gate (false, code)) ++
      (layout.service.instructions.zeroOraclePhaseCodes.map fun code =>
          OracleGateCode.gate (PhaseGateCode.relabel layout.serviceWire code)) ++
      (GateCode.blockCopyCodes layout.serviceBase (layout.replyBase + 1)
          layout.ciphertextWidth).map (fun code => OracleGateCode.gate (false, code)) ++
      (GateCode.blockCopyCodes (layout.replyBase + 1)
          (layout.secondBase + (2 * layout.input.securityParameter + 1))
          layout.ciphertextWidth).map (fun code => OracleGateCode.gate (false, code)) ++
      (layout.second.instructions.zeroOraclePhaseCodes.map fun code =>
          OracleGateCode.gate (PhaseGateCode.relabel layout.secondWire code)) ++
      (GateCode.prefixSwapCodes layout.secondBase 1).map
          (fun code => OracleGateCode.gate (false, code)) ++
      (GateCode.compareBits layout.replyBase 0).map
          (fun code => OracleGateCode.gate (false, code)) at hinstruction
    simp only [List.append_assoc] at hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact wellFormed_gateInstructions
        (fun code hcode => (hcopyServiceInput code hcode).2) instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact wellFormed_gateInstructions
        (fun code hcode => (hcopySecondHeader code hcode).2) instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact hfirstRelabel instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact wellFormed_gateInstructions
        (fun code hcode => (hcopyRequest code hcode).2) instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact wellFormed_gateInstructions
        (wellFormed_hadamardCodes hhiddenFit) instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact wellFormed_gateInstructions
        (fun code hcode => (hcopyHidden code hcode).2) instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact hserviceRelabel instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact wellFormed_gateInstructions
        (fun code hcode => (hcopyServiceOutput code hcode).2) instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact wellFormed_gateInstructions
        (fun code hcode => (hcopySecondCiphertext code hcode).2) instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact hsecondRelabel instruction hinstruction
    rcases List.mem_append.mp hinstruction with hinstruction | hinstruction
    · exact wellFormed_gateInstructions
        (fun code hcode => (hmoveGuess code hcode).2) instruction hinstruction
    exact wellFormed_gateInstructions
      (fun code hcode => (hcompare code hcode).2) instruction hinstruction

/-- The compiled classical-query controller is genuinely query-free even when its three input
descriptions contain oracle-query instructions. -/
theorem queryCount_compileClassicalQuery (layout : ClassicalQueryLayout) :
    (compileClassicalQuery layout).instructions.queryCount = 0 := by
  simp [compileClassicalQuery, OracleCircuit.queryCount, OracleGateCode.isQuery]

/-- Exact online elementary-gate count of the compiled controller. Component query instructions
are absent, while every retained component gate and every layout/service-boundary gate is charged
once. -/
theorem gateCount_compileClassicalQuery (layout : ClassicalQueryLayout) :
    (compileClassicalQuery layout).instructions.gateCount =
      layout.first.instructions.gateCount + layout.service.instructions.gateCount +
        layout.second.instructions.gateCount +
      (2 * layout.input.securityParameter + 1 + layout.input.classicalInputLength) +
      (2 * layout.input.securityParameter + 1) + layout.first.outputWidth +
      2 * (layout.input.classicalInputLength - layout.publicKeyWidth) + 7 := by
  have hpartition := OracleCircuit.gateCount_add_queryCount
    (compileClassicalQuery layout).instructions
  rw [queryCount_compileClassicalQuery, Nat.add_zero] at hpartition
  rw [hpartition]
  let gates : List GateCode → OracleCircuit :=
    fun codes => codes.map fun code => OracleGateCode.gate (false, code)
  let relabel : OracleCircuit → (ℕ → ℕ) → OracleCircuit := fun instructions wireMap =>
    instructions.zeroOraclePhaseCodes.map fun code =>
      OracleGateCode.gate (PhaseGateCode.relabel wireMap code)
  change
    (gates (GateCode.blockCopyCodes 0 layout.serviceBase layout.fullInputWidth) ++
      gates (GateCode.blockCopyCodes 0 layout.secondBase
        (2 * layout.input.securityParameter + 1)) ++
      relabel layout.first.instructions layout.firstWire ++
      gates (GateCode.blockCopyCodes 0 layout.requestBase layout.first.outputWidth) ++
      gates (hadamardCodes layout.hiddenWire 1) ++
      gates (GateCode.blockCopyCodes layout.hiddenWire layout.replyBase 1) ++
      relabel layout.service.instructions layout.serviceWire ++
      gates (GateCode.blockCopyCodes layout.serviceBase (layout.replyBase + 1)
        layout.ciphertextWidth) ++
      gates (GateCode.blockCopyCodes (layout.replyBase + 1)
        (layout.secondBase + (2 * layout.input.securityParameter + 1))
        layout.ciphertextWidth) ++
      relabel layout.second.instructions layout.secondWire ++
      gates (GateCode.prefixSwapCodes layout.secondBase 1) ++
      gates (GateCode.compareBits layout.replyBase 0)).length =
        layout.first.instructions.gateCount + layout.service.instructions.gateCount +
          layout.second.instructions.gateCount +
        (2 * layout.input.securityParameter + 1 + layout.input.classicalInputLength) +
        (2 * layout.input.securityParameter + 1) + layout.first.outputWidth +
        2 * (layout.input.classicalInputLength - layout.publicKeyWidth) + 7
  simp [gates, relabel, ClassicalQueryLayout.fullInputWidth,
    ClassicalQueryLayout.ciphertextWidth, GateCode.compareBits, hadamardCodes]
  omega

/-- Retain the complete generator that links three specialized component-description compilers
into `compileClassicalQuery`. The service-input and second-stage adapters are the explicit block
copies assembled above; callers do not supply a separate adapter program or efficiency claim. -/
@[expose] def compileClassicalQueryCompiler
    {publicKeyWidth : OracleInputSize → ℕ}
    {firstFamily serviceFamily secondFamily : OracleInputSize → OracleCircuitDescription}
    (publicKeyWidthCompiler : NativeCompiler publicKeyWidth encOracleInputSize encUnary)
    (firstCompiler : NativeCompiler firstFamily encOracleInputSize encOracleCircuitDescription)
    (serviceCompiler : NativeCompiler serviceFamily encOracleInputSize encOracleCircuitDescription)
    (secondCompiler : NativeCompiler secondFamily encOracleInputSize encOracleCircuitDescription) :
    NativeCompiler
      (fun input => compileClassicalQuery
        ⟨input, publicKeyWidth input, firstFamily input, serviceFamily input, secondFamily input⟩)
      encOracleInputSize encOracleCircuitDescription := by
  let OracleDescriptionFields :=
    ℕ × (ℕ × (ℕ × (ℕ × (ℕ × OracleCircuit))))
  
  let encOracleDescriptionFields : OracleDescriptionFields ↪ List Bool :=
    encPair encUnary
      (encPair encUnary
        (encPair encUnary
          (encPair encUnary (encPair encUnary (encList encOracleGateCode)))))
  
  let oracleDescriptionFields (description : OracleCircuitDescription) :
      OracleDescriptionFields :=
    (description.width,
      (description.queryWidth,
        (description.responseWidth,
          (description.quantumInputWidth,
            (description.outputWidth, description.instructions)))))
  
  let oracleDescriptionFieldsCompiler :
      NativeCompiler oracleDescriptionFields encOracleCircuitDescription
        encOracleDescriptionFields :=
    (identity encOracleCircuitDescription).ofOutputEq fun _ => rfl
  
  let oracleDescriptionWidthCompiler :
      NativeCompiler OracleCircuitDescription.width encOracleCircuitDescription encUnary :=
    (first encUnary
      (encPair encUnary
        (encPair encUnary
          (encPair encUnary (encPair encUnary (encList encOracleGateCode)))))).comp
      oracleDescriptionFieldsCompiler
  
  let oracleDescriptionOutputWidthCompiler :
      NativeCompiler OracleCircuitDescription.outputWidth encOracleCircuitDescription encUnary := by
    let tail₁ := (second encUnary
      (encPair encUnary
        (encPair encUnary
          (encPair encUnary (encPair encUnary (encList encOracleGateCode)))))).comp
      oracleDescriptionFieldsCompiler
    let tail₂ := (second encUnary
      (encPair encUnary
        (encPair encUnary (encPair encUnary (encList encOracleGateCode))))).comp tail₁
    let tail₃ := (second encUnary
      (encPair encUnary (encPair encUnary (encList encOracleGateCode)))).comp tail₂
    let tail₄ := (second encUnary (encPair encUnary (encList encOracleGateCode))).comp tail₃
    exact (first encUnary (encList encOracleGateCode)).comp tail₄
  
  let oracleDescriptionInstructionsCompiler :
      NativeCompiler OracleCircuitDescription.instructions encOracleCircuitDescription
        (encList encOracleGateCode) := by
    let tail₁ := (second encUnary
      (encPair encUnary
        (encPair encUnary
          (encPair encUnary (encPair encUnary (encList encOracleGateCode)))))).comp
      oracleDescriptionFieldsCompiler
    let tail₂ := (second encUnary
      (encPair encUnary
        (encPair encUnary (encPair encUnary (encList encOracleGateCode))))).comp tail₁
    let tail₃ := (second encUnary
      (encPair encUnary (encPair encUnary (encList encOracleGateCode)))).comp tail₂
    let tail₄ := (second encUnary (encPair encUnary (encList encOracleGateCode))).comp tail₃
    exact (second encUnary (encList encOracleGateCode)).comp tail₄
  
  let oracleInputFieldsCompiler :
      NativeCompiler
        (fun input : OracleInputSize => (input.securityParameter, input.classicalInputLength))
        encOracleInputSize (encPair encUnary encUnary) :=
    (identity encOracleInputSize).ofOutputEq fun input => by
      simp [encOracleInputSize_apply, encOracleInputSizeFields]
  
  let oracleInputSecurityCompiler :
      NativeCompiler OracleInputSize.securityParameter encOracleInputSize encUnary :=
    (first encUnary encUnary).comp oracleInputFieldsCompiler
  
  let oracleInputLengthCompiler :
      NativeCompiler OracleInputSize.classicalInputLength encOracleInputSize encUnary :=
    (second encUnary encUnary).comp oracleInputFieldsCompiler
  
  let appendOracleCircuitCompiler {left right : ClassicalQueryLayout → OracleCircuit}
      (leftCompiler : NativeCompiler left encClassicalQueryLayout (encList encOracleGateCode))
      (rightCompiler : NativeCompiler right encClassicalQueryLayout (encList encOracleGateCode)) :
      NativeCompiler (fun input => left input ++ right input) encClassicalQueryLayout
        (encList encOracleGateCode) := by
    let leftRaw : NativeCompiler (fun input => encList encOracleGateCode (left input))
        encClassicalQueryLayout encBits := leftCompiler.ofOutputEq fun _ => rfl
    let rightRaw : NativeCompiler (fun input => encList encOracleGateCode (right input))
        encClassicalQueryLayout encBits := rightCompiler.ofOutputEq fun _ => rfl
    exact (leftRaw.append rightRaw).ofOutputEq fun input => by
      simp only [encList_append, encBits_apply]
  let gateInstructionsCompiler := oracleGateCodeList
  let linker : NativeCompiler compileClassicalQuery encClassicalQueryLayout
      encOracleCircuitDescription := by
    let encDescriptions := encPair encOracleCircuitDescription
      (encPair encOracleCircuitDescription encOracleCircuitDescription)
    let encRest := encPair encUnary encDescriptions
    let layoutFields (layout : ClassicalQueryLayout) :=
      (layout.input,
        (layout.publicKeyWidth, (layout.first, (layout.service, layout.second))))
    have enc_layoutFields (layout : ClassicalQueryLayout) :
        encClassicalQueryLayout layout =
          (encPair encOracleInputSize encRest) (layoutFields layout) := by
      rw [encClassicalQueryLayout_apply]
    let input := (first encOracleInputSize encRest).ofInputEq layoutFields enc_layoutFields
    let rest := (second encOracleInputSize encRest).ofInputEq layoutFields enc_layoutFields
    let publicKeyWidth := (first encUnary encDescriptions).comp rest
    let descriptions := (second encUnary encDescriptions).comp rest
    let firstDescription :=
      (first encOracleCircuitDescription
        (encPair encOracleCircuitDescription encOracleCircuitDescription)).comp descriptions
    let remainingDescriptions :=
      (second encOracleCircuitDescription
        (encPair encOracleCircuitDescription encOracleCircuitDescription)).comp descriptions
    let serviceDescription :=
      (first encOracleCircuitDescription encOracleCircuitDescription).comp remainingDescriptions
    let secondDescription :=
      (second encOracleCircuitDescription encOracleCircuitDescription).comp remainingDescriptions
    let security := oracleInputSecurityCompiler.comp input
    let sampleWidth := oracleInputLengthCompiler.comp input
    let twoSecurity := unaryAdd.comp (security.pair security)
    let one := const encClassicalQueryLayout encUnary 1
    let zero := const encClassicalQueryLayout encUnary 0
    let headerWidth := unaryAdd.comp (twoSecurity.pair one)
    let ciphertextWidth := unarySub.comp (sampleWidth.pair publicKeyWidth)
    let fullInputWidth := unaryAdd.comp (headerWidth.pair sampleWidth)
    let firstInputWidth := unaryAdd.comp (headerWidth.pair publicKeyWidth)
    let secondInputWidth := unaryAdd.comp (headerWidth.pair ciphertextWidth)
    let firstWidth := oracleDescriptionWidthCompiler.comp firstDescription
    let firstOutputWidth := oracleDescriptionOutputWidthCompiler.comp firstDescription
    let serviceWidth := oracleDescriptionWidthCompiler.comp serviceDescription
    let secondWidth := oracleDescriptionWidthCompiler.comp secondDescription
    let firstEnvelope := unaryAdd.comp (firstWidth.pair ciphertextWidth)
    let requestBase := firstEnvelope
    let hiddenWire := unaryAdd.comp (requestBase.pair firstOutputWidth)
    let serviceBase := unaryAdd.comp (hiddenWire.pair one)
    let replyBase := unaryAdd.comp (serviceBase.pair serviceWidth)
    let replyAfterHidden := unaryAdd.comp (replyBase.pair one)
    let secondBase := unaryAdd.comp (replyAfterHidden.pair ciphertextWidth)
    let width := unaryAdd.comp (secondBase.pair secondWidth)
    let wireEncoding := encPair encClassicalQueryLayout encUnary
    let wireContext := first encClassicalQueryLayout encUnary
    let wire := second encClassicalQueryLayout encUnary
    let firstWire : NativeCompiler
        (fun value : ClassicalQueryLayout × ℕ => value.1.firstWire value.2)
        wireEncoding encUnary := by
      let cut := firstInputWidth.comp wireContext
      let shift := ciphertextWidth.comp wireContext
      let beforeCut := unaryLtTest.comp (wire.pair cut)
      let shifted := unaryAdd.comp (wire.pair shift)
      exact (ite beforeCut wire shifted).ofOutputEq fun value => by
        simp only [layoutFields, ClassicalQueryLayout.firstWire,
          ClassicalQueryLayout.firstInputWidth, ClassicalQueryLayout.ciphertextWidth, two_mul]
        by_cases h : value.2 < value.1.input.securityParameter +
            value.1.input.securityParameter + 1 + value.1.publicKeyWidth <;> simp [h]
    let serviceWire : NativeCompiler
        (fun value : ClassicalQueryLayout × ℕ => value.1.serviceWire value.2)
        wireEncoding encUnary := by
      let fullInput := fullInputWidth.comp wireContext
      let request := requestBase.comp wireContext
      let serviceStart := serviceBase.comp wireContext
      let requestWidth := firstOutputWidth.comp wireContext
      let localOne := const wireEncoding encUnary 1
      let requestAndHiddenWidth := unaryAdd.comp (requestWidth.pair localOne)
      let beforeInputEnd := unaryLtTest.comp (wire.pair fullInput)
      let offset := unarySub.comp (wire.pair fullInput)
      let insideRequestAndHidden := unaryLtTest.comp (offset.pair requestAndHiddenWidth)
      let outer := unaryAdd.comp (serviceStart.pair wire)
      let inner := unaryAdd.comp (request.pair offset)
      exact (ite beforeInputEnd outer (ite insideRequestAndHidden inner outer)).ofOutputEq
        fun value => by
          simp only [layoutFields, ClassicalQueryLayout.serviceWire,
            ClassicalQueryLayout.fullInputWidth, ClassicalQueryLayout.serviceBase,
            ClassicalQueryLayout.hiddenWire, ClassicalQueryLayout.requestBase,
            ClassicalQueryLayout.ciphertextWidth, two_mul]
          by_cases hinput : value.2 < value.1.input.securityParameter +
              value.1.input.securityParameter + 1 + value.1.input.classicalInputLength
          · simp [hinput]
          · simp [hinput]
    let secondWire : NativeCompiler
        (fun value : ClassicalQueryLayout × ℕ => value.1.secondWire value.2)
        wireEncoding encUnary := by
      let secondInput := secondInputWidth.comp wireContext
      let firstRegisterWidth := firstWidth.comp wireContext
      let secondStart := secondBase.comp wireContext
      let beforeInputEnd := unaryLtTest.comp (wire.pair secondInput)
      let offset := unarySub.comp (wire.pair secondInput)
      let insideSavedFirst := unaryLtTest.comp (offset.pair firstRegisterWidth)
      let outer := unaryAdd.comp (secondStart.pair wire)
      let inner := firstWire.comp (wireContext.pair offset)
      exact (ite beforeInputEnd outer (ite insideSavedFirst inner outer)).ofOutputEq
        fun value => by
          simp only [layoutFields, ClassicalQueryLayout.secondWire,
            ClassicalQueryLayout.secondInputWidth, ClassicalQueryLayout.ciphertextWidth,
            ClassicalQueryLayout.secondBase, ClassicalQueryLayout.replyBase,
            ClassicalQueryLayout.serviceBase, ClassicalQueryLayout.hiddenWire,
            ClassicalQueryLayout.requestBase, ClassicalQueryLayout.firstWire, two_mul]
          by_cases hinput : value.2 < value.1.input.securityParameter +
              value.1.input.securityParameter + 1 +
                (value.1.input.classicalInputLength - value.1.publicKeyWidth)
          · simp [hinput]
          · by_cases hsaved :
                value.2 - (value.1.input.securityParameter +
                  value.1.input.securityParameter + 1 +
                    (value.1.input.classicalInputLength - value.1.publicKeyWidth)) <
                      value.1.first.width
            · simp [hinput, hsaved]
              rfl
            · simp [hinput, hsaved]
    let firstInstructions := oracleDescriptionInstructionsCompiler.comp firstDescription
    let serviceInstructions := oracleDescriptionInstructionsCompiler.comp serviceDescription
    let secondInstructions := oracleDescriptionInstructionsCompiler.comp secondDescription
    let layoutIdentity := identity encClassicalQueryLayout
    let firstRelabelled :=
      (zeroOracleRelabel
        (wireMap := fun layout wire => layout.firstWire wire)
        encClassicalQueryLayout firstWire).comp
        (layoutIdentity.pair firstInstructions)
    let serviceRelabelled :=
      (zeroOracleRelabel
        (wireMap := fun layout wire => layout.serviceWire wire)
        encClassicalQueryLayout serviceWire).comp
        (layoutIdentity.pair serviceInstructions)
    let secondRelabelled :=
      (zeroOracleRelabel
        (wireMap := fun layout wire => layout.secondWire wire)
        encClassicalQueryLayout secondWire).comp
        (layoutIdentity.pair secondInstructions)
    let copiedServiceInput := gateInstructionsCompiler.comp
      (GateCode.blockCopyCodesCompiler.comp (zero.pair (serviceBase.pair fullInputWidth)))
    let copiedSecondHeader := gateInstructionsCompiler.comp
      (GateCode.blockCopyCodesCompiler.comp (zero.pair (secondBase.pair headerWidth)))
    let copiedRequest := gateInstructionsCompiler.comp
      (GateCode.blockCopyCodesCompiler.comp
        (zero.pair (requestBase.pair firstOutputWidth)))
    let hiddenHadamard := gateInstructionsCompiler.comp
      (GateCode.hadamardCodesCompiler.comp (hiddenWire.pair one))
    let copiedHidden := gateInstructionsCompiler.comp
      (GateCode.blockCopyCodesCompiler.comp
        (hiddenWire.pair (replyBase.pair one)))
    let copiedServiceOutput := gateInstructionsCompiler.comp
      (GateCode.blockCopyCodesCompiler.comp
        (serviceBase.pair (replyAfterHidden.pair ciphertextWidth)))
    let secondCiphertextBase := unaryAdd.comp (secondBase.pair headerWidth)
    let copiedSecondCiphertext := gateInstructionsCompiler.comp
      (GateCode.blockCopyCodesCompiler.comp
        (replyAfterHidden.pair (secondCiphertextBase.pair ciphertextWidth)))
    let movedGuess := gateInstructionsCompiler.comp
      (GateCode.prefixSwapCodesCompiler.comp (secondBase.pair one))
    let comparedGuess := gateInstructionsCompiler.comp
      (GateCode.compareBitsCompiler.comp (replyBase.pair zero))
    let instructions₁ := appendOracleCircuitCompiler copiedServiceInput copiedSecondHeader
    let instructions₂ := appendOracleCircuitCompiler instructions₁ firstRelabelled
    let instructions₃ := appendOracleCircuitCompiler instructions₂ copiedRequest
    let instructions₄ := appendOracleCircuitCompiler instructions₃ hiddenHadamard
    let instructions₅ := appendOracleCircuitCompiler instructions₄ copiedHidden
    let instructions₆ := appendOracleCircuitCompiler instructions₅ serviceRelabelled
    let instructions₇ := appendOracleCircuitCompiler instructions₆ copiedServiceOutput
    let instructions₈ := appendOracleCircuitCompiler instructions₇ copiedSecondCiphertext
    let instructions₉ := appendOracleCircuitCompiler instructions₈ secondRelabelled
    let instructions₁₀ := appendOracleCircuitCompiler instructions₉ movedGuess
    let instructions := appendOracleCircuitCompiler instructions₁₀ comparedGuess
    let fields := width.pair
      (zero.pair (zero.pair (zero.pair (one.pair instructions))))
    exact fields.ofOutputEq fun layout => by
      simp [layoutFields, compileClassicalQuery, encOracleCircuitDescription_apply,
        encOracleCircuitDescriptionFields,
        ClassicalQueryLayout.width, ClassicalQueryLayout.requestBase,
        ClassicalQueryLayout.hiddenWire, ClassicalQueryLayout.serviceBase,
        ClassicalQueryLayout.replyBase, ClassicalQueryLayout.secondBase,
        ClassicalQueryLayout.fullInputWidth, ClassicalQueryLayout.ciphertextWidth,
        List.append_assoc, two_mul]
  let layoutFields :=
    (identity encOracleInputSize).pair
      (publicKeyWidthCompiler.pair
        (firstCompiler.pair (serviceCompiler.pair secondCompiler)))
  let layoutCompiler : NativeCompiler
      (fun input =>
        ClassicalQueryLayout.mk input (publicKeyWidth input) (firstFamily input)
          (serviceFamily input) (secondFamily input))
      encOracleInputSize encClassicalQueryLayout :=
    layoutFields.ofOutputEq fun input => by
      rw [encClassicalQueryLayout_apply]
      rfl
  exact linker.comp layoutCompiler

end Cslib.Quantum
