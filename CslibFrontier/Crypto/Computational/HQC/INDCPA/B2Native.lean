/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.ClassicalQuery.Semantics
public import CslibFrontier.Crypto.Computational.HQC.INDCPA.B2Service
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Native query-free controller for the HQC B2 reduction

The B2 reduction receives the complete `3 * n + codeLen` truncated-syndrome word.  Its first
native stage sees exactly the two `n`-bit public blocks, the reversible service receives the full
word together with the two-message request and hidden bit, and the second stage sees exactly the
`n + codeLen` ciphertext plus the complete saved first-stage register.

`b2ClassicalQueryLayout` instantiates the shared query-free controller with those exact component
descriptions.  Its compatibility theorem derives the service shape and validity from the actual
`b2ServiceDescription`; callers provide only the two adversary stages' admitted input/output
shapes and the elementary bound placing the two-message output inside the first stage's classical
prefix.

This module still uses fixed ideal parameters `P` and one installed Boolean encoder.  It does not
supply the concrete NIST concatenated encoder, a growing parameter/encoder-family generator, the
full native success-law equality, or a QPT security theorem.

## Main definitions

* `Cslib.Crypto.HQC.b2ClassicalQueryLayout`: the exact component/register layout of the native
  query-free B2 controller.

## Main results

* `Cslib.Crypto.HQC.compatible_b2ClassicalQueryLayout`: the actual HQC service and admitted native
  stage shapes satisfy every shared controller compatibility condition.
* `Cslib.Crypto.HQC.initialPrefixBranch_b2ServiceInput`: every actual prefix branch is the
  service input for its own two messages and hidden bit, the initialized reply, and the retained
  physical complement.
* `Cslib.Crypto.HQC.matrix_b2ServiceBlock_initializedInput_withReference`: the actual embedded
  service block, on its initialized input, coherently records its complete reversible environment
  while retaining every other controller wire and an arbitrary reference.
* `Cslib.Crypto.HQC.matrix_b2ServiceReplyCopy_initializedInput`: the actual embedded service
  followed by its physical ciphertext copy produces the retained hidden-bit-and-ciphertext reply
  while preserving every other controller wire.
* `Cslib.Crypto.HQC.matrix_b2ReplyCopySecondStage_withReference`: the actual reply-to-input copy
  and erased second stage run on the retained ciphertext and saved first-stage memory while
  acting as the identity on the protected hidden bit and an arbitrary external reference.
* `Cslib.Crypto.HQC.partialTraceLeft_b2ServiceEnvironment_fullReply`: discarding the actual
  reversible service environment traces out the complete message-pair-and-hidden-bit request and
  groups the remaining state by complete hidden-bit-and-ciphertext reply.

## References

This retained controller is original formalization infrastructure for [HQC2026], Theorem 6.3,
pp. 61--64.
-/

public section

namespace Cslib.Crypto.HQC

open Cslib.Quantum
open Cslib.Quantum.GateCode
open Circuits Circuits.Boolean
open Matrix Finset
open scoped Kronecker
open Turing.MultiTapeTM

/-- Exact shared-controller layout of the fixed-parameter native B2 reduction.  The first stage
receives the two public syndrome blocks; the second receives the remaining first-value and
masked-second-value ciphertext blocks. -/
@[expose] def b2ClassicalQueryLayout (P : PKEParams)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (first second : UniformOracleCircuitFamily) (securityParameter : ℕ) :
    ClassicalQueryLayout :=
  { input := ⟨securityParameter, 3 * P.n + P.codeLen⟩
    publicKeyWidth := 2 * P.n
    first := first.description securityParameter (2 * P.n)
    service := b2ServiceDescription P securityParameter encoder
    second := second.description securityParameter (P.n + P.codeLen) }

/-- The actual fixed-parameter B2 service and two admitted native stages satisfy the complete
shared-controller shape contract.  In particular, the choose stage receives only the public-key
projection, the guess stage receives all saved first-stage qubits but not the protected hidden
bit, and the service emits exactly one HQC ciphertext. -/
theorem compatible_b2ClassicalQueryLayout (P : PKEParams)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (first second : UniformOracleCircuitFamily) (securityParameter : ℕ)
    (hfirstInput :
      (first.description securityParameter (2 * P.n)).quantumInputWidth = 0)
    (hfirstOutput :
      (first.description securityParameter (2 * P.n)).outputWidth = 2 * P.k)
    (hmessagesFit : 2 * P.k ≤ 2 * securityParameter + 1 + 2 * P.n)
    (hsecondInput :
      (second.description securityParameter (P.n + P.codeLen)).quantumInputWidth =
        (first.description securityParameter (2 * P.n)).width)
    (hsecondOutput :
      1 ≤ (second.description securityParameter (P.n + P.codeLen)).outputWidth) :
    (b2ClassicalQueryLayout P encoder first second securityParameter).Compatible := by
  let layout := b2ClassicalQueryLayout P encoder first second securityParameter
  have hciphertext : layout.ciphertextWidth = P.n + P.codeLen := by
    simp only [layout, b2ClassicalQueryLayout, ClassicalQueryLayout.ciphertextWidth]
    omega
  refine
    { publicKey_le := by
        simp only [b2ClassicalQueryLayout]
        omega
      first_wellFormed := first.wellFormed securityParameter (2 * P.n)
      service_wellFormed := wellFormed_b2ServiceDescription P securityParameter encoder
      second_wellFormed := by
        change layout.second.WellFormed
          ⟨layout.input.securityParameter, layout.ciphertextWidth⟩
        rw [hciphertext]
        exact second.wellFormed securityParameter (P.n + P.codeLen)
      first_quantumInputWidth := hfirstInput
      first_output_le := by
        simp only [b2ClassicalQueryLayout, ClassicalQueryLayout.firstInputWidth,
          hfirstOutput]
        exact hmessagesFit
      service_quantumInputWidth := by
        simp only [b2ClassicalQueryLayout,
          b2ServiceDescription_quantumInputWidth, hfirstOutput]
      service_outputWidth := by
        change (b2ServiceDescription P securityParameter encoder).outputWidth =
          layout.ciphertextWidth
        rw [b2ServiceDescription_outputWidth]
        exact hciphertext.symm
      second_quantumInputWidth := hsecondInput
      second_outputWidth := hsecondOutput }

/-- Each coherent prefix branch is an actual initialized HQC service input, the matching
hidden-bit/zero-ciphertext reply, and the untouched physical complement. The two messages are
read from this branch's first-stage output, so this identity also applies across distinct
message requests when the branch sum is converted to a density matrix. -/
theorem initialPrefixBranch_b2ServiceInput (P : PKEParams)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (first second : UniformOracleCircuitFamily) (securityParameter : ℕ)
    (h : (b2ClassicalQueryLayout P encoder first second securityParameter).Compatible)
    (houtput : (first.description securityParameter (2 * P.n)).outputWidth = 2 * P.k)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (z : Fin (first.description securityParameter (2 * P.n)).width → Bool)
    (bit : Fin 1 → Bool) :
    let layout := b2ClassicalQueryLayout P encoder first second securityParameter
    let hwidth : 2 * P.k ≤ (first.description securityParameter (2 * P.n)).width := by
      have hi := h.first_wellFormed.input_le
      have ho := h.first_output_le
      rw [h.first_quantumInputWidth, Nat.add_zero] at hi
      change (first.description securityParameter (2 * P.n)).outputWidth ≤ _ at ho
      rw [houtput] at ho
      exact ho.trans hi
    let messages : MessagePair (PKEMessage P) :=
      { msg₀ := fun i => z ⟨i, by omega⟩
        msg₁ := fun i => z ⟨P.k + i, by omega⟩ }
    let branch := h.initialPrefixBranch sample.toWord z bit
    let rest := (splitEquiv layout.serviceEmbedding branch).2
    let saved := (splitEquiv layout.serviceReplyEmbedding rest).2
    branch = (splitEquiv layout.serviceEmbedding).symm
      (inputState layout.service.width
        (encPair encUnary encBits (securityParameter, sample.toWord) ++
          List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [bit 0]),
        (splitEquiv layout.serviceReplyEmbedding).symm
          (Fin.append (fun _ : Fin 1 => bit 0)
            (fun _ : Fin layout.ciphertextWidth => false), saved)) := by
  classical
  dsimp only
  let layout := b2ClassicalQueryLayout P encoder first second securityParameter
  have hfirstInput : layout.firstInputWidth ≤ layout.first.width := by
    have hi := h.first_wellFormed.input_le
    rw [h.first_quantumInputWidth, Nat.add_zero] at hi
    exact hi
  have hwidth : 2 * P.k ≤ (first.description securityParameter (2 * P.n)).width := by
    have ho := h.first_output_le
    change (first.description securityParameter (2 * P.n)).outputWidth ≤ _ at ho
    rw [houtput] at ho
    exact ho.trans hfirstInput
  let messages : MessagePair (PKEMessage P) :=
    { msg₀ := fun i => z ⟨i, by omega⟩
      msg₁ := fun i => z ⟨P.k + i, by omega⟩ }
  let request : Fin layout.first.outputWidth → Bool :=
    fun i => z ⟨i, lt_of_lt_of_le i.isLt (h.first_output_le.trans hfirstInput)⟩
  let branch := h.initialPrefixBranch sample.toWord z bit
  let rest := (splitEquiv layout.serviceEmbedding branch).2
  let saved := (splitEquiv layout.serviceReplyEmbedding rest).2
  have hregisters := h.initialPrefixBranch_registers sample.toWord
    (TruncatedSyndromeSample.length_toWord sample) z bit
  have hrequest : List.ofFn request = List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ := by
    have hout : layout.first.outputWidth = P.k + P.k := by
      change (first.description securityParameter (2 * P.n)).outputWidth = _
      omega
    rw [List.ofFn_congr hout request, List.ofFn_add]
    rfl
  change branch = (splitEquiv layout.serviceEmbedding).symm
    (inputState layout.service.width
      (encPair encUnary encBits (securityParameter, sample.toWord) ++
        List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [bit 0]),
      (splitEquiv layout.serviceReplyEmbedding).symm
        (Fin.append (fun _ : Fin 1 => bit 0)
          (fun _ : Fin layout.ciphertextWidth => false), saved))
  apply (splitEquiv layout.serviceEmbedding).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · rw [splitEquiv_apply_fst]
    have hs := hregisters.1
    change branch ∘ layout.serviceEmbedding = inputState layout.service.width
      (encPair encUnary encBits (securityParameter, sample.toWord) ++
        List.ofFn request ++ [bit 0]) at hs
    rw [hs, hrequest]
    simp only [List.append_assoc]
  · apply (splitEquiv layout.serviceReplyEmbedding).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · funext i
      simp only [splitEquiv_apply_fst, splitEquiv_apply_snd, Function.comp_apply]
      rw [← readBit_fin branch (layout.serviceReplyEmbedding i).val]
      change readBit branch (layout.replyBase + i) = _
      rw [hregisters.2.2 i i.isLt]
      refine Fin.addCases ?_ ?_ i
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        simp
      · intro j
        simp
    · rfl


/-- **The embedded B2 service block coherently records its actual reversible environment.**
Reindexing the physical controller register by its service embedding exposes the actual erased
service circuit tensored with the identity.  Restricting its input to the initialized HQC sample,
measured messages and the protected hidden-bit copy therefore gives the coherent record of
`classicalRun b2ServiceCodes`.  Every physical wire outside the service embedding and an
arbitrary inaccessible reference are retained; no product-state hypothesis is used.

This is a physical block identity, not yet the complete controller success law: the subsequent
reply copies, ciphertext-only second stage and final comparison remain to be composed. -/
theorem matrix_b2ServiceBlock_initializedInput_withReference (P : PKEParams)
    (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P))
    (first second : UniformOracleCircuitFamily)
    {Reference : Type*} [DecidableEq Reference] :
    let layout := b2ClassicalQueryLayout P encoder first second securityParameter
    let Rest := {j : Fin layout.width //
      ¬ ∃ i, layout.serviceEmbedding i = j}
    let protectedHidden : (Rest → Bool) → Bool :=
      fun rest => readBit
        ((splitEquiv layout.serviceEmbedding).symm (fun _ => false, rest))
        layout.replyBase
    let serviceInput : (Rest → Bool) →
        Fin layout.service.width → Bool :=
      fun rest =>
        inputState layout.service.width
          (encPair encUnary encBits (securityParameter, sample.toWord) ++
            List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [protectedHidden rest])
    let physical :=
      (((Circuit.matrix
          ((Circuit.ofPhaseCodes layout.service.width
            layout.service.instructions.zeroOraclePhaseCodes).mapWires
              layout.serviceEmbedding) : Matrix _ _ ℂ) ⊗ₖ
          (1 : Matrix Reference Reference ℂ)).submatrix
        (fun p :
            (Fin layout.service.width → Bool) × ((Rest → Bool) × Reference) =>
          ((splitEquiv layout.serviceEmbedding).symm (p.1, p.2.1), p.2.2))
        (fun p : (Rest → Bool) × Reference =>
          ((splitEquiv layout.serviceEmbedding).symm (serviceInput p.1, p.1), p.2)))
    physical = coherentRecord (fun p : (Rest → Bool) × Reference =>
      classicalRun (b2ServiceCodes P securityParameter encoder) (serviceInput p.1)) := by
  classical
  dsimp only
  let layout := b2ClassicalQueryLayout P encoder first second securityParameter
  let serviceInput :
      ({j : Fin layout.width // ¬ ∃ i, layout.serviceEmbedding i = j} → Bool) →
        Fin layout.service.width → Bool :=
    fun rest =>
      inputState layout.service.width
        (encPair encUnary encBits (securityParameter, sample.toWord) ++
          List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++
            [readBit ((splitEquiv layout.serviceEmbedding).symm (fun _ => false, rest))
              layout.replyBase])
  have hserviceCircuit :
      Circuit.ofPhaseCodes layout.service.width
          layout.service.instructions.zeroOraclePhaseCodes =
        Circuit.ofCodes layout.service.width
          (b2ServiceCodes P securityParameter encoder) := by
    simp [layout, b2ClassicalQueryLayout,
      OracleCircuit.zeroOraclePhaseCodes, Circuit.ofPhaseCodes_map]
  have hclass : IsClassical layout.service.width
      (b2ServiceCodes P securityParameter encoder) := by
    simpa only [layout, b2ClassicalQueryLayout] using
      isClassical_b2ServiceDescription P securityParameter encoder
  have hsplit := Circuit.matrix_mapWires_splitEquiv layout.serviceEmbedding
    (Circuit.ofCodes layout.service.width
      (b2ServiceCodes P securityParameter encoder))
  rw [hserviceCircuit]
  ext ⟨environment, restOut, referenceOut⟩ ⟨restIn, referenceIn⟩
  change
    ((Circuit.matrix
        ((Circuit.ofCodes layout.service.width
          (b2ServiceCodes P securityParameter encoder)).mapWires layout.serviceEmbedding) :
          Matrix _ _ ℂ).submatrix
        (splitEquiv layout.serviceEmbedding).symm
        (splitEquiv layout.serviceEmbedding).symm
        (environment, restOut) (serviceInput restIn, restIn)) *
      (1 : Matrix Reference Reference ℂ) referenceOut referenceIn = _
  rw [hsplit]
  simp only [kroneckerMap_apply, Matrix.one_apply, coherentRecord]
  have hmatrix :
      (Circuit.matrix (Circuit.ofCodes layout.service.width
        (b2ServiceCodes P securityParameter encoder)) : Matrix _ _ ℂ)
          environment (serviceInput restIn) =
        if environment = classicalRun (b2ServiceCodes P securityParameter encoder)
          (serviceInput restIn) then 1 else 0 := by
    calc
      _ = ((Circuit.ofCodes layout.service.width
          (b2ServiceCodes P securityParameter encoder)).eval
            (ket (serviceInput restIn))).ofLp environment :=
        (Circuit.eval_ket_apply _ _ _).symm
      _ = (ket (classicalRun (b2ServiceCodes P securityParameter encoder)
          (serviceInput restIn))).ofLp environment := by
        rw [Circuit.eval_ofCodes_ket hclass]
      _ = _ := by simp only [ket_apply]
  rw [hmatrix]
  simp only [serviceInput, layout, encPair_apply, encUnary_apply, encBits_apply,
    List.append_assoc]
  by_cases hreference : referenceOut = referenceIn <;>
    by_cases hrest : restOut = restIn <;>
      by_cases henvironment : environment =
        classicalRun (b2ServiceCodes P securityParameter encoder) (serviceInput restIn) <;>
        simp [hreference, hrest, henvironment]

/-- **The physical service and ciphertext copy produce the complete retained reply.**  Split the
controller register first along the service placement and then along the protected reply block.
On columns where that reply contains the copied hidden bit and a zero ciphertext target, the
product of the actual embedded service matrix and the actual service-to-reply CNOT block replaces
the hidden input by the reversible service environment and records the complete `[hidden|u|v]`
word. The message pair and hidden bit are both variable input labels, and every other physical
wire is retained as one arbitrary factor, so the equality can be used under a density matrix
entangled across distinct requests and the saved first-stage state.

This is the exact physical service contract consumed by the prefix branch decomposition and the
full-request trace law. It does not yet include the ciphertext-to-second-input copy, second-stage
execution or final comparison. -/
theorem matrix_b2ServiceReplyCopy_initializedInput (P : PKEParams)
    (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (first second : UniformOracleCircuitFamily) :
    let layout := b2ClassicalQueryLayout P encoder first second securityParameter
    let ServiceState := Fin layout.service.width → Bool
    let replyEmbedding := layout.serviceReplyEmbedding
    let Saved := {j : {j : Fin layout.width //
      ¬ ∃ i, layout.serviceEmbedding i = j} // ¬ ∃ i, replyEmbedding i = j}
    let initialReply : Bool → Fin (1 + layout.ciphertextWidth) → Bool :=
      fun hidden => Fin.append (fun _ : Fin 1 => hidden)
        (fun _ : Fin layout.ciphertextWidth => false)
    let physicalState :=
      fun (service : ServiceState)
          (reply : Fin (1 + layout.ciphertextWidth) → Bool)
          (saved : Saved → Bool) =>
        (splitEquiv layout.serviceEmbedding).symm
          (service,
            (splitEquiv replyEmbedding).symm (reply, saved))
    let serviceInput : MessagePair (PKEMessage P) × Bool → ServiceState :=
      fun request =>
        inputState layout.service.width
          (encPair encUnary encBits (securityParameter, sample.toWord) ++
            List.ofFn request.1.msg₀ ++ List.ofFn request.1.msg₁ ++ [request.2])
    let serviceEnvironment : MessagePair (PKEMessage P) × Bool → ServiceState :=
      fun request => classicalRun (b2ServiceCodes P securityParameter encoder)
        (serviceInput request)
    let serviceReply : ServiceState → Bool →
        Fin (1 + layout.ciphertextWidth) → Bool :=
      fun environment hidden =>
        Fin.append (fun _ : Fin 1 => hidden)
          (fun i : Fin layout.ciphertextWidth => readBit environment i)
    let serviceMatrix : Matrix (ServiceState × (Bool × (Saved → Bool)))
        ((MessagePair (PKEMessage P) × Bool) × (Saved → Bool)) ℂ :=
      (Circuit.matrix
        ((Circuit.ofPhaseCodes layout.service.width
          layout.service.instructions.zeroOraclePhaseCodes).mapWires
            layout.serviceEmbedding) : Matrix _ _ ℂ).submatrix
        (fun p => physicalState p.1 (initialReply p.2.1) p.2.2)
        (fun p => physicalState (serviceInput p.1) (initialReply p.1.2) p.2)
    let replyCopyMatrix : Matrix
        (ServiceState × ((Fin (1 + layout.ciphertextWidth) → Bool) × (Saved → Bool)))
        (ServiceState × (Bool × (Saved → Bool))) ℂ :=
      (Circuit.matrix (Circuit.ofCodes layout.width
        (blockCopyCodes layout.serviceBase (layout.replyBase + 1)
          layout.ciphertextWidth)) : Matrix _ _ ℂ).submatrix
        (fun p => physicalState p.1 p.2.1 p.2.2)
        (fun p => physicalState p.1 (initialReply p.2.1) p.2.2)
    replyCopyMatrix * serviceMatrix =
      coherentEnvironmentRecord serviceEnvironment
        (fun request => serviceReply (serviceEnvironment request) request.2) := by
  classical
  let layout := b2ClassicalQueryLayout P encoder first second securityParameter
  let ServiceState := Fin layout.service.width → Bool
  let ServiceRest := {j : Fin layout.width //
    ¬ ∃ i, layout.serviceEmbedding i = j}
  let replyEmbedding := layout.serviceReplyEmbedding
  let Saved := {j : ServiceRest // ¬ ∃ i, replyEmbedding i = j}
  let initialReply : Bool → Fin (1 + layout.ciphertextWidth) → Bool :=
    fun hidden => Fin.append (fun _ : Fin 1 => hidden)
      (fun _ : Fin layout.ciphertextWidth => false)
  let physicalState :=
    fun (service : ServiceState)
        (reply : Fin (1 + layout.ciphertextWidth) → Bool)
        (saved : Saved → Bool) =>
      (splitEquiv layout.serviceEmbedding).symm
        (service, (splitEquiv replyEmbedding).symm (reply, saved))
  let serviceInput : MessagePair (PKEMessage P) × Bool → ServiceState :=
    fun request =>
      inputState layout.service.width
        (encPair encUnary encBits (securityParameter, sample.toWord) ++
          List.ofFn request.1.msg₀ ++ List.ofFn request.1.msg₁ ++ [request.2])
  let serviceEnvironment : MessagePair (PKEMessage P) × Bool → ServiceState :=
    fun request => classicalRun (b2ServiceCodes P securityParameter encoder)
      (serviceInput request)
  let serviceReply : ServiceState → Bool →
      Fin (1 + layout.ciphertextWidth) → Bool :=
    fun environment hidden =>
      Fin.append (fun _ : Fin 1 => hidden)
        (fun i : Fin layout.ciphertextWidth => readBit environment i)
  let serviceMatrix : Matrix (ServiceState × (Bool × (Saved → Bool)))
      ((MessagePair (PKEMessage P) × Bool) × (Saved → Bool)) ℂ :=
    (Circuit.matrix
      ((Circuit.ofPhaseCodes layout.service.width
        layout.service.instructions.zeroOraclePhaseCodes).mapWires
          layout.serviceEmbedding) : Matrix _ _ ℂ).submatrix
      (fun p => physicalState p.1 (initialReply p.2.1) p.2.2)
      (fun p => physicalState (serviceInput p.1) (initialReply p.1.2) p.2)
  let replyCopyMatrix : Matrix
      (ServiceState × ((Fin (1 + layout.ciphertextWidth) → Bool) × (Saved → Bool)))
      (ServiceState × (Bool × (Saved → Bool))) ℂ :=
    (Circuit.matrix (Circuit.ofCodes layout.width
      (blockCopyCodes layout.serviceBase (layout.replyBase + 1)
        layout.ciphertextWidth)) : Matrix _ _ ℂ).submatrix
      (fun p => physicalState p.1 p.2.1 p.2.2)
      (fun p => physicalState p.1 (initialReply p.2.1) p.2.2)
  change replyCopyMatrix * serviceMatrix =
    coherentEnvironmentRecord serviceEnvironment
      (fun request => serviceReply (serviceEnvironment request) request.2)
  have hreplyBase : layout.replyBase < layout.width := by
    simp only [layout, ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
    omega
  have hreadReplyBase (service : ServiceState)
      (reply : Fin (1 + layout.ciphertextWidth) → Bool) (saved : Saved → Bool) :
      readBit (physicalState service reply saved) layout.replyBase = reply 0 := by
    rw [readBit_of_lt _ hreplyBase]
    have hwire : (⟨layout.replyBase, hreplyBase⟩ : Fin layout.width) =
        (replyEmbedding 0).1 := by
      apply Fin.ext
      change layout.replyBase = layout.replyBase + (0 : Fin (1 + layout.ciphertextWidth))
      simp only [Fin.val_zero, Nat.add_zero]
    rw [hwire]
    change
      (splitEquiv layout.serviceEmbedding).symm
          (service, (splitEquiv replyEmbedding).symm (reply, saved))
          (replyEmbedding 0).1 = reply 0
    rw [splitEquiv_symm_apply_of_not]
    exact splitEquiv_symm_apply_wire replyEmbedding reply saved 0
  have hserviceMatrix : serviceMatrix =
      coherentEnvironmentRecord serviceEnvironment
        (fun request : MessagePair (PKEMessage P) × Bool => request.2) := by
    ext ⟨environmentOut, hiddenOut, savedOut⟩ ⟨requestIn, savedIn⟩
    have hservice := matrix_b2ServiceBlock_initializedInput_withReference P securityParameter
      encoder sample requestIn.1 first second (Reference := Unit)
    dsimp only at hservice
    have hentry := congrFun (congrFun hservice
      (environmentOut,
        (splitEquiv replyEmbedding).symm (initialReply hiddenOut, savedOut), ()))
      ((splitEquiv replyEmbedding).symm (initialReply requestIn.2, savedIn), ())
    simp only [Matrix.submatrix_apply, kroneckerMap_apply, Matrix.one_apply,
      coherentRecord] at hentry
    have hhidden :
        readBit
            ((splitEquiv layout.serviceEmbedding).symm
              (fun _ => false,
                (splitEquiv replyEmbedding).symm (initialReply requestIn.2, savedIn)))
            layout.replyBase = requestIn.2 := by
      rw [hreadReplyBase]
      exact Fin.append_left _ _ 0
    have hinitialReply : Function.Injective initialReply := by
      intro left right heq
      have heq := congrFun heq (Fin.castAdd layout.ciphertextWidth (0 : Fin 1))
      simpa only [initialReply, Fin.append_left] using heq
    dsimp only [layout] at hentry hhidden
    simpa only [serviceMatrix, physicalState, serviceInput, serviceEnvironment, layout,
      Matrix.submatrix_apply, coherentEnvironmentRecord, hhidden,
      Prod.mk.injEq, true_and, ite_true, mul_one, and_true,
      hinitialReply.eq_iff,
      Equiv.apply_eq_iff_eq] using hentry
  rw [hserviceMatrix]
  ext ⟨environmentOut, replyOut, savedOut⟩ ⟨requestIn, savedIn⟩
  simp only [Matrix.mul_apply, coherentEnvironmentRecord, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, reduceIte, Prod.mk.injEq]
  let htarget : layout.replyBase + 1 + layout.ciphertextWidth ≤ layout.width := by
    simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
    omega
  let targetEmbedding := blockEmb (layout.replyBase + 1) htarget
  let TargetRest := {j : Fin layout.width // ¬ ∃ i, targetEmbedding i = j}
  let inputPhysical := physicalState (serviceEnvironment requestIn)
    (initialReply requestIn.2) savedIn
  let inputRest : TargetRest → Bool := (splitEquiv targetEmbedding inputPhysical).2
  have hciphertext : layout.ciphertextWidth = P.n + P.codeLen := by
    simp only [layout, b2ClassicalQueryLayout, ClassicalQueryLayout.ciphertextWidth]
    omega
  have hserviceOutput : layout.ciphertextWidth ≤ layout.service.width := by
    rw [hciphertext]
    simpa only [layout, b2ClassicalQueryLayout, b2ServiceDescription_outputWidth] using
      (wellFormed_b2ServiceDescription P securityParameter encoder).output_le
  have hfullInput : layout.ciphertextWidth ≤ layout.fullInputWidth := by
    simp only [layout, b2ClassicalQueryLayout, ClassicalQueryLayout.ciphertextWidth,
      ClassicalQueryLayout.fullInputWidth]
    omega
  have htargetZero : (splitEquiv targetEmbedding inputPhysical).1 =
      (fun _ : Fin layout.ciphertextWidth => false) := by
    funext i
    rw [splitEquiv_apply_fst]
    have hwire : targetEmbedding i =
        (replyEmbedding (Fin.natAdd 1 i)).1 := by
      apply Fin.ext
      change i + (layout.replyBase + 1) =
        layout.replyBase + (Fin.natAdd 1 i : Fin (1 + layout.ciphertextWidth))
      simp only [Fin.val_natAdd]
      omega
    change inputPhysical (targetEmbedding i) = false
    rw [hwire]
    change
      (splitEquiv layout.serviceEmbedding).symm
          (serviceEnvironment requestIn,
            (splitEquiv replyEmbedding).symm (initialReply requestIn.2, savedIn))
          (replyEmbedding (Fin.natAdd 1 i)).1 = false
    have houtside := (replyEmbedding (Fin.natAdd 1 i)).2
    rw [splitEquiv_symm_apply_of_not _ _ _ _ houtside,
      splitEquiv_symm_apply_wire]
    exact Fin.append_right _ _ i
  have hinputPhysical :
      (splitEquiv targetEmbedding).symm
          (fun _ : Fin layout.ciphertextWidth => false, inputRest) = inputPhysical := by
    apply (splitEquiv targetEmbedding).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext htargetZero.symm rfl
  let sourceLabel : (TargetRest → Bool) → Fin layout.ciphertextWidth → Bool :=
    fun rest i =>
      (splitEquiv targetEmbedding).symm (fun _ => false, rest)
        ⟨layout.serviceBase + i, by
          simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
            ClassicalQueryLayout.replyBase]
          omega⟩
  have hsourceLabel : sourceLabel inputRest =
      fun i : Fin layout.ciphertextWidth =>
        readBit (serviceEnvironment requestIn) i := by
    funext i
    dsimp only [sourceLabel]
    rw [hinputPhysical]
    have hsourceWire :
        (⟨layout.serviceBase + i, by
          simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
            ClassicalQueryLayout.replyBase]
          omega⟩ : Fin layout.width) =
          layout.serviceEmbedding ⟨i, i.isLt.trans_le hserviceOutput⟩ := by
      apply Fin.ext
      change layout.serviceBase + i =
        layout.serviceWire i
      rw [ClassicalQueryLayout.serviceWire, ite_eq_left (i.isLt.trans_le hfullInput)]
    rw [hsourceWire]
    change
      (splitEquiv layout.serviceEmbedding).symm
          (serviceEnvironment requestIn,
            (splitEquiv replyEmbedding).symm (initialReply requestIn.2, savedIn))
          (layout.serviceEmbedding ⟨i, i.isLt.trans_le hserviceOutput⟩) = _
    rw [splitEquiv_symm_apply_wire]
    rw [readBit_of_lt _ (i.isLt.trans_le hserviceOutput)]
  have hcopy := Circuit.matrix_blockCopyCodes_zeroTarget
    (source := layout.serviceBase) (target := layout.replyBase + 1)
    (count := layout.ciphertextWidth) (width := layout.width)
    (Or.inl (by
      simp only [ClassicalQueryLayout.replyBase]
      omega))
    (by
      simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase,
        ClassicalQueryLayout.replyBase]
      omega)
    htarget
  dsimp only at hcopy
  let expectedReply := serviceReply (serviceEnvironment requestIn) requestIn.2
  let expectedPhysical := physicalState (serviceEnvironment requestIn) expectedReply savedIn
  have hsplitExpected :
      splitEquiv targetEmbedding expectedPhysical = (sourceLabel inputRest, inputRest) := by
    apply Prod.ext
    · funext i
      rw [splitEquiv_apply_fst]
      have hwire : targetEmbedding i =
          (replyEmbedding (Fin.natAdd 1 i)).1 := by
        apply Fin.ext
        change i + (layout.replyBase + 1) =
          layout.replyBase + (Fin.natAdd 1 i : Fin (1 + layout.ciphertextWidth))
        simp only [Fin.val_natAdd]
        omega
      change expectedPhysical (targetEmbedding i) = sourceLabel inputRest i
      rw [hwire]
      change
        (splitEquiv layout.serviceEmbedding).symm
            (serviceEnvironment requestIn,
              (splitEquiv replyEmbedding).symm (expectedReply, savedIn))
            (replyEmbedding (Fin.natAdd 1 i)).1 = _
      rw [splitEquiv_symm_apply_of_not _ _ _ _
          (replyEmbedding (Fin.natAdd 1 i)).2,
        splitEquiv_symm_apply_wire]
      dsimp only [expectedReply, serviceReply]
      rw [Fin.append_right]
      exact (congrFun hsourceLabel i).symm
    · funext j
      rw [splitEquiv_apply_snd]
      change expectedPhysical j.1 = inputPhysical j.1
      by_cases hservice : ∃ i, layout.serviceEmbedding i = j.1
      · obtain ⟨i, hi⟩ := hservice
        rw [← hi]
        change
          (splitEquiv layout.serviceEmbedding).symm
              (serviceEnvironment requestIn,
                (splitEquiv replyEmbedding).symm (expectedReply, savedIn))
              (layout.serviceEmbedding i) =
            (splitEquiv layout.serviceEmbedding).symm
              (serviceEnvironment requestIn,
                (splitEquiv replyEmbedding).symm (initialReply requestIn.2, savedIn))
              (layout.serviceEmbedding i)
        rw [splitEquiv_symm_apply_wire, splitEquiv_symm_apply_wire]
      · let serviceRest : ServiceRest := ⟨j.1, hservice⟩
        change
          (splitEquiv layout.serviceEmbedding).symm
              (serviceEnvironment requestIn,
                (splitEquiv replyEmbedding).symm (expectedReply, savedIn)) j.1 =
            (splitEquiv layout.serviceEmbedding).symm
              (serviceEnvironment requestIn,
                (splitEquiv replyEmbedding).symm (initialReply requestIn.2, savedIn)) j.1
        rw [splitEquiv_symm_apply_of_not _ _ _ _ hservice,
          splitEquiv_symm_apply_of_not _ _ _ _ hservice]
        change
          (splitEquiv replyEmbedding).symm (expectedReply, savedIn) serviceRest =
            (splitEquiv replyEmbedding).symm (initialReply requestIn.2, savedIn) serviceRest
        by_cases hreply : ∃ i, replyEmbedding i = serviceRest
        · obtain ⟨i, hi⟩ := hreply
          rw [← hi, splitEquiv_symm_apply_wire, splitEquiv_symm_apply_wire]
          by_cases hi0 : i = 0
          · subst i
            dsimp only [expectedReply, serviceReply, initialReply]
            change requestIn.2 = requestIn.2
            rfl
          · exfalso
            have hival : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
            have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hival
            let k : Fin layout.ciphertextWidth := ⟨i - 1, by omega⟩
            apply j.2
            refine ⟨k, ?_⟩
            apply Fin.ext
            have hi' := congrArg (fun wire => ((wire.1 : Fin layout.width) : ℕ)) hi
            change layout.replyBase + i = j.1 at hi'
            change k + (layout.replyBase + 1) = j.1
            dsimp only [k]
            omega
        · rw [splitEquiv_symm_apply_of_not _ _ _ _ hreply,
            splitEquiv_symm_apply_of_not _ _ _ _ hreply]
  have hphysicalState_eq (serviceLeft serviceRight : ServiceState)
      (replyLeft replyRight : Fin (1 + layout.ciphertextWidth) → Bool)
      (savedLeft savedRight : Saved → Bool) :
      physicalState serviceLeft replyLeft savedLeft =
          physicalState serviceRight replyRight savedRight ↔
        serviceLeft = serviceRight ∧ replyLeft = replyRight ∧ savedLeft = savedRight := by
    constructor
    · intro h
      have houter := congrArg (splitEquiv layout.serviceEmbedding) h
      simp only [physicalState, Equiv.apply_symm_apply, Prod.mk.injEq] at houter
      have hinner := congrArg (splitEquiv replyEmbedding) houter.2
      simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at hinner
      exact ⟨houter.1, hinner.1, hinner.2⟩
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  have hcoordinates :
      splitEquiv targetEmbedding (physicalState environmentOut replyOut savedOut) =
          (sourceLabel inputRest, inputRest) ↔
        environmentOut = serviceEnvironment requestIn ∧
          replyOut = expectedReply ∧ savedOut = savedIn := by
    constructor
    · intro h
      apply (hphysicalState_eq _ _ _ _ _ _).mp
      apply (splitEquiv targetEmbedding).injective
      exact h.trans hsplitExpected.symm
    · intro h
      have hphysical := (hphysicalState_eq _ _ _ _ _ _).mpr h
      exact (congrArg (splitEquiv targetEmbedding) hphysical).trans hsplitExpected
  have hentry := congrFun
    (congrFun hcopy
      (splitEquiv targetEmbedding (physicalState environmentOut replyOut savedOut))) inputRest
  have hentry' :
      replyCopyMatrix (environmentOut, replyOut, savedOut)
          (serviceEnvironment requestIn, requestIn.2, savedIn) =
        if splitEquiv targetEmbedding (physicalState environmentOut replyOut savedOut) =
            (sourceLabel inputRest, inputRest) then 1 else 0 := by
    change
      (Circuit.matrix (Circuit.ofCodes layout.width
        (blockCopyCodes layout.serviceBase (layout.replyBase + 1)
          layout.ciphertextWidth)) : Matrix _ _ ℂ)
          (physicalState environmentOut replyOut savedOut) inputPhysical = _
    rw [← hinputPhysical]
    simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply, coherentRecord,
      targetEmbedding, sourceLabel] using hentry
  rw [hentry', if_congr hcoordinates rfl rfl]

/-- **The physical reply copy and second stage are controlled by the complete retained reply.**
Split the physical register into the second-stage placement, the complete hidden-bit-and-
ciphertext reply, and an arbitrary saved complement.  Copying the ciphertext suffix into the
fresh second-stage input and then running the actual erased second-stage circuit is block diagonal
in the complete reply.  Its reply block is exactly that circuit on the standard
`(security parameter, ciphertext, saved memory)` input, tensored with the identity on the saved
complement and an arbitrary external reference.

Thus cross-reply matrix entries are zero, the hidden bit is retained outside the second-stage
input, and the equality applies to states entangled across the complete reply, saved first-stage
memory, other physical wires and external reference.  It makes no product-state assumption and
stops before moving the guess to wire zero or comparing it with the hidden bit. -/
theorem matrix_b2ReplyCopySecondStage_withReference (P : PKEParams)
    (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (first second : UniformOracleCircuitFamily)
    {Reference : Type*} [DecidableEq Reference] :
    let layout := b2ClassicalQueryLayout P encoder first second securityParameter
    let SecondState := Fin layout.second.width → Bool
    let FullReply := Fin (1 + layout.ciphertextWidth) → Bool
    let SecondRest := {j : Fin layout.width //
      ¬ ∃ i, layout.secondEmbedding i = j}
    let replyEmbedding : Fin (1 + layout.ciphertextWidth) ↪ SecondRest :=
      { toFun := fun wire => ⟨⟨layout.replyBase + wire, by
          simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
          omega⟩, by
            rintro ⟨secondWire, hsecondWire⟩
            exact layout.secondWire_ne_replyBlock secondWire wire
              (congrArg Fin.val hsecondWire)⟩
        inj' := fun left right heq => Fin.ext <| by
          have heq := congrArg (fun wire => ((wire.1 : Fin layout.width) : ℕ)) heq
          change layout.replyBase + left = layout.replyBase + right at heq
          omega }
    let Saved := {j : SecondRest // ¬ ∃ i, replyEmbedding i = j}
    let secondInput (ciphertext : Fin layout.ciphertextWidth → Bool)
        (memory : Fin layout.second.quantumInputWidth → Bool) : SecondState :=
      inputState layout.second.width
        (encPair encUnary encBits
          (securityParameter, List.ofFn ciphertext) ++ List.ofFn memory)
    let physicalState (secondState : SecondState)
        (fullReply : FullReply)
        (saved : Saved → Bool) : Fin layout.width → Bool :=
      (splitEquiv layout.secondEmbedding).symm
        (secondState, (splitEquiv replyEmbedding).symm (fullReply, saved))
    let secondCircuit := Circuit.ofPhaseCodes layout.second.width
      layout.second.instructions.zeroOraclePhaseCodes
    let suffixCircuit :=
      Circuit.ofCodes layout.width
          (blockCopyCodes (layout.replyBase + 1)
            (layout.secondBase + (2 * securityParameter + 1))
            layout.ciphertextWidth) ++
        secondCircuit.mapWires layout.secondEmbedding
    let physical :=
      ((Circuit.matrix suffixCircuit : Matrix _ _ ℂ) ⊗ₖ
        (1 : Matrix Reference Reference ℂ)).submatrix
        (fun p : (SecondState × ((Saved → Bool) × Reference)) × FullReply =>
          (physicalState p.1.1 p.2 p.1.2.1, p.1.2.2))
        (fun p : ((Fin layout.second.quantumInputWidth → Bool) ×
            ((Saved → Bool) × Reference)) × FullReply =>
          (physicalState (secondInput (fun _ => false) p.1.1) p.2 p.1.2.1, p.1.2.2))
    let ciphertext (reply : FullReply) : Fin layout.ciphertextWidth → Bool :=
      fun i => reply (Fin.natAdd 1 i)
    let block : FullReply → Matrix
        (SecondState × ((Saved → Bool) × Reference))
        ((Fin layout.second.quantumInputWidth → Bool) ×
          ((Saved → Bool) × Reference)) ℂ :=
      fun reply =>
        ((Circuit.matrix secondCircuit : Matrix _ _ ℂ).submatrix id
            (fun memory => secondInput (ciphertext reply) memory)) ⊗ₖ
          (1 : Matrix ((Saved → Bool) × Reference)
            ((Saved → Bool) × Reference) ℂ)
    physical = Matrix.blockDiagonal block := by
  classical
  let layout := b2ClassicalQueryLayout P encoder first second securityParameter
  let SecondState := Fin layout.second.width → Bool
  let FullReply := Fin (1 + layout.ciphertextWidth) → Bool
  let SecondRest := {j : Fin layout.width //
    ¬ ∃ i, layout.secondEmbedding i = j}
  let replyEmbedding : Fin (1 + layout.ciphertextWidth) ↪ SecondRest :=
    { toFun := fun wire => ⟨⟨layout.replyBase + wire, by
        simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
        omega⟩, by
          rintro ⟨secondWire, hsecondWire⟩
          exact layout.secondWire_ne_replyBlock secondWire wire
            (congrArg Fin.val hsecondWire)⟩
      inj' := fun left right heq => Fin.ext <| by
        have heq := congrArg (fun wire => ((wire.1 : Fin layout.width) : ℕ)) heq
        change layout.replyBase + left = layout.replyBase + right at heq
        omega }
  let Saved := {j : SecondRest // ¬ ∃ i, replyEmbedding i = j}
  let secondInput (ciphertext : Fin layout.ciphertextWidth → Bool)
      (memory : Fin layout.second.quantumInputWidth → Bool) : SecondState :=
    inputState layout.second.width
      (encPair encUnary encBits
        (securityParameter, List.ofFn ciphertext) ++ List.ofFn memory)
  let physicalState (secondState : SecondState)
      (fullReply : FullReply)
      (saved : Saved → Bool) : Fin layout.width → Bool :=
    (splitEquiv layout.secondEmbedding).symm
      (secondState, (splitEquiv replyEmbedding).symm (fullReply, saved))
  let secondCircuit := Circuit.ofPhaseCodes layout.second.width
    layout.second.instructions.zeroOraclePhaseCodes
  let suffixCircuit :=
    Circuit.ofCodes layout.width
        (blockCopyCodes (layout.replyBase + 1)
          (layout.secondBase + (2 * securityParameter + 1))
          layout.ciphertextWidth) ++
      secondCircuit.mapWires layout.secondEmbedding
  let physical :=
    ((Circuit.matrix suffixCircuit : Matrix _ _ ℂ) ⊗ₖ
      (1 : Matrix Reference Reference ℂ)).submatrix
      (fun p : (SecondState × ((Saved → Bool) × Reference)) × FullReply =>
        (physicalState p.1.1 p.2 p.1.2.1, p.1.2.2))
      (fun p : ((Fin layout.second.quantumInputWidth → Bool) ×
          ((Saved → Bool) × Reference)) × FullReply =>
        (physicalState (secondInput (fun _ => false) p.1.1) p.2 p.1.2.1, p.1.2.2))
  let ciphertext (reply : FullReply) : Fin layout.ciphertextWidth → Bool :=
    fun i => reply (Fin.natAdd 1 i)
  let block : FullReply → Matrix
      (SecondState × ((Saved → Bool) × Reference))
      ((Fin layout.second.quantumInputWidth → Bool) ×
        ((Saved → Bool) × Reference)) ℂ :=
    fun reply =>
      ((Circuit.matrix secondCircuit : Matrix _ _ ℂ).submatrix id
          (fun memory => secondInput (ciphertext reply) memory)) ⊗ₖ
        (1 : Matrix ((Saved → Bool) × Reference)
          ((Saved → Bool) × Reference) ℂ)
  change physical = Matrix.blockDiagonal block
  ext ⟨⟨secondOut, savedOut, referenceOut⟩, replyOut⟩
    ⟨⟨memoryIn, savedIn, referenceIn⟩, replyIn⟩
  have hsecondInput := (second.wellFormed securityParameter (P.n + P.codeLen)).input_le
  change 2 * securityParameter + 1 + (P.n + P.codeLen) +
      layout.second.quantumInputWidth ≤ layout.second.width at hsecondInput
  have hciphertextWidth : layout.ciphertextWidth = P.n + P.codeLen := by
    simp only [layout, b2ClassicalQueryLayout, ClassicalQueryLayout.ciphertextWidth]
    omega
  rw [← hciphertextWidth] at hsecondInput
  have hsecondInputBit (bits : Fin layout.ciphertextWidth → Bool)
      (memory : Fin layout.second.quantumInputWidth → Bool)
      (i : Fin layout.ciphertextWidth) :
      secondInput bits memory
          ⟨2 * securityParameter + 1 + i, by omega⟩ = bits i := by
    simp only [secondInput, inputState, encPair_apply, encUnary_apply, encBits_apply]
    rw [List.getD_append _ _ _ _ (by
      simp only [List.length_append, length_frame, List.length_replicate, List.length_ofFn]
      omega)]
    rw [List.getD_append_right _ _ _ _ (by
      simp only [length_frame, List.length_replicate]
      omega), length_frame, List.length_replicate]
    have hindex : 2 * securityParameter + 1 + i - (2 * securityParameter + 1) = i := by
      omega
    rw [hindex]
    exact (List.getD_eq_getElem (l := List.ofFn bits)
      (d := false) (n := i) (by simp)).trans (by simp)
  let htarget : layout.secondBase + (2 * securityParameter + 1) +
      layout.ciphertextWidth ≤ layout.width := by
    simp only [ClassicalQueryLayout.width]
    omega
  let targetEmbedding :=
    blockEmb (layout.secondBase + (2 * securityParameter + 1)) htarget
  let TargetRest := {j : Fin layout.width // ¬ ∃ i, targetEmbedding i = j}
  let inputPhysical :=
    physicalState (secondInput (fun _ => false) memoryIn) replyIn savedIn
  let inputRest : TargetRest → Bool := (splitEquiv targetEmbedding inputPhysical).2
  have htargetWire (i : Fin layout.ciphertextWidth) :
      targetEmbedding i = layout.secondEmbedding
        ⟨2 * securityParameter + 1 + i, by omega⟩ := by
    apply Fin.ext
    dsimp only [targetEmbedding, blockEmb_apply_val,
      ClassicalQueryLayout.secondEmbedding, Function.Embedding.coeFn_mk]
    change i + (layout.secondBase + (2 * securityParameter + 1)) =
      layout.secondWire (2 * securityParameter + 1 + i)
    rw [ClassicalQueryLayout.secondWire, ite_eq_left]
    · omega
    · simp only [ClassicalQueryLayout.secondInputWidth]
      simp only [layout, b2ClassicalQueryLayout]
      omega
  have htargetZero : (splitEquiv targetEmbedding inputPhysical).1 =
      (fun _ : Fin layout.ciphertextWidth => false) := by
    funext i
    rw [splitEquiv_apply_fst, Function.comp_apply, htargetWire]
    simp only [inputPhysical, physicalState, splitEquiv_symm_apply_wire]
    exact hsecondInputBit (fun _ => false) memoryIn i
  have hinputPhysical :
      (splitEquiv targetEmbedding).symm
          (fun _ : Fin layout.ciphertextWidth => false, inputRest) = inputPhysical := by
    apply (splitEquiv targetEmbedding).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext htargetZero.symm rfl
  let sourceLabel : (TargetRest → Bool) → Fin layout.ciphertextWidth → Bool :=
    fun rest i =>
      (splitEquiv targetEmbedding).symm (fun _ => false, rest)
        ⟨layout.replyBase + 1 + i, by
          simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
          omega⟩
  have hsourceLabel : sourceLabel inputRest = ciphertext replyIn := by
    funext i
    dsimp only [sourceLabel]
    rw [hinputPhysical]
    have hwire :
        (⟨layout.replyBase + 1 + i, by
          simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
          omega⟩ : Fin layout.width) =
          (replyEmbedding (Fin.natAdd 1 i)).1 := by
      apply Fin.ext
      change layout.replyBase + 1 + i =
        layout.replyBase + (Fin.natAdd 1 i : Fin (1 + layout.ciphertextWidth))
      simp only [Fin.val_natAdd]
      omega
    rw [hwire]
    simp only [inputPhysical, physicalState]
    rw [splitEquiv_symm_apply_of_not _ _ _ _
        (replyEmbedding (Fin.natAdd 1 i)).2,
      splitEquiv_symm_apply_wire]
  have hsecondInputOutside (bitsLeft bitsRight : Fin layout.ciphertextWidth → Bool)
      (memory : Fin layout.second.quantumInputWidth → Bool)
      (i : Fin layout.second.width)
      (hi : i < 2 * securityParameter + 1 ∨
        2 * securityParameter + 1 + layout.ciphertextWidth ≤ i) :
      secondInput bitsLeft memory i = secondInput bitsRight memory i := by
    simp only [secondInput, inputState, encPair_apply, encUnary_apply, encBits_apply]
    rcases hi with hi | hi
    · rw [List.getD_append _ _ _ _ (by
          simp only [List.length_append, length_frame, List.length_replicate,
            List.length_ofFn]
          omega),
        List.getD_append _ _ _ _ (by
          simp only [length_frame, List.length_replicate]
          omega),
        List.getD_append _ _ _ _ (by
          simp only [List.length_append, length_frame, List.length_replicate,
            List.length_ofFn]
          omega),
        List.getD_append _ _ _ _ (by
          simp only [length_frame, List.length_replicate]
          omega)]
    · rw [List.getD_append_right _ _ _ _ (by
          simp only [List.length_append, length_frame, List.length_replicate,
            List.length_ofFn]
          omega),
        List.getD_append_right _ _ _ _ (by
          simp only [List.length_append, length_frame, List.length_replicate,
            List.length_ofFn]
          omega)]
      simp only [List.length_append, length_frame, List.length_replicate,
        List.length_ofFn]
  let expectedPhysical :=
    physicalState (secondInput (ciphertext replyIn) memoryIn) replyIn savedIn
  have hsplitExpected :
      splitEquiv targetEmbedding expectedPhysical = (sourceLabel inputRest, inputRest) := by
    apply Prod.ext
    · funext i
      rw [splitEquiv_apply_fst, Function.comp_apply, htargetWire]
      simp only [expectedPhysical, physicalState, splitEquiv_symm_apply_wire]
      rw [hsecondInputBit, hsourceLabel]
    · funext j
      rw [splitEquiv_apply_snd]
      change expectedPhysical j.1 = inputPhysical j.1
      by_cases hsecond : ∃ i, layout.secondEmbedding i = j.1
      · obtain ⟨i, hi⟩ := hsecond
        rw [← hi]
        simp only [expectedPhysical, inputPhysical, physicalState,
          splitEquiv_symm_apply_wire]
        apply hsecondInputOutside
        by_contra houtside
        push Not at houtside
        let k : Fin layout.ciphertextWidth :=
          ⟨i - (2 * securityParameter + 1), by omega⟩
        apply j.2
        refine ⟨k, ?_⟩
        rw [htargetWire, ← hi]
        apply congrArg layout.secondEmbedding
        apply Fin.ext
        dsimp only [k]
        omega
      · simp only [expectedPhysical, inputPhysical, physicalState]
        rw [splitEquiv_symm_apply_of_not _ _ _ _ hsecond,
          splitEquiv_symm_apply_of_not _ _ _ _ hsecond]
  have hcopy := Circuit.matrix_blockCopyCodes_zeroTarget
    (source := layout.replyBase + 1)
    (target := layout.secondBase + (2 * securityParameter + 1))
    (count := layout.ciphertextWidth) (width := layout.width)
    (Or.inl (by
      simp only [ClassicalQueryLayout.secondBase]
      omega))
    (by
      simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
      omega)
    htarget
  dsimp only at hcopy
  have hcopyEntry (middle : Fin layout.width → Bool) :
      (Circuit.matrix (Circuit.ofCodes layout.width
        (blockCopyCodes (layout.replyBase + 1)
          (layout.secondBase + (2 * securityParameter + 1))
          layout.ciphertextWidth)) : Matrix _ _ ℂ) middle inputPhysical =
        if middle = expectedPhysical then 1 else 0 := by
    have hentry := congrFun (congrFun hcopy
      (splitEquiv targetEmbedding middle)) inputRest
    have hcoordinates :
        splitEquiv targetEmbedding middle = (sourceLabel inputRest, inputRest) ↔
          middle = expectedPhysical := by
      constructor
      · intro hm
        apply (splitEquiv targetEmbedding).injective
        exact hm.trans hsplitExpected.symm
      · intro hm
        exact congrArg (splitEquiv targetEmbedding) hm |>.trans hsplitExpected
    have hentry' :
        (Circuit.matrix (Circuit.ofCodes layout.width
          (blockCopyCodes (layout.replyBase + 1)
            (layout.secondBase + (2 * securityParameter + 1))
            layout.ciphertextWidth)) : Matrix _ _ ℂ) middle inputPhysical =
          if splitEquiv targetEmbedding middle =
            (sourceLabel inputRest, inputRest) then 1 else 0 := by
      simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply, coherentRecord,
        hinputPhysical, targetEmbedding, sourceLabel] using hentry
    rw [hentry', if_congr hcoordinates rfl rfl]
  have hmapEntry :
      (Circuit.matrix (secondCircuit.mapWires layout.secondEmbedding) : Matrix _ _ ℂ)
          (physicalState secondOut replyOut savedOut) expectedPhysical =
        (Circuit.matrix secondCircuit : Matrix _ _ ℂ)
            secondOut (secondInput (ciphertext replyIn) memoryIn) *
          if replyOut = replyIn ∧ savedOut = savedIn then 1 else 0 := by
    have hsplit := Circuit.matrix_mapWires_splitEquiv layout.secondEmbedding secondCircuit
    have hentry := congrFun (congrFun hsplit
      (secondOut, (splitEquiv replyEmbedding).symm (replyOut, savedOut)))
      (secondInput (ciphertext replyIn) memoryIn,
        (splitEquiv replyEmbedding).symm (replyIn, savedIn))
    simpa only [Matrix.submatrix_apply, kroneckerMap_apply, Matrix.one_apply,
      physicalState, expectedPhysical, Equiv.apply_eq_iff_eq, Prod.mk.injEq,
      true_and] using hentry
  simp only [physical, Matrix.submatrix_apply, kroneckerMap_apply, Matrix.one_apply,
    suffixCircuit, Circuit.matrix_append, Submonoid.coe_mul, Matrix.mul_apply]
  rw [show physicalState (secondInput (fun _ => false) memoryIn) replyIn savedIn =
      inputPhysical from rfl]
  simp only [hcopyEntry, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
    reduceIte, hmapEntry, Matrix.blockDiagonal_apply, block,
    Matrix.submatrix_apply, kroneckerMap_apply, Matrix.one_apply]
  by_cases hreply : replyOut = replyIn <;>
    by_cases hsaved : savedOut = savedIn <;>
      by_cases hreference : referenceOut = referenceIn <;>
        simp [hreply, hsaved, hreference]

/-- **The actual reversible B2 service discards its full request and records its complete reply.**
For a fixed truncated-syndrome sample, the discarded service environment is injective in the
two-message request and hidden bit. Tracing it therefore removes all cross-request coherence,
including between distinct requests that emit the same retained reply. The retained record is the
complete `[hidden bit | u | v]` reply emitted by the service. The identity accepts an arbitrary,
possibly entangled state on the request, hidden bit and saved reference, and permits a
full-reply-selected continuation on that reference; no product-state or independence hypothesis
is used. To preserve an inaccessible subfactor, that continuation must be instantiated as the
active continuation tensored with its identity.

The original hidden register is part of the discarded service environment, rather than being
duplicated in the output. The continuation acts only on the saved reference factor; in the B2
controller this is where the saved first-stage state and inaccessible reference live. The
preceding `matrix_b2ServiceReplyCopy_initializedInput` supplies the physical service-and-reply-copy
bridge, and `matrix_b2ReplyCopySecondStage_withReference` supplies the subsequent complete-reply-
controlled copy-and-second-stage identity. Composing those identities through the controller
prefix and complete reply mixture, then moving and comparing the guess, remains open; this is not
the native B2 success-law or a security theorem. -/
theorem partialTraceLeft_b2ServiceEnvironment_fullReply (P : PKEParams)
    (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    {Reference ι' : Type*} [Fintype Reference] [DecidableEq Reference]
    (V : (Fin (1 + (P.n + P.codeLen)) → Bool) →
      Matrix ι' Reference ℂ)
    (ρ : Matrix ((MessagePair (PKEMessage P) × Bool) × Reference)
      ((MessagePair (PKEMessage P) × Bool) × Reference) ℂ) :
    let serviceInput : MessagePair (PKEMessage P) × Bool →
        Fin (b2ServiceDescription P securityParameter encoder).width → Bool :=
      fun request =>
        inputState (b2ServiceDescription P securityParameter encoder).width
          (encPair encUnary encBits (securityParameter, sample.toWord) ++
            List.ofFn request.1.msg₀ ++ List.ofFn request.1.msg₁ ++ [request.2])
    let serviceEnvironment : MessagePair (PKEMessage P) × Bool →
        (Fin (b2ServiceDescription P securityParameter encoder).width → Bool) :=
      fun request => classicalRun (b2ServiceCodes P securityParameter encoder)
        (serviceInput request)
    let serviceReply : MessagePair (PKEMessage P) × Bool →
        Fin (1 + (P.n + P.codeLen)) → Bool :=
      fun request =>
        let environment := serviceEnvironment request
        let ciphertext := b2ServiceReadout P environment
        Fin.append
          (fun _ : Fin 1 => readBit environment
            (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k))
          (Fin.append ciphertext.u ciphertext.v)
    let fullReply : MessagePair (PKEMessage P) × Bool →
        Fin (1 + (P.n + P.codeLen)) → Bool :=
      fun request =>
        let ciphertext := sample.toPKECiphertext P
          (encoder.eval interpretation) (request.1.select request.2)
        Fin.append (fun _ : Fin 1 => request.2) (Fin.append ciphertext.u ciphertext.v)
    partialTraceLeft
        (densityConj
          (((1 : Matrix
                (Fin (b2ServiceDescription P securityParameter encoder).width → Bool)
                (Fin (b2ServiceDescription P securityParameter encoder).width → Bool) ℂ) ⊗ₖ
              (Matrix.blockDiagonal V).submatrix Prod.swap Prod.swap) *
            coherentEnvironmentRecord serviceEnvironment serviceReply) ρ) =
      ∑ reply, (pureState (ket reply) ⊗ₖ
        densityConj (V reply)
          (partialTraceLeft
            (classicalDensityBranch (fullReply ∘ Prod.fst) reply ρ))) := by
  classical
  dsimp only
  have hfit (request : MessagePair (PKEMessage P) × Bool) :
      (encPair encUnary encBits (securityParameter, sample.toWord) ++
        List.ofFn request.1.msg₀ ++ List.ofFn request.1.msg₁ ++ [request.2]).length ≤
          (b2ServiceDescription P securityParameter encoder).width := by
    have h := (wellFormed_b2ServiceDescription P securityParameter encoder).input_le
    simp only [b2ServiceDescription_quantumInputWidth] at h
    simp only [List.length_append, length_encPair, encUnary_apply,
      List.length_replicate, encBits_apply, TruncatedSyndromeSample.length_toWord,
      List.length_ofFn, List.length_singleton]
    omega
  have hinputHidden (request : MessagePair (PKEMessage P) × Bool) :
      readBit
          (inputState (b2ServiceDescription P securityParameter encoder).width
            (encPair encUnary encBits (securityParameter, sample.toWord) ++
              List.ofFn request.1.msg₀ ++ List.ofFn request.1.msg₁ ++ [request.2]))
          (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k) = request.2 := by
    rw [readBit_inputState (hfit request)]
    let inputPrefix := encPair encUnary encBits (securityParameter, sample.toWord) ++
      List.ofFn request.1.msg₀ ++ List.ofFn request.1.msg₁
    have hprefix : inputPrefix.length =
        2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k := by
      dsimp only [inputPrefix]
      simp only [List.length_append, length_encPair, encUnary_apply,
        List.length_replicate, encBits_apply, TruncatedSyndromeSample.length_toWord,
        List.length_ofFn]
      omega
    change (inputPrefix ++ [request.2]).getD
      (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k) false = request.2
    rw [List.getD_append_right inputPrefix [request.2] false _ (by omega), hprefix]
    simp
  have hserviceHidden (request : MessagePair (PKEMessage P) × Bool) :
      readBit
          (classicalRun (b2ServiceCodes P securityParameter encoder)
            (inputState (b2ServiceDescription P securityParameter encoder).width
              (encPair encUnary encBits (securityParameter, sample.toWord) ++
                List.ofFn request.1.msg₀ ++ List.ofFn request.1.msg₁ ++ [request.2])))
          (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k) = request.2 := by
    rw [readBit_classicalRun_b2ServiceCodes_quantumInput P securityParameter encoder _
      ⟨2 * P.k, by omega⟩, hinputHidden]
  have hserviceReply :
      (fun request : MessagePair (PKEMessage P) × Bool =>
        let environment := classicalRun (b2ServiceCodes P securityParameter encoder)
          (inputState (b2ServiceDescription P securityParameter encoder).width
            (encPair encUnary encBits (securityParameter, sample.toWord) ++
              List.ofFn request.1.msg₀ ++ List.ofFn request.1.msg₁ ++ [request.2]))
        let ciphertext := b2ServiceReadout P environment
        Fin.append
          (fun _ : Fin 1 => readBit environment
            (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k))
          (Fin.append ciphertext.u ciphertext.v)) =
        (fun request : MessagePair (PKEMessage P) × Bool =>
          let ciphertext := sample.toPKECiphertext P
            (encoder.eval interpretation) (request.1.select request.2)
          Fin.append (fun _ : Fin 1 => request.2) (Fin.append ciphertext.u ciphertext.v)) := by
    funext request
    dsimp only
    rw [hserviceHidden]
    rw [b2ServiceReadout_classicalRun P securityParameter encoder sample request.1 request.2]
  rw [hserviceReply]
  apply partialTraceLeft_densityConj_controlled_coherentEnvironmentRecord
  let requestWord : MessagePair (PKEMessage P) × Bool → List Bool :=
    fun request =>
      encPair encUnary encBits (securityParameter, sample.toWord) ++
        List.ofFn request.1.msg₀ ++ List.ofFn request.1.msg₁ ++ [request.2]
  have hrequestWord : Function.Injective requestWord := by
    rintro ⟨messagesLeft, hiddenLeft⟩ ⟨messagesRight, hiddenRight⟩ hword
    have htail :
        List.ofFn messagesLeft.msg₀ ++ (List.ofFn messagesLeft.msg₁ ++ [hiddenLeft]) =
          List.ofFn messagesRight.msg₀ ++ (List.ofFn messagesRight.msg₁ ++ [hiddenRight]) := by
      exact (List.append_inj
        (by simpa only [requestWord, List.append_assoc] using hword) rfl).2
    have hrequestParts := List.append_inj htail (by simp only [List.length_ofFn])
    have hmessageZeroList :
        List.ofFn messagesLeft.msg₀ = List.ofFn messagesRight.msg₀ := hrequestParts.1
    have hrest :
        List.ofFn messagesLeft.msg₁ ++ [hiddenLeft] =
          List.ofFn messagesRight.msg₁ ++ [hiddenRight] := hrequestParts.2
    have hhiddenParts := List.append_inj hrest (by simp only [List.length_ofFn])
    have hmessageOneList :
        List.ofFn messagesLeft.msg₁ = List.ofFn messagesRight.msg₁ := hhiddenParts.1
    have hhidden : hiddenLeft = hiddenRight := by
      exact (List.cons.inj hhiddenParts.2).1
    have hmessages : messagesLeft = messagesRight :=
      MessagePair.equivProd.injective
        (Prod.ext (List.ofFn_injective hmessageZeroList)
          (List.ofFn_injective hmessageOneList))
    exact Prod.ext
      hmessages hhidden
  intro requestLeft requestRight henvironment
  apply hrequestWord
  have hinput := congrArg
    (classicalUnrun (b2ServiceCodes P securityParameter encoder)) henvironment
  rw [classicalUnrun_classicalRun
      (isClassical_b2ServiceDescription P securityParameter encoder),
    classicalUnrun_classicalRun
      (isClassical_b2ServiceDescription P securityParameter encoder)] at hinput
  have hbits := congrArg List.ofFn hinput
  rw [ofFn_inputState (hfit requestLeft), ofFn_inputState (hfit requestRight)] at hbits
  change
    requestWord requestLeft ++
        List.replicate ((b2ServiceDescription P securityParameter encoder).width -
          (requestWord requestLeft).length) false =
      requestWord requestRight ++
        List.replicate ((b2ServiceDescription P securityParameter encoder).width -
          (requestWord requestRight).length) false at hbits
  have hlength : (requestWord requestLeft).length = (requestWord requestRight).length := by
    simp only [requestWord, List.length_append, List.length_ofFn, List.length_singleton]
  exact (List.append_inj hbits hlength).1

end Cslib.Crypto.HQC
