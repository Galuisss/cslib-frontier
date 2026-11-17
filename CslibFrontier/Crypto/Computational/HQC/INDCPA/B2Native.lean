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
* `Cslib.Crypto.HQC.matrix_b2ServiceBlock_initializedInput_withReference`: the actual embedded
  service block, on its initialized input, coherently records its complete reversible environment
  while retaining every other controller wire and an arbitrary reference.
* `Cslib.Crypto.HQC.matrix_b2ServiceReplyCopy_initializedInput`: the actual embedded service
  followed by its physical ciphertext copy produces the retained hidden-bit-and-ciphertext reply
  while preserving every other controller wire.
* `Cslib.Crypto.HQC.partialTraceLeft_b2ServiceEnvironment_fullReply`: discarding the actual
  reversible service environment dephases exactly the complete hidden-bit-and-ciphertext reply,
  while retaining an arbitrary reference and a reply-controlled continuation.

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
word.  Every other physical wire is retained as one arbitrary factor, so the equality can be
used under a density matrix entangled with the saved first-stage state.

This is the exact input-space contract for the still-separate prefix proof.  It does not yet
include the ciphertext-to-second-input copy, second-stage execution or final comparison. -/
theorem matrix_b2ServiceReplyCopy_initializedInput (P : PKEParams)
    (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P))
    (first second : UniformOracleCircuitFamily) :
    let layout := b2ClassicalQueryLayout P encoder first second securityParameter
    let ServiceState := Fin layout.service.width → Bool
    let replyEmbedding : Fin (1 + layout.ciphertextWidth) ↪
        {j : Fin layout.width // ¬ ∃ i, layout.serviceEmbedding i = j} :=
      { toFun := fun wire => ⟨⟨layout.replyBase + wire, by
          simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
          omega⟩, by
            rintro ⟨serviceWire, hserviceWire⟩
            have hlt := layout.serviceEmbedding_lt_replyBase serviceWire
            have heq := congrArg Fin.val hserviceWire
            change layout.serviceWire serviceWire = layout.replyBase + wire at heq
            omega⟩
        inj' := fun left right heq => Fin.ext <| by
          have heq := congrArg (fun wire => ((wire.1 : Fin layout.width) : ℕ)) heq
          change layout.replyBase + left = layout.replyBase + right at heq
          omega }
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
    let serviceInput : Bool → ServiceState :=
      fun hidden =>
        inputState layout.service.width
          (encPair encUnary encBits (securityParameter, sample.toWord) ++
            List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden])
    let serviceEnvironment : Bool → ServiceState :=
      fun hidden => classicalRun (b2ServiceCodes P securityParameter encoder)
        (serviceInput hidden)
    let serviceReply : ServiceState → Bool →
        Fin (1 + layout.ciphertextWidth) → Bool :=
      fun environment hidden =>
        Fin.append (fun _ : Fin 1 => hidden)
          (fun i : Fin layout.ciphertextWidth => readBit environment i)
    let serviceMatrix : Matrix (ServiceState × (Bool × (Saved → Bool)))
        (Bool × (Saved → Bool)) ℂ :=
      (Circuit.matrix
        ((Circuit.ofPhaseCodes layout.service.width
          layout.service.instructions.zeroOraclePhaseCodes).mapWires
            layout.serviceEmbedding) : Matrix _ _ ℂ).submatrix
        (fun p => physicalState p.1 (initialReply p.2.1) p.2.2)
        (fun p => physicalState (serviceInput p.1) (initialReply p.1) p.2)
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
        (fun hidden => serviceReply (serviceEnvironment hidden) hidden) := by
  classical
  let layout := b2ClassicalQueryLayout P encoder first second securityParameter
  let ServiceState := Fin layout.service.width → Bool
  let ServiceRest := {j : Fin layout.width //
    ¬ ∃ i, layout.serviceEmbedding i = j}
  let replyEmbedding : Fin (1 + layout.ciphertextWidth) ↪ ServiceRest :=
    { toFun := fun wire => ⟨⟨layout.replyBase + wire, by
        simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
        omega⟩, by
          rintro ⟨serviceWire, hserviceWire⟩
          have hlt := layout.serviceEmbedding_lt_replyBase serviceWire
          have heq := congrArg Fin.val hserviceWire
          change layout.serviceWire serviceWire = layout.replyBase + wire at heq
          omega⟩
      inj' := fun left right heq => Fin.ext <| by
        have heq := congrArg (fun wire => ((wire.1 : Fin layout.width) : ℕ)) heq
        change layout.replyBase + left = layout.replyBase + right at heq
        omega }
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
  let serviceInput : Bool → ServiceState :=
    fun hidden =>
      inputState layout.service.width
        (encPair encUnary encBits (securityParameter, sample.toWord) ++
          List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden])
  let serviceEnvironment : Bool → ServiceState :=
    fun hidden => classicalRun (b2ServiceCodes P securityParameter encoder)
      (serviceInput hidden)
  let serviceReply : ServiceState → Bool →
      Fin (1 + layout.ciphertextWidth) → Bool :=
    fun environment hidden =>
      Fin.append (fun _ : Fin 1 => hidden)
        (fun i : Fin layout.ciphertextWidth => readBit environment i)
  let serviceMatrix : Matrix (ServiceState × (Bool × (Saved → Bool)))
      (Bool × (Saved → Bool)) ℂ :=
    (Circuit.matrix
      ((Circuit.ofPhaseCodes layout.service.width
        layout.service.instructions.zeroOraclePhaseCodes).mapWires
          layout.serviceEmbedding) : Matrix _ _ ℂ).submatrix
      (fun p => physicalState p.1 (initialReply p.2.1) p.2.2)
      (fun p => physicalState (serviceInput p.1) (initialReply p.1) p.2)
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
      (fun hidden => serviceReply (serviceEnvironment hidden) hidden)
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
      coherentEnvironmentRecord serviceEnvironment (fun hidden : Bool => hidden) := by
    ext ⟨environmentOut, hiddenOut, savedOut⟩ ⟨hiddenIn, savedIn⟩
    have hservice := matrix_b2ServiceBlock_initializedInput_withReference P securityParameter
      encoder sample messages first second (Reference := Unit)
    dsimp only at hservice
    have hentry := congrFun (congrFun hservice
      (environmentOut,
        (splitEquiv replyEmbedding).symm (initialReply hiddenOut, savedOut), ()))
      ((splitEquiv replyEmbedding).symm (initialReply hiddenIn, savedIn), ())
    simp only [Matrix.submatrix_apply, kroneckerMap_apply, Matrix.one_apply,
      coherentRecord] at hentry
    have hhidden :
        readBit
            ((splitEquiv layout.serviceEmbedding).symm
              (fun _ => false,
                (splitEquiv replyEmbedding).symm (initialReply hiddenIn, savedIn)))
            layout.replyBase = hiddenIn := by
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
  ext ⟨environmentOut, replyOut, savedOut⟩ ⟨hiddenIn, savedIn⟩
  simp only [Matrix.mul_apply, coherentEnvironmentRecord, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, reduceIte, Prod.mk.injEq]
  let htarget : layout.replyBase + 1 + layout.ciphertextWidth ≤ layout.width := by
    simp only [ClassicalQueryLayout.width, ClassicalQueryLayout.secondBase]
    omega
  let targetEmbedding := blockEmb (layout.replyBase + 1) htarget
  let TargetRest := {j : Fin layout.width // ¬ ∃ i, targetEmbedding i = j}
  let inputPhysical := physicalState (serviceEnvironment hiddenIn)
    (initialReply hiddenIn) savedIn
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
          (serviceEnvironment hiddenIn,
            (splitEquiv replyEmbedding).symm (initialReply hiddenIn, savedIn))
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
        readBit (serviceEnvironment hiddenIn) i := by
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
          (serviceEnvironment hiddenIn,
            (splitEquiv replyEmbedding).symm (initialReply hiddenIn, savedIn))
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
  let expectedReply := serviceReply (serviceEnvironment hiddenIn) hiddenIn
  let expectedPhysical := physicalState (serviceEnvironment hiddenIn) expectedReply savedIn
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
            (serviceEnvironment hiddenIn,
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
              (serviceEnvironment hiddenIn,
                (splitEquiv replyEmbedding).symm (expectedReply, savedIn))
              (layout.serviceEmbedding i) =
            (splitEquiv layout.serviceEmbedding).symm
              (serviceEnvironment hiddenIn,
                (splitEquiv replyEmbedding).symm (initialReply hiddenIn, savedIn))
              (layout.serviceEmbedding i)
        rw [splitEquiv_symm_apply_wire, splitEquiv_symm_apply_wire]
      · let serviceRest : ServiceRest := ⟨j.1, hservice⟩
        change
          (splitEquiv layout.serviceEmbedding).symm
              (serviceEnvironment hiddenIn,
                (splitEquiv replyEmbedding).symm (expectedReply, savedIn)) j.1 =
            (splitEquiv layout.serviceEmbedding).symm
              (serviceEnvironment hiddenIn,
                (splitEquiv replyEmbedding).symm (initialReply hiddenIn, savedIn)) j.1
        rw [splitEquiv_symm_apply_of_not _ _ _ _ hservice,
          splitEquiv_symm_apply_of_not _ _ _ _ hservice]
        change
          (splitEquiv replyEmbedding).symm (expectedReply, savedIn) serviceRest =
            (splitEquiv replyEmbedding).symm (initialReply hiddenIn, savedIn) serviceRest
        by_cases hreply : ∃ i, replyEmbedding i = serviceRest
        · obtain ⟨i, hi⟩ := hreply
          rw [← hi, splitEquiv_symm_apply_wire, splitEquiv_symm_apply_wire]
          by_cases hi0 : i = 0
          · subst i
            dsimp only [expectedReply, serviceReply, initialReply]
            change hiddenIn = hiddenIn
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
        environmentOut = serviceEnvironment hiddenIn ∧
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
          (serviceEnvironment hiddenIn, hiddenIn, savedIn) =
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

/-- **The actual reversible B2 service dephases exactly its complete reply.**  For a fixed
truncated-syndrome sample and measured message pair, the discarded service environment
distinguishes precisely the complete `[hidden bit | u | v]` labels emitted by the service.  The
identity accepts an arbitrary, possibly entangled state on the hidden bit and saved reference,
and permits a full-reply-selected continuation on that reference; no product-state or
independence hypothesis is used. To preserve an inaccessible subfactor, that continuation must
be instantiated as the active continuation tensored with its identity.

The original hidden register is part of the discarded service environment, rather than being
duplicated in the output. The continuation acts only on the saved reference factor; in the B2
controller this is where the saved first-stage state and inaccessible reference live. The
preceding `matrix_b2ServiceReplyCopy_initializedInput` supplies the physical service-and-reply-copy
bridge. Composing it with the controller prefix, the reply-to-second-stage copy, the actual second
stage and final comparison remains open; this is not the native B2 success-law or a security
theorem. -/
theorem partialTraceLeft_b2ServiceEnvironment_fullReply (P : PKEParams)
    (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P))
    {Reference ι' : Type*} [Fintype Reference] [DecidableEq Reference]
    (V : (Fin (1 + (P.n + P.codeLen)) → Bool) →
      Matrix ι' Reference ℂ)
    (ρ : Matrix (Bool × Reference) (Bool × Reference) ℂ) :
    let serviceInput : Bool →
        Fin (b2ServiceDescription P securityParameter encoder).width → Bool :=
      fun hidden =>
        inputState (b2ServiceDescription P securityParameter encoder).width
          (encPair encUnary encBits (securityParameter, sample.toWord) ++
            List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden])
    let serviceEnvironment : Bool →
        (Fin (b2ServiceDescription P securityParameter encoder).width → Bool) :=
      fun hidden => classicalRun (b2ServiceCodes P securityParameter encoder)
        (serviceInput hidden)
    let serviceReply : Bool → Fin (1 + (P.n + P.codeLen)) → Bool :=
      fun hidden =>
        let environment := serviceEnvironment hidden
        let ciphertext := b2ServiceReadout P environment
        Fin.append
          (fun _ : Fin 1 => readBit environment
            (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k))
          (Fin.append ciphertext.u ciphertext.v)
    let fullReply : Bool → Fin (1 + (P.n + P.codeLen)) → Bool :=
      fun hidden =>
        let ciphertext := sample.toPKECiphertext P
          (encoder.eval interpretation) (messages.select hidden)
        Fin.append (fun _ : Fin 1 => hidden) (Fin.append ciphertext.u ciphertext.v)
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
  have hfit (hidden : Bool) :
      (encPair encUnary encBits (securityParameter, sample.toWord) ++
        List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden]).length ≤
          (b2ServiceDescription P securityParameter encoder).width := by
    have h := (wellFormed_b2ServiceDescription P securityParameter encoder).input_le
    simp only [b2ServiceDescription_quantumInputWidth] at h
    simp only [List.length_append, length_encPair, encUnary_apply,
      List.length_replicate, encBits_apply, TruncatedSyndromeSample.length_toWord,
      List.length_ofFn, List.length_singleton]
    omega
  have hinputHidden (hidden : Bool) :
      readBit
          (inputState (b2ServiceDescription P securityParameter encoder).width
            (encPair encUnary encBits (securityParameter, sample.toWord) ++
              List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden]))
          (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k) = hidden := by
    rw [readBit_inputState (hfit hidden)]
    let inputPrefix := encPair encUnary encBits (securityParameter, sample.toWord) ++
      List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁
    have hprefix : inputPrefix.length =
        2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k := by
      dsimp only [inputPrefix]
      simp only [List.length_append, length_encPair, encUnary_apply,
        List.length_replicate, encBits_apply, TruncatedSyndromeSample.length_toWord,
        List.length_ofFn]
      omega
    change (inputPrefix ++ [hidden]).getD
      (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k) false = hidden
    rw [List.getD_append_right inputPrefix [hidden] false _ (by omega), hprefix]
    simp
  have hserviceHidden (hidden : Bool) :
      readBit
          (classicalRun (b2ServiceCodes P securityParameter encoder)
            (inputState (b2ServiceDescription P securityParameter encoder).width
              (encPair encUnary encBits (securityParameter, sample.toWord) ++
                List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden])))
          (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k) = hidden := by
    rw [readBit_classicalRun_b2ServiceCodes_quantumInput P securityParameter encoder _
      ⟨2 * P.k, by omega⟩, hinputHidden]
  have hserviceReply :
      (fun hidden : Bool =>
        let environment := classicalRun (b2ServiceCodes P securityParameter encoder)
          (inputState (b2ServiceDescription P securityParameter encoder).width
            (encPair encUnary encBits (securityParameter, sample.toWord) ++
              List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden]))
        let ciphertext := b2ServiceReadout P environment
        Fin.append
          (fun _ : Fin 1 => readBit environment
            (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k))
          (Fin.append ciphertext.u ciphertext.v)) =
        (fun hidden : Bool =>
          let ciphertext := sample.toPKECiphertext P
            (encoder.eval interpretation) (messages.select hidden)
          Fin.append (fun _ : Fin 1 => hidden) (Fin.append ciphertext.u ciphertext.v)) := by
    funext hidden
    dsimp only
    rw [hserviceHidden]
    rw [b2ServiceReadout_classicalRun P securityParameter encoder sample messages hidden]
  rw [hserviceReply]
  apply partialTraceLeft_densityConj_controlled_coherentEnvironmentRecord
  intro hiddenLeft hiddenRight henvironment
  have hhidden := congrArg
    (fun state => readBit state
      (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k))
    henvironment
  rw [hserviceHidden hiddenLeft, hserviceHidden hiddenRight] at hhidden
  exact hhidden

end Cslib.Crypto.HQC
