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

/-- **The actual reversible B2 service dephases exactly its complete reply.**  For a fixed
truncated-syndrome sample and measured message pair, the discarded service environment
distinguishes precisely the complete `[hidden bit | u | v]` labels emitted by the service.  The
identity retains an arbitrary reference register and permits a branch-dependent continuation
selected by the full reply; no product-state or independence hypothesis is used.

This is the service-level density identity.  Connecting its two coherent records and continuation
to the physical controller register blocks, and then to the final comparison measurement, are
separate obligations; this statement is not the native B2 success-law or a security theorem. -/
theorem partialTraceLeft_b2ServiceEnvironment_fullReply (P : PKEParams)
    (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P))
    {Reference ι' : Type*} [Fintype Reference] [DecidableEq Reference]
    (V : (Fin (1 + (P.n + P.codeLen)) → Bool) →
      Matrix ι' (Bool × Reference) ℂ)
    (ρ : Matrix (Bool × Reference) (Bool × Reference) ℂ) :
    let serviceInput : Bool →
        Fin (b2ServiceDescription P securityParameter encoder).width → Bool :=
      fun hidden =>
        inputState (b2ServiceDescription P securityParameter encoder).width
          (encPair encUnary encBits (securityParameter, sample.toWord) ++
            List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden])
    let serviceEnvironment : (Bool × Reference) →
        (Fin (b2ServiceDescription P securityParameter encoder).width → Bool) :=
      fun p => classicalRun (b2ServiceCodes P securityParameter encoder) (serviceInput p.1)
    let serviceReply : (Bool × Reference) → Fin (1 + (P.n + P.codeLen)) → Bool :=
      fun p =>
        let environment := serviceEnvironment p
        let ciphertext := b2ServiceReadout P environment
        Fin.append
          (fun _ : Fin 1 => readBit environment
            (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k))
          (Fin.append ciphertext.u ciphertext.v)
    let fullReply : (Bool × Reference) → Fin (1 + (P.n + P.codeLen)) → Bool :=
      fun p =>
        let ciphertext := sample.toPKECiphertext P
          (encoder.eval interpretation) (messages.select p.1)
        Fin.append (fun _ : Fin 1 => p.1) (Fin.append ciphertext.u ciphertext.v)
    partialTraceLeft
        (densityConj
          (((1 : Matrix
                (Fin (b2ServiceDescription P securityParameter encoder).width → Bool)
                (Fin (b2ServiceDescription P securityParameter encoder).width → Bool) ℂ) ⊗ₖ
              (Matrix.blockDiagonal V).submatrix Prod.swap Prod.swap) *
            (coherentRecord (serviceEnvironment ∘ Prod.snd) *
              coherentRecord serviceReply)) ρ) =
      ∑ reply, (pureState (ket reply) ⊗ₖ
        densityConj (V reply) (classicalDensityBranch fullReply reply ρ)) := by
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
      (fun p : Bool × Reference =>
        let environment := classicalRun (b2ServiceCodes P securityParameter encoder)
          (inputState (b2ServiceDescription P securityParameter encoder).width
            (encPair encUnary encBits (securityParameter, sample.toWord) ++
              List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [p.1]))
        let ciphertext := b2ServiceReadout P environment
        Fin.append
          (fun _ : Fin 1 => readBit environment
            (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k))
          (Fin.append ciphertext.u ciphertext.v)) =
        (fun p : Bool × Reference =>
          let ciphertext := sample.toPKECiphertext P
            (encoder.eval interpretation) (messages.select p.1)
          Fin.append (fun _ : Fin 1 => p.1) (Fin.append ciphertext.u ciphertext.v)) := by
    funext p
    dsimp only
    rw [hserviceHidden]
    rw [b2ServiceReadout_classicalRun P securityParameter encoder sample messages p.1]
  rw [hserviceReply]
  apply partialTraceLeft_densityConj_controlled_environmentRecord
  rintro ⟨hiddenLeft, _referenceLeft⟩ ⟨hiddenRight, _referenceRight⟩
  constructor
  · intro henvironment
    have hhidden := congrArg
      (fun state => readBit state
        (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k))
      henvironment
    rw [hserviceHidden hiddenLeft, hserviceHidden hiddenRight] at hhidden
    subst hiddenRight
    rfl
  · intro hreply
    have hhidden : hiddenLeft = hiddenRight := by
      have h := congrFun hreply
        (Fin.castAdd (P.n + P.codeLen) (0 : Fin 1))
      simpa only [Fin.append_left] using h
    subst hiddenRight
    rfl

end Cslib.Crypto.HQC
