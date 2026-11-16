/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Input
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Code.NativeCompiler
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
public import CslibFrontier.Computability.Circuit.Quantum.Parallel
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.BlockCopy.NativeCompiler
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling
public import CslibFrontier.Crypto.Computational.HQC.DQCSD
public import CslibFrontier.Crypto.Computational.HQC.INDCPA
import Mathlib.Data.List.GetD

/-!
# Reversible service for the HQC 3-DQCSD reduction

The second HQC IND-CPA reduction reads a 3-DQCSD sample, asks the first adversary stage for two
messages, samples a hidden bit, and supplies the second stage with the sample's first value and
the sample's second value masked by the selected encoded message. `b2ServiceDescription` is the
classical reversible service used at that interaction boundary.

The service saves the complete encoded family input before using its prefix as the output block.
It selects one of the two messages with three gates per bit, runs the existing reversible
realization `Reversible.samplerClassicalCodes` of a typed Boolean encoder, and XORs the copied
encoder output into the sample's second value. The hidden bit is an input control and is not an
output of the service; the surrounding controller copies it to a protected record before this
service runs.

The encoder parameter here is an existing typed De Morgan circuit. No concrete retained circuit
for the NIST HQC concatenated encoder is supplied by this module; instantiating this component
from the retained Reed--Solomon, Reed--Muller and GF(256) prerequisites remains open.

## Main definitions

* `Cslib.Crypto.HQC.b2ServiceDescription`: the query-free reversible service description.
* `Cslib.Crypto.HQC.b2ServiceReadout`: its ciphertext-prefix interpretation.
* `Cslib.Crypto.HQC.b2ServiceCompiler`: the retained description compiler for fixed parameters
  and a fixed installed Boolean encoder.

## Main results

* `Cslib.Crypto.HQC.b2ServiceReadout_classicalRun`: on every encoded sample, message pair and
  hidden bit, the service emits exactly `TruncatedSyndromeSample.toPKECiphertext` for the selected
  message and the supplied Boolean encoder.
* `Cslib.Crypto.HQC.readBit_classicalRun_b2ServiceCodes_hidden`: the complete reversible service
  leaves its hidden-bit input unchanged for every basis state.

This construction is original infrastructure for [HQC2026], Theorem 6.3, pp. 61--64.
-/

public section

namespace Cslib.Crypto.HQC

open Cslib.Quantum Cslib.Quantum.GateCode Cslib.Quantum.Reversible
open Circuits Circuits.Boolean Turing.MultiTapeTM Turing.MultiTapeTM.Internal
open Turing.MultiTapeTM.Internal.NativeCompiler

private def b2HeaderWidth (securityParameter : ℕ) : ℕ :=
  2 * securityParameter + 1

private def b2SampleWidth (P : PKEParams) : ℕ :=
  3 * P.n + P.codeLen

private def b2ServiceInputWidth (P : PKEParams) (securityParameter : ℕ) : ℕ :=
  b2HeaderWidth securityParameter + b2SampleWidth P

private def b2ServiceRequestWidth (P : PKEParams) : ℕ :=
  2 * P.k

private def b2ServiceCiphertextWidth (P : PKEParams) : ℕ :=
  P.n + P.codeLen

private def b2ServiceSavedInputBase (P : PKEParams) (securityParameter : ℕ) : ℕ :=
  b2ServiceInputWidth P securityParameter + b2ServiceRequestWidth P + 1

private def b2ServiceEncoderBase (P : PKEParams) (securityParameter : ℕ) : ℕ :=
  b2ServiceSavedInputBase P securityParameter + b2ServiceInputWidth P securityParameter

private def b2ServiceEncoderOutputBase (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) : ℕ :=
  b2ServiceEncoderBase P securityParameter + samplerOutputStart P.k encoder.code

private def b2ServiceWidth (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) : ℕ :=
  b2ServiceEncoderBase P securityParameter + samplerWidth P.k encoder.code

private def b2ControlledBlockCodes (control source target count : ℕ) : List GateCode :=
  (List.range count).map fun offset =>
    (false, target + offset, [control, source + offset])

private theorem isClassical_b2ControlledBlockCodes
    {control source target count width : ℕ}
    (hcontrolTarget : ∀ offset < count, control ≠ target + offset)
    (hsourceTarget : source + count ≤ target ∨ target + count ≤ source)
    (hcontrolSource : ∀ offset < count, control ≠ source + offset)
    (hcontrol : control < width) (hsource : source + count ≤ width)
    (htarget : target + count ≤ width) :
    IsClassical width (b2ControlledBlockCodes control source target count) := by
  intro gate hgate
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hgate
  have hoffset' := List.mem_range.mp hoffset
  refine ⟨rfl, ?_⟩
  simp only [GateCode.WellFormed, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.succ_le_succ_iff, Nat.zero_le, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, List.nodup_nil, not_false_eq_true, and_true,
    true_and, forall_eq_or_imp, forall_eq]
  refine ⟨⟨?_, hcontrolSource offset hoffset'⟩, ?_, ?_, ?_⟩
  · simp only [not_or]
    refine ⟨Ne.symm (hcontrolTarget offset hoffset'), ?_⟩
    rcases hsourceTarget with hsourceTarget | hsourceTarget <;> omega
  · omega
  · omega
  · omega

private theorem readBit_classicalRun_blockCopyCodes_of_outside
    {source target count width wire : ℕ}
    (hwire : wire < target ∨ target + count ≤ wire) (state : Fin width → Bool) :
    readBit (classicalRun (blockCopyCodes source target count) state) wire =
      readBit state wire := by
  apply readBit_classicalRun_of_forall_ne
  intro gate hgate
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hgate
  have hoffset' := List.mem_range.mp hoffset
  simp only
  omega

private theorem readBit_classicalRun_b2ControlledBlockCodes_of_outside
    {control source target count width wire : ℕ}
    (hwire : wire < target ∨ target + count ≤ wire) (state : Fin width → Bool) :
    readBit (classicalRun (b2ControlledBlockCodes control source target count) state) wire =
      readBit state wire := by
  apply readBit_classicalRun_of_forall_ne
  intro gate hgate
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hgate
  have hoffset' := List.mem_range.mp hoffset
  simp only
  omega

private theorem readBit_classicalRun_b2ControlledBlockCodes
    {control source target count width : ℕ}
    (htarget : target + count ≤ width)
    (hcontrolTarget : ∀ offset < count, control ≠ target + offset)
    (hsourceTarget : source + count ≤ target ∨ target + count ≤ source)
    (state : Fin width → Bool) {offset : ℕ} (hoffset : offset < count) :
    readBit (classicalRun (b2ControlledBlockCodes control source target count) state)
        (target + offset) =
      (readBit state (target + offset) ^^
        (readBit state control && readBit state (source + offset))) := by
  have hlt : ∀ gate ∈ b2ControlledBlockCodes control source target count,
      gate.2.1 < width := by
    intro gate hgate
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hgate
    have hi' := List.mem_range.mp hi
    simp only
    omega
  have hnd :
      ((b2ControlledBlockCodes control source target count).map fun gate => gate.2.1).Nodup := by
    rw [b2ControlledBlockCodes, List.map_map]
    exact List.nodup_range.map fun left right h => by
      simp only [Function.comp_apply] at h
      omega
  have hread : ∀ gate ∈ b2ControlledBlockCodes control source target count,
      ∀ gate' ∈ b2ControlledBlockCodes control source target count,
        gate.2.1 ∉ gate'.2.2 := by
    intro gate hgate gate' hgate'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hgate
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hgate'
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨Ne.symm (hcontrolTarget i hi'), ?_⟩
    rcases hsourceTarget with hsourceTarget | hsourceTarget <;> omega
  have hmem : ((false, target + offset, [control, source + offset]) : GateCode) ∈
      b2ControlledBlockCodes control source target count := by
    rw [b2ControlledBlockCodes, List.mem_map]
    exact ⟨offset, List.mem_range.mpr hoffset, rfl⟩
  simpa using readBit_classicalRun_of_mem hlt hnd hread state hmem

private def b2SelectMessageCodes (P : PKEParams) (securityParameter : ℕ) : List GateCode :=
  let request := b2ServiceInputWidth P securityParameter
  let hidden := request + 2 * P.k
  let target := b2ServiceEncoderBase P securityParameter
  blockCopyCodes request target P.k ++
    b2ControlledBlockCodes hidden request target P.k ++
    b2ControlledBlockCodes hidden (request + P.k) target P.k

private theorem readBit_classicalRun_b2SelectMessageCodes
    (P : PKEParams) (securityParameter width : ℕ)
    (hwidth : b2ServiceEncoderBase P securityParameter + P.k ≤ width)
    (state : Fin width → Bool)
    (hzero : ∀ i < P.k,
      readBit state (b2ServiceEncoderBase P securityParameter + i) = false)
    (i : Fin P.k) :
    readBit (classicalRun (b2SelectMessageCodes P securityParameter) state)
        (b2ServiceEncoderBase P securityParameter + i) =
      bif readBit state (b2ServiceInputWidth P securityParameter + 2 * P.k) then
        readBit state (b2ServiceInputWidth P securityParameter + P.k + i)
      else readBit state (b2ServiceInputWidth P securityParameter + i) := by
  let request := b2ServiceInputWidth P securityParameter
  let hidden := request + 2 * P.k
  let target := b2ServiceEncoderBase P securityParameter
  let copied := classicalRun (blockCopyCodes request target P.k) state
  let selectedZero := classicalRun
    (b2ControlledBlockCodes hidden request target P.k) copied
  have hrequestTarget : request + 2 * P.k + 1 ≤ target := by
    dsimp only [request, target]
    unfold b2ServiceEncoderBase b2ServiceSavedInputBase b2ServiceRequestWidth
    omega
  have hcopyTarget : request + P.k ≤ target := by omega
  have hhiddenTarget : hidden < target := by omega
  have hselectedZeroTarget := readBit_classicalRun_b2ControlledBlockCodes
    (width := width) (control := hidden) (source := request) (target := target)
    (count := P.k) hwidth (by intro offset hoffset; omega) (Or.inl hcopyTarget)
    copied i.2
  have hselectedOneTarget := readBit_classicalRun_b2ControlledBlockCodes
    (width := width) (control := hidden) (source := request + P.k) (target := target)
    (count := P.k) hwidth (by intro offset hoffset; omega)
    (Or.inl (by omega)) selectedZero i.2
  have hcopyTargetBit := readBit_classicalRun_blockCopyCodes
    (width := width) (source := request) (target := target) (count := P.k)
    (Or.inl hcopyTarget) (by omega) hwidth state i.2
  have hcopiedHidden : readBit copied hidden = readBit state hidden :=
    readBit_classicalRun_blockCopyCodes_of_outside
      (Or.inl hhiddenTarget) state
  have hcopiedMessageZero :
      readBit copied (request + i) = readBit state (request + i) :=
    readBit_classicalRun_blockCopyCodes_of_outside
      (Or.inl (by omega)) state
  have hcopiedMessageOne :
      readBit copied (request + P.k + i) = readBit state (request + P.k + i) :=
    readBit_classicalRun_blockCopyCodes_of_outside
      (Or.inl (by omega)) state
  have hselectedZeroHidden :
      readBit selectedZero hidden = readBit copied hidden :=
    readBit_classicalRun_b2ControlledBlockCodes_of_outside
      (Or.inl hhiddenTarget) copied
  have hselectedZeroMessageOne :
      readBit selectedZero (request + P.k + i) =
        readBit copied (request + P.k + i) :=
    readBit_classicalRun_b2ControlledBlockCodes_of_outside
      (Or.inl (by omega)) copied
  rw [b2SelectMessageCodes, classicalRun_append, classicalRun_append]
  change readBit (classicalRun
    (b2ControlledBlockCodes hidden (request + P.k) target P.k) selectedZero)
      (target + i) = _
  rw [hselectedOneTarget, hselectedZeroTarget, hcopyTargetBit,
    hselectedZeroHidden, hcopiedHidden, hselectedZeroMessageOne,
    hcopiedMessageOne, hcopiedMessageZero, hzero i i.2]
  change _ = bif readBit state hidden then _ else _
  cases readBit state hidden <;> simp <;> rfl

private theorem readBit_classicalRun_b2SelectMessageCodes_of_outside
    (P : PKEParams) (securityParameter width wire : ℕ)
    (hwire : wire < b2ServiceEncoderBase P securityParameter ∨
      b2ServiceEncoderBase P securityParameter + P.k ≤ wire)
    (state : Fin width → Bool) :
    readBit (classicalRun (b2SelectMessageCodes P securityParameter) state) wire =
      readBit state wire := by
  rw [b2SelectMessageCodes, classicalRun_append, classicalRun_append]
  rw [readBit_classicalRun_b2ControlledBlockCodes_of_outside hwire]
  rw [readBit_classicalRun_b2ControlledBlockCodes_of_outside hwire]
  rw [readBit_classicalRun_blockCopyCodes_of_outside hwire]

private def b2ShiftCodes (base : ℕ) (codes : List GateCode) : List GateCode :=
  codes.map (GateCode.shift base)

private theorem classicalRun_b2ShiftCodes {smallWidth width base : ℕ}
    {codes : List GateCode} (hfit : base + smallWidth ≤ width)
    (hcodes : IsClassical smallWidth codes) (state : Fin width → Bool) :
    classicalRun (b2ShiftCodes base codes) state =
      glue (blockEmb base hfit)
        (classicalRun codes (state ∘ blockEmb base hfit)) state := by
  have hshift : IsClassical width (b2ShiftCodes base codes) := by
    intro gate hgate
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hgate
    exact ⟨(hcodes source hsource).1, (hcodes source hsource).2.shift hfit⟩
  have hket :
      ket (classicalRun (b2ShiftCodes base codes) state) =
        ket (glue (blockEmb base hfit)
          (classicalRun codes (state ∘ blockEmb base hfit)) state) := by
    rw [← Circuit.eval_ofCodes_ket hshift]
    rw [b2ShiftCodes, Circuit.ofCodes_map_shift hfit
      (fun gate hgate => (hcodes gate hgate).2)]
    conv_lhs =>
      rw [show ket state = embedState (blockEmb base hfit) state
          (ket (state ∘ blockEmb base hfit)) by
        rw [embedState_ket, glue_comp_of_agreeOff (AgreeOff.refl _ _)]]
    rw [Circuit.eval_mapWires_embedState, Circuit.eval_ofCodes_ket hcodes, embedState_ket]
  by_contra hne
  have hentry := congrArg (fun psi => psi.ofLp (classicalRun
    (b2ShiftCodes base codes) state)) hket
  simp only [ket_apply, ite_eq_right hne] at hentry
  exact one_ne_zero hentry

private theorem readBit_classicalRun_b2ShiftCodes {smallWidth width base : ℕ}
    {codes : List GateCode} (hfit : base + smallWidth ≤ width)
    (hcodes : IsClassical smallWidth codes) (state : Fin width → Bool)
    (i : Fin smallWidth) :
    readBit (classicalRun (b2ShiftCodes base codes) state) (base + i) =
      readBit (classicalRun codes (state ∘ blockEmb base hfit)) i := by
  rw [classicalRun_b2ShiftCodes hfit hcodes]
  rw [readBit_of_lt _ (by omega)]
  rw [readBit_fin]
  have hindex : (⟨base + i, by omega⟩ : Fin width) = blockEmb base hfit i :=
    Fin.ext (by simp only [blockEmb_apply_val]; omega)
  rw [hindex, glue_apply_emb]

private theorem readBit_classicalRun_b2ShiftCodes_of_lt {smallWidth width base wire : ℕ}
    {codes : List GateCode} (hfit : base + smallWidth ≤ width)
    (hcodes : IsClassical smallWidth codes) (hwire : wire < base)
    (state : Fin width → Bool) :
    readBit (classicalRun (b2ShiftCodes base codes) state) wire = readBit state wire := by
  rw [classicalRun_b2ShiftCodes hfit hcodes]
  by_cases hw : wire < width
  · rw [readBit_of_lt _ hw, readBit_of_lt _ hw, glue_blockEmb_apply]
    simp only [dite_eq_right_iff]
    omega
  · rw [readBit_of_le _ (not_lt.mp hw), readBit_of_le _ (not_lt.mp hw)]

private def b2PrepareCodes (P : PKEParams) (securityParameter : ℕ) : List GateCode :=
  let inputWidth := b2ServiceInputWidth P securityParameter
  let savedInput := b2ServiceSavedInputBase P securityParameter
  blockCopyCodes 0 savedInput inputWidth ++
    blockCopyCodes savedInput 0 (b2ServiceCiphertextWidth P) ++
    blockCopyCodes
      (savedInput + b2HeaderWidth securityParameter + 2 * P.n)
      0 (b2ServiceCiphertextWidth P)

private theorem readBit_classicalRun_b2PrepareCodes_of_middle
    (P : PKEParams) (securityParameter width : ℕ)
    (input : List Bool) (hinput : input.length ≤ width)
    {wire : ℕ} (hlower : b2ServiceCiphertextWidth P ≤ wire)
    (hupper : wire < b2ServiceSavedInputBase P securityParameter) :
    readBit (classicalRun (b2PrepareCodes P securityParameter)
      (inputState width input)) wire = input.getD wire false := by
  rw [b2PrepareCodes, classicalRun_append, classicalRun_append]
  rw [readBit_classicalRun_blockCopyCodes_of_outside
    (source := b2ServiceSavedInputBase P securityParameter +
      b2HeaderWidth securityParameter + 2 * P.n)
    (target := 0) (count := b2ServiceCiphertextWidth P) (Or.inr (by omega))]
  rw [readBit_classicalRun_blockCopyCodes_of_outside
    (source := b2ServiceSavedInputBase P securityParameter)
    (target := 0) (count := b2ServiceCiphertextWidth P) (Or.inr (by omega))]
  rw [readBit_classicalRun_blockCopyCodes_of_outside
    (source := 0) (target := b2ServiceSavedInputBase P securityParameter)
    (count := b2ServiceInputWidth P securityParameter) (Or.inl hupper)]
  exact readBit_inputState hinput wire

private theorem readBit_classicalRun_b2PrepareCodes
    (P : PKEParams) (securityParameter width : ℕ)
    (hwidth : b2ServiceEncoderBase P securityParameter ≤ width)
    (input : List Bool)
    (hinput : input.length = b2ServiceSavedInputBase P securityParameter)
    (i : Fin (b2ServiceCiphertextWidth P)) :
    readBit (classicalRun (b2PrepareCodes P securityParameter)
        (inputState width input)) i =
      input.getD (b2HeaderWidth securityParameter + 2 * P.n + i) false := by
  let inputWidth := b2ServiceInputWidth P securityParameter
  let savedInput := b2ServiceSavedInputBase P securityParameter
  let ciphertextWidth := b2ServiceCiphertextWidth P
  let initial := inputState width input
  let saved := classicalRun (blockCopyCodes 0 savedInput inputWidth) initial
  let cleared := classicalRun (blockCopyCodes savedInput 0 ciphertextWidth) saved
  have hinputWidth : savedInput + inputWidth ≤ width := by
    dsimp only [inputWidth, savedInput]
    exact hwidth
  have hciphertextInput : ciphertextWidth ≤ inputWidth := by
    dsimp only [ciphertextWidth, inputWidth]
    unfold b2ServiceCiphertextWidth b2ServiceInputWidth b2HeaderWidth b2SampleWidth
    omega
  have hciphertextSaved : ciphertextWidth ≤ savedInput :=
    hciphertextInput.trans (by
      change b2ServiceInputWidth P securityParameter ≤
        b2ServiceSavedInputBase P securityParameter
      unfold b2ServiceSavedInputBase
      omega)
  have hinitialFits : input.length ≤ width := by
    rw [hinput]
    exact (show b2ServiceSavedInputBase P securityParameter ≤
      b2ServiceEncoderBase P securityParameter by
        unfold b2ServiceEncoderBase
        omega).trans hwidth
  have hsavedBit (j : ℕ) (hj : j < inputWidth) :
      readBit saved (savedInput + j) = readBit initial j := by
    rw [readBit_classicalRun_blockCopyCodes (source := 0) (target := savedInput)
      (count := inputWidth) (Or.inl (by
        dsimp only [inputWidth, savedInput]
        unfold b2ServiceSavedInputBase
        omega))
      (by simpa only [Nat.zero_add] using
        Nat.le_trans (Nat.le_add_left inputWidth savedInput) hinputWidth)
      hinputWidth initial hj]
    rw [readBit_inputState_of_le (by rw [hinput]; omega), Bool.false_xor]
    simp only [Nat.zero_add]
  have hsavedPrefix (j : ℕ) (hj : j < ciphertextWidth) :
      readBit saved j = readBit initial j := by
    exact readBit_classicalRun_blockCopyCodes_of_outside
      (Or.inl (by omega)) initial
  have hclearedPrefix (j : ℕ) (hj : j < ciphertextWidth) :
      readBit cleared j = false := by
    have hclear := readBit_classicalRun_blockCopyCodes (source := savedInput) (target := 0)
      (count := ciphertextWidth) (Or.inr (by omega))
      (by omega) (by omega) saved hj
    rw [show readBit cleared j =
        (readBit saved j ^^ readBit saved (savedInput + j)) by
      simpa only [Nat.zero_add] using hclear,
      hsavedPrefix j hj, hsavedBit j (hj.trans_le hciphertextInput), Bool.xor_self]
  have hsource :
      b2HeaderWidth securityParameter + 2 * P.n + i < inputWidth := by
    dsimp only [inputWidth, ciphertextWidth] at i ⊢
    unfold b2ServiceInputWidth b2ServiceCiphertextWidth b2SampleWidth
    omega
  have hclearedSource :
      readBit cleared
          (savedInput + b2HeaderWidth securityParameter + 2 * P.n + i) =
        readBit saved
          (savedInput + b2HeaderWidth securityParameter + 2 * P.n + i) := by
    exact readBit_classicalRun_blockCopyCodes_of_outside
      (Or.inr (by omega)) saved
  have hsourceBlock :
      savedInput + b2HeaderWidth securityParameter + 2 * P.n + ciphertextWidth ≤ width := by
    calc
      savedInput + b2HeaderWidth securityParameter + 2 * P.n + ciphertextWidth =
          savedInput + inputWidth := by
        dsimp only [inputWidth, ciphertextWidth]
        unfold b2ServiceInputWidth b2ServiceCiphertextWidth b2SampleWidth
        omega
      _ ≤ width := hinputWidth
  have htargetBlock : ciphertextWidth ≤ width :=
    hciphertextSaved.trans
      ((Nat.le_add_right savedInput inputWidth).trans hinputWidth)
  have hfinal := readBit_classicalRun_blockCopyCodes
    (source := savedInput + b2HeaderWidth securityParameter + 2 * P.n)
    (target := 0) (count := ciphertextWidth) (Or.inr (by omega))
    hsourceBlock
    (by simpa only [Nat.zero_add] using htargetBlock)
    cleared i.2
  rw [b2PrepareCodes, classicalRun_append, classicalRun_append]
  rw [show readBit (classicalRun
      (blockCopyCodes
        (savedInput + b2HeaderWidth securityParameter + 2 * P.n)
        0 ciphertextWidth) cleared) i =
      (readBit cleared i ^^ readBit cleared
        (savedInput + b2HeaderWidth securityParameter + 2 * P.n + i)) by
      simpa only [Nat.zero_add] using hfinal,
    hclearedPrefix i i.2, hclearedSource,
    show savedInput + b2HeaderWidth securityParameter + 2 * P.n + i =
      savedInput + (b2HeaderWidth securityParameter + 2 * P.n + i) by omega,
    hsavedBit _ hsource,
    Bool.false_xor, readBit_inputState hinitialFits]

private theorem readBit_classicalRun_b2PrepareCodes_of_encoderBase_le
    (P : PKEParams) (securityParameter width : ℕ)
    (input : List Bool)
    (hinput : input.length = b2ServiceSavedInputBase P securityParameter)
    {wire : ℕ} (hwire : b2ServiceEncoderBase P securityParameter ≤ wire) :
    readBit (classicalRun (b2PrepareCodes P securityParameter)
      (inputState width input)) wire = false := by
  let inputWidth := b2ServiceInputWidth P securityParameter
  let savedInput := b2ServiceSavedInputBase P securityParameter
  let ciphertextWidth := b2ServiceCiphertextWidth P
  rw [b2PrepareCodes, classicalRun_append, classicalRun_append]
  rw [readBit_classicalRun_blockCopyCodes_of_outside (Or.inr (by
    have hbase : b2ServiceCiphertextWidth P ≤
        b2ServiceEncoderBase P securityParameter := by
      unfold b2ServiceCiphertextWidth b2ServiceEncoderBase b2ServiceSavedInputBase
        b2ServiceInputWidth b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
      omega
    omega))]
  rw [readBit_classicalRun_blockCopyCodes_of_outside (Or.inr (by
    have hbase : b2ServiceCiphertextWidth P ≤
        b2ServiceEncoderBase P securityParameter := by
      unfold b2ServiceCiphertextWidth b2ServiceEncoderBase b2ServiceSavedInputBase
        b2ServiceInputWidth b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
      omega
    omega))]
  rw [readBit_classicalRun_blockCopyCodes_of_outside (Or.inr (by
    unfold b2ServiceEncoderBase at hwire
    omega))]
  apply readBit_inputState_of_le
  rw [hinput]
  unfold b2ServiceEncoderBase at hwire
  omega

/-- Elementary classical program of the B2 service. Its explicit gate list is retained so the
controller compiler and concrete resource theorem charge the actual reduction program. -/
def b2ServiceCodes (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) : List GateCode :=
  let encoderBase := b2ServiceEncoderBase P securityParameter
  b2PrepareCodes P securityParameter ++
    b2SelectMessageCodes P securityParameter ++
    b2ShiftCodes encoderBase (samplerClassicalCodes P.k encoder.code) ++
    blockCopyCodes
      (b2ServiceEncoderOutputBase P securityParameter encoder)
      P.n P.codeLen

private theorem isClassical_b2ServiceCodes (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) :
    IsClassical (b2ServiceWidth P securityParameter encoder)
      (b2ServiceCodes P securityParameter encoder) := by
  let inputWidth := b2ServiceInputWidth P securityParameter
  let ciphertextWidth := b2ServiceCiphertextWidth P
  let savedInput := b2ServiceSavedInputBase P securityParameter
  let encoderBase := b2ServiceEncoderBase P securityParameter
  let encoderWidth := samplerWidth P.k encoder.code
  let width := b2ServiceWidth P securityParameter encoder
  have hsavedFit : savedInput + inputWidth ≤ width := by
    dsimp only [savedInput, inputWidth, width, encoderBase]
    unfold b2ServiceWidth b2ServiceEncoderBase
    omega
  have hencoderFit : encoderBase + encoderWidth ≤ width := by
    dsimp only [encoderBase, encoderWidth, width]
    unfold b2ServiceWidth
    omega
  have hciphertextInput : ciphertextWidth ≤ inputWidth := by
    dsimp only [ciphertextWidth, inputWidth]
    unfold b2ServiceCiphertextWidth b2ServiceInputWidth b2HeaderWidth b2SampleWidth
    omega
  have hinputSaved : inputWidth ≤ savedInput := by
    dsimp only [inputWidth, savedInput]
    unfold b2ServiceSavedInputBase
    omega
  have hciphertextSaved : ciphertextWidth ≤ savedInput :=
    hciphertextInput.trans hinputSaved
  have hinputFit : inputWidth ≤ width :=
    (Nat.le_add_left inputWidth savedInput).trans hsavedFit
  have hciphertextFit : ciphertextWidth ≤ width :=
    hciphertextInput.trans hinputFit
  have hencoderBaseFit : encoderBase ≤ width :=
    (Nat.le_add_right encoderBase encoderWidth).trans hencoderFit
  have hkEncoderWidth : P.k ≤ encoderWidth := by
    dsimp only [encoderWidth]
    unfold samplerWidth samplerOutputStart samplerZero
    omega
  have htargetFit : encoderBase + P.k ≤ width :=
    (Nat.add_le_add_left hkEncoderWidth encoderBase).trans hencoderFit
  have hrequestTarget : inputWidth + 2 * P.k + 1 ≤ encoderBase := by
    dsimp only [inputWidth, encoderBase]
    unfold b2ServiceEncoderBase b2ServiceSavedInputBase b2ServiceRequestWidth
    omega
  have hprepare : IsClassical width (b2PrepareCodes P securityParameter) := by
    rw [b2PrepareCodes, IsClassical.append, IsClassical.append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply isClassical_blockCopyCodes
      · left
        simpa only [Nat.zero_add] using hinputSaved
      · simpa only [Nat.zero_add] using hinputFit
      · exact hsavedFit
    · apply isClassical_blockCopyCodes
      · right
        simpa only [Nat.zero_add] using hciphertextSaved
      · exact (Nat.add_le_add_left hciphertextInput savedInput).trans hsavedFit
      · simpa only [Nat.zero_add] using hciphertextFit
    · apply isClassical_blockCopyCodes
      · right
        simp only [Nat.zero_add]
        unfold b2ServiceCiphertextWidth b2ServiceSavedInputBase
          b2ServiceInputWidth b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
        omega
      · calc
          savedInput + b2HeaderWidth securityParameter + 2 * P.n + ciphertextWidth =
              savedInput + inputWidth := by
            dsimp only [inputWidth, ciphertextWidth]
            unfold b2ServiceInputWidth b2ServiceCiphertextWidth b2SampleWidth
            omega
          _ ≤ width := hsavedFit
      · simpa only [Nat.zero_add] using hciphertextFit
  have hselect : IsClassical width (b2SelectMessageCodes P securityParameter) := by
    rw [b2SelectMessageCodes, IsClassical.append, IsClassical.append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply isClassical_blockCopyCodes
      · left
        change inputWidth + P.k ≤ encoderBase
        omega
      · change inputWidth + P.k ≤ width
        omega
      · exact htargetFit
    · apply isClassical_b2ControlledBlockCodes
      · intro offset hoffset
        change inputWidth + 2 * P.k ≠ encoderBase + offset
        omega
      · left
        change inputWidth + P.k ≤ encoderBase
        omega
      · intro offset hoffset
        change inputWidth + 2 * P.k ≠ inputWidth + offset
        omega
      · change inputWidth + 2 * P.k < width
        omega
      · change inputWidth + P.k ≤ width
        omega
      · exact htargetFit
    · apply isClassical_b2ControlledBlockCodes
      · intro offset hoffset
        change inputWidth + 2 * P.k ≠ encoderBase + offset
        omega
      · left
        change inputWidth + P.k + P.k ≤ encoderBase
        omega
      · intro offset hoffset
        change inputWidth + 2 * P.k ≠ inputWidth + P.k + offset
        omega
      · change inputWidth + 2 * P.k < width
        omega
      · change inputWidth + P.k + P.k ≤ width
        omega
      · exact htargetFit
  have hshift : IsClassical width
      (b2ShiftCodes encoderBase (samplerClassicalCodes P.k encoder.code)) := by
    intro gate hgate
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hgate
    have hsource' := isClassical_samplerClassicalCodes P.k encoder.code source hsource
    refine ⟨by simpa [GateCode.shift] using hsource'.1, ?_⟩
    exact hsource'.2.shift hencoderFit
  have houtput : IsClassical width
      (blockCopyCodes (b2ServiceEncoderOutputBase P securityParameter encoder)
        P.n P.codeLen) := by
    apply isClassical_blockCopyCodes
    · right
      unfold b2ServiceEncoderOutputBase b2ServiceEncoderBase b2ServiceSavedInputBase
        b2ServiceInputWidth b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
        samplerOutputStart samplerZero
      omega
    · dsimp only [width]
      unfold b2ServiceWidth b2ServiceEncoderOutputBase
      simp only [samplerWidth, Circuit.code, List.length_ofFn]
      omega
    · dsimp only [width, encoderBase]
      unfold b2ServiceWidth b2ServiceEncoderBase b2ServiceSavedInputBase
        b2ServiceInputWidth b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
      simp only [samplerWidth, samplerOutputStart, samplerZero, Circuit.code,
        List.length_ofFn]
      omega
  rw [b2ServiceCodes, IsClassical.append, IsClassical.append, IsClassical.append]
  exact ⟨⟨⟨hprepare, hselect⟩, hshift⟩, houtput⟩

private def b2ServiceInputWord (P : PKEParams) (securityParameter : ℕ)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P)) (hidden : Bool) : List Bool :=
  encPair encUnary encBits (securityParameter, sample.toWord) ++
    List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden]

private theorem length_b2ServiceInputWord (P : PKEParams) (securityParameter : ℕ)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P)) (hidden : Bool) :
    (b2ServiceInputWord P securityParameter sample messages hidden).length =
      b2ServiceSavedInputBase P securityParameter := by
  simp [b2ServiceInputWord, b2ServiceSavedInputBase, b2ServiceRequestWidth,
    b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth]
  omega

private theorem getD_truncatedSyndromeWord_firstValue {n codeLen : ℕ}
    (sample : TruncatedSyndromeSample n codeLen) (i : Fin n) :
    sample.toWord.getD (2 * n + i) false = sample.firstValue i := by
  rw [TruncatedSyndromeSample.toWord, List.ofFn_fin_append,
    List.ofFn_fin_append, List.ofFn_fin_append]
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  have hindex : 2 * n + i - n - n = i := by omega
  rw [hindex]
  exact (List.getD_eq_getElem (l := List.ofFn sample.firstValue)
    (d := false) (n := i) (by simp)).trans (by simp)

private theorem getD_truncatedSyndromeWord_secondValue {n codeLen : ℕ}
    (sample : TruncatedSyndromeSample n codeLen) (i : Fin codeLen) :
    sample.toWord.getD (3 * n + i) false = sample.secondValue i := by
  rw [TruncatedSyndromeSample.toWord, List.ofFn_fin_append,
    List.ofFn_fin_append, List.ofFn_fin_append]
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
  have hindex : 3 * n + i - n - n - n = i := by omega
  rw [hindex]
  exact (List.getD_eq_getElem (l := List.ofFn sample.secondValue)
    (d := false) (n := i) (by simp)).trans (by simp)

private theorem getD_b2ServiceInputWord_sample (P : PKEParams) (securityParameter : ℕ)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P)) (hidden : Bool)
    {j : ℕ} (hj : j < b2SampleWidth P) :
    (b2ServiceInputWord P securityParameter sample messages hidden).getD
        (b2HeaderWidth securityParameter + j) false = sample.toWord.getD j false := by
  unfold b2SampleWidth at hj
  rw [b2ServiceInputWord]
  rw [List.getD_append _ _ _ _ (by simp [b2HeaderWidth]; omega)]
  rw [List.getD_append _ _ _ _ (by simp [b2HeaderWidth]; omega)]
  rw [List.getD_append _ _ _ _ (by simp [b2HeaderWidth]; omega)]
  rw [encPair_apply, List.getD_append_right _ _ _ _ (by
    simp only [encUnary_apply, length_frame, List.length_replicate]
    unfold b2HeaderWidth
    omega)]
  simp only [encUnary_apply, length_frame, List.length_replicate, encBits_apply]
  congr 2
  unfold b2HeaderWidth
  omega

private theorem getD_b2ServiceInputWord_messageZero (P : PKEParams) (securityParameter : ℕ)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P)) (hidden : Bool) (i : Fin P.k) :
    (b2ServiceInputWord P securityParameter sample messages hidden).getD
        (b2ServiceInputWidth P securityParameter + i) false = messages.msg₀ i := by
  rw [b2ServiceInputWord]
  rw [List.getD_append _ _ _ _ (by simp [b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth]; omega)]
  rw [List.getD_append _ _ _ _ (by simp [b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth]; omega)]
  rw [List.getD_append_right _ _ _ _ (by
    simp [b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth])]
  have hindex : b2ServiceInputWidth P securityParameter + i -
      (encPair encUnary encBits (securityParameter, sample.toWord)).length = i := by
    simp [b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth]
  rw [hindex]
  exact (List.getD_eq_getElem (l := List.ofFn messages.msg₀)
    (d := false) (n := i) (by simp)).trans (by simp)

private theorem getD_b2ServiceInputWord_messageOne (P : PKEParams) (securityParameter : ℕ)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P)) (hidden : Bool) (i : Fin P.k) :
    (b2ServiceInputWord P securityParameter sample messages hidden).getD
        (b2ServiceInputWidth P securityParameter + P.k + i) false = messages.msg₁ i := by
  rw [b2ServiceInputWord]
  rw [List.getD_append _ _ _ _ (by simp [b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth]; omega)]
  rw [List.getD_append_right _ _ _ _ (by
    simp [b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth]
    omega)]
  have hindex : b2ServiceInputWidth P securityParameter + P.k + i -
      ((encPair encUnary encBits (securityParameter, sample.toWord)).length + P.k) = i := by
    simp [b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth]
  rw [show (encPair encUnary encBits (securityParameter, sample.toWord) ++
    List.ofFn messages.msg₀).length =
      (encPair encUnary encBits (securityParameter, sample.toWord)).length + P.k by
        simp
        omega]
  rw [hindex]
  exact (List.getD_eq_getElem (l := List.ofFn messages.msg₁)
    (d := false) (n := i) (by simp)).trans (by simp)

private theorem getD_b2ServiceInputWord_hidden (P : PKEParams) (securityParameter : ℕ)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P)) (hidden : Bool) :
    (b2ServiceInputWord P securityParameter sample messages hidden).getD
        (b2ServiceInputWidth P securityParameter + 2 * P.k) false = hidden := by
  rw [b2ServiceInputWord, List.getD_append_right]
  · have hindex : b2ServiceInputWidth P securityParameter + 2 * P.k -
        ((encPair encUnary encBits (securityParameter, sample.toWord) ++
          List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁).length) = 0 := by
      simp [b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth]
      omega
    rw [hindex]
    rfl
  · simp [b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth]
    omega

/-- Interpret the service's output prefix as the two components of an HQC ciphertext. -/
@[expose] def b2ServiceReadout (P : PKEParams) {width : ℕ}
    (state : Fin width → Bool) : PKECiphertext P :=
  ⟨fun i => readBit state i, fun i => readBit state (P.n + i)⟩

/-- Query-free reversible description of the service in the HQC 3-DQCSD reduction. The logical
quantum input is the two-message request followed by the hidden bit. The output prefix is the
complete `(u, v)` ciphertext. -/
def b2ServiceDescription (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) :
    OracleCircuitDescription :=
  { width := b2ServiceWidth P securityParameter encoder
    queryWidth := 0
    responseWidth := 0
    quantumInputWidth := b2ServiceRequestWidth P + 1
    outputWidth := b2ServiceCiphertextWidth P
    instructions :=
      (b2ServiceCodes P securityParameter encoder).map fun code => .gate (false, code) }

/-- The service consumes exactly the two `P.k`-bit messages followed by the hidden bit. -/
@[simp] theorem b2ServiceDescription_quantumInputWidth (P : PKEParams)
    (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) :
    (b2ServiceDescription P securityParameter encoder).quantumInputWidth = 2 * P.k + 1 := by
  simp [b2ServiceDescription, b2ServiceRequestWidth]

/-- The service emits exactly the first and second HQC ciphertext components. -/
@[simp] theorem b2ServiceDescription_outputWidth (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) :
    (b2ServiceDescription P securityParameter encoder).outputWidth = P.n + P.codeLen := by
  simp [b2ServiceDescription, b2ServiceCiphertextWidth]

/-- The retained B2 service is structurally valid on the complete three-block truncated-syndrome
sample. Its logical quantum input is exactly the two-message request and hidden bit. -/
theorem wellFormed_b2ServiceDescription (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) :
    (b2ServiceDescription P securityParameter encoder).WellFormed
      ⟨securityParameter, 3 * P.n + P.codeLen⟩ := by
  have hcodes := isClassical_b2ServiceCodes P securityParameter encoder
  constructor
  · change b2ServiceInputWidth P securityParameter + b2ServiceRequestWidth P + 1 ≤
      b2ServiceWidth P securityParameter encoder
    unfold b2ServiceWidth b2ServiceEncoderBase b2ServiceSavedInputBase
    omega
  · simp [b2ServiceDescription]
  · change b2ServiceCiphertextWidth P ≤ b2ServiceWidth P securityParameter encoder
    unfold b2ServiceWidth b2ServiceEncoderBase b2ServiceSavedInputBase
      b2ServiceInputWidth b2ServiceCiphertextWidth b2HeaderWidth b2SampleWidth
      b2ServiceRequestWidth
    omega
  · intro instruction hinstruction
    simp only [b2ServiceDescription, List.mem_map] at hinstruction
    obtain ⟨code, hcode, rfl⟩ := hinstruction
    change code.WellFormed (b2ServiceWidth P securityParameter encoder)
    exact (hcodes code hcode).2

/-- Exact elementary-gate count of the service. In particular, the cost includes the complete
reversible encoder program rather than charging only its input/output dimensions. -/
@[simp] theorem length_b2ServiceCodes (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) :
    (b2ServiceCodes P securityParameter encoder).length =
      (2 * securityParameter + 1 + (3 * P.n + P.codeLen)) +
        2 * (P.n + P.codeLen) + 3 * P.k +
        (samplerClassicalCodes P.k encoder.code).length + P.codeLen := by
  simp only [b2ServiceCodes, b2PrepareCodes, b2SelectMessageCodes, b2ShiftCodes,
    List.length_append, List.length_map, length_blockCopyCodes]
  simp [b2ControlledBlockCodes, b2ServiceInputWidth, b2HeaderWidth, b2SampleWidth,
    b2ServiceCiphertextWidth]
  omega

/-- The actual service program makes no oracle calls. -/
@[simp] theorem queryCount_b2ServiceDescription (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) :
    (b2ServiceDescription P securityParameter encoder).instructions.queryCount = 0 := by
  simp [b2ServiceDescription, OracleCircuit.queryCount, OracleGateCode.isQuery]

/-- Retained native compiler for the complete B2 service description at fixed scheme parameters
and a fixed installed encoder circuit. The fixed gate list is part of the compiler's static
description; every security-dependent copy, selector, shift and description field is emitted by
the retained machine. This is a concrete component certificate, not the still-open compiler for
an asymptotic parameter-dependent NIST encoder family. -/
@[expose] def b2ServiceCompiler (P : PKEParams)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen) :
    NativeCompiler
      (fun input : OracleInputSize =>
        b2ServiceDescription P input.securityParameter encoder)
      encOracleInputSize encOracleCircuitDescription := by
  let inputFields : NativeCompiler
      (fun input : OracleInputSize =>
        (input.securityParameter, input.classicalInputLength))
      encOracleInputSize (encPair encUnary encUnary) :=
    (identity encOracleInputSize).ofOutputEq fun input => by
      simp [encOracleInputSize_apply, encOracleInputSizeFields]
  let security : NativeCompiler OracleInputSize.securityParameter
      encOracleInputSize encUnary :=
    (first encUnary encUnary).comp inputFields
  let zero := const encOracleInputSize encUnary 0
  let one := const encOracleInputSize encUnary 1
  let n := const encOracleInputSize encUnary P.n
  let twoN := const encOracleInputSize encUnary (2 * P.n)
  let k := const encOracleInputSize encUnary P.k
  let twoK := const encOracleInputSize encUnary (2 * P.k)
  let codeLen := const encOracleInputSize encUnary P.codeLen
  let sampleWidth := const encOracleInputSize encUnary (3 * P.n + P.codeLen)
  let requestWidth := const encOracleInputSize encUnary (2 * P.k)
  let ciphertextWidth := const encOracleInputSize encUnary (P.n + P.codeLen)
  let samplerStart := const encOracleInputSize encUnary
    (samplerOutputStart P.k encoder.code)
  let samplerRegisterWidth := const encOracleInputSize encUnary
    (samplerWidth P.k encoder.code)
  let twoSecurity : NativeCompiler (fun input : OracleInputSize =>
      2 * input.securityParameter) encOracleInputSize encUnary :=
    (unaryAdd.comp (security.pair security)).ofOutputEq fun _ => by
      simp only [two_mul]
  let headerWidth : NativeCompiler (fun input : OracleInputSize =>
      2 * input.securityParameter + 1) encOracleInputSize encUnary :=
    (unaryAdd.comp (twoSecurity.pair one)).ofOutputEq fun _ => by
      rfl
  let inputWidth : NativeCompiler (fun input : OracleInputSize =>
      2 * input.securityParameter + 1 + (3 * P.n + P.codeLen))
      encOracleInputSize encUnary :=
    (unaryAdd.comp (headerWidth.pair sampleWidth)).ofOutputEq fun _ => by
      rfl
  let requestAndHidden : NativeCompiler (fun _ : OracleInputSize =>
      2 * P.k + 1) encOracleInputSize encUnary :=
    (unaryAdd.comp (requestWidth.pair one)).ofOutputEq fun _ => rfl
  let inputAndRequest : NativeCompiler (fun input : OracleInputSize =>
      (2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)) + 2 * P.k)
      encOracleInputSize encUnary :=
    (unaryAdd.comp (inputWidth.pair requestWidth)).ofOutputEq fun _ => rfl
  let savedInput : NativeCompiler (fun input : OracleInputSize =>
      (2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)) + 2 * P.k + 1)
      encOracleInputSize encUnary :=
    (unaryAdd.comp (inputAndRequest.pair one)).ofOutputEq fun _ => rfl
  let encoderBase : NativeCompiler (fun input : OracleInputSize =>
      ((2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)) + 2 * P.k + 1) +
        (2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)))
      encOracleInputSize encUnary :=
    (unaryAdd.comp (savedInput.pair inputWidth)).ofOutputEq fun _ => rfl
  let encoderOutputBase : NativeCompiler (fun input : OracleInputSize =>
      (((2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)) + 2 * P.k + 1) +
          (2 * input.securityParameter + 1 + (3 * P.n + P.codeLen))) +
        samplerOutputStart P.k encoder.code)
      encOracleInputSize encUnary :=
    (unaryAdd.comp (encoderBase.pair samplerStart)).ofOutputEq fun _ => rfl
  let width : NativeCompiler (fun input : OracleInputSize =>
      (((2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)) + 2 * P.k + 1) +
          (2 * input.securityParameter + 1 + (3 * P.n + P.codeLen))) +
        samplerWidth P.k encoder.code) encOracleInputSize encUnary :=
    (unaryAdd.comp (encoderBase.pair samplerRegisterWidth)).ofOutputEq fun _ => rfl
  let hidden : NativeCompiler (fun input : OracleInputSize =>
      (2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)) + 2 * P.k)
      encOracleInputSize encUnary :=
    (unaryAdd.comp (inputWidth.pair twoK)).ofOutputEq fun _ => rfl
  let messageOne : NativeCompiler (fun input : OracleInputSize =>
      (2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)) + P.k)
      encOracleInputSize encUnary :=
    (unaryAdd.comp (inputWidth.pair k)).ofOutputEq fun _ => rfl
  let savedHeader : NativeCompiler (fun input : OracleInputSize =>
      ((2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)) + 2 * P.k + 1) +
        (2 * input.securityParameter + 1)) encOracleInputSize encUnary :=
    (unaryAdd.comp (savedInput.pair headerWidth)).ofOutputEq fun _ => rfl
  let sampleValueBase : NativeCompiler (fun input : OracleInputSize =>
      (((2 * input.securityParameter + 1 + (3 * P.n + P.codeLen)) + 2 * P.k + 1) +
          (2 * input.securityParameter + 1)) + 2 * P.n)
      encOracleInputSize encUnary :=
    (unaryAdd.comp (savedHeader.pair twoN)).ofOutputEq fun _ => rfl
  let appendGateCodesCompiler {left right : OracleInputSize → List GateCode}
      (leftCompiler : NativeCompiler left encOracleInputSize (encList encGateCode))
      (rightCompiler : NativeCompiler right encOracleInputSize (encList encGateCode)) :
      NativeCompiler (fun input => left input ++ right input)
        encOracleInputSize (encList encGateCode) :=
    (listAppendCompiler encGateCode).comp (leftCompiler.pair rightCompiler)
  let gateCodeShiftCompiler : NativeCompiler
      (fun input : ℕ × GateCode => input.2.shift input.1)
      (encPair encUnary encGateCode) encGateCode := by
    let contextEncoding := encPair encUnary encGateCode
    let base := first encUnary encGateCode
    let code := second encUnary encGateCode
    let phase := (first encBool (encPair encUnary (encList encUnary))).comp code
    let targetAndControls :=
      (second encBool (encPair encUnary (encList encUnary))).comp code
    let target := (first encUnary (encList encUnary)).comp targetAndControls
    let controls := (second encUnary (encList encUnary)).comp targetAndControls
    let wireContext := encPair encUnary encUnary
    let wireBase := first encUnary encUnary
    let wire := second encUnary encUnary
    let shiftedWire := unaryAdd.comp (wire.pair wireBase)
    let shiftedTarget := shiftedWire.comp (base.pair target)
    let shiftedControls :=
      (listMapWithStateCompiler encUnary encUnary encUnary shiftedWire).comp
        (base.pair controls)
    exact (phase.pair (shiftedTarget.pair shiftedControls)).ofOutputEq fun input => by
      rcases input with ⟨base, phase, target, controls⟩
      rfl
  let ControlledInput := ℕ × (ℕ × (ℕ × ℕ))
  let encControlledInput : ControlledInput ↪ List Bool :=
    encPair encUnary (encPair encUnary (encPair encUnary encUnary))
  let controlledBlockCodesCompiler : NativeCompiler
      (fun input : ControlledInput =>
        (List.range input.2.2.2).map fun offset =>
          (false, input.2.2.1 + offset, [input.1, input.2.1 + offset]))
      encControlledInput (encList encGateCode) := by
    let encState := encPair encUnary (encPair encUnary encUnary)
    let control := first encUnary (encPair encUnary (encPair encUnary encUnary))
    let rest := second encUnary (encPair encUnary (encPair encUnary encUnary))
    let source := (first encUnary (encPair encUnary encUnary)).comp rest
    let targetAndCount := (second encUnary (encPair encUnary encUnary)).comp rest
    let target := (first encUnary encUnary).comp targetAndCount
    let count := (second encUnary encUnary).comp targetAndCount
    let state := control.pair (source.pair target)
    let marshal : NativeCompiler
        (fun input : ControlledInput =>
          ((input.1, (input.2.1, input.2.2.1)), List.range input.2.2.2))
        encControlledInput (encPair encState (encList encUnary)) :=
      state.pair (rangeUnaryCompiler.comp count)
    let callbackEncoding := encPair encState encUnary
    let callbackState := first encState encUnary
    let offset := second encState encUnary
    let callbackControl :=
      (first encUnary (encPair encUnary encUnary)).comp callbackState
    let callbackRest :=
      (second encUnary (encPair encUnary encUnary)).comp callbackState
    let callbackSource := (first encUnary encUnary).comp callbackRest
    let callbackTarget := (second encUnary encUnary).comp callbackRest
    let sourceWire := unaryAdd.comp (callbackSource.pair offset)
    let targetWire := unaryAdd.comp (callbackTarget.pair offset)
    let sourceControl : NativeCompiler
        (fun input : (ℕ × (ℕ × ℕ)) × ℕ =>
          [input.1.2.1 + input.2])
        callbackEncoding (encList encUnary) :=
      ((framedValue encUnary).comp sourceWire).ofOutputEq fun _ => by
        simp [encFramed_apply, encList_cons]
    let controls := (listConsCompiler encUnary).comp
      (callbackControl.pair sourceControl)
    let flag := const callbackEncoding encBool false
    let code : NativeCompiler
        (fun input : ((ℕ × (ℕ × ℕ)) × ℕ) =>
          (false, input.1.2.2 + input.2,
            [input.1.1, input.1.2.1 + input.2]))
        callbackEncoding encGateCode :=
      flag.pair (targetWire.pair controls)
    exact ((listMapWithStateCompiler encState encUnary encGateCode code).comp marshal).ofOutputEq
      fun _ => rfl
  let copiedInput := GateCode.blockCopyCodesCompiler.comp
    (zero.pair (savedInput.pair inputWidth))
  let clearedOutput := GateCode.blockCopyCodesCompiler.comp
    (savedInput.pair (zero.pair ciphertextWidth))
  let copiedSampleValue := GateCode.blockCopyCodesCompiler.comp
    (sampleValueBase.pair (zero.pair ciphertextWidth))
  let prepare := appendGateCodesCompiler
    (appendGateCodesCompiler copiedInput clearedOutput) copiedSampleValue
  let copiedMessageZero := GateCode.blockCopyCodesCompiler.comp
    (inputWidth.pair (encoderBase.pair k))
  let selectedMessageZero := controlledBlockCodesCompiler.comp
    (hidden.pair (inputWidth.pair (encoderBase.pair k)))
  let selectedMessageOne := controlledBlockCodesCompiler.comp
    (hidden.pair (messageOne.pair (encoderBase.pair k)))
  let select := appendGateCodesCompiler
    (appendGateCodesCompiler copiedMessageZero selectedMessageZero) selectedMessageOne
  let samplerCodes := const encOracleInputSize (encList encGateCode)
    (samplerClassicalCodes P.k encoder.code)
  let shiftedSampler :=
    (listMapWithStateCompiler encUnary encGateCode encGateCode gateCodeShiftCompiler).comp
      (encoderBase.pair samplerCodes)
  let copiedEncoderOutput := GateCode.blockCopyCodesCompiler.comp
    (encoderOutputBase.pair (n.pair codeLen))
  let codes : NativeCompiler
      (fun input : OracleInputSize =>
        b2ServiceCodes P input.securityParameter encoder)
      encOracleInputSize (encList encGateCode) := by
    exact (appendGateCodesCompiler
      (appendGateCodesCompiler (appendGateCodesCompiler prepare select) shiftedSampler)
      copiedEncoderOutput).ofOutputEq fun input => by
        simp [b2ServiceCodes, b2PrepareCodes, b2SelectMessageCodes,
          b2ControlledBlockCodes, b2ShiftCodes, b2ServiceEncoderOutputBase,
          b2ServiceEncoderBase, b2ServiceSavedInputBase, b2ServiceInputWidth,
          b2ServiceRequestWidth, b2ServiceCiphertextWidth, b2HeaderWidth, b2SampleWidth,
          encList_append, two_mul, Nat.add_assoc]
  let instructions := oracleGateCodeList.comp codes
  let fields := width.pair (zero.pair (zero.pair
    (requestAndHidden.pair (ciphertextWidth.pair instructions))))
  exact fields.ofOutputEq fun input => by
    simp [b2ServiceDescription, b2ServiceWidth, b2ServiceEncoderBase,
      b2ServiceSavedInputBase, b2ServiceInputWidth, b2ServiceRequestWidth,
      b2ServiceCiphertextWidth, b2HeaderWidth, b2SampleWidth,
      encOracleCircuitDescription_apply, encOracleCircuitDescriptionFields,
      two_mul, Nat.add_assoc]

/-- The complete reversible service leaves its hidden-bit input unchanged on every basis state.
This is the protected-bit half of the full service-reply record: the controller copies this bit
before the service and later pairs it with the service's ciphertext output. -/
theorem readBit_classicalRun_b2ServiceCodes_hidden (P : PKEParams)
    (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (state : Fin (b2ServiceDescription P securityParameter encoder).width → Bool) :
    readBit (classicalRun (b2ServiceCodes P securityParameter encoder) state)
        (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k) =
      readBit state (2 * securityParameter + 1 + (3 * P.n + P.codeLen) + 2 * P.k) := by
  let inputWidth := b2ServiceInputWidth P securityParameter
  let hidden := inputWidth + 2 * P.k
  let savedInput := b2ServiceSavedInputBase P securityParameter
  let encoderBase := b2ServiceEncoderBase P securityParameter
  let encoderWidth := samplerWidth P.k encoder.code
  let width := b2ServiceWidth P securityParameter encoder
  have hhiddenCiphertext : b2ServiceCiphertextWidth P ≤ hidden := by
    dsimp only [hidden, inputWidth]
    unfold b2ServiceCiphertextWidth b2ServiceInputWidth b2HeaderWidth b2SampleWidth
    omega
  have hhiddenSaved : hidden < savedInput := by
    dsimp only [hidden, inputWidth, savedInput]
    unfold b2ServiceSavedInputBase b2ServiceRequestWidth
    omega
  have hhiddenEncoder : hidden < encoderBase := by
    dsimp only [hidden, inputWidth, encoderBase]
    unfold b2ServiceEncoderBase b2ServiceSavedInputBase b2ServiceRequestWidth
    omega
  have hencoderFit : encoderBase + encoderWidth ≤ width := by
    dsimp only [encoderBase, encoderWidth, width]
    unfold b2ServiceWidth
    rfl
  change readBit (classicalRun (b2ServiceCodes P securityParameter encoder) state) hidden =
    readBit state hidden
  rw [b2ServiceCodes, classicalRun_append, classicalRun_append, classicalRun_append]
  rw [readBit_classicalRun_blockCopyCodes_of_outside (Or.inr (by
    dsimp only [hidden, inputWidth]
    unfold b2ServiceInputWidth b2HeaderWidth b2SampleWidth
    omega))]
  change readBit (classicalRun
      (b2ShiftCodes encoderBase (samplerClassicalCodes P.k encoder.code))
      (classicalRun (b2SelectMessageCodes P securityParameter)
        (classicalRun (b2PrepareCodes P securityParameter) state))) hidden =
    readBit state hidden
  calc
    _ = readBit (classicalRun (b2SelectMessageCodes P securityParameter)
          (classicalRun (b2PrepareCodes P securityParameter) state)) hidden :=
      readBit_classicalRun_b2ShiftCodes_of_lt
        (base := encoderBase) (width := width) hencoderFit
        (isClassical_samplerClassicalCodes P.k encoder.code) hhiddenEncoder _
    _ = readBit (classicalRun (b2PrepareCodes P securityParameter) state) hidden :=
      readBit_classicalRun_b2SelectMessageCodes_of_outside
        P securityParameter width hidden (Or.inl hhiddenEncoder) _
    _ = readBit state hidden := by
      rw [b2PrepareCodes, classicalRun_append, classicalRun_append]
      calc
        _ = readBit (classicalRun
              (blockCopyCodes savedInput 0 (b2ServiceCiphertextWidth P))
              (classicalRun (blockCopyCodes 0 savedInput inputWidth) state)) hidden :=
          readBit_classicalRun_blockCopyCodes_of_outside
            (source := savedInput + b2HeaderWidth securityParameter + 2 * P.n)
            (target := 0) (count := b2ServiceCiphertextWidth P)
            (width := width) (wire := hidden)
            (Or.inr (by simpa only [Nat.zero_add] using hhiddenCiphertext)) _
        _ = readBit (classicalRun (blockCopyCodes 0 savedInput inputWidth) state) hidden :=
          readBit_classicalRun_blockCopyCodes_of_outside
            (source := savedInput) (target := 0) (count := b2ServiceCiphertextWidth P)
            (width := width) (wire := hidden)
            (Or.inr (by simpa only [Nat.zero_add] using hhiddenCiphertext)) _
        _ = readBit state hidden :=
          readBit_classicalRun_blockCopyCodes_of_outside
            (source := 0) (target := savedInput) (count := inputWidth)
            (width := width) (wire := hidden) (Or.inl hhiddenSaved) _

/-- The actual service circuit emits the HQC ciphertext determined by the sample, selected
message and supplied Boolean encoder. This is a basis-state statement for the complete reversible
construction, not an assumption about the service built by the reduction. -/
theorem b2ServiceReadout_classicalRun (P : PKEParams) (securityParameter : ℕ)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (sample : TruncatedSyndromeSample P.n P.codeLen)
    (messages : MessagePair (PKEMessage P)) (hidden : Bool) :
    b2ServiceReadout P
        (classicalRun (b2ServiceCodes P securityParameter encoder)
          (inputState (b2ServiceDescription P securityParameter encoder).width
            (encPair encUnary encBits (securityParameter, sample.toWord) ++
              List.ofFn messages.msg₀ ++ List.ofFn messages.msg₁ ++ [hidden]))) =
      sample.toPKECiphertext P (encoder.eval interpretation) (messages.select hidden) := by
  change b2ServiceReadout P
    (classicalRun (b2ServiceCodes P securityParameter encoder)
      (inputState (b2ServiceWidth P securityParameter encoder)
        (b2ServiceInputWord P securityParameter sample messages hidden))) = _
  let input := b2ServiceInputWord P securityParameter sample messages hidden
  let width := b2ServiceWidth P securityParameter encoder
  let encoderBase := b2ServiceEncoderBase P securityParameter
  let prepared := classicalRun (b2PrepareCodes P securityParameter)
    (inputState width input)
  let selected := classicalRun (b2SelectMessageCodes P securityParameter) prepared
  let encoded := classicalRun
    (b2ShiftCodes encoderBase (samplerClassicalCodes P.k encoder.code)) selected
  have hinput : input.length = b2ServiceSavedInputBase P securityParameter :=
    length_b2ServiceInputWord P securityParameter sample messages hidden
  have hinputWidth : input.length ≤ width := by
    rw [hinput]
    dsimp only [width]
    unfold b2ServiceWidth b2ServiceEncoderBase
    omega
  have hencoderFit : encoderBase + samplerWidth P.k encoder.code ≤ width := by
    dsimp only [encoderBase, width]
    unfold b2ServiceWidth
    rfl
  have hpreparedU (i : Fin P.n) : readBit prepared i = sample.firstValue i := by
    have hrun := readBit_classicalRun_b2PrepareCodes P securityParameter width
      (by dsimp only [width]; unfold b2ServiceWidth b2ServiceEncoderBase; omega)
      input hinput ⟨i, by unfold b2ServiceCiphertextWidth; omega⟩
    change readBit prepared i = _
    rw [hrun]
    dsimp only [input]
    rw [show b2HeaderWidth securityParameter + 2 * P.n + i =
      b2HeaderWidth securityParameter + (2 * P.n + i) by omega]
    rw [getD_b2ServiceInputWord_sample P securityParameter sample messages hidden
      (j := 2 * P.n + i) (by unfold b2SampleWidth; omega)]
    exact getD_truncatedSyndromeWord_firstValue sample i
  have hpreparedV (i : Fin P.codeLen) :
      readBit prepared (P.n + i) = sample.secondValue i := by
    have hrun := readBit_classicalRun_b2PrepareCodes P securityParameter width
      (by dsimp only [width]; unfold b2ServiceWidth b2ServiceEncoderBase; omega)
      input hinput ⟨P.n + i, by unfold b2ServiceCiphertextWidth; omega⟩
    change readBit prepared (P.n + i) = _
    rw [hrun]
    dsimp only [input]
    rw [show b2HeaderWidth securityParameter + 2 * P.n + (P.n + i) =
      b2HeaderWidth securityParameter + (3 * P.n + i) by omega]
    rw [getD_b2ServiceInputWord_sample P securityParameter sample messages hidden
      (j := 3 * P.n + i) (by unfold b2SampleWidth; omega)]
    exact getD_truncatedSyndromeWord_secondValue sample i
  have hpreparedMessageZero (i : Fin P.k) :
      readBit prepared (b2ServiceInputWidth P securityParameter + i) = messages.msg₀ i := by
    rw [readBit_classicalRun_b2PrepareCodes_of_middle P securityParameter width input hinputWidth
      (by unfold b2ServiceCiphertextWidth b2ServiceInputWidth b2HeaderWidth b2SampleWidth; omega)
      (by unfold b2ServiceSavedInputBase b2ServiceRequestWidth; omega)]
    exact getD_b2ServiceInputWord_messageZero P securityParameter sample messages hidden i
  have hpreparedMessageOne (i : Fin P.k) :
      readBit prepared (b2ServiceInputWidth P securityParameter + P.k + i) = messages.msg₁ i := by
    rw [readBit_classicalRun_b2PrepareCodes_of_middle P securityParameter width input hinputWidth
      (by unfold b2ServiceCiphertextWidth b2ServiceInputWidth b2HeaderWidth b2SampleWidth; omega)
      (by unfold b2ServiceSavedInputBase b2ServiceRequestWidth; omega)]
    exact getD_b2ServiceInputWord_messageOne P securityParameter sample messages hidden i
  have hpreparedHidden :
      readBit prepared (b2ServiceInputWidth P securityParameter + 2 * P.k) = hidden := by
    rw [readBit_classicalRun_b2PrepareCodes_of_middle P securityParameter width input hinputWidth
      (by unfold b2ServiceCiphertextWidth b2ServiceInputWidth b2HeaderWidth b2SampleWidth; omega)
      (by unfold b2ServiceSavedInputBase b2ServiceRequestWidth; omega)]
    exact getD_b2ServiceInputWord_hidden P securityParameter sample messages hidden
  have hpreparedEncoder (j : ℕ) : readBit prepared (encoderBase + j) = false := by
    apply readBit_classicalRun_b2PrepareCodes_of_encoderBase_le
      P securityParameter width input hinput
    dsimp only [encoderBase]
    omega
  have hselectedBlock : selected ∘ blockEmb encoderBase hencoderFit =
      inputState (samplerWidth P.k encoder.code)
        (List.ofFn (messages.select hidden)) := by
    apply funext_readBit
    intro j
    by_cases hsmall : j < samplerWidth P.k encoder.code
    · rw [readBit_of_lt _ hsmall]
      change selected (blockEmb encoderBase hencoderFit ⟨j, hsmall⟩) = _
      rw [← readBit_of_lt selected (by omega)]
      rw [show ((blockEmb encoderBase hencoderFit ⟨j, hsmall⟩ : Fin width) : ℕ) =
        encoderBase + j by simp only [blockEmb_apply_val]; omega]
      by_cases hj : j < P.k
      · let i : Fin P.k := ⟨j, hj⟩
        rw [readBit_classicalRun_b2SelectMessageCodes P securityParameter width
          (by
            dsimp only [encoderBase, width]
            unfold b2ServiceWidth samplerWidth samplerOutputStart samplerZero
            omega)
          prepared (fun offset hoffset => hpreparedEncoder offset) i]
        rw [hpreparedHidden, hpreparedMessageZero i, hpreparedMessageOne i]
        rw [readBit_inputState
          (by
            simp only [List.length_ofFn]
            unfold samplerWidth samplerOutputStart samplerZero
            omega)]
        have hget := List.getD_eq_getElem
          (l := List.ofFn (messages.select hidden)) (d := false) (n := j)
          (by simpa only [List.length_ofFn] using hj)
        rw [hget, List.getElem_ofFn]
        cases hidden <;> rfl
      · rw [readBit_classicalRun_b2SelectMessageCodes_of_outside P securityParameter width
          (encoderBase + j) (Or.inr (by omega)) prepared, hpreparedEncoder]
        rw [readBit_inputState_of_le]
        simp only [List.length_ofFn]
        exact Nat.le_of_not_lt hj
    · rw [readBit_of_le _ (not_lt.mp hsmall),
        readBit_of_le _ (not_lt.mp hsmall)]
  have hencodedOutput (i : Fin P.codeLen) :
      readBit encoded (b2ServiceEncoderOutputBase P securityParameter encoder + i) =
        encoder.eval interpretation (messages.select hidden) i := by
    dsimp only [encoded, b2ServiceEncoderOutputBase]
    rw [Nat.add_assoc]
    rw [readBit_classicalRun_b2ShiftCodes hencoderFit
      (isClassical_samplerClassicalCodes P.k encoder.code) selected
      ⟨samplerOutputStart P.k encoder.code + i, by
        unfold samplerWidth
        simp [Circuit.code]⟩]
    change samplerReadout encoder
      (classicalRun (samplerClassicalCodes P.k encoder.code)
        (selected ∘ blockEmb encoderBase hencoderFit)) i = _
    rw [hselectedBlock, samplerReadout_classicalRun]
  have hencodedU (i : Fin P.n) : readBit encoded i = sample.firstValue i := by
    dsimp only [encoded]
    rw [readBit_classicalRun_b2ShiftCodes_of_lt hencoderFit
      (isClassical_samplerClassicalCodes P.k encoder.code)
      (by
        dsimp only [encoderBase]
        unfold b2ServiceEncoderBase b2ServiceSavedInputBase b2ServiceInputWidth
          b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
        omega) selected]
    rw [readBit_classicalRun_b2SelectMessageCodes_of_outside P securityParameter width i
      (Or.inl (by
        change i < encoderBase
        dsimp only [encoderBase]
        unfold b2ServiceEncoderBase b2ServiceSavedInputBase b2ServiceInputWidth
          b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
        omega)) prepared]
    exact hpreparedU i
  have hencodedV (i : Fin P.codeLen) :
      readBit encoded (P.n + i) = sample.secondValue i := by
    dsimp only [encoded]
    rw [readBit_classicalRun_b2ShiftCodes_of_lt hencoderFit
      (isClassical_samplerClassicalCodes P.k encoder.code)
      (by
        dsimp only [encoderBase]
        unfold b2ServiceEncoderBase b2ServiceSavedInputBase b2ServiceInputWidth
          b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
        omega) selected]
    rw [readBit_classicalRun_b2SelectMessageCodes_of_outside P securityParameter width (P.n + i)
      (Or.inl (by
        change P.n + i < encoderBase
        dsimp only [encoderBase]
        unfold b2ServiceEncoderBase b2ServiceSavedInputBase b2ServiceInputWidth
          b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
        omega)) prepared]
    exact hpreparedV i
  change b2ServiceReadout P
    (classicalRun (b2ServiceCodes P securityParameter encoder)
      (inputState width input)) = _
  rw [b2ServiceCodes, classicalRun_append, classicalRun_append, classicalRun_append]
  change b2ServiceReadout P (classicalRun
    (blockCopyCodes (b2ServiceEncoderOutputBase P securityParameter encoder)
      P.n P.codeLen) encoded) = _
  apply congrArg₂ fun (u : RingWord P) (v : Codeword P) => PKECiphertext.mk u v
  · funext i
    rw [readBit_classicalRun_blockCopyCodes_of_outside (Or.inl i.2), hencodedU]
  · funext i
    rw [readBit_classicalRun_blockCopyCodes
      (Or.inr (by
        unfold b2ServiceEncoderOutputBase
        unfold b2ServiceEncoderBase b2ServiceSavedInputBase b2ServiceInputWidth
          b2HeaderWidth b2SampleWidth b2ServiceRequestWidth samplerOutputStart samplerZero
        omega))
      (by
        dsimp only [width]
        unfold b2ServiceWidth b2ServiceEncoderOutputBase
        simp only [samplerWidth, Circuit.code, List.length_ofFn]
        omega)
      (by
        dsimp only [width]
        unfold b2ServiceWidth b2ServiceEncoderBase b2ServiceSavedInputBase
          b2ServiceInputWidth b2HeaderWidth b2SampleWidth b2ServiceRequestWidth
        simp only [samplerWidth, samplerOutputStart, samplerZero, Circuit.code,
          List.length_ofFn]
        omega)
      encoded i.2, hencodedV, hencodedOutput]
    rw [Pi.add_apply, Bool.add_eq_xor, Bool.xor_comm]

end Cslib.Crypto.HQC
