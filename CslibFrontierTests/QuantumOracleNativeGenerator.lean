/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Generator.NativeCompiler
import CslibFrontier.Computability.Circuit.Quantum.Output
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec

/-! A retained generator for a nonempty query-free oracle-circuit description. -/

set_option linter.privateModule false

public section

namespace CslibFrontierTests.QuantumOracleNativeGenerator

open Cslib Cslib.Quantum Turing.MultiTapeTM
open Turing.MultiTapeTM.Internal

private def oneXInstructions : OracleCircuit :=
  (GateCode.flipCodes [0]).map fun g => OracleGateCode.gate (false, g)

private def oneXDescription (n ℓ : ℕ) : OracleCircuitDescription where
  width := 2 * n + 1 + ℓ
  queryWidth := 0
  responseWidth := 0
  quantumInputWidth := 0
  outputWidth := 1
  instructions := oneXInstructions

private def inputLengthCompiler : NativeCompiler
    (fun input : OracleInputSize => (encOracleInputSize input).length)
    encOracleInputSize encUnary :=
  NativeCompiler.unaryDecoder.ofInputEq (fun input => encOracleInputSize input) fun _ => by
    rfl

private def oneXCompiler : NativeCompiler
    (fun input : OracleInputSize =>
      oneXDescription input.securityParameter input.classicalInputLength)
    encOracleInputSize encOracleCircuitDescription := by
  let zero := NativeCompiler.const encOracleInputSize encUnary 0
  let one := NativeCompiler.const encOracleInputSize encUnary 1
  let instructions := NativeCompiler.const encOracleInputSize (encList encOracleGateCode)
    oneXInstructions
  let fields := inputLengthCompiler.pair
    (zero.pair (zero.pair (zero.pair (one.pair instructions))))
  refine fields.ofOutputEq ?_
  rintro ⟨n, ℓ⟩
  simp [oneXDescription, encOracleCircuitDescription_apply,
    encOracleCircuitDescriptionFields, encOracleInputSize_apply, encOracleInputSizeFields,
    oneXInstructions]

private def generatorTime (inputBits : ℕ) : ℕ :=
  12 * inputBits + (encList encOracleGateCode oneXInstructions).length + 107

private def generatorWorkspace (inputBits : ℕ) : ℕ :=
  5 * inputBits + 125

private theorem oneXCompiler_time (input : OracleInputSize) :
    oneXCompiler.time input = generatorTime (encOracleInputSize input).length := by
  simp [oneXCompiler, inputLengthCompiler, generatorTime, NativeCompiler.pair,
    NativeCompiler.comp, NativeCompiler.encodeFrame,
    NativeCompiler.unaryDecoder, NativeCompiler.ofTransducer, NativeCompiler.const,
    NativeCompiler.ofInputEq, NativeCompiler.ofOutputEq,
    encUnary_apply]
  omega

private theorem oneXCompiler_workspace (input : OracleInputSize) :
    oneXCompiler.workspace input = generatorWorkspace (encOracleInputSize input).length := by
  simp [oneXCompiler, inputLengthCompiler, generatorWorkspace, NativeCompiler.pair,
    NativeCompiler.comp, NativeCompiler.encodeFrame, NativeCompiler.unaryDecoder,
    NativeCompiler.ofTransducer, NativeCompiler.const, NativeCompiler.ofInputEq,
    NativeCompiler.ofOutputEq]

private theorem computableInPolyTime_oneXDescription :
    ComputableInPolyTime
      (fun input : OracleInputSize =>
        oneXDescription input.securityParameter input.classicalInputLength)
      encOracleInputSize encOracleCircuitDescription := by
  refine ⟨generatorTime, generatorWorkspace, by unfold generatorTime; fun_prop,
    by unfold generatorWorkspace; fun_prop, ?_⟩
  exact oneXCompiler.computableInTimeAndSpace.mono
    (fun input => (oneXCompiler_time input).le)
    (fun input => (oneXCompiler_workspace input).le)

private theorem wellFormed_oneXDescription (n ℓ : ℕ) :
    (oneXDescription n ℓ).WellFormed ⟨n, ℓ⟩ := by
  refine ⟨by simp [oneXDescription], by simp [oneXDescription], by simp [oneXDescription]; omega,
    ?_⟩
  intro instruction hinstruction
  change instruction ∈ oneXInstructions at hinstruction
  rw [show oneXInstructions = [OracleGateCode.gate (false, false, 0, [])] by rfl,
    List.mem_singleton] at hinstruction
  subst instruction
  change GateCode.WellFormed (2 * n + 1 + ℓ) (false, 0, [])
  refine ⟨by simp, by simp, ?_⟩
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  omega

private abbrev oneXFamily : UniformOracleCircuitFamily where
  description := oneXDescription
  computableInPolyTime_description := computableInPolyTime_oneXDescription
  wellFormed := wellFormed_oneXDescription

private abbrev oneXCertificate : oneXFamily.GeneratorCertificate :=
  .ofNativeCompiler oneXCompiler generatorTime generatorWorkspace
    (by unfold generatorTime; fun_prop) (by unfold generatorWorkspace; fun_prop)
    (fun input => (oneXCompiler_time input).le)
    (fun input => (oneXCompiler_workspace input).le)

-- The retained machine, its length schedules and both exact artifact sizes agree in one check.
example (input : OracleInputSize) :
    oneXCertificate.resources input =
      ⟨oneXCompiler.staticBits, generatorTime (encOracleInputSize input).length,
        generatorWorkspace (encOracleInputSize input).length,
        oneXCompiler.outputBits input⟩ := by
  simp [oneXCertificate, UniformOracleCircuitFamily.GeneratorCertificate.resources,
    UniformOracleCircuitFamily.GeneratorCertificate.ofNativeCompiler,
    NativeCompiler.staticBits, NativeCompiler.outputBits, Universal.descLen]

-- This is the first semantic property of the nonempty generated description: its lone query-free
-- gate really flips the first basis bit.
private theorem oneXCircuit_flips_first_basis_bit (n ℓ : ℕ)
    (x : Fin (2 * n + 1 + ℓ) → Bool) :
    ∃ y, Circuit.eval
        (OracleCircuit.toCircuit (oneXDescription n ℓ).width
          (fun (_ : Fin 0 → Bool) (_ : Fin 0) => false)
          (oneXDescription n ℓ).instructions)
        (ket x) = ket y ∧
          y ⟨0, by simp [oneXDescription]⟩ = !x ⟨0, by omega⟩ := by
  simp only [oneXDescription, oneXInstructions]
  let width := 2 * n + 1 + ℓ
  let y := GateCode.classicalRun (GateCode.flipCodes [0]) x
  refine ⟨y, ?_, ?_⟩
  · rw [OracleCircuit.toCircuit_map_gateCode]
    exact Circuit.eval_ofCodes_ket
      (GateCode.isClassical_flipCodes (by simp)) x
  · have h := GateCode.readBit_classicalRun_flipCodes (m := width)
      (S := [0]) (by simp) (by simp [width]) x 0
    simpa [y, width, readBit] using h

end CslibFrontierTests.QuantumOracleNativeGenerator
