/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.ClassicalQuery

/-! A nondegenerate checked client of the retained classical-query controller. -/

set_option linter.privateModule false

public section

namespace CslibFrontierTests.QuantumClassicalQuery

open Cslib Cslib.Quantum
open Turing.MultiTapeTM
open Turing.MultiTapeTM.Internal
open Turing.MultiTapeTM.Internal.NativeCompiler

private def fixtureInput : OracleInputSize := ⟨2, 5⟩

private def fixtureFirst : OracleCircuitDescription where
  width := 10
  queryWidth := 1
  responseWidth := 1
  quantumInputWidth := 0
  outputWidth := 1
  instructions := [.query, .gate (false, false, 8, [])]

private def fixtureService : OracleCircuitDescription where
  width := 14
  queryWidth := 1
  responseWidth := 1
  quantumInputWidth := 2
  outputWidth := 2
  instructions := [.query, .gate (false, false, 12, [])]

private def fixtureSecond : OracleCircuitDescription where
  width := 19
  queryWidth := 1
  responseWidth := 1
  quantumInputWidth := 10
  outputWidth := 1
  instructions := [.query, .gate (false, false, 18, [])]

private def fixtureLayout : ClassicalQueryLayout :=
  ⟨fixtureInput, 3, fixtureFirst, fixtureService, fixtureSecond⟩

-- The structure migration preserves the former nested tuple words exactly.
example (layout : ClassicalQueryLayout) :
    encClassicalQueryLayout layout =
      (encPair encOracleInputSize
        (encPair encUnary
          (encPair encOracleCircuitDescription
            (encPair encOracleCircuitDescription encOracleCircuitDescription))))
        (layout.input,
          (layout.publicKeyWidth, (layout.first, (layout.service, layout.second)))) := by
  rw [encClassicalQueryLayout_apply]

private theorem wellFormed_fixtureDescription
    (securityParameter classicalInputLength width quantumInputWidth outputWidth target : ℕ)
    (hinput : 2 * securityParameter + 1 + classicalInputLength + quantumInputWidth ≤ width)
    (hquery : 2 ≤ width) (houtput : outputWidth ≤ width) (htarget : target < width) :
    ({ width := width
       queryWidth := 1
       responseWidth := 1
       quantumInputWidth := quantumInputWidth
       outputWidth := outputWidth
       instructions := [.query, .gate (false, false, target, [])] } :
      OracleCircuitDescription).WellFormed ⟨securityParameter, classicalInputLength⟩ := by
  refine ⟨hinput, hquery, houtput, ?_⟩
  intro instruction hinstruction
  change instruction ∈ [.query, .gate (false, false, target, [])] at hinstruction
  change OracleGateCode.WellFormed 1 1 width instruction
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hinstruction
  rcases hinstruction with rfl | rfl
  · exact hquery
  · simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed,
      GateCode.WellFormed, htarget]

private theorem fixtureFirst_wellFormed :
    fixtureFirst.WellFormed ⟨2, 3⟩ := by
  exact wellFormed_fixtureDescription 2 3 10 0 1 8
    (by omega) (by omega) (by omega) (by omega)

private theorem fixtureService_wellFormed :
    fixtureService.WellFormed fixtureInput := by
  exact wellFormed_fixtureDescription 2 5 14 2 2 12
    (by omega) (by omega) (by omega) (by omega)

private theorem fixtureSecond_wellFormed :
    fixtureSecond.WellFormed ⟨2, 2⟩ := by
  exact wellFormed_fixtureDescription 2 2 19 10 1 18
    (by omega) (by omega) (by omega) (by omega)

private theorem fixture_compatible : fixtureLayout.Compatible where
  publicKey_le := by decide
  first_wellFormed := fixtureFirst_wellFormed
  service_wellFormed := fixtureService_wellFormed
  second_wellFormed := fixtureSecond_wellFormed
  first_quantumInputWidth := rfl
  first_output_le := by decide
  service_quantumInputWidth := rfl
  service_outputWidth := rfl
  second_quantumInputWidth := rfl
  second_outputWidth := by decide

-- The fixture is intentionally nondegenerate: κ=2 differs from the three-bit public key,
-- the two-bit ciphertext suffix is nonempty, and each component contains a real query that the
-- controller erases. The first stage also has saved ancilla wires beyond its eight-bit input.
example : (compileClassicalQuery fixtureLayout).WellFormed fixtureInput ∧
    (compileClassicalQuery fixtureLayout).instructions.queryCount = 0 :=
  ⟨fixture_compatible.wellFormed_compileClassicalQuery,
    queryCount_compileClassicalQuery fixtureLayout⟩

-- The second stage's logical wire 15 is saved-F wire 8 (zero-based). It maps to physical wire 10,
-- after the hidden two-bit sample suffix, and cannot map to the protected hidden-bit record.
example : fixtureLayout.secondWire 15 = 10 ∧
    fixtureLayout.secondWire 15 ≠ fixtureLayout.replyBase := by
  constructor
  · decide
  · exact fixtureLayout.secondWire_ne_replyBase 15

private def fixtureCompiler : NativeCompiler
    (fun input : OracleInputSize =>
      compileClassicalQuery
        ⟨input, 3, fixtureFirst, fixtureService, fixtureSecond⟩)
    encOracleInputSize encOracleCircuitDescription :=
  compileClassicalQueryCompiler
    (const encOracleInputSize encUnary 3)
    (const encOracleInputSize encOracleCircuitDescription fixtureFirst)
    (const encOracleInputSize encOracleCircuitDescription fixtureService)
    (const encOracleInputSize encOracleCircuitDescription fixtureSecond)

-- The retained computation certificate emits that exact controller and therefore pays for its
-- complete encoded description in the construction-derived clock.
example : (encOracleCircuitDescription (compileClassicalQuery fixtureLayout)).length ≤
    fixtureCompiler.time fixtureInput := by
  exact (fixtureCompiler.computes fixtureInput).length_output_le

end CslibFrontierTests.QuantumClassicalQuery
