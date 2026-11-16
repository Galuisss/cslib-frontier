/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.ZeroQuery
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode.NativeCompiler

/-!
# Retained native zero-oracle erasure and relabelling

An actual retained wire-map compiler lifts to one compiler that removes every coherent oracle
query, relabels every remaining phase-gate code, and rewraps it as an oracle-circuit
instruction. The construction admits arbitrary source oracle circuits: query erasure is justified
separately by the arbitrary-state semantics in
`CslibFrontier/Computability/Circuit/Quantum/Oracle/ZeroQuery.lean`.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.zeroOracleRelabel`: retained query erasure and
  phase-code relabelling over one encoded oracle-circuit instruction list.

## Main results

The returned `NativeCompiler` accepts every oracle-circuit instruction list, removes each query,
and computes the relabelled gate list with its construction resource maps retained.

## References

This retained compiler constructor is original formalization infrastructure.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM
open Cslib.Quantum

universe u

/-- Retain the elementary instructions of an arbitrary oracle circuit, relabel all of their wires,
and emit only query-free oracle instructions. The internal default phase code is evaluated only
on the discarded payload branch for a query instruction. -/
@[expose] def zeroOracleRelabel {State : Type u} {wireMap : State → ℕ → ℕ}
    (encState : State ↪ List Bool)
    (wireCompiler : NativeCompiler
      (fun input : State × ℕ => wireMap input.1 input.2)
      (encPair encState encUnary) encUnary) :
    NativeCompiler
      (fun input : State × OracleCircuit =>
        input.2.zeroOraclePhaseCodes.map fun code =>
          OracleGateCode.gate (code.relabel (wireMap input.1)))
      (encPair encState (encList encOracleGateCode)) (encList encOracleGateCode) := by
  let defaultCode : PhaseGateCode := (false, false, 0, [])
  let state := first encState encOracleGateCode
  let instruction := second encState encOracleGateCode
  let phaseOption : NativeCompiler
      (fun input : State × OracleGateCode => match input.2 with
        | .gate code => some code
        | .query => none)
      (encPair encState encOracleGateCode) (encOption encPhaseGateCode) :=
    ((identity encOracleGateCode).ofOutputEq
      (g := fun instruction => match instruction with
        | .gate code => some code
        | .query => none)
      fun instruction => by cases instruction <;> rfl).comp instruction
  let present := (optionIsSomeTest encPhaseGateCode).comp phaseOption
  let phase := (optionGetD defaultCode encPhaseGateCode).comp phaseOption
  let relabelled :=
    (phaseGateCodeRelabel encState wireCompiler).comp (state.pair phase)
  let gate : NativeCompiler
      (fun input : State × OracleGateCode => OracleGateCode.gate
        ((match input.2 with
          | .gate code => code
          | .query => defaultCode).relabel (wireMap input.1)))
      (encPair encState encOracleGateCode) encOracleGateCode :=
    ((optionSome encPhaseGateCode).comp relabelled).ofOutputEq fun input => by
      rcases input with ⟨state, instruction⟩
      cases instruction <;> rfl
  let someGate := (optionSome encOracleGateCode).comp gate
  let noGate := const (encPair encState encOracleGateCode) (encOption encOracleGateCode) none
  let callback : NativeCompiler
      (fun input : State × OracleGateCode => match input.2 with
        | .gate code => some (.gate (code.relabel (wireMap input.1)))
        | .query => none)
      (encPair encState encOracleGateCode) (encOption encOracleGateCode) :=
    (ite present someGate noGate).ofOutputEq fun input => by
      rcases input with ⟨state, instruction⟩
      cases instruction <;> rfl
  let compiler := listFilterMapWithStateCompiler (.query : OracleGateCode)
    encState encOracleGateCode encOracleGateCode callback
  refine compiler.ofOutputEq ?_
  intro input
  apply congrArg (encList encOracleGateCode)
  rw [OracleCircuit.zeroOraclePhaseCodes, List.map_filterMap]
  apply List.filterMap_congr
  intro instruction _
  cases instruction <;> rfl

end Turing.MultiTapeTM.Internal.NativeCompiler
