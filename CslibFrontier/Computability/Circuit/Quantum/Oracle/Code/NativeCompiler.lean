/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List

/-!
# Retained native embedding of ordinary quantum gate codes

An actual retained list compiler embeds each ordinary `GateCode` as a non-phase oracle-circuit
instruction. It charges both the per-instruction option wrapper and the framed list traversal,
rather than treating the conversion as a free representation change.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.oracleGateCodeList`: compile a list of ordinary
  gate codes to its query-free oracle-circuit instruction list.

## Main results

The returned `NativeCompiler` certifies the exact mapped instruction list under the existing
gate-code and oracle-instruction encodings.

## References

This retained compiler constructor is original formalization infrastructure.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM
open Cslib.Quantum

/-- Retained compiler that embeds every ordinary gate code as a non-phase oracle instruction. -/
@[expose] def oracleGateCodeList : NativeCompiler
    (fun codes : List GateCode =>
      codes.map fun code => OracleGateCode.gate (false, code))
    (encList encGateCode) (encList encOracleGateCode) := by
  let phase : NativeCompiler (fun code : GateCode => (false, code))
      encGateCode encPhaseGateCode :=
    (const encGateCode encBool false).pair (identity encGateCode)
  let instruction : NativeCompiler
      (fun code : GateCode => OracleGateCode.gate (false, code))
      encGateCode encOracleGateCode :=
    ((optionSome encPhaseGateCode).comp phase).ofOutputEq fun _ => rfl
  exact (listMapCompiler encGateCode encOracleGateCode instruction).ofOutputEq fun _ => rfl

end Turing.MultiTapeTM.Internal.NativeCompiler
