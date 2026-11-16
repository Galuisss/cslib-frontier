/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.HadamardLayer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Range

/-!
# Retained native generation of Hadamard layers

The retained generator enumerates the unary offsets, adds the supplied block origin, and emits
the standard framed `GateCode` list. Its actual transition table and construction resource maps
remain available to clients that install the layer inside a larger generated circuit.

## Main definitions

* `Cslib.Quantum.GateCode.hadamardCodesCompiler`: retained generation of a contiguous Hadamard
  layer from unary origin and length.

## Main results

The returned `NativeCompiler` computes exactly `hadamardCodes origin count` while retaining its
construction resource maps.

## References

This retained compiler constructor is original formalization infrastructure.
-/

public section

namespace Cslib.Quantum.GateCode

open Turing.MultiTapeTM
open Turing.MultiTapeTM.Internal
open Turing.MultiTapeTM.Internal.NativeCompiler

/-- Generate `hadamardCodes origin count` with an actual retained machine. -/
@[expose] def hadamardCodesCompiler :
    NativeCompiler (fun input : ℕ × ℕ => hadamardCodes input.1 input.2)
      (encPair encUnary encUnary) (encList encGateCode) := by
  let contextEncoding := encPair encUnary encUnary
  let target := unaryAdd
  let kind := const contextEncoding encBool true
  let controls := const contextEncoding (encList encUnary) []
  let code : NativeCompiler
      (fun input : ℕ × ℕ => (true, input.1 + input.2, ([] : List ℕ)))
      contextEncoding encGateCode :=
    kind.pair (target.pair controls)
  let marshal : NativeCompiler (fun input : ℕ × ℕ => (input.1, List.range input.2))
      (encPair encUnary encUnary) (encPair encUnary (encList encUnary)) :=
    (first encUnary encUnary).pair (rangeUnaryCompiler.comp (second encUnary encUnary))
  exact ((listMapWithStateCompiler encUnary encUnary encGateCode code).comp marshal).ofOutputEq
    fun _ => rfl

end Cslib.Quantum.GateCode
