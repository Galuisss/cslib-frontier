/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Reversible.BlockCopy
public import CslibFrontier.Computability.Circuit.Quantum.Uniform
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Range

/-!
# Retained native generation of contiguous block copies

The retained generator enumerates a unary block length and emits the CNOT from each source wire
to its corresponding target wire. Its actual transition table and construction resource maps
remain available to the complete controller generator.

## Main definitions

* `Cslib.Quantum.GateCode.blockCopyCodesCompiler`: retained generation of a contiguous CNOT
  copy from unary source, target and length coordinates.

## Main results

The returned `NativeCompiler` computes exactly `blockCopyCodes source target count` for every
input and retains its time, workspace, static-description and output-length maps.

## References

This retained compiler constructor is original formalization infrastructure.
-/

public section

namespace Cslib.Quantum.GateCode

open Turing.MultiTapeTM
open Turing.MultiTapeTM.Internal
open Turing.MultiTapeTM.Internal.NativeCompiler

/-- Generate a contiguous CNOT block copy from unary source, target and length coordinates. -/
@[expose] def blockCopyCodesCompiler :
    NativeCompiler
      (fun input : ℕ × (ℕ × ℕ) => blockCopyCodes input.1 input.2.1 input.2.2)
      (encPair encUnary (encPair encUnary encUnary)) (encList encGateCode) := by
  let encInput := encPair encUnary (encPair encUnary encUnary)
  let encState := encPair encUnary encUnary
  let source := first encUnary (encPair encUnary encUnary)
  let rest := second encUnary (encPair encUnary encUnary)
  let target := (first encUnary encUnary).comp rest
  let count := (second encUnary encUnary).comp rest
  let marshal : NativeCompiler
      (fun input : ℕ × (ℕ × ℕ) => ((input.1, input.2.1), List.range input.2.2))
      encInput (encPair encState (encList encUnary)) :=
    (source.pair target).pair (rangeUnaryCompiler.comp count)
  let context := first encState encUnary
  let offset := second encState encUnary
  let sourceBase := (first encUnary encUnary).comp context
  let targetBase := (second encUnary encUnary).comp context
  let sourceWire := unaryAdd.comp (sourceBase.pair offset)
  let targetWire := unaryAdd.comp (targetBase.pair offset)
  let flag := const (encPair encState encUnary) encBool false
  let controls : NativeCompiler
      (fun input : (ℕ × ℕ) × ℕ => [input.1.1 + input.2])
      (encPair encState encUnary) (encList encUnary) :=
    ((framedValue encUnary).comp sourceWire).ofOutputEq fun _ => by
      simp [encFramed_apply, encList_cons]
  let code : NativeCompiler
      (fun input : (ℕ × ℕ) × ℕ =>
        (false, input.1.2 + input.2, [input.1.1 + input.2]))
      (encPair encState encUnary) encGateCode :=
    flag.pair (targetWire.pair controls)
  exact ((listMapWithStateCompiler encState encUnary encGateCode code).comp marshal).ofOutputEq
    fun _ => rfl

end Cslib.Quantum.GateCode
