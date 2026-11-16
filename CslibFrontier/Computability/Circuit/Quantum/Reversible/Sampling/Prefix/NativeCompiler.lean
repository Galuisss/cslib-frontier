/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling.Prefix
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Range

/-!
# Retained native generation of prefix block swaps

The retained generator enumerates a unary block length and emits the three CNOT codes that swap
each source wire with the corresponding output-prefix wire. It retains the actual transition
table and all construction resource maps used by a larger circuit generator.

## Main definitions

* `Cslib.Quantum.GateCode.prefixSwapCodesCompiler`: retained generation of
  `prefixSwapCodes source count` from unary positions.

## Main results

The returned `NativeCompiler` computes exactly the three-CNOT swap sequence for every offset and
retains its construction resource maps.

## References

This retained compiler constructor is original formalization infrastructure.
-/

public section

namespace Cslib.Quantum.GateCode

open Turing.MultiTapeTM
open Turing.MultiTapeTM.Internal
open Turing.MultiTapeTM.Internal.NativeCompiler

/-- Generate `prefixSwapCodes source count` with an actual retained machine. -/
@[expose] def prefixSwapCodesCompiler :
    NativeCompiler (fun input : ℕ × ℕ => prefixSwapCodes input.1 input.2)
      (encPair encUnary encUnary) (encList encGateCode) := by
  let contextEncoding := encPair encUnary encUnary
  let source := first encUnary encUnary
  let offset := second encUnary encUnary
  let sourceWire := unaryAdd
  let flag := const contextEncoding encBool false
  let sourceControl : NativeCompiler (fun input : ℕ × ℕ => [input.1 + input.2])
      contextEncoding (encList encUnary) :=
    ((framedValue encUnary).comp sourceWire).ofOutputEq fun _ => by
      simp [encFramed_apply, encList_cons]
  let offsetControl : NativeCompiler (fun input : ℕ × ℕ => [input.2])
      contextEncoding (encList encUnary) :=
    ((framedValue encUnary).comp offset).ofOutputEq fun _ => by
      simp [encFramed_apply, encList_cons]
  let leftCode := flag.pair (offset.pair sourceControl)
  let rightCode := flag.pair (sourceWire.pair offsetControl)
  let emit : NativeCompiler
      (fun input : ℕ × ℕ => encList encGateCode
        (swapWireCodes input.2 (input.1 + input.2)))
      contextEncoding encBits :=
    (((encodeFrame encGateCode).comp leftCode).append
      (((encodeFrame encGateCode).comp rightCode).append
        ((encodeFrame encGateCode).comp leftCode))).ofOutputEq fun input => by
      simp [swapWireCodes, encList_cons, encBits_apply]
  let fold : NativeCompiler
      (fun input : ℕ × List ℕ =>
        input.2.flatMap fun offset => swapWireCodes offset (input.1 + offset))
      (encPair encUnary (encList encUnary)) (encList encGateCode) := by
    apply listFoldEmitCompiler encUnary encUnary (encList encGateCode)
      (first encUnary encUnary) emit
    intro input
    induction input.2 with
    | nil => rfl
    | cons offset offsets ih =>
        simpa [streamEmit, encList_append] using ih
  let marshal : NativeCompiler (fun input : ℕ × ℕ => (input.1, List.range input.2))
      (encPair encUnary encUnary) (encPair encUnary (encList encUnary)) :=
    source.pair (rangeUnaryCompiler.comp (second encUnary encUnary))
  exact (fold.comp marshal).ofOutputEq fun _ => rfl

end Cslib.Quantum.GateCode
