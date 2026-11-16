/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Replicate

/-!
# Retained native unary range generation

`rangeUnaryCompiler` converts a unary count to the standard framed encoding of
`[0, ..., count - 1]`. It first retains one framed token per unary input bit, then uses the
stateful list-fold compiler with the current unary index as fold state. The actual transition
tables and their construction resource maps remain available to callers.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.rangeUnaryCompiler`: retained unary-driven
  `List.range` generation.

## Main results

The returned `NativeCompiler` computes the standard framed unary encoding of `List.range` and
retains the transition table, time, workspace and output-length maps of that construction.

## References

This retained compiler constructor is original formalization infrastructure.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- Retained generation of `[0, ..., count - 1]` from a unary count. -/
@[expose] def rangeUnaryCompiler :
    NativeCompiler List.range encUnary (encList encUnary) := by
  let inputEncoding := encPair encUnary encBool
  let current := first encUnary encBool
  let one := const inputEncoding encUnary 1
  let next : NativeCompiler (fun input : ℕ × Bool => input.1 + 1) inputEncoding encUnary :=
    unaryAdd.comp (current.pair one)
  let emit : NativeCompiler (fun input : ℕ × Bool => frame (encUnary input.1))
      inputEncoding encBits :=
    ((framedValue encUnary).comp current).ofOutputEq fun _ => rfl
  let fold : NativeCompiler
      (fun input : ℕ × List Bool => List.range' input.1 input.2.length)
      (encPair encUnary (encList encBool)) (encList encUnary) := by
    apply listFoldEmitCompiler encUnary encBool (encList encUnary) next emit
    intro input
    rcases input with ⟨start, bits⟩
    induction bits generalizing start with
    | nil => rfl
    | cons bit bits ih =>
        simpa [List.range'_succ, streamEmit, encList_cons] using ih (start + 1)
  let marshal : NativeCompiler (fun count : ℕ => (0, List.replicate count true)) encUnary
      (encPair encUnary (encList encBool)) :=
    (const encUnary encUnary 0).pair unaryTrueListCompiler
  refine (fold.comp marshal).ofOutputEq ?_
  intro count
  apply congrArg (encList encUnary)
  simp only [List.length_replicate, List.range_eq_range']

end Turing.MultiTapeTM.Internal.NativeCompiler
