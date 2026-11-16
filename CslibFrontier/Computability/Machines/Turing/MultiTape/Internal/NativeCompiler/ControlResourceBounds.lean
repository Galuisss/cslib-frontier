/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Universal

/-!
# Resource bounds for retained universal-control primitives

This module bounds the actual retained compiler for boundary-aware input-head movement. The
bounds cover every direction, boundary position and optional input symbol; installed program size
remains a separate static coordinate.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.moveInput_time_le`: a concrete linear time bound.
* `Turing.MultiTapeTM.Internal.NativeCompiler.moveInput_workspace_le`: an independent concrete
  linear workspace bound.
* `Turing.MultiTapeTM.Internal.NativeCompiler.moveInput_tapeCount_le`: a static tape-count bound.

The construction and bounds are original formalization infrastructure.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM.Universal

/-- The actual retained input-head movement compiler has linear time in its complete encoded
input. -/
theorem moveInput_time_le (input : ℕ × (Option ℕ × SignType)) :
    moveInput.time input ≤
      1000000 * ((encPair encNat (encPair eSym encSign) input).length + 1) := by
  obtain ⟨position, symbol, movement⟩ := input
  cases movement <;> cases position <;> cases symbol <;>
    simp [moveInput, first, second, wordEqTest, wordEqBool, natPred, natSucc,
      natIsZeroTest, natIsZeroBool, optionIsSomeTest, optionIsSomeBool, boolDecoder,
      boolToTest, ofTransducer, ofZipTransducer, pair, comp, ite, const, encodeFrame,
      ofInputEq, ofOutputEq, encSign, encTest_false, encTest_true] <;>
    omega

/-- The actual retained input-head movement compiler has linear workspace in its complete encoded
input, independently of its time coordinate. -/
theorem moveInput_workspace_le (input : ℕ × (Option ℕ × SignType)) :
    moveInput.workspace input ≤
      1000000 * ((encPair encNat (encPair eSym encSign) input).length + 1) := by
  obtain ⟨position, symbol, movement⟩ := input
  cases movement <;> cases position <;> cases symbol <;>
    simp [moveInput, first, second, wordEqTest, wordEqBool, natPred, natSucc,
      natIsZeroTest, natIsZeroBool, optionIsSomeTest, optionIsSomeBool, boolDecoder,
      boolToTest, ofTransducer, ofZipTransducer, pair, comp, ite, const, encodeFrame,
      ofInputEq, ofOutputEq, encSign, encTest_false, encTest_true] <;>
    omega

/-- A construction-derived static tape-count bound for retained input-head movement. -/
theorem moveInput_tapeCount_le : moveInput.tapeCount ≤ 1000 := by
  simp [moveInput, first, second, wordEqTest, wordEqBool, natPred, natSucc,
    natIsZeroTest, natIsZeroBool, optionIsSomeTest, optionIsSomeBool, boolDecoder,
    boolToTest, ofTransducer, ofZipTransducer, pair, comp, ite, const, encodeFrame,
    ofInputEq, ofOutputEq, encSign]

end Turing.MultiTapeTM.Internal.NativeCompiler
