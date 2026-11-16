/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Replicate

/-!
# Resource bounds for retained unary token generation

The clock and bounded interpreter both convert a unary count into a framed list of tokens.
These bounds apply to that retained constructor's actual time and workspace fields.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryTrueListCompiler_time_le`: a linear upper
  bound for the actual running time.
* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryTrueListCompiler_workspace_le`: a separate
  linear upper bound for the actual workspace.

## References

These construction-derived bounds are original.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- The retained unary-to-token conversion runs in linear time in the unary count. -/
theorem unaryTrueListCompiler_time_le (count : ℕ) :
    unaryTrueListCompiler.time count ≤ 100 * (count + 1) := by
  let seedCompiler : NativeCompiler unaryFrameSeed encUnary encBits :=
    ofTransducer unaryFrameSeedT unitStateEncoding fun count => by
      simpa only [encBits_apply] using unaryFrameSeedT_run count
  have hseed : (unaryFrameSeed count).length ≤ seedCompiler.time count := by
    simpa only [encBits_apply] using (seedCompiler.computes count).length_output_le
  simp only [unaryTrueListCompiler, ofOutputEq, comp, ofTransducer, encUnary_apply,
    List.length_replicate, encBits_apply]
  simp only [seedCompiler, ofTransducer, encUnary_apply, List.length_replicate] at hseed
  nlinarith

/-- The retained unary-to-token conversion uses linear workspace in the unary count. -/
theorem unaryTrueListCompiler_workspace_le (count : ℕ) :
    unaryTrueListCompiler.workspace count ≤ 100 * (count + 1) := by
  let seedCompiler : NativeCompiler unaryFrameSeed encUnary encBits :=
    ofTransducer unaryFrameSeedT unitStateEncoding fun count => by
      simpa only [encBits_apply] using unaryFrameSeedT_run count
  have hseed : (unaryFrameSeed count).length ≤ seedCompiler.time count := by
    simpa only [encBits_apply] using (seedCompiler.computes count).length_output_le
  simp only [unaryTrueListCompiler, ofOutputEq, comp, ofTransducer, encUnary_apply,
    List.length_replicate, encBits_apply]
  simp only [seedCompiler, ofTransducer, encUnary_apply, List.length_replicate] at hseed
  have hscaled := Nat.mul_le_mul_left 5 hseed
  omega

end Turing.MultiTapeTM.Internal.NativeCompiler
