/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Conditional

/-!
# Resource bounds for retained compiler combinators

The native composition and pairing constructors charge the encoded intermediate word. Their
component computation certificates imply that this word is no longer than the component clock,
which gives bounds stated only in terms of the retained component resources. These inequalities
are useful when a concrete compiler is assembled from independently certified generators.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.time_comp_le`: composition time after replacing the
  intermediate-output charge by the inner clock.
* `Turing.MultiTapeTM.Internal.NativeCompiler.workspace_comp_le`: the analogous workspace bound.
* `Turing.MultiTapeTM.Internal.NativeCompiler.time_pair_le`: standard-pair time after replacing
  the framed left-output charge by the left clock.
* `Turing.MultiTapeTM.Internal.NativeCompiler.workspace_pair_le`: the analogous workspace bound.
* `Turing.MultiTapeTM.Internal.NativeCompiler.time_ite_le`: conditional time bounded by all three
  component clocks and the Boolean framing constant.
* `Turing.MultiTapeTM.Internal.NativeCompiler.workspace_ite_le`: the analogous workspace bound,
  retaining the conditional's exact tape-count term.

## References

These construction-derived bounds are original.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- A composed retained compiler's intermediate-output charge is bounded by the inner clock. -/
theorem time_comp_le {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    (outer : NativeCompiler f encMid encOut) (inner : NativeCompiler g encIn encMid) (input : α) :
    (outer.comp inner).time input ≤
      5 * inner.time input + outer.time (g input) + 9 := by
  have hlength := (inner.computes input).length_output_le
  change inner.time input + outer.time (g input) + 4 * (encMid (g input)).length + 9 ≤ _
  omega

/-- A composed retained compiler's intermediate-output workspace charge is bounded by the inner
clock; the finite tape-count charge remains exact. -/
theorem workspace_comp_le {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    (outer : NativeCompiler f encMid encOut) (inner : NativeCompiler g encIn encMid) (input : α) :
    (outer.comp inner).workspace input ≤
      inner.workspace input + outer.workspace (g input) + 5 * inner.time input +
        (6 * max inner.tapeCount outer.tapeCount + 20) := by
  have hlength := (inner.computes input).length_output_le
  change inner.workspace input + outer.workspace (g input) +
      5 * (encMid (g input)).length +
        (6 * max inner.tapeCount outer.tapeCount + 20) ≤ _
  omega

/-- A retained standard pair charges at most nine left clocks, one right clock and the exact
seventeen-step framing constant. -/
theorem time_pair_le {α β γ : Type*} {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encLeft : β ↪ List Bool} {encRight : γ ↪ List Bool}
    (left : NativeCompiler f encIn encLeft) (right : NativeCompiler g encIn encRight) (input : α) :
    (left.pair right).time input ≤
      9 * left.time input + right.time input + 17 := by
  have hlength := (left.computes input).length_output_le
  change
    (left.time input + (4 * (encLeft (f input)).length + 8) +
      4 * (encLeft (f input)).length + 9) + right.time input ≤ _
  omega

/-- A retained standard pair's framed-left workspace charge is bounded by the left clock; both
component workspaces and the finite tape-count charge remain explicit. -/
theorem workspace_pair_le {α β γ : Type*} {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encLeft : β ↪ List Bool} {encRight : γ ↪ List Bool}
    (left : NativeCompiler f encIn encLeft) (right : NativeCompiler g encIn encRight) (input : α) :
    (left.pair right).workspace input ≤
      left.workspace input + right.workspace input + 5 * left.time input +
        6 * left.tapeCount + 20 + 2 * max (left.tapeCount + 2) right.tapeCount := by
  have hlength := (left.computes input).length_output_le
  change
    (left.workspace input + 0 + 5 * (encLeft (f input)).length +
        (6 * max left.tapeCount 0 + 20)) +
      right.workspace input + 2 * max (max left.tapeCount 0 + 2) right.tapeCount ≤ _
  simp only [Nat.max_eq_left (Nat.zero_le _)]
  omega

/-- A retained conditional runs its condition and one branch, so charging both branch clocks
gives a branch-independent upper bound with the exact worst-case Boolean framing constant. -/
theorem time_ite_le {α β : Type*} {condition : α → Bool} {ifTrue ifFalse : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (conditionCompiler : NativeCompiler condition encIn encTest)
    (trueCompiler : NativeCompiler ifTrue encIn encOut)
    (falseCompiler : NativeCompiler ifFalse encIn encOut) (input : α) :
    (ite conditionCompiler trueCompiler falseCompiler).time input ≤
      conditionCompiler.time input + trueCompiler.time input + falseCompiler.time input + 10 := by
  cases hcondition : condition input with
  | false =>
      simp [ite, hcondition, encTest_false]
      omega
  | true => simp [ite, hcondition, encTest_true]

/-- A retained conditional's workspace is bounded independently of the selected branch while its
finite tape-count charge remains exactly the constructor's maximum. -/
theorem workspace_ite_le {α β : Type*} {condition : α → Bool} {ifTrue ifFalse : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (conditionCompiler : NativeCompiler condition encIn encTest)
    (trueCompiler : NativeCompiler ifTrue encIn encOut)
    (falseCompiler : NativeCompiler ifFalse encIn encOut) (input : α) :
    (ite conditionCompiler trueCompiler falseCompiler).workspace input ≤
      conditionCompiler.workspace input + trueCompiler.workspace input +
        falseCompiler.workspace input +
        5 * max conditionCompiler.tapeCount
          (max trueCompiler.tapeCount falseCompiler.tapeCount) + 13 := by
  cases hcondition : condition input with
  | false =>
      simp [ite, hcondition, encTest_false]
      omega
  | true =>
      simp [ite, hcondition, encTest_true]
      omega

end Turing.MultiTapeTM.Internal.NativeCompiler
