/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode.Relabel
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List

/-!
# Retained native relabelling of phase-gate codes

An actual native compiler for a wire map lifts constructively to one phase-gate code. The same
encoded context is reused for the target and every control, and the returned compiler records the
assembled transition table and all of its resource coordinates. No existential computability
witness is selected.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.phaseGateCodeRelabel`: lift a retained wire-map
  compiler to `PhaseGateCode.relabel`.

## Main results

The returned `NativeCompiler` certifies the exact relabelled encoded phase-gate code; contextual
control-list traversal is charged by the retained stream machine.

## References

This retained compiler constructor is original formalization infrastructure.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM
open Cslib.Quantum

universe u

/-- Lift an actual retained compiler for `wireMap` to relabel one phase-gate code. -/
@[expose] def phaseGateCodeRelabel {State : Type u} {wireMap : State → ℕ → ℕ}
    (encState : State ↪ List Bool)
    (wireCompiler : NativeCompiler
      (fun input : State × ℕ => wireMap input.1 input.2)
      (encPair encState encUnary) encUnary) :
    NativeCompiler
      (fun input : State × PhaseGateCode => input.2.relabel (wireMap input.1))
      (encPair encState encPhaseGateCode) encPhaseGateCode := by
  let state := first encState encPhaseGateCode
  let code := second encState encPhaseGateCode
  let phase := (first encBool encGateCode).comp code
  let gate := (second encBool encGateCode).comp code
  let kind := (first encBool (encPair encUnary (encList encUnary))).comp gate
  let targetAndControls :=
    (second encBool (encPair encUnary (encList encUnary))).comp gate
  let target := (first encUnary (encList encUnary)).comp targetAndControls
  let controls := (second encUnary (encList encUnary)).comp targetAndControls
  let mappedTarget := wireCompiler.comp (state.pair target)
  let mappedControls :=
    (listMapWithStateCompiler encState encUnary encUnary wireCompiler).comp
      (state.pair controls)
  let mappedGate := kind.pair (mappedTarget.pair mappedControls)
  exact (phase.pair mappedGate).ofOutputEq fun input => by
    rcases input with ⟨state, phase, kind, target, controls⟩
    rfl

end Turing.MultiTapeTM.Internal.NativeCompiler
