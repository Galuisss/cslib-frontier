/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Basic

/-!
# Output accumulation in the universal simulation

The simulated output is write-only: a prior output prefix changes neither the final configuration
nor the symbols subsequently emitted. This law is shared by windowed and streaming interpreters.

## Main results

* `Turing.MultiTapeTM.Universal.stepOut_iterate_append`: a prior output prefix is preserved.
-/

namespace Turing.MultiTapeTM.Universal

/-- A prior output prefix does not affect the simulated execution. -/
public theorem stepOut_iterate_append (d : Desc) (x : List ℕ) (n : ℕ)
    (c : SCfg) (output : List ℕ) :
    (stepOut d x)^[n] (c, output) =
      (((stepOut d x)^[n] (c, [])).1, output ++ ((stepOut d x)^[n] (c, [])).2) := by
  induction n generalizing c output with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepOut, stepOut]
      rw [ih _ (output ++ (step d x c).2.toList)]
      simp only [List.nil_append]
      rw [ih _ (step d x c).2.toList]
      simp only [List.append_assoc]

end Turing.MultiTapeTM.Universal
