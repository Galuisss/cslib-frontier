/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Algorithms.Reachability.MinIsolation.Weights

/-! # Checked indexing of Hoza's base-six coefficients -/

set_option linter.privateModule false

namespace CslibFrontierTests.HozaWeights

open Cslib.Reachability.Hoza

-- On layer 4, the first of two bits has coefficient 6³ and the second 6².
private theorem valuation_four : padicValNat 2 4 = 2 := by
  change (Nat.maxPowDvdDiv 2 4).1 = 2
  rw [Nat.maxPowDvdDiv_of_pow_mul_eq (by decide) (show 2 ^ 2 * 1 = 4 by decide) (by decide)]

example : coefficient 4 (0 : Fin 2) = 216 := by
  rw [coefficient, valuation_four]
  decide

example : coefficient 4 (1 : Fin 2) = 36 := by
  rw [coefficient, valuation_four]
  decide

example : vertexWeight (ℓ := 2) (fun (_ : Unit) _ => true) (fun _ => true) 0 () = 0 := rfl

end CslibFrontierTests.HozaWeights
