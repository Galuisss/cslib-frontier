/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.DensityMatrix.QuantumRaz

/-! The coordinate information bound for two correlated classical labels. -/

namespace CslibFrontierTests.QuantumRaz

open Cslib.Quantum Matrix
open Cslib.Probability.PMF (pi)

-- The input law can correlate the labels arbitrarily. The conditional block is a
-- rank-one qubit state chosen by the first label.
example (p : PMF (Fin 2 → Bool)) (q : Fin 2 → PMF Bool) :
    let ρ (z : Fin 2 → Bool) := pureState (ket (z 0))
    mutualInformation (classicalQuantumMarginal p ρ (fun z => z 0)) +
      mutualInformation (classicalQuantumMarginal p ρ (fun z => z 1)) ≤
      relativeEntropy (classicalQuantumState p ρ)
        (classicalQuantumState (pi q) (fun _ => pureState (ket false))) := by
  dsimp only
  simpa only [Fin.sum_univ_two] using
    sum_mutualInformation_classicalQuantumMarginal_le_relativeEntropy (fun _ : Fin 2 => Bool) p
      (fun z => isDensityMatrix_pureState (norm_ket (z 0))) q
      (isDensityMatrix_pureState (norm_ket false))

end CslibFrontierTests.QuantumRaz
