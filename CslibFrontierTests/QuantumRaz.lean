/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumConditioning
import CslibFrontier.Foundations.Quantum.DensityMatrix.QuantumRaz

/-! The coordinate information bound for two correlated classical labels. -/

namespace CslibFrontierTests.QuantumRaz

open Cslib.Quantum Matrix
open scoped ComplexOrder
open Cslib.Probability.PMF (conditionalSnd pi)

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

-- Both the reference question law and the reference density can depend on the
-- transcript. The source may assign zero mass to either transcript.
example (p : PMF (Bool × (Fin 1 → Bool))) (q : PMF Bool) (r : Bool → Fin 1 → PMF Bool) :
    let ρ (z : Bool × (Fin 1 → Bool)) := pureState (ket (z.2 0))
    (∑ t, (((p.map Prod.fst) t).toReal : WithTop ℝ) *
      mutualInformation (classicalQuantumMarginal (conditionalSnd p t)
        (fun y => ρ (t, y)) (fun y => y 0))) ≤
      relativeEntropy (classicalQuantumState p ρ)
        (classicalQuantumState (q.bind fun t => (pi (r t)).map (t, ·))
          (fun (t, _) => pureState (ket t))) := by
  dsimp only
  simpa only [Fin.sum_univ_one, Function.comp_def] using
    sum_weighted_coordinate_mutualInformation_le_relativeEntropy (fun _ : Fin 1 => Bool) p
      (fun z => isDensityMatrix_pureState (norm_ket (z.2 0))) q r
      (fun t => isDensityMatrix_pureState (norm_ket t))

-- A pure classical label gives one supported block. The other block contributes
-- zero regardless of the fallback density.
example :
    ∃ ρ : Bool → Matrix Bool Bool ℂ, (∀ b, IsDensityMatrix (ρ b)) ∧
      classicalQuantumState (PMF.pure false) ρ =
        blockDiagonal (fun b => if b then 0 else pureState (ket false)) := by
  let A (b : Bool) := if b then 0 else pureState (ket false)
  have hρ := isDensityMatrix_pureState (norm_ket false)
  have hA (b : Bool) : (A b).PosSemidef := by
    cases b
    · exact hρ.posSemidef
    · exact PosSemidef.zero
  have ht (b : Bool) : (A b).trace.re = ((PMF.pure false) b).toReal := by
    cases b <;> simp [A, hρ.trace_eq_one, PMF.pure_apply]
  obtain ⟨ρ, hρ', _, he⟩ := exists_classicalQuantumState_eq_blockDiagonal
    (PMF.pure false) A hA ht (isDensityMatrix_pureState (norm_ket true))
  exact ⟨ρ, hρ', he⟩

end CslibFrontierTests.QuantumRaz
