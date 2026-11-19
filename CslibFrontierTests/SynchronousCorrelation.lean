/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.SynchronousCorrelation
import CslibFrontier.Foundations.Quantum.POVM.Mixture
import CslibFrontier.Probability.PMF.Uniform

/-! # Synchronous rounding for a rectangular strategy with a randomized measurement -/

set_option linter.privateModule false

open Cslib.PCP Cslib.Quantum
open Cslib.Probability.PMF (uniformOfFintype)

private noncomputable def rectangular : QuantumStrategy Bool Bool Bool Bool Bool Unit where
  state := EuclideanSpace.single (false, ()) 1
  norm_state := by simp
  alice _ := POVM.mixture (uniformOfFintype Bool) fun b => POVM.const b
  bob y := POVM.const y

/-- The POVM-level result gives a synchronous mixture on a joint law with off-diagonal questions. -/
example :
    let μ := uniformOfFintype (Bool × Bool)
    let δ := rectangular.synchronyDefect (μ.map Prod.fst)
    ∃ (p : PMF {s : Finset (Unit × Bool) // s.Nonempty})
        (T : (s : {s : Finset (Unit × Bool) // s.Nonempty}) →
          QuantumStrategy Bool Bool Bool Bool s.val s.val),
      (∀ s x a b, a ≠ b → (T s).prob x x a b = 0) ∧
      (∑ q, (μ q).toReal * ∑ a, ∑ b,
        |rectangular.prob q.1 q.2 a b - ∑ s, (p s).toReal * (T s).prob q.1 q.2 a b|) ≤
        2 * √(2 * δ) + 4 * √(18 * δ + 20 * √δ) := by
  intro μ δ
  have hm : μ.map Prod.snd = μ.map Prod.fst := by
    rw [Cslib.Probability.PMF.uniformOfFintype_prod_map_snd,
      Cslib.Probability.PMF.uniformOfFintype_prod_map_fst]
  obtain ⟨p, T, _, _, hT, _, h⟩ := rectangular.exists_synchronous_correlation_mixture μ hm
  exact ⟨p, T, hT, h⟩
