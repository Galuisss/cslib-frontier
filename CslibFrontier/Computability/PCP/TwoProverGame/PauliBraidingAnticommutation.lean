/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingConsistency
public import CslibFrontier.Computability.PCP.TwoProverGame.AnticommutationTest

/-!
# The CHSH strategy on an odd pair in the braiding test

Restricting the tagged anticommutation questions of a single strategy to one odd
pair gives a commuting CHSH strategy. Its logical second player's observables
are exactly those checked in the matched consistency rounds.
-/

public section

namespace Cslib.PCP

open BitString Quantum

variable {n : ℕ} {𝒜 : Type*} [Ring 𝒜] [PartialOrder 𝒜] [Algebra ℂ 𝒜]
variable [IsOrderedAddMonoid 𝒜]

/-- Extract CHSH on an odd pair. Use the two role tags of the anticommutation branch and
decode malformed answers as false. The Boolean role assignment selects the logical order. -/
@[expose] def pauliBraidingCHSHStrategy
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜)
    (roles : Bool) (p : ↥(oddPairs (Fin n))) : CommutingStrategy Bool Bool Bool Bool 𝒜 :=
  let logical := cond roles S.swap S
  let read : (Bool × Bool) ⊕ Bool → Bool := Sum.elim (fun _ => false) id
  logical.map (fun q => .anticommutation false q p) (fun q => .anticommutation true q p)
    (fun _ => read) (fun _ => read)

/-- The extracted CHSH strategy uses the original state. -/
@[simp] theorem pauliBraidingCHSHStrategy_state
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜)
    (roles : Bool) (p : ↥(oddPairs (Fin n))) :
    (pauliBraidingCHSHStrategy S roles p).state = S.state := by
  cases roles <;> rfl

variable [StarRing 𝒜] [StarOrderedRing 𝒜]

/-- The second-role observable of CHSH is exactly the special observable used in the
consistency estimate on the same pair. -/
theorem pauliBraidingCHSHStrategy_bob_observable
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜)
    (roles : Bool) (p : ↥(oddPairs (Fin n))) (q : Bool) :
    ((pauliBraidingCHSHStrategy S roles p).bob q).observable =
      pauliBraidingSpecialObservable (cond roles S.alice S.bob) q id p := by
  cases roles <;> rfl

/-- The CHSH branch conditioned on a single odd pair and role assignment, with the
verifier's original rejection rule for malformed answers. -/
@[expose] noncomputable def pauliBraidingCHSHGame (n : ℕ) [Nonempty (Fin n)]
    (roles : Bool) (p : ↥(oddPairs (Fin n))) :
    SeededGame (Bool × Bool) (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) :=
  (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).pullbackSeed
    TwoProverGame.chsh.questions fun (x, y) => .anticommutation roles p x y

open Finset in
/-- Scoring the decoded CHSH strategy can only increase acceptance, since the actual
verifier rejects every malformed answer before decoding. -/
theorem commutingWinProb_pauliBraidingCHSHGame_le [Nonempty (Fin n)]
    [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
    [NonnegSpectrumClass ℝ 𝒜]
    (S : CommutingStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) 𝒜)
    (roles : Bool) (p : ↥(oddPairs (Fin n))) :
    (pauliBraidingCHSHGame n roles p).commutingWinProb S ≤
      TwoProverGame.chsh.commutingWinProb (pauliBraidingCHSHStrategy S roles p) := by
  classical
  let game := pauliBraidingCHSHGame n roles p
  let logical := cond roles S.swap S
  let q₁ (x : Bool) : PauliBraidingQuestion n Bool := .anticommutation false x p
  let q₂ (y : Bool) : PauliBraidingQuestion n Bool := .anticommutation true y p
  let read : (Bool × Bool) ⊕ Bool → Bool := Sum.elim (fun _ => false) id
  change game.commutingWinProb S ≤ _
  rw [SeededGame.commutingWinProb_eq_sum]
  unfold TwoProverGame.commutingWinProb
  change _ ≤ TwoProverGame.chsh.toSeeded.commutingWinProb _
  let : ∀ q a b, Decidable (TwoProverGame.chsh.toSeeded.accepts q a b) :=
    fun q a b => inferInstanceAs (Decidable (TwoProverGame.chsh.accepts q.1 q.2 a b))
  rw [SeededGame.commutingWinProb_eq_sum]
  refine sum_le_sum fun ⟨x, y⟩ _ =>
    mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  change (∑ a, ∑ b, if game.accepts (x, y) a b then
    S.prob (game.query (x, y)).1 (game.query (x, y)).2 a b else 0) ≤
      (∑ a, ∑ b, if TwoProverGame.chsh.accepts x y a b then
        (logical.map q₁ q₂ (fun _ => read) (fun _ => read)).prob x y a b else 0)
  rw [logical.sum_ite_prob_map]
  have hquery : game.query (x, y) = cond roles Prod.swap id (q₁ x, q₂ y) := rfl
  have hswap : (∑ a, ∑ b, if game.accepts (x, y) a b then
      S.prob (game.query (x, y)).1 (game.query (x, y)).2 a b else 0) =
      ∑ a, ∑ b, if game.accepts (x, y) (cond roles b a) (cond roles a b) then
        logical.prob (q₁ x) (q₂ y) a b else 0 := by
    rw [hquery]
    cases roles
    · rfl
    · simp only [logical, Bool.cond_true, Prod.swap_prod_mk, S.prob_swap]
      exact sum_comm
  rw [hswap]
  refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
  have haccept (h : game.accepts (x, y) (cond roles b a) (cond roles a b)) :
      TwoProverGame.chsh.accepts x y (read a) (read b) := by
    cases roles <;> cases a <;> cases b <;> first | exact h | exact False.elim h
  split_ifs with h₁ h₂ h₂
  · exact le_rfl
  · exact False.elim (h₂ (haccept h₁))
  · exact logical.prob_nonneg _ _ _ _
  · exact le_rfl

end Cslib.PCP
