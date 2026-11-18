/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Linearity
import Mathlib.Data.List.Lex

/-!
# The symmetric linearity game

In Figure 1 of [Natarajan and Vidick][NatarajanVidick2017] (arXiv:1610.03574v1),
both players answer a pair of strings in lexicographic order. The verifier assigns roles
uniformly at random. The pair player receives two independent uniform strings; the point
player receives the selected linearity query together with an independent uniform dummy.
The verifier tracks which coordinate carries each answer when sorting the questions.

## Main definitions

* `Cslib.PCP.symmetricLinearityGame`: the seeded game with random roles and sorted questions.
-/

public section

namespace Cslib.PCP

/-- The symmetric two-player linearity game. The seed specifies the role assignment, the
check, the pair player's two strings and the point player's dummy. The check remains indexed
by the sampled choice even when candidate query strings coincide. -/
@[expose] noncomputable def symmetricLinearityGame (n : ℕ) :
    SeededGame (Bool × Fin 3 × (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool))
      ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) :=
  -- Use the same comparison for sending questions and restoring the answer coordinates.
  let lexSwap (a b : Fin n → Bool) : Bool := decide (List.ofFn b < List.ofFn a)
  { seed := Probability.PMF.uniformOfFintype _
    query := fun
    | (swapRoles, k, a, b, dummy) =>
      let c := linearityQuery k a b
      let pair := cond (lexSwap a b) Prod.swap id (a, b)
      let point := cond (lexSwap c dummy) Prod.swap id (c, dummy)
      cond swapRoles Prod.swap id (pair, point)
    accepts := fun
    | (swapRoles, k, a, b, dummy), alice, bob =>
      let (pair, point) := cond swapRoles Prod.swap id (alice, bob)
      let c := linearityQuery k a b
      (cond (lexSwap c dummy) Prod.swap id point).1 =
        linearityCheck k (cond (lexSwap a b) Prod.swap id pair) }

instance (seed : Bool × Fin 3 × (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool))
    (alice bob : Bool × Bool) : Decidable ((symmetricLinearityGame n).accepts seed alice bob) := by
  rcases seed with ⟨swapRoles, k, a, b, dummy⟩
  unfold symmetricLinearityGame
  dsimp only
  infer_instance

end Cslib.PCP
