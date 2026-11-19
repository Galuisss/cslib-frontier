/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerticalAxis
import Mathlib.Algebra.Field.ZMod

/-! # The two-coordinate low individual degree verifier over three elements -/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum
open scoped MatrixOrder ComplexOrder BigOperators

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def prodVars : MvPolynomial (Fin 2) (ZMod 3) :=
  MvPolynomial.X 0 * MvPolynomial.X 1

private theorem prodVars_degree (i : Fin 2) : prodVars.degreeOf i ≤ 1 := by
  refine (MvPolynomial.degreeOf_mul_le i _ _).trans ?_
  fin_cases i <;> simp [MvPolynomial.degreeOf_X]

/-- The verifier accepts a polynomial of individual degree one and total degree two. -/
example : (game (F := ZMod 3) 1 1).winProb (honest prodVars) (honest prodVars) = 1 :=
  winProb_honest prodVars prodVars_degree

/-- The diagonal law includes a singleton line, with its point and line on opposite roles. -/
example (u : Point (ZMod 3) 2) :
    (Question.diagonal (linePoints u 0), Question.point u) ∈
      (diagonalQuestions (F := ZMod 3) 1).support := by
  refine mem_diagonalQuestions_support.mpr ⟨u, 0, 0, true, ?_⟩
  simp


private noncomputable def verticalStrategy :
    QuantumStrategy (Question (ZMod 3) 2) (Question (ZMod 3) 2)
      (Answer (ZMod 3) 2) (Answer (ZMod 3) 2) (Fin 1) (Fin 1) := by
  classical
  exact QuantumStrategy.ofDeterministic (honest prodVars) (honest prodVars)

/-- For the honest product polynomial on two coordinates, the decoded vertical
measurements and the endpoint measurements have zero state distance. -/
example : let S := verticalStrategy.toCommuting
    (𝔼 u : Point (ZMod 3) 1, 𝔼 t : ZMod 3, ∑ a, S.state.norm
      ((decodedPoint S.bob (Fin.snoc u t)).effect a -
        ((decodedVertical S.bob 1 u).map (fun f => f.value t)).effect a) ^ 2) ≤ 0 := by
  intro S
  classical
  have h (b : Branch) : (branchGame (F := ZMod 3) 1 1 b).commutingWinProb S = 1 := by
    dsimp only [S]
    rw [TwoProverGame.commutingWinProb_toCommuting]
    unfold verticalStrategy
    rw [TwoProverGame.quantumWinProb_ofDeterministic]
    exact winProb_branch_honest prodVars prodVars_degree b
  simpa only [h, sub_self, mul_zero, add_zero] using bob_vertical_stateDist_le S 1
