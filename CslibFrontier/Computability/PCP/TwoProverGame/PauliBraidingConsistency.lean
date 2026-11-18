/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingGame

/-!
# Consistency rounds of the Pauli braiding verifier

The same-basis round of the combined verifier samples an odd pair and a uniform independent
dummy. With the roles and basis fixed, its rejection bounds the squared distance between
the observables read from the answers at the sampled questions. Both observables refer to
the same checked string. A second bound compares the basis marginal and the special-question
observable, conditional on the matched question. These are steps toward the averaged
consistency bound of
[Natarajan and Vidick, Lemma 17][NatarajanVidick2017] (arXiv:1610.03574v1, p. 21).

## Main definitions

* `Cslib.PCP.pauliBraidingSameBasisGame`: the same-basis round with fixed roles and basis.

* `Cslib.PCP.pauliBraidingMatchedGame`: the special-question round at the matched question.

## Main results

* `Cslib.PCP.sum_norm_sub_sq_le_of_pauliBraidingSameBasisGame`: the same-basis distance bound.
* `Cslib.PCP.sum_norm_sub_sq_le_of_pauliBraidingMatchedGame`: the matched distance bound.
-/

public section

namespace Cslib.PCP

open BitString Quantum

variable {n : ℕ} [Nonempty (Fin n)] {Q A 𝒜 : Type*}

/-- The same-basis consistency subtest conditioned on a role assignment and basis. Its
seed retains the odd pair and independent dummy as separate choices. -/
@[expose] noncomputable def pauliBraidingSameBasisGame (n : ℕ) [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool) :
    SeededGame (↥(oddPairs (Fin n)) × (Fin n → Bool))
      (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) :=
  letI := oddPairs_nonempty (ι := Fin n)
  (pauliBraidingGame n G special decode).pullbackSeed (Probability.PMF.uniformOfFintype _)
    fun (p, dummy) => .sameBasis swapRoles basis p dummy

/-- Condition the special-question round on the matching question of the chosen basis,
with the basis and role assignment fixed. The odd pair remains uniform. -/
@[expose] noncomputable def pauliBraidingMatchedGame (n : ℕ) [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool) :
    SeededGame ↥(oddPairs (Fin n)) (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) :=
  letI := oddPairs_nonempty (ι := Fin n)
  (pauliBraidingGame n G special decode).pullbackSeed (Probability.PMF.uniformOfFintype _)
    fun p => .special swapRoles basis p (special basis)

/-- Decoders for the matched round in physical player order. Malformed answers
have a default decoded bit of `false`. -/
@[expose] def pauliBraidingMatchedDecoders (decode : Bool → A → Bool) (swapRoles basis : Bool)
    (p : ↥(oddPairs (Fin n))) :
    (((Bool × Bool) ⊕ A) → Bool) × (((Bool × Bool) ⊕ A) → Bool) :=
  let q : PauliConsistencyQuestion (Fin n) := ⟨p.val.1, p.val.2, basis⟩
  let readPair := Sum.elim q.braidingCheckedBit (fun _ : A => false)
  let readSpecial := Sum.elim (fun _ : Bool × Bool => false) (decode basis)
  cond swapRoles Prod.swap id (readPair, readSpecial)

variable [Fintype A] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- Rejection in the same-basis round bounds the seed-weighted squared distance of the
two observables that decode the shared string. In the decoded measurements a malformed
answer is read as `false`. The verifier itself rejects such an answer. -/
theorem sum_norm_sub_sq_le_of_pauliBraidingSameBasisGame
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let test := pauliBraidingSameBasisGame n G special decode swapRoles basis
    (∑ r, (test.seed r).toReal *
      let (x, y) := pauliBraidingSameBasisQuestions swapRoles basis r.1 r.2
      S.state.norm
        (((S.alice x.toBraidingQuestion).map
            (Sum.elim x.braidingCheckedBit fun _ => false)).observable -
          ((S.bob y.toBraidingQuestion).map
            (Sum.elim y.braidingCheckedBit fun _ => false)).observable) ^ 2) ≤
      4 * (1 - test.commutingWinProb S) := by
  let test := pauliBraidingSameBasisGame n G special decode swapRoles basis
  let read (q : PauliConsistencyQuestion (Fin n)) : (Bool × Bool) ⊕ A → Bool :=
    Sum.elim q.braidingCheckedBit fun _ => false
  let questions (r : ↥(oddPairs (Fin n)) × (Fin n → Bool)) :=
    pauliBraidingSameBasisQuestions swapRoles basis r.1 r.2
  refine test.sum_norm_sub_sq_le_of_accepts_imp_eq
    (fun r => read (questions r).1) (fun r => read (questions r).2) ?_ S
  rintro ⟨_, _⟩ a b h
  cases a <;> cases b <;> first | exact h | exact False.elim h

/-- Rejection in the matched special-question round bounds the seed-weighted squared
distance between the decoded basis marginal and the decoded special observable. -/
theorem sum_norm_sub_sq_le_of_pauliBraidingMatchedGame
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (swapRoles basis : Bool)
    (S : CommutingStrategy (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) 𝒜) :
    let test := pauliBraidingMatchedGame n G special decode swapRoles basis
    (∑ p, (test.seed p).toReal *
      let q := test.query p
      let read := pauliBraidingMatchedDecoders decode swapRoles basis p
      S.state.norm (((S.alice q.1).map read.1).observable -
        ((S.bob q.2).map read.2).observable) ^ 2) ≤
      4 * (1 - test.commutingWinProb S) := by
  let test := pauliBraidingMatchedGame n G special decode swapRoles basis
  let read := pauliBraidingMatchedDecoders (n := n) decode swapRoles basis
  refine test.sum_norm_sub_sq_le_of_accepts_imp_eq (fun p => (read p).1) (fun p => (read p).2) ?_ S
  intro p a b h
  cases swapRoles <;> cases a <;> cases b <;>
    first | exact False.elim h | exact h rfl | exact (h rfl).symm

end Cslib.PCP
