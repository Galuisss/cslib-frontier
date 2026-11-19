/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerticalAxis
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Restriction to a coordinate slice

Fixing the final coordinate embeds a lower-dimensional verifier question in
the original space. Restrict the answers to this slice, preserving both
degree bounds. For repeated restriction the diagonal cutoff is held fixed,
even though the ambient dimension decreases. This is the restriction estimate
of [JNVWY2020LowIndividualDegree, Lemma 6.6], with the cutoff explicit.

## Main definitions

* `Cslib.PCP.LowIndividualDegree.restrictSlice` restricts a commuting strategy
  to a fixed last coordinate.
* `Cslib.PCP.LowIndividualDegree.restrictSliceTensor` restricts a tensor strategy
  while retaining the same state and preserving projectivity.

## Main results

* `Cslib.PCP.LowIndividualDegree.average_slice_axis_loss_le`,
  `Cslib.PCP.LowIndividualDegree.average_slice_consistency_loss_le`, and
  `Cslib.PCP.LowIndividualDegree.average_slice_diagonal_loss_le` bound the
  expected branch losses of the restricted strategy.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset
open scoped BigOperators

variable {F A : Type*} {m : ℕ}

/-- Append the fixed coordinate of a slice to each point. -/
def sliceEmbedding (t : F) : Point F m ↪ Point F (m + 1) :=
  ⟨fun u => Fin.snoc u t, fun _ _ h => by simpa using congrArg Fin.init h⟩

@[simp] theorem sliceEmbedding_apply (t : F) (u : Point F m) :
    sliceEmbedding t u = Fin.snoc u t := by
  unfold sliceEmbedding
  rfl

variable [Field F] [Fintype F] [DecidableEq F]

/-- View a point or line question inside the ambient space. -/
def sliceQuestion (t : F) : Question F m → Question F (m + 1)
  | .point u => .point (sliceEmbedding t u)
  | .axis L => .axis (L.map (sliceEmbedding t))
  | .diagonal L => .diagonal (L.map (sliceEmbedding t))

/-- Keep the point value or restrict a line function to the points in the slice. -/
def sliceAnswer (t : F) : Answer F (m + 1) → Answer F m
  | .inl a => .inl a
  | .inr ⟨L, f⟩ => .inr ⟨univ.filter (fun u => sliceEmbedding t u ∈ L),
      fun u => f ⟨sliceEmbedding t u, (mem_filter.mp u.prop).2⟩⟩

omit [Fintype F] [DecidableEq F] in
private theorem snoc_add_smul (t c : F) (u v : Point F m) :
    Fin.snoc (u + c • v) t = Fin.snoc u t + c • Fin.snoc v 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

theorem linePoints_map_slice (t : F) (u v : Point F m) :
    (linePoints u v).map (sliceEmbedding t) =
      linePoints (Fin.snoc u t) (Fin.snoc v 0) := by
  ext x
  simp only [mem_map, mem_linePoints_iff]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (snoc_add_smul t c u v).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨u + c • v, ⟨c, rfl⟩, snoc_add_smul t c u v⟩

private theorem sliceAnswer_preserves_lineAgrees (t : F) (d : ℕ) (u v : Point F m)
    (a : Σ L : Finset (Point F (m + 1)), L → F) (b : F)
    (h : lineAgrees d ((linePoints u v).map (sliceEmbedding t)) (Fin.snoc u t) a b) :
    ∃ a' : Σ L : Finset (Point F m), L → F,
      sliceAnswer t (.inr a) = .inr a' ∧ lineAgrees d (linePoints u v) u a' b := by
  obtain ⟨L, f⟩ := a
  unfold lineAgrees at h
  obtain ⟨hL, hdegree, hu, he⟩ := h
  dsimp only at hL hdegree hu he
  subst L
  let K := univ.filter fun w : Point F m => sliceEmbedding t w ∈
    (linePoints u v).map (sliceEmbedding t)
  let f' : K → F := fun w => f ⟨sliceEmbedding t w, (mem_filter.mp w.prop).2⟩
  have hK : K = linePoints u v := by
    ext w
    simp [K]
  have hL := linePoints_map_slice t u v
  obtain ⟨p, hp, hval⟩ := hdegree.exists_polynomial_of_eq hL.symm
  unfold lineAgrees
  refine ⟨⟨K, f'⟩, rfl, hK, ⟨u, v, hK.symm, p, hp, ?_⟩, ?_⟩
  · intro c
    rw [← hval c]
    exact congrArg f (Subtype.ext (snoc_add_smul t c u v))
  · have hu' : u ∈ K := by
      rw [hK]
      simpa using mem_linePoints u v (0 : F)
    exact ⟨hu', he⟩

/-- An accepted ambient answer to an axis line and its point stays accepted
after restricting both answers to the slice. -/
theorem sliceAnswer_preserves_axis (t : F) (d D : ℕ) (u v : Point F m)
    (a b : Answer F (m + 1))
    (h : acceptsAtDegrees d D (sliceQuestion t (.axis (linePoints u v)))
      (sliceQuestion t (.point u)) a b) :
    acceptsAtDegrees d D (.axis (linePoints u v)) (.point u)
      (sliceAnswer t a) (sliceAnswer t b) := by
  cases a <;> cases b <;> simp only [sliceQuestion, sliceEmbedding_apply, acceptsAtDegrees] at h
  rename_i a b
  obtain ⟨a', ha', h⟩ := sliceAnswer_preserves_lineAgrees t d u v a b h
  rw [ha']
  simpa only [sliceAnswer, acceptsAtDegrees] using h

/-- Diagonal acceptance is preserved when the degree cutoff is kept fixed. -/
theorem sliceAnswer_preserves_diagonal (t : F) (d D : ℕ) (u v : Point F m)
    (a b : Answer F (m + 1))
    (h : acceptsAtDegrees d D (sliceQuestion t (.diagonal (linePoints u v)))
      (sliceQuestion t (.point u)) a b) :
    acceptsAtDegrees d D (.diagonal (linePoints u v)) (.point u)
      (sliceAnswer t a) (sliceAnswer t b) := by
  cases a <;> cases b <;> simp only [sliceQuestion, sliceEmbedding_apply, acceptsAtDegrees] at h
  rename_i a b
  obtain ⟨a', ha', h⟩ := sliceAnswer_preserves_lineAgrees t D u v a b h
  rw [ha']
  simpa only [sliceAnswer, acceptsAtDegrees] using h

private theorem sliceAnswer_preserves_points (t : F) (d D : ℕ) (u v : Point F m)
    (a b : Answer F (m + 1))
    (h : acceptsAtDegrees d D (sliceQuestion t (.point u)) (sliceQuestion t (.point v)) a b) :
    acceptsAtDegrees d D (.point u) (.point v) (sliceAnswer t a) (sliceAnswer t b) := by
  cases a <;> cases b <;> simp only [sliceQuestion, acceptsAtDegrees] at h
  exact h

variable [Ring A] [PartialOrder A] [IsOrderedAddMonoid A] [Algebra ℂ A]

/-- Ask ambient questions in the fixed slice and postprocess the answers.
This operation keeps the original shared state. -/
noncomputable def restrictSlice (S : CommutingStrategy (Question F (m + 1))
    (Question F (m + 1)) (Answer F (m + 1)) (Answer F (m + 1)) A) (t : F) :
    CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A := by
  classical
  exact {
    state := S.state
    alice q := (S.alice (sliceQuestion t q)).map (sliceAnswer t)
    bob q := (S.bob (sliceQuestion t q)).map (sliceAnswer t)
    commute q q' := Measurement.commute_map_map _ _ (S.commute _ _) _ _ }

variable [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

private theorem sum_over_answer_fibers {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (r : X → Y) (f : Y → X → ℝ) :
    (∑ y, ∑ x with r x = y, f y x) = ∑ x, f (r x) x := by
  calc
    _ = ∑ y, ∑ x with r x = y, f (r x) x := by
      refine sum_congr rfl fun y _ => sum_congr rfl fun x hx => ?_
      rw [(mem_filter.mp hx).2]
    _ = _ := sum_fiberwise univ r _

private theorem sliceScore_le
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) A)
    (t : F) (d D : ℕ) (x y : Question F m)
    (h : ∀ a b, acceptsAtDegrees d D (sliceQuestion t x) (sliceQuestion t y) a b →
      acceptsAtDegrees d D x y (sliceAnswer t a) (sliceAnswer t b)) :
    acceptScoreAtDegrees S d D (sliceQuestion t x) (sliceQuestion t y) ≤
      acceptScoreAtDegrees (restrictSlice S t) d D x y := by
  classical
  let r := sliceAnswer (m := m) t
  let p := S.prob (sliceQuestion t x) (sliceQuestion t y)
  let w (c e : Answer F m) (a b : Answer F (m + 1)) :=
    if acceptsAtDegrees d D x y c e then p a b else 0
  have he (c e : Answer F m) : (restrictSlice S t).prob x y c e =
      ∑ a with r a = c, ∑ b with r b = e, p a b := by
    simp only [CommutingStrategy.prob, restrictSlice, Measurement.map_effect, r, p, sum_mul,
      mul_sum, map_sum, Complex.re_sum]
    exact sum_comm
  have hex : acceptScoreAtDegrees (restrictSlice S t) d D x y =
      ∑ c, ∑ e, ∑ a with r a = c, ∑ b with r b = e, w c e a b := by
    unfold acceptScoreAtDegrees
    refine sum_congr rfl fun c _ => sum_congr rfl fun e _ => ?_
    rw [he]
    by_cases hh : acceptsAtDegrees d D x y c e <;> simp [w, hh]
  rw [hex]
  calc
    acceptScoreAtDegrees S d D (sliceQuestion t x) (sliceQuestion t y) ≤
        ∑ a, ∑ b, w (r a) (r b) a b := by
      unfold acceptScoreAtDegrees
      refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
      by_cases hh : acceptsAtDegrees d D (sliceQuestion t x) (sliceQuestion t y) a b
      · have hg : acceptsAtDegrees d D x y (r a) (r b) := h a b hh
        simp only [hh, ite_true, w, hg, p, le_refl]
      · simp only [hh, ite_false, w]
        exact ite_nonneg (S.prob_nonneg _ _ _ _) le_rfl
    _ = ∑ c, ∑ a with r a = c, ∑ e, ∑ b with r b = e, w c e a b := by
      simp only [sum_over_answer_fibers]
    _ = _ := sum_congr rfl fun c _ => sum_comm

private theorem sliceLineScore_le
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) A) (t : F) (d D : ℕ)
    (u : Point F m) (line : Question F m)
    (h : ∀ a b, acceptsAtDegrees d D (sliceQuestion t line) (sliceQuestion t (.point u)) a b →
      acceptsAtDegrees d D line (.point u) (sliceAnswer t a) (sliceAnswer t b)) :
    lineScoreAtDegrees S d D (Fin.snoc u t) (sliceQuestion t line) ≤
      lineScoreAtDegrees (restrictSlice S t) d D u line := by
  have hrev (a b : Answer F (m + 1)) :
      acceptsAtDegrees d D (sliceQuestion t (.point u)) (sliceQuestion t line) a b →
      acceptsAtDegrees d D (.point u) line (sliceAnswer t a) (sliceAnswer t b) := fun hh =>
    (acceptsAtDegrees_swap d D _ _ _ _).mp (h _ _ ((acceptsAtDegrees_swap d D _ _ _ _).mp hh))
  have h1 := sliceScore_le S t d D (.point u) line hrev
  have h2 := sliceScore_le S t d D line (.point u) h
  have hp : sliceQuestion t (.point u) = .point (Fin.snoc u t) := by simp [sliceQuestion]
  rw [hp] at h1 h2
  unfold lineScoreAtDegrees
  linarith only [h1, h2]

omit [Fintype F] [DecidableEq F] in
private theorem snoc_single (i : Fin m) :
    Fin.snoc (Pi.single i (1 : F) : Point F m) 0 = (Pi.single i.castSucc 1 : Point F (m + 1)) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · simp [Pi.single_apply]

private theorem one_sub_expect {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    1 - (𝔼 x, f x) = 𝔼 x, (1 - f x) := by
  rw [expect_sub_distrib, Fintype.expect_const]

omit [Field F] [DecidableEq F] in
private theorem average_slice_loss_le (n : ℕ)
    (f : Point F (n + 2) → Fin (n + 2) → ℝ)
    (g : F → Point F (n + 1) → Fin (n + 1) → ℝ)
    (hf : ∀ u i, 0 ≤ f u i)
    (h : ∀ t u i, g t u i ≤ f (Fin.snoc u t) i.castSucc) :
    (n + 1 : ℝ) * (𝔼 t : F, 𝔼 u, 𝔼 i, g t u i) ≤
      (n + 2 : ℝ) * (𝔼 u, 𝔼 i, f u i) := by
  calc
    _ ≤ (n + 1 : ℝ) * (𝔼 t : F, 𝔼 u : Point F (n + 1),
        𝔼 i : Fin (n + 1), f (Fin.snoc u t) i.castSucc) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact expect_le_expect fun t _ => expect_le_expect fun u _ =>
        expect_le_expect fun i _ => h t u i
    _ = (n + 1 : ℝ) * (𝔼 u : Point F (n + 2), 𝔼 i : Fin (n + 1), f u i.castSucc) := by
      rw [expect_comm (ι := F) (κ := Point F (n + 1)) univ univ]
      exact congrArg ((n + 1 : ℝ) * ·) (Fintype.expect_fin_snoc
        (fun u => 𝔼 i : Fin (n + 1), f u i.castSucc))
    _ ≤ _ := by
      rw [Finset.mul_expect univ _ (n + 1 : ℝ), Finset.mul_expect univ _ (n + 2 : ℝ)]
      refine expect_le_expect fun u _ => ?_
      have hleft : (n + 1 : ℝ) * (𝔼 i : Fin (n + 1), f u i.castSucc) =
          ∑ i : Fin (n + 1), f u i.castSucc := by
        simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
          (Fintype.card_mul_expect (M := ℝ) (fun i : Fin (n + 1) => f u i.castSucc))
      have hright : (n + 2 : ℝ) * (𝔼 i, f u i) = ∑ i, f u i := by
        simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using
          (Fintype.card_mul_expect (M := ℝ) (f u))
      rw [hleft, hright, Fin.sum_univ_castSucc (f u)]
      exact le_add_of_nonneg_right (hf u _)

/-- Restricting to a uniform last coordinate costs at most the ratio of the
ambient and slice dimensions in the mean axis rejection probability. -/
theorem average_slice_axis_loss_le {n : ℕ}
    (S : CommutingStrategy (Question F (n + 2)) (Question F (n + 2))
      (Answer F (n + 2)) (Answer F (n + 2)) A) (d D : ℕ) :
    (n + 1 : ℝ) * (𝔼 t : F, (1 - (branchGameAtDegrees (F := F) n d D .axis).commutingWinProb
      (restrictSlice S t))) ≤
      (n + 2 : ℝ) * (1 - (branchGameAtDegrees (F := F) (n + 1) d D .axis).commutingWinProb S) := by
  simp only [axisScoreAtDegrees_eq_expect, one_sub_expect]
  apply average_slice_loss_le n
  · intro u i
    exact sub_nonneg.mpr (lineScoreAtDegrees_le_one S d D u _)
  · intro t u i
    apply sub_le_sub_left
    have h := sliceLineScore_le S t d D u (.axis (linePoints u (Pi.single i 1)))
      (sliceAnswer_preserves_axis t d D u (Pi.single i 1))
    simpa only [sliceQuestion, linePoints_map_slice, snoc_single] using h

/-- A shared point sampled in a uniform slice is a uniform ambient point. -/
theorem average_slice_consistency_loss_le {n : ℕ}
    (S : CommutingStrategy (Question F (n + 2)) (Question F (n + 2))
      (Answer F (n + 2)) (Answer F (n + 2)) A) (d D : ℕ) :
    (𝔼 t : F, (1 - (branchGameAtDegrees (F := F) n d D .consistency).commutingWinProb
      (restrictSlice S t))) ≤
      1 - (branchGameAtDegrees (F := F) (n + 1) d D .consistency).commutingWinProb S := by
  simp only [consistencyScoreAtDegrees_eq_expect, one_sub_expect]
  rw [← Fintype.expect_fin_snoc (fun u =>
    1 - acceptScoreAtDegrees S d D (.point u) (.point u)),
    expect_comm (ι := Point F (n + 1)) (κ := F) univ univ]
  refine expect_le_expect fun t _ => expect_le_expect fun u _ => sub_le_sub_left ?_ _
  exact sliceScore_le S t d D (.point u) (.point u) (sliceAnswer_preserves_points t d D u u)

/-- Restricting to a uniform slice discards only the longest diagonal prefix.
The diagonal degree cutoff is held fixed on both sides of the bound. -/
theorem average_slice_diagonal_loss_le {n : ℕ}
    (S : CommutingStrategy (Question F (n + 2)) (Question F (n + 2))
      (Answer F (n + 2)) (Answer F (n + 2)) A) (d D : ℕ) :
    (n + 1 : ℝ) * (𝔼 t : F, (1 - (branchGameAtDegrees (F := F) n d D .diagonal).commutingWinProb
      (restrictSlice S t))) ≤
      (n + 2 : ℝ) *
        (1 - (branchGameAtDegrees (F := F) (n + 1) d D .diagonal).commutingWinProb S) := by
  simp only [diagonalScoreAtDegrees_eq_expect, one_sub_expect]
  apply average_slice_loss_le n
  · intro u i
    exact expect_nonneg fun v _ => sub_nonneg.mpr (lineScoreAtDegrees_le_one S d D u _)
  · intro t u i
    refine expect_le_expect fun v _ => sub_le_sub_left ?_ _
    have h := sliceLineScore_le S t d D u (.diagonal (linePoints u (prefixDirection i v)))
      (sliceAnswer_preserves_diagonal t d D u (prefixDirection i v))
    simpa only [sliceQuestion, linePoints_map_slice, ← prefixDirection_castSucc] using h

private theorem decodePoint_comp_sliceAnswer (t : F) :
    decodePoint ∘ (sliceAnswer (m := m) t) = decodePoint := by
  funext a
  cases a with
  | inl a => simp [sliceAnswer]
  | inr a => obtain ⟨L, f⟩ := a; simp [sliceAnswer]

omit [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A] in
/-- The decoded point measurement of a slice is the ambient point measurement
at the appended coordinate. -/
theorem decodedPoint_restrictSlice
    (S : CommutingStrategy (Question F (m + 2)) (Question F (m + 2))
      (Answer F (m + 2)) (Answer F (m + 2)) A) (t : F) (u : Point F (m + 1)) :
    decodedPoint (restrictSlice S t).alice u = decodedPoint S.alice (Fin.snoc u t) := by
  classical
  simp only [decodedPoint, restrictSlice, sliceQuestion, sliceEmbedding_apply, Measurement.map_map,
    decodePoint_comp_sliceAnswer]

section Tensor

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private noncomputable def restrictAnswerPOVM
    (M : POVM (Answer F (m + 1)) ι) (t : F) : POVM (Answer F m) ι := by
  classical
  exact (M.toMeasurement.map (sliceAnswer t)).toPOVM

/-- Restrict a finite tensor strategy while retaining its local spaces and shared state. -/
noncomputable def restrictSliceTensor
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι κ) (t : F) :
    QuantumStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) ι κ where
  state := S.state
  norm_state := S.norm_state
  alice q := restrictAnswerPOVM (S.alice (sliceQuestion t q)) t
  bob q := restrictAnswerPOVM (S.bob (sliceQuestion t q)) t

omit [Field F] in
@[simp] theorem restrictSliceTensor_state
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι κ) (t : F) :
    (restrictSliceTensor S t).state = S.state := by
  unfold restrictSliceTensor
  rfl

omit [Field F] in
/-- Equal local measurements remain equal upon restriction. -/
theorem restrictSliceTensor_bob_eq_alice
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι ι) (t : F) (h : S.bob = S.alice) :
    (restrictSliceTensor S t).bob = (restrictSliceTensor S t).alice := by
  unfold restrictSliceTensor
  rw [h]

omit [Field F] in
/-- The restricted strategy uses projective measurements when the original does. -/
theorem restrictSliceTensor_alice_isProjective
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι κ) (t : F)
    (h : ∀ q, ((S.alice q).toMeasurement).IsProjective) (q : Question F m) :
    (((restrictSliceTensor S t).alice q).toMeasurement).IsProjective := by
  classical
  unfold restrictSliceTensor restrictAnswerPOVM
  intro a
  simpa only [POVM.toMeasurement_effect, Measurement.toPOVM_effect] using
    ((h (sliceQuestion t q)).map (sliceAnswer t)) a

omit [Field F] in
/-- The tensor and commuting restrictions use the same bipartite effects. -/
theorem restrictSliceTensor_toCommuting
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι κ) (t : F) :
    (restrictSliceTensor S t).toCommuting = restrictSlice S.toCommuting t := by
  classical
  unfold restrictSliceTensor QuantumStrategy.toCommuting restrictSlice
  congr 1
  · funext q
    apply Measurement.ext
    intro a
    change kroneckerOne ((restrictAnswerPOVM (S.alice (sliceQuestion t q)) t).effect a) =
      ((QuantumStrategy.leftMeasurement (κ := κ) (S.alice (sliceQuestion t q))).map
        (sliceAnswer t)).effect a
    unfold restrictAnswerPOVM
    simp only [Measurement.toPOVM_effect, Measurement.map_effect, map_sum,
      POVM.toMeasurement_effect]
    rfl
  · funext q
    apply Measurement.ext
    intro a
    change oneKronecker ((restrictAnswerPOVM (S.bob (sliceQuestion t q)) t).effect a) =
      ((QuantumStrategy.rightMeasurement (ι := ι) (S.bob (sliceQuestion t q))).map
        (sliceAnswer t)).effect a
    unfold restrictAnswerPOVM
    simp only [Measurement.toPOVM_effect, Measurement.map_effect, map_sum,
      POVM.toMeasurement_effect]
    rfl

end Tensor

end Cslib.PCP.LowIndividualDegree
