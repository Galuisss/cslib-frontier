/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PastingConsistency
import CslibFrontier.Foundations.Data.MvPolynomial.SchwartzZippel
import CslibFrontier.Foundations.Data.MvPolynomial.Shift
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Union
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Local agreement of incompatible slice transcripts

An unsuccessful readout with enough successful slices has an interpolant
through any selected `d + 1` slices, and an additional successful slice that
differs from this interpolant. Agreement with a univariate line at a prefix
forces the difference polynomial to vanish there. This is the algebraic
step of [Ji, Natarajan, Vidick, Wright and Yuen, Lemma 12.20]
[JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.PCP.LowIndividualDegree.card_locallyInterpolable_mul_card_le` bounds the number of
  prefixes on which an incompatible transcript can agree with a line.
* `Cslib.PCP.LowIndividualDegree.enoughSlices_prob_le_paste_prob_add` bounds the probability
  lost when discarding incompatible transcripts at distinct slice locations.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset MvPolynomial

variable {F ι : Type*} {m d : ℕ} [Field F] [Fintype ι]

/-- The successful slices agree at `u` with some univariate polynomial of degree at most `d`. -/
@[expose] def LocallyInterpolable (x : ι → F)
    (g : ι → Option (BoundedPolynomial F m d)) (u : Fin m → F) : Prop :=
  ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ i q, g i = some q → eval u q.val = f.eval (x i)

open scoped Classical in
/-- When global pasting fails despite enough successful outcomes, local interpolation
on a line is possible on at most an `m d / |F|` fraction of its prefixes, in counting form. -/
theorem card_locallyInterpolable_mul_card_le [Fintype F] (x : ι ↪ F)
    (g : ι → Option (BoundedPolynomial F m d)) (hcard : d < (successfulSlices g).card)
    (hfail : pasteOutcome x g = none) :
    #{u | LocallyInterpolable x g u} * Fintype.card F ≤
      (m * d) * (Fintype.card F) ^ m := by
  classical
  obtain ⟨s, hs, hsize⟩ := exists_subset_card_eq (Nat.succ_le_of_lt hcard)
  let selected (i : ι) := if i ∈ s then g i else none
  have hselected : successfulSlices selected = s := by
    ext i
    by_cases hi : i ∈ s
    · simpa [selected, hi] using hs hi
    · simp [selected, hi]
  obtain ⟨p, hp⟩ := pasteOutcome_eq_some_of_card x selected ((congrArg card hselected).trans hsize)
  have hfit : ¬ FitsSlices x g p := by
    intro h
    have := (pasteOutcome_eq_some_iff x g p).2 ⟨hcard, h⟩
    rw [hfail] at this
    cases this
  obtain ⟨i, q, hq, hne⟩ := not_forall.mp hfit |>.imp fun j hj =>
    not_forall.mp hj |>.imp fun q hq => not_imp.mp hq
  let difference := (p.specialize (x i)).val - q.val
  have hdiff : difference ≠ 0 := fun he => hne (Subtype.ext (sub_eq_zero.mp he))
  have hdeg : difference.totalDegree ≤ m * d := by
    refine (totalDegree_le_card_mul_of_degreeOf_le fun j =>
      (degreeOf_sub_le j _ _).trans (max_le ((p.specialize (x i)).prop j) (q.prop j))).trans_eq ?_
    rw [Fintype.card_fin]
  have hsubset :
      ({u | LocallyInterpolable x g u} : Finset (Fin m → F)) ⊆
          ({u | eval u difference = 0} : Finset (Fin m → F)) := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    obtain ⟨f, hf, hagree⟩ := hu
    have hline : evalPrefix u p.val = f := by
      refine evalPrefix_eq_of_paste_agrees x u hp hf fun j r hr => hagree j r ?_
      by_cases hj : j ∈ s
      · simpa [selected, hj] using hr
      · simp [selected, hj] at hr
    change eval u ((p.specialize (x i)).val - q.val) = 0
    rw [map_sub, hagree i q hq, ← hline, eval_evalPrefix]
    exact sub_self _
  exact (Nat.mul_le_mul_right _ (card_le_card hsubset)).trans
    (card_filter_eval_eq_zero_mul_card_le hdiff hdeg)

open Cslib.Probability.PMF
open scoped BigOperators

/-- The loss from discarding incompatible transcripts with enough successful slices is
bounded by the sum of the slice-line mismatches and the Schwartz–Zippel error. The
transcript marginal must be independent of the prefix queried on the other side. -/
theorem enoughSlices_prob_le_paste_prob_add [Fintype F] {β : Type*}
    (x : ι ↪ F) (lineValue : β → F → F)
    (hline : ∀ b, ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = lineValue b t)
    (law : (Fin m → F) → PMF ((ι → Option (BoundedPolynomial F m d)) × β))
    (p : PMF (ι → Option (BoundedPolynomial F m d)))
    (hmarg : ∀ u, (law u).map Prod.fst = p) :
    (p.toOuterMeasure {g | d < (successfulSlices g).card}).toReal ≤
      ((p.map (pasteOutcome x)).toOuterMeasure {q | q.isSome}).toReal +
      (∑ i, 𝔼 u, ((law u).toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal) +
      (m * d : ℝ) / Fintype.card F := by
  classical
  let bad : Set (ι → Option (BoundedPolynomial F m d)) :=
    {g | d < (successfulSlices g).card ∧ pasteOutcome x g = none}
  let survives (u : Fin m → F) : Set (ι → Option (BoundedPolynomial F m d)) :=
    {g | g ∈ bad ∧ LocallyInterpolable x g u}
  have hsplit :
      (p.toOuterMeasure {g | d < (successfulSlices g).card}).toReal =
        ((p.map (pasteOutcome x)).toOuterMeasure {q | q.isSome}).toReal +
        (p.toOuterMeasure bad).toReal := by
    rw [PMF.toOuterMeasure_map_apply]
    simp only [toOuterMeasure_apply_toReal, ← sum_add_distrib]
    refine sum_congr rfl fun g _ => ?_
    by_cases h : d < (successfulSlices g).card
    · cases hp : pasteOutcome x g <;> simp [h, hp, bad]
    · have hp : pasteOutcome x g = none := by
        cases he : pasteOutcome x g with
        | none => rfl
        | some q => exact (h ((pasteOutcome_eq_some_iff x g q).mp he).1).elim
      simp [bad, h, hp]
  rw [hsplit, add_assoc]
  apply add_le_add_right
  have hsurv (u : Fin m → F) :
      (p.toOuterMeasure bad).toReal ≤
        (∑ i, ((law u).toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal) +
        (p.toOuterMeasure (survives u)).toReal := by
    let misses := ⋃ i ∈ (univ : Finset ι), sliceLineMismatch (d := d) u x lineValue i
    have hloc : Prod.fst ⁻¹' bad ⊆ misses ∪ Prod.fst ⁻¹' survives u := by
      rintro ⟨g, b⟩ hg
      by_cases hmiss : (g, b) ∈ misses
      · exact Or.inl hmiss
      · apply Or.inr
        change g ∈ bad ∧ LocallyInterpolable x g u
        refine ⟨hg, ?_⟩
        obtain ⟨f, hf, he⟩ := hline b
        refine ⟨f, hf, fun i q hq => ?_⟩
        rw [he]
        by_contra hne
        exact hmiss (Set.mem_iUnion₂.mpr ⟨i, mem_univ i, q, hq, hne⟩)
    have hpre (e : Set (ι → Option (BoundedPolynomial F m d))) :
        ((law u).toOuterMeasure (Prod.fst ⁻¹' e)).toReal = (p.toOuterMeasure e).toReal := by
      rw [← PMF.toOuterMeasure_map_apply, hmarg u]
    have h := (toOuterMeasure_toReal_mono (law u) hloc).trans
      (ENNReal.toReal_le_add (MeasureTheory.measure_union_le _ _)
        (toOuterMeasure_ne_top _ _) (toOuterMeasure_ne_top _ _))
    rw [hpre, hpre] at h
    exact h.trans (add_le_add_left (toOuterMeasure_toReal_biUnion_finset_le (law u) _ _) _)
  have hlocal : (𝔼 u, (p.toOuterMeasure (survives u)).toReal) ≤ (m * d : ℝ) / Fintype.card F := by
    simp_rw [toOuterMeasure_toReal_eq_sum_ite (p := p), Finset.expect_sum_comm,
      ← Finset.mul_expect]
    calc
      _ ≤ ∑ g, (p g).toReal * ((m * d : ℝ) / Fintype.card F) := by
        refine sum_le_sum fun g _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        by_cases hg : g ∈ bad
        · rw [Fintype.expect_eq_sum_div_card]
          have hc : (∑ u : Fin m → F, if g ∈ survives u then (1 : ℝ) else 0) =
              (#{u | LocallyInterpolable x g u} : ℝ) := by
            simp [survives, hg]
          rw [hc]
          have hcard := card_locallyInterpolable_mul_card_le x g hg.1 hg.2
          have hcard' : (#{u | LocallyInterpolable x g u} : ℝ) * Fintype.card F ≤
              (m * d : ℝ) * (Fintype.card F : ℝ) ^ m := by exact_mod_cast hcard
          have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
          rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
            div_le_div_iff₀ (pow_pos hF m) hF]
          exact hcard'
        · have hnonneg : 0 ≤ (m * d : ℝ) / Fintype.card F := by positivity
          simpa [survives, hg] using hnonneg
      _ = _ := by rw [← sum_mul, sum_toReal, one_mul]
  calc
    _ = 𝔼 _u : Fin m → F, (p.toOuterMeasure bad).toReal := (Fintype.expect_const _).symm
    _ ≤ 𝔼 u, ((∑ i, ((law u).toOuterMeasure (sliceLineMismatch u x lineValue i)).toReal) +
        (p.toOuterMeasure (survives u)).toReal) := expect_le_expect fun u _ => hsurv u
    _ ≤ _ := by
      rw [expect_add_distrib, expect_sum_comm]
      exact add_le_add_right hlocal _

end Cslib.PCP.LowIndividualDegree
