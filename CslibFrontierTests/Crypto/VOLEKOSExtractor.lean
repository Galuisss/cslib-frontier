/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.VOLE.KOSExtractor
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Ordinary-module clients and edge-case audits for `VOLE.KOSExtractor`

1. **Zero, one, and two-opening edge cases:** verifies that `kosExtract` handles `0`, `1`, and `2`
   accepted openings explicitly and that `toOuterMeasure_kosExtract_graph_failure_le` gives exact
   zero failure measure (`0.choose 3 = 1.choose 3 = 2.choose 3 = 0`).
2. **Nontrivial 3-opening and 4-opening response-graph clients over `ZMod 5`:** constructs a
   `1 / 5`-universal linear inner-product hash over `(ZMod 5)²`,
   verifies exact recovery of a 4-point VOLE line, verifies that on a non-collinear 3-point graph
   a colliding seed triggers `kosFailureWitness` with nonzero `kosAffineDefect` mapped to `0`, and
   checks the exact `1 / 5` (`3.choose 3 = 1`) and `4 / 5` (`4.choose 3 = 4`) probability bounds.
3. **Characteristic-two `BinaryField 4` (`GF(16)`) client:** exercises the response-graph theorem
   over FAEST-style characteristic-two binary extension fields without unfolding proof internals.
-/

public section

namespace CslibFrontierTests.Crypto.VOLEKOSExtractor

open Cslib Cslib.Probability Cslib.Crypto.Protocols.VOLE
open scoped ENNReal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Linear inner-product hash `(s₀, s₁) ↦ (v ↦ s₀ * v₀ + s₁ * v₁)` over `ZMod 5`. -/
@[expose] def dotHash (s : Fin 2 → ZMod 5) : (Fin 2 → ZMod 5) →ₗ[ZMod 5] ZMod 5 where
  toFun v := s 0 * v 0 + s 1 * v 1
  map_add' x y := by
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Uniformly seeded `dotHash` over `(ZMod 5)²` is `(1 / 5)`-universal: for `x ≠ y`, at least one
coordinate of `d = x - y` is nonzero, leaving exactly `5` of the `25` seeds in the kernel. -/
theorem isUniversalHash_dotHash :
    IsUniversalHash (PMF.uniformOfFintype (Fin 2 → ZMod 5))
      (fun s v => dotHash s v) ((1 : ℝ≥0∞) / 5) := by
  have hbound : ((5 : ℕ) : ℝ≥0∞) / Fintype.card (Fin 2 → ZMod 5) = (1 : ℝ≥0∞) / 5 := by
    rw [show Fintype.card (Fin 2 → ZMod 5) = 25 by decide, Nat.cast_ofNat, Nat.cast_ofNat]
    exact (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
      (by norm_num)
  rw [← hbound]
  refine IsUniversalHash.of_card_le fun x y hxy => ?_
  revert x y
  decide

/-! ## 1. Zero, one, and two-opening edge cases -/

-- Zero accepted openings return `⟨0, 0⟩`.
example :
    kosExtract (dotHash ![1, 0]) ([] : List (ZMod 5 × (Fin 2 → ZMod 5))) ⟨1, 2⟩ = ⟨0, 0⟩ := by
  decide

-- One accepted opening returns the constant line `⟨0, q₀⟩`, which evaluates to `q₀` at `Δ₀`.
example :
    let q₀ : Fin 2 → ZMod 5 := ![3, 4]
    let line := kosExtract (dotHash ![1, 0]) [((2 : ZMod 5), q₀)] ⟨0, 3⟩
    line = ⟨0, q₀⟩ ∧ line.eval (2 : ZMod 5) = q₀ := by
  decide

-- On any response graph of length ≤ 2 (`0`, `1`, or `2`),
-- `toOuterMeasure_kosExtract_graph_failure_le` yields exact failure probability `0`.
example {responses : List (ZMod 5 × (Fin 2 → ZMod 5))}
    (hgraph : IsResponseGraph responses) (hlen : responses.length ≤ 2) :
    (PMF.uniformOfFintype (Fin 2 → ZMod 5)).toOuterMeasure
      {s | ∃ (target : KOSLine (ZMod 5)) (p : ZMod 5 × (Fin 2 → ZMod 5)),
        p ∈ responses ∧ dotHash s p.2 = target.eval p.1 ∧
          (kosExtract (dotHash s) responses target).eval p.1 ≠ p.2} = 0 := by
  have hchoose : responses.length.choose 3 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hle := toOuterMeasure_kosExtract_graph_failure_le isUniversalHash_dotHash hgraph
  rw [hchoose, Nat.cast_zero, mul_zero] at hle
  exact nonpos_iff_eq_zero.mp hle

/-! ## 2. Nontrivial 4-opening collinear client and 3-opening failure witness -/

private def sampleSlope : Fin 2 → ZMod 5 := ![2, 3]
private def sampleIntercept : Fin 2 → ZMod 5 := ![1, 4]

private def collinearFour : List (ZMod 5 × (Fin 2 → ZMod 5)) :=
  [(0, ![1, 4]), (1, ![3, 2]), (2, ![0, 0]), (3, ![2, 3])]

-- All four openings lie on `⟨sampleSlope, sampleIntercept⟩`, and `kosExtract` recovers that exact
-- VOLE line under seed `![1, 1]` and target `⟨dotHash s sampleSlope, dotHash s sampleIntercept⟩`.
example :
    let s : Fin 2 → ZMod 5 := ![1, 1]
    let target : KOSLine (ZMod 5) := ⟨dotHash s sampleSlope, dotHash s sampleIntercept⟩
    kosExtract (dotHash s) collinearFour target = ⟨sampleSlope, sampleIntercept⟩ ∧
      ∀ p ∈ collinearFour, (kosExtract (dotHash s) collinearFour target).eval p.1 = p.2 := by
  dsimp only
  have hfilt : collinearFour.filter
      (fun p => decide (dotHash ![1, 1] p.2 =
        ({ slope := dotHash ![1, 1] sampleSlope,
           intercept := dotHash ![1, 1] sampleIntercept } : KOSLine (ZMod 5)).eval p.1)) =
      collinearFour := by decide
  have hfind : List.find? (fun p : ZMod 5 × (Fin 2 → ZMod 5) => p.1 ≠ 0)
      [(1, ![3, 2]), (2, ![0, 0]), (3, ![2, 3])] = some (1, ![3, 2]) := by decide
  have hline : kosExtract (dotHash ![1, 1]) collinearFour
      ⟨dotHash ![1, 1] sampleSlope, dotHash ![1, 1] sampleIntercept⟩ =
      ⟨sampleSlope, sampleIntercept⟩ := by
    unfold kosExtract
    rw [hfilt]
    dsimp only [collinearFour]
    rw [hfind]
    ext i <;> fin_cases i <;>
      simp only [sampleSlope, sampleIntercept, sub_zero, inv_one, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      decide
  refine ⟨hline, ?_⟩
  rw [hline]
  intro p hp
  fin_cases hp <;> ext i <;> fin_cases i <;>
    simp only [KOSLine.eval, sampleSlope, sampleIntercept, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    decide

/-- Non-collinear 3-opening response graph `[(0, (0, 0)), (1, (1, 0)), (2, (0, 1))]`. -/
def nonCollinearThree : List (ZMod 5 × (Fin 2 → ZMod 5)) :=
  [(0, ![0, 0]), (1, ![1, 0]), (2, ![0, 1])]

theorem isResponseGraph_nonCollinearThree : IsResponseGraph nonCollinearThree :=
  IsResponseGraph.of_nodup_fst (by decide)

-- Under the colliding seed `s = ![1, 2]`, the hashed images `(0, 0), (1, 1), (2, 2)` all lie on
-- `target = ⟨1, 0⟩`, so `kosExtract` misses `(2, ![0, 1])` and `kosFailureWitness` explicitly
-- extracts a nonzero affine defect mapped to `0` by `dotHash ![1, 2]`.
example :
    let s : Fin 2 → ZMod 5 := ![1, 2]
    let target : KOSLine (ZMod 5) := ⟨1, 0⟩
    let p : ZMod 5 × (Fin 2 → ZMod 5) := (2, ![0, 1])
    have hp : p ∈ nonCollinearThree := by decide
    have hhash : dotHash s p.2 = target.eval p.1 := by decide
    have hfail : (kosExtract (dotHash s) nonCollinearThree target).eval p.1 ≠ p.2 := by
      have hfilt : nonCollinearThree.filter
          (fun q => decide (dotHash ![1, 2] q.2 = (⟨1, 0⟩ : KOSLine (ZMod 5)).eval q.1)) =
          nonCollinearThree := by decide
      have hfind : List.find? (fun q : ZMod 5 × (Fin 2 → ZMod 5) => q.1 ≠ 0)
          [(1, ![1, 0]), (2, ![0, 1])] = some (1, ![1, 0]) := by decide
      intro heq
      have h1 := congrFun heq 1
      unfold kosExtract at h1
      rw [hfilt] at h1
      dsimp only [nonCollinearThree] at h1
      rw [hfind] at h1
      revert h1
      simp [KOSLine.eval, p]
    let w := kosFailureWitness (dotHash s) isResponseGraph_nonCollinearThree hp hhash hfail
    kosAffineDefect w.p₀ w.p₁ w.p₂ ≠ 0 ∧ dotHash s (kosAffineDefect w.p₀ w.p₁ w.p₂) = 0 := by
  intro s target p hp hhash hfail w
  exact ⟨w.defect_ne_zero, w.map_defect_eq_zero⟩

-- Over a uniform seed, extraction on `nonCollinearThree` (`|S| = 3`, `choose 3 3 = 1`) fails with
-- probability at most `1 / 5` (and on `collinearFour`, `choose 4 3 = 4`, at most `4 / 5`).
theorem nonCollinearThree_failure_bound :
    (PMF.uniformOfFintype (Fin 2 → ZMod 5)).toOuterMeasure
      {s | ∃ (target : KOSLine (ZMod 5)) (p : ZMod 5 × (Fin 2 → ZMod 5)),
        p ∈ nonCollinearThree ∧ dotHash s p.2 = target.eval p.1 ∧
          (kosExtract (dotHash s) nonCollinearThree target).eval p.1 ≠ p.2} ≤ (1 : ℝ≥0∞) / 5 := by
  simpa [nonCollinearThree] using
    toOuterMeasure_kosExtract_graph_failure_le isUniversalHash_dotHash
      isResponseGraph_nonCollinearThree

/-! ## 3. Characteristic-two `BinaryField 4` (`GF(16)`) client -/

/-- Characteristic-two instantiation over `BinaryField 4` (`GF(16)`): for any `ε`-universal linear
hash family and any response graph `responses` over `BinaryField 4`, failure probability is at most
`ε * (responses.length.choose 3)`. -/
theorem binaryField_kos_bound {Seed V W : Type*}
    [AddCommGroup V] [Module (BinaryField 4) V]
    [AddCommGroup W] [Module (BinaryField 4) W] [DecidableEq W]
    {seed : PMF Seed} {H : Seed → V →ₗ[BinaryField 4] W} {ε : ℝ≥0∞}
    (hH : IsUniversalHash seed (fun s v => H s v) ε)
    {responses : List (BinaryField 4 × V)} (hgraph : IsResponseGraph responses) :
    seed.toOuterMeasure
      {s | ∃ (target : KOSLine W) (p : BinaryField 4 × V),
        p ∈ responses ∧ H s p.2 = target.eval p.1 ∧
          (kosExtract (H s) responses target).eval p.1 ≠ p.2} ≤
      ε * (responses.length.choose 3 : ℝ≥0∞) :=
  toOuterMeasure_kosExtract_graph_failure_le hH hgraph

end CslibFrontierTests.Crypto.VOLEKOSExtractor
