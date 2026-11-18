/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SigningROM
public import CslibFrontier.Crypto.Computational.SIS.Hermite
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Probability.Collision
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Guessing an ML-DSA signing commitment

An original way to bound the commitment-guessing term for the ideal-mask signing experiment.
Choose the lower or upper half of each mask coefficient interval independently, then
sample two masks independently in that common subbox. Equal commitments mean that the matrix
images of the masks differ only in their low bits. Unless the masks coincide, this gives a short
integer solution for the ordinary Hermite-form Module-SIS challenge. The squared maximum
point probability of the original mask law is bounded by the average collision probability
conditional on the common subbox, also after averaging over public matrices.
-/

public section

namespace Cslib.Crypto.MLDSA

open Cslib.Probability Finset
open Cslib.OracleComp Cslib.Crypto.Protocols.ROMSignature
open scoped BigOperators ENNReal

variable (P : Params)

private abbrev Mask := Fin P.ℓ → Fin P.n → ZMod P.q
private abbrev Mat := Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q)

private def maskDifference (A : Mat P) (y z : Mask P) : Fin (P.k + P.ℓ) → Fin P.n → ℤ :=
  Fin.append
    (fun i j => lowBits P.q P.γ₂ (moduleSISMap A z i j) - lowBits P.q P.γ₂ (moduleSISMap A y i j))
    (fun i j => (y i j).valMinAbs - (z i j).valMinAbs)

/-- Sample the half-interval of each coefficient once, then draw two independent masks
in that common subbox. Return the differences of their images' low bits and their centered
coefficients in the two blocks of the MSIS witness. -/
noncomputable def maskCollisionSolver (hγ : 0 < P.γ₁)
    (A : Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q)) :
    ProbComp (Fin (P.k + P.ℓ) → Fin P.n → ℤ) := do
  let b ← ProbComp.uniform (MaskSigns P)
  let y ← sampleHalfMask P hγ b
  let z ← sampleHalfMask P hγ b
  return maskDifference P A y z

private theorem isSolution_maskDifference [NeZero P.q] (h₂ : 0 < P.γ₂) {hγ : 0 < P.γ₁}
    (hq : 2 * P.γ₁ < P.q) (A : Mat P) {b : MaskSigns P} {y z : Mask P}
    (hy : y ∈ (halfMaskLaw P hγ b).support) (hz : z ∈ (halfMaskLaw P hγ b).support) (hne : y ≠ z)
    (hw : highBitsVec P (moduleSISMap A y) = highBitsVec P (moduleSISMap A z)) :
    ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix A) (max (P.γ₁ - 1) (2 * P.γ₂))
      (maskDifference P A y z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    apply hne
    funext i j
    apply ZMod.injective_valMinAbs
    have h := congrFun (congrFun he (Fin.natAdd P.k i)) j
    simpa [maskDifference, sub_eq_zero] using h
  · refine Fin.addCases (fun i j => ?_) (fun i j => ?_)
    · simp only [maskDifference, Fin.append_left]
      have h := abs_sub (lowBits P.q P.γ₂ (moduleSISMap A z i j))
        (lowBits P.q P.γ₂ (moduleSISMap A y i j))
      have h₁ := abs_lowBits_le h₂ (moduleSISMap A y i j)
      have h₂' := abs_lowBits_le h₂ (moduleSISMap A z i j)
      have := Nat.le_max_right (P.γ₁ - 1) (2 * P.γ₂)
      lia
    · simp only [maskDifference, Fin.append_right]
      exact (abs_sub_le_of_mem_halfMaskLaw P hq hy hz i j).trans
        (by exact_mod_cast Nat.le_max_left (P.γ₁ - 1) (2 * P.γ₂))
  · let u (i : Fin P.k) (j : Fin P.n) : ZMod P.q :=
      (lowBits P.q P.γ₂ (moduleSISMap A z i j) - lowBits P.q P.γ₂ (moduleSISMap A y i j) : ℤ)
    have hcast : (fun i j => ((maskDifference P A y z i j : ℤ) : ZMod P.q)) =
        Fin.append u (y - z) := by
      funext i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> funext j <;> simp [maskDifference, u]
    have hlin : moduleSISMap A (y - z) = moduleSISMap A y - moduleSISMap A z :=
      eq_sub_iff_add_eq.mpr (by rw [← moduleSISMap_add, sub_add_cancel])
    rw [hcast, ModuleSIS.moduleSISMap_hermiteMatrix, hlin]
    funext i j
    have hw' := congrFun (congrFun hw i) j
    change highBits _ _ _ = highBits _ _ _ at hw'
    have hs := intCast_highBits_mul_add_lowBits (γ₂ := P.γ₂) (moduleSISMap A y i j)
    rw [hw'] at hs
    have ht := intCast_highBits_mul_add_lowBits (γ₂ := P.γ₂) (moduleSISMap A z i j)
    push_cast at hs ht
    simp only [u, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Int.cast_sub]
    linear_combination ht - hs

private theorem guess_sq_le_solver_add [NeZero P.q] (hγ : 0 < P.γ₁) (h₂ : 0 < P.γ₂)
    (hq : 2 * P.γ₁ < P.q) (A : Mat P) :
    (commitmentGuessProbability P hγ A).toReal ^ 2 ≤
      (((maskCollisionSolver P hγ A).eval.map fun x =>
        decide (ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix A)
          (max (P.γ₁ - 1) (2 * P.γ₂)) x)) true).toReal +
      (↑(P.γ₁ ^ (P.ℓ * P.n)) : ℝ)⁻¹ := by
  classical
  let f (y : Mask P) := highBitsVec P (moduleSISMap A y)
  let pairs (b : MaskSigns P) := (halfMaskLaw P hγ b).bind fun y =>
    (halfMaskLaw P hγ b).map (y, ·)
  let collisions (yz : Mask P × Mask P) := decide (f yz.1 = f yz.2)
  let equal (yz : Mask P × Mask P) := decide (yz.1 = yz.2)
  let solved (yz : Mask P × Mask P) := decide (ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix A)
    (max (P.γ₁ - 1) (2 * P.γ₂)) (maskDifference P A yz.1 yz.2))
  let succ (b : MaskSigns P) := (((pairs b).map solved) true).toReal
  let diag := (↑(P.γ₁ ^ (P.ℓ * P.n)) : ℝ)⁻¹
  have hcond (b : MaskSigns P) :
      Probability.PMF.collisionProbability ((halfMaskLaw P hγ b).map f) ≤ succ b + diag := by
    let d := halfMaskLaw P hγ b
    have hu : ((pairs b).map collisions) true ≤ ((pairs b).map solved) true +
        ((pairs b).map equal) true := by
      apply Probability.PMF.map_true_le_add
      rintro ⟨y, z⟩ hyz h
      obtain ⟨a, ha, hz⟩ := (PMF.mem_support_bind_iff ..).1 hyz
      obtain ⟨t, ht, eq⟩ := (PMF.mem_support_map_iff ..).1 hz
      cases eq
      simp only [collisions, solved, equal, decide_eq_true_eq] at h ⊢
      by_cases he : y = z
      · exact Or.inr he
      · exact Or.inl (isSolution_maskDifference P h₂ hq A ha ht he h)
    have hur := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨((pairs b).map solved).apply_ne_top _, ((pairs b).map equal).apply_ne_top _⟩) hu
    rw [ENNReal.toReal_add (((pairs b).map solved).apply_ne_top _)
      (((pairs b).map equal).apply_ne_top _)] at hur
    have hc : Probability.PMF.collisionProbability (d.map f) =
        (((pairs b).map collisions) true).toReal := by
      simp [Probability.PMF.collisionProbability_eq_probability, pairs, collisions, d,
        PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
    have he : Probability.PMF.collisionProbability d = (((pairs b).map equal) true).toReal := by
      simp [Probability.PMF.collisionProbability_eq_probability, pairs, equal, d, PMF.map_bind,
        PMF.map_comp, Function.comp_def]
    have hsize : (↑(P.γ₁ ^ (P.ℓ * P.n)) : ℝ≥0∞) ≠ 0 := by positivity
    have heq := Probability.PMF.collisionProbability_le_of_mass_le d fun y =>
      ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr hsize) (halfMaskLaw_apply_le P hγ hq b y)
    rw [he, ENNReal.toReal_inv, ENNReal.toReal_natCast] at heq
    exact hc.le.trans (hur.trans (add_le_add le_rfl heq))
  have avg (w) : (((signingMaskLaw P hγ).map f) w).toReal =
      𝔼 b : MaskSigns P, (((halfMaskLaw P hγ b).map f) w).toReal := by
    rw [← uniformSigns_bind_halfMaskLaw P hγ hq, PMF.map_bind,
      Probability.PMF.toReal_uniformOfFintype_bind_apply]
  have hmean : 0 ≤ (𝔼 b, succ b) + diag :=
    add_nonneg (expect_nonneg fun _ _ => ENNReal.toReal_nonneg) (by positivity)
  have hatom : commitmentGuessProbability P hγ A ≤
      ENNReal.ofReal (Real.sqrt ((𝔼 b, succ b) + diag)) := by
    unfold commitmentGuessProbability
    refine iSup_le fun w => (ENNReal.le_ofReal_iff_toReal_le
      (((signingMaskLaw P hγ).map f).apply_ne_top w) (Real.sqrt_nonneg _)).2 ?_
    apply Real.le_sqrt_of_sq_le
    rw [avg]
    refine (sq_expect_le_expect_sq _ _).trans ((expect_le_expect fun b _ =>
      (Probability.PMF.toReal_sq_le_collisionProbability _ w).trans (hcond b)).trans_eq ?_)
    rw [expect_add_distrib, Fintype.expect_const]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hatom
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hreal
  have hsq := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 2
  rw [Real.sq_sqrt hmean] at hsq
  refine hsq.trans_eq (congrArg (· + diag) ?_)
  simp only [maskCollisionSolver, ProbComp.eval_bind, ProbComp.eval_uniform, PMF.map_bind,
    Probability.PMF.toReal_uniformOfFintype_bind_apply]
  simp [succ, pairs, solved, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Under a uniform matrix, the expected largest signing-commitment probability is at most
the square root of the two-mask solver's standard Hermite MSIS success plus the reciprocal
subbox size. This discharges the matrix-dependent guessing term in the ideal-mask ROM
simulation using a specified solver at the displayed infinity-norm radius. -/
theorem mean_commitmentGuessProbability_le_hermite [NeZero P.q] (hγ : 0 < P.γ₁)
    (h₂ : 0 < P.γ₂) (hq : 2 * P.γ₁ < P.q) :
    (𝔼 A, (commitmentGuessProbability P hγ A).toReal) ≤
      Real.sqrt (Game.succProbability
        (ModuleSIS.hermiteExperiment (max (P.γ₁ - 1) (2 * P.γ₂))
          (maskCollisionSolver P hγ)).eval + (↑(P.γ₁ ^ (P.ℓ * P.n)) : ℝ)⁻¹) := by
  classical
  apply Real.le_sqrt_of_sq_le
  have hcs := sq_expect_le_expect_sq univ (fun A => (commitmentGuessProbability P hγ A).toReal)
  refine hcs.trans ((expect_le_expect fun A _ => guess_sq_le_solver_add P hγ h₂ hq A).trans_eq ?_)
  rw [expect_add_distrib, Fintype.expect_const]
  congr 1
  change _ = (((ModuleSIS.hermiteExperiment _ (maskCollisionSolver P hγ)).eval) true).toReal
  simp only [ModuleSIS.hermiteExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, Probability.PMF.toReal_uniformOfFintype_bind_apply]
  rfl

/-- The adaptive signing simulation averaged over a uniform matrix, with the guessing loss
discharged by the explicit two-mask Module-SIS solver. The short secrets may be fixed before
drawing the matrix. The forger may choose its entire subsequent program using the public key. -/
theorem closeTo_simulateSigning_uniformMatrix [NeZero P.q] (hP : P.Valid)
    (hq : 2 * P.γ₁ < P.q) (hβ : P.β < P.γ₁) (d ω K : ℕ) {Digest α : Type}
    (dist : PMF Digest) (expand : Digest → Fin P.n → ZMod P.q)
    (hc : ∀ c, InBall P.τ (expand c))
    (s₁ : Fin P.ℓ → Fin P.n → ZMod P.q) (s₂ : Fin P.k → Fin P.n → ZMod P.q)
    (hs₁ : ∀ i j, |(s₁ i j).valMinAbs| ≤ P.η) (hs₂ : ∀ i j, |(s₂ i j).valMinAbs| ≤ P.η)
    (forger : PublicKey P → OracleComp (SigningROMSpec P Digest) α) {S H : ℕ}
    (hS : ∀ pk, IsCostBounded signingCost (forger pk) S)
    (hH : ∀ pk, IsCostBounded hashCost (forger pk) H) :
    CloseTo ((PMF.uniformOfFintype _).bind fun A =>
      let sk : SecretKey P := ⟨A, s₁, s₂⟩
      (runBoundedSigningROM P false d ω K (by lia) dist expand sk (forger sk.publicKey)).map
        Prod.fst)
      ((PMF.uniformOfFintype _).bind fun A =>
        let pk := (SecretKey.mk A s₁ s₂ : SecretKey P).publicKey
        (runAcceptedSigningROM P K dist
          (fun c => simulateFreshSigningAttempt P d ω hβ pk (expand c)) (forger pk)).map Prod.fst)
      ((2 * (S * K) * H + (S * K).choose 2 : ℕ) * ENNReal.ofReal
        (Real.sqrt (Game.succProbability
          (ModuleSIS.hermiteExperiment (max (P.γ₁ - 1) (2 * P.γ₂))
            (maskCollisionSolver P (by lia))).eval + (↑(P.γ₁ ^ (P.ℓ * P.n)) : ℝ)⁻¹))) := by
  classical
  let hγ : 0 < P.γ₁ := by lia
  let count := 2 * (S * K) * H + (S * K).choose 2
  let err (A : Mat P) := (count : ℝ≥0∞) * commitmentGuessProbability P hγ A
  refine (CloseTo.bind_right_tsum (PMF.uniformOfFintype (Mat P)) (err := err) (fun A _ =>
    closeTo_runBoundedSigningROM_simulate P hP hq hβ d ω K dist expand ⟨A, s₁, s₂⟩
      hs₁ hs₂ hc (hS _) (hH _))).mono ?_
  have hmean := mean_commitmentGuessProbability_le_hermite P hγ hP.γ₂_pos hq
  have finite (A : Mat P) : commitmentGuessProbability P hγ A ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    unfold commitmentGuessProbability
    exact iSup_le fun _ => PMF.coe_le_one _ _
  rw [tsum_fintype]
  simp only [err, PMF.uniformOfFintype_apply, mul_left_comm _ (count : ℝ≥0∞), ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply (ENNReal.le_ofReal_iff_toReal_le ?_ (Real.sqrt_nonneg _)).2
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_sum (fun a _ => finite a),
      ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.expect_eq_sum_div_card,
      div_eq_inv_mul] using hmean
  · exact ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.mpr fun a _ => finite a)

end Cslib.Crypto.MLDSA
