/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import CslibFrontier.Computability.Complexity.RealAlgebraic.MultivariateCoefficients
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueSign

/-!
# Indexed coefficients of controlled integer families

A polynomial-time list of binary exponents specifies one coefficient. The
uniform grid algorithm supplies its residues at one higher function level.
The original logarithmic mass bound also bounds that integer coefficient,
so Frontier's residue-sign theorem applies without expanding the polynomial.

Adapted from [lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/ControlledCoefficients.lean).

## Main definitions

* `Cslib.Complexity.RealAlgebraic.Controlled.coefficientAccess`: uniform residue access to
  coefficients addressed by binary exponents.

## Main results

* `Cslib.Complexity.RealAlgebraic.Controlled.coefficientAccess_mem`: coefficient residues in
  the next function level.
* `Cslib.Complexity.RealAlgebraic.Controlled.coefficientSign_mem`: signs from those residues.

## References

* [OpenAI, *Existential--universal real sentences in the counting hierarchy*]
  [OpenAI2026CountingHierarchy], Definition 2.3 (p. 6) and Lemma 2.4 (p. 7).
  This module supplies the scalar, all-variable coefficient-extraction ingredient;
  partial extraction retaining a polynomial in parameters is tracked by
  [#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM MvPolynomial

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}

/-- A short cutoff that covers evaluator correctness and Fourier non-aliasing. -/
@[expose] def coefficientCutoff (C : Controlled P enc a) (β : α → List ℕ) (w : α) : ℕ :=
  max (C.cutoff w) (max (C.degreeBound w) (β w).sum) + 1

theorem coefficientCutoff_polyTime (C : Controlled P enc a) {β : α → List ℕ}
    (hβ : ComputableInPolyTime β enc (encList encNat)) :
    ComputableInPolyTime (C.coefficientCutoff β) enc encNat :=
  ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_max' C.cutoff_computable
      (ComputableInPolyTime.binary_max' C.degree_computable
        (ComputableInPolyTime.binary_sum.comp hβ))) (.const 1)

/-- The coefficient is a mathematical integer; its actual realizing function
uses only the controlled evaluator and short grid addresses. -/
@[expose] noncomputable def coefficientAccess (C : Controlled P enc a)
    (e : (w : α) → Fin (n w) →₀ ℕ) (β : α → List ℕ)
    (hβ : ∀ w (i : Fin (n w)), (β w)[i.val]?.getD 0 = e w i) :
    IntegerResidueAccess (fun w => (P w).coeff (e w)) where
  magnitudeExponent := C.massExponent
  admissible := fun w p => p.Prime ∧ C.coefficientCutoff β w < p
  modulus_pos := fun _ _ hp => hp.1.pos
  residue := fun (w, modulus) => multivariateCoefficientResidue modulus (n w) (β w)
    (fun coordinates => C.evaluate (w, modulus, coordinates))
  magnitude_le w := (MvPolynomial.natAbs_coeff_le_coeffNorm1 _ _).trans (C.mass_le w)
  residue_eq w p hp := by
    dsimp only
    let : Fact p.Prime := ⟨hp.1⟩
    have hcut := hp.2
    change max (C.cutoff w) (max (C.degreeBound w) (β w).sum) + 1 < p at hcut
    have hold : C.cutoff w < p := by omega
    let Q := (P w).map (Int.castRingHom (ZMod p))
    have hmap : Q.totalDegree ≤ (P w).totalDegree :=
      Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    have hQ : Q.totalDegree < p - 1 := by
      have := C.degree_le w
      omega
    have he (i : Fin (n w)) : e w i < p - 1 := by
      have hh : (β w)[i.val]?.getD 0 ≤ (β w).sum := by
        cases hget : (β w)[i.val]? with
        | none => simp only [Option.getD_none, Nat.zero_le]
        | some value =>
          simpa only [hget, Option.getD_some] using
            List.le_sum_of_mem (List.mem_of_getElem? hget)
      rw [hβ w i] at hh
      omega
    have hvalue (r : ℕ) (_hr : r < p ^ n w) :
        (C.evaluate (w, p, gridPoint p (n w) r) : ZMod p) =
          MvPolynomial.eval
            (fun i : Fin (n w) => (((gridPoint p (n w) r)[i.val]?.getD 0 : ℕ) : ZMod p)) Q := by
      rw [C.evaluate_eq w p _ hp.1 hold]
      simp only [evaluation, ZMod.natCast_zmod_val, Q, MvPolynomial.eval_map]
    have hres := multivariateCoefficientResidue_eq_val Q (e w) (β w)
      (fun z => C.evaluate (w, p, z)) hQ he (hβ w) hvalue
    rw [hres]
    simp only [Q, MvPolynomial.coeff_map, Int.coe_castRingHom]
    simpa only [Int.toNat_natCast] using
      congrArg Int.toNat (ZMod.val_intCast (n := p) ((P w).coeff (e w)))

/-- All indexed coefficient residues use a single oracle at one higher level. -/
theorem coefficientAccess_mem (C : Controlled P enc a) (E : Decoder enc)
    (e : (w : α) → Fin (n w) →₀ ℕ) {β : α → List ℕ}
    (hβ : ComputableInPolyTime β enc (encList encNat))
    (he : ∀ w (i : Fin (n w)), (β w)[i.val]?.getD 0 = e w i) :
    (C.coefficientAccess e β he).InCountingFunction (a + 1) enc := by
  have hvalue := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) (encList encNat)) C.evaluate_mem
    (g := fun ((w, modulus), coordinates) => (w, modulus, coordinates)) (by fun_prop)
  exact ⟨C.mass_computable,
    multivariateCoefficientResidue_mem (Decoder.pair E Decoder.nat)
      (ComputableInPolyTime.snd enc encNat)
      (C.arity_computable.comp (ComputableInPolyTime.fst enc encNat))
      (hβ.comp (ComputableInPolyTime.fst enc encNat)) hvalue⟩

/-- Signs of arbitrary addressed coefficients have a fixed CH bound. -/
theorem coefficientSign_mem (C : Controlled P enc a) (E : Decoder enc)
    (e : (w : α) → Fin (n w) →₀ ℕ) {β : α → List ℕ}
    (hβ : ComputableInPolyTime β enc (encList encNat))
    (he : ∀ w (i : Fin (n w)), (β w)[i.val]?.getD 0 = e w i) :
    (fun w => ((P w).coeff (e w)).sign) ∈
      CountingFunction (max (a + 1) 5 + 3) enc encIntBin := by
  apply IntegerResidueAccess.sign_mem_CountingFunction E (C.coefficientAccess e β he)
    (C.coefficientAccess_mem E e hβ he) (C.coefficientCutoff_polyTime hβ)
  intro w p hp
  exact ⟨Cslib.PrimeWindowSign.prime _ _ ⟨p, hp⟩,
    (Nat.mem_primesLE_sdiff_primesLE_iff.mp hp).2.1⟩

end Cslib.Complexity.RealAlgebraic.Controlled
