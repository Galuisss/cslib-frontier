/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryField
public import CslibFrontier.Foundations.FieldTheory.Finite.HornerCoordinates
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

/-!
# Binary-label Horner evaluation with a supplied modulus

The coefficient of degree `i` is the width-bit block at offset `width * i` in a binary label.
Horner evaluation visits these blocks in descending order with a binary counter. The supplied
modulus and evaluation point remain available throughout; no coefficient table is constructed.
This component belongs to the native weight-generator development in #6747. Modulus selection,
seed access and the full generator are separate components.
-/

public section

namespace Turing.BinaryField

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib Cslib.BinaryField

/-- Runtime data for evaluating a polynomial packed into a binary label. The coefficient width
is the degree `modulus.length - 1`; the coefficient count is supplied in binary. -/
structure HornerInput where
  /-- Little-endian modulus coefficients. -/
  modulus : List Bool
  /-- Coordinate word of the evaluation point. -/
  point : List Bool
  /-- Coefficients packed least-significant block first. -/
  label : ℕ
  /-- Number of coefficient blocks, including any leading zero blocks. -/
  count : ℕ

/-- Framed modulus and point words followed by the binary label and coefficient count. -/
enc_structure encHornerInput : HornerInput where
  modulus : encCoefficients, point : encCoefficients, label : encNat, count : encNat

private theorem coefficient_eq (width value offset : ℕ) :
    BitString.lowBits width (value >>> offset) =
      List.ofFn (fun i : Fin width => (value.bits.drop offset).getD i false) := by
  rw [BitString.lowBits_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [Nat.testBit_shiftRight, Nat.testBit_eq_inth, List.getI_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_drop]
  rfl

private theorem coefficientSlice_inSpace :
    ComputableInSpace (fun p : HornerInput × ℕ =>
      p.1.label.bits.drop ((p.1.modulus.length - 1) * p.2))
      (encPair encHornerInput encNat) encCoefficients
      (fun p => (encPair encHornerInput encNat p).length) := by
  have hp := fst encHornerInput encNat
  have hm := encHornerInput_modulus_budget hp
  have hl := encHornerInput_label_budget hp
  have hw := budget_natPred (budget_length hm)
  have ho := budget_natMul hw (snd encHornerInput encNat)
  have hb := hl.of_enc_eq (encC := encBits)
    (g := fun p : HornerInput × ℕ => p.1.label.bits) (fun _ => rfl)
  have hc : ComputableInSpace (fun word : List Bool => word) encBits encCoefficients
      (fun word => (encBits word).length) :=
    of_inO ComputableInDegree.bitsToList.inO_one
  exact budget_comp_linear hc (budget_comp_linear bitsDrop (budget_prod hb ho))

private abbrev HornerState := HornerInput × ℕ × List Bool

private def encHornerState := encPair encHornerInput (encPair encNat encCoefficients)

private def hornerAdvance (s : HornerState) : HornerState :=
  let i := s.2.1 - 1
  (s.1, i, BitString.listXor (s.1.modulus.length - 1)
    [BitString.lowBits (s.1.modulus.length - 1)
      (s.1.label >>> ((s.1.modulus.length - 1) * i)),
      fieldMulMod s.1.modulus s.2.2 s.1.point])

private theorem horner_input (p : HornerInput) (n k : ℕ) (acc : List Bool) :
    (hornerAdvance^[k] (p, n, acc)).1 = p := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [Function.iterate_succ_apply', hornerAdvance] using ih

private theorem horner_counter (p : HornerInput) (n k : ℕ) (acc : List Bool) :
    (hornerAdvance^[k] (p, n, acc)).2.1 = n - k := by
  induction k with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply', hornerAdvance, ih, Nat.sub_sub]

private theorem horner_word_length (p : HornerInput) (k : ℕ) :
    (hornerAdvance^[k] (p, p.count, [])).2.2.length ≤ p.modulus.length - 1 := by
  cases k with
  | zero => simp
  | succ k => simp [Function.iterate_succ_apply', hornerAdvance, horner_input]

private theorem horner_state_length (p : HornerInput) (k : ℕ) :
    (encHornerState (hornerAdvance^[k] (p, p.count, []))).length ≤
      8 * ((encHornerInput p).length + 1) := by
  have hc := length_encNat_mono (Nat.sub_le p.count k)
  rw [← horner_counter p p.count k []] at hc
  have hw := horner_word_length p k
  have hm := encHornerInput_modulus_length_le p
  have hn := encHornerInput_count_length_le p
  simp only [encCoefficients, length_encList, encBool_apply, List.length_singleton,
    List.map_const', List.sum_replicate, smul_eq_mul] at hm
  simp only [encHornerState, length_encPair, horner_input, encCoefficients,
    length_encList, encBool_apply, List.length_singleton, List.map_const', List.sum_replicate,
    smul_eq_mul]
  omega

private theorem horner_agrees (p : HornerInput) :
    (hornerAdvance^[p.count] (p, p.count, [])).2.2 =
      hornerBits (p.modulus.length - 1) (fieldMulMod p.modulus) p.point
        (fun i : Fin p.count => BitString.lowBits (p.modulus.length - 1)
          (p.label >>> ((p.modulus.length - 1) * i))) := by
  let step := fun s : ℕ × List Bool =>
    (s.1 - 1, BitString.listXor (p.modulus.length - 1)
      [BitString.lowBits (p.modulus.length - 1)
        (p.label >>> ((p.modulus.length - 1) * (s.1 - 1))),
        fieldMulMod p.modulus s.2 p.point])
  have h (k : ℕ) (s : ℕ × List Bool) :
      hornerAdvance^[k] (p, s) = (p, step^[k] s) := by
    induction k with
    | zero => rfl
    | succ k ih => simp [Function.iterate_succ_apply', ih, hornerAdvance, step]
  rw [h]
  exact (hornerBits_eq_iterate (p.modulus.length - 1) (fieldMulMod p.modulus) p.point
    (fun i => BitString.lowBits (p.modulus.length - 1)
      (p.label >>> ((p.modulus.length - 1) * i))) p.count).symm

end Turing.BinaryField
