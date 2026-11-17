/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3.Order
public import CslibFrontier.Computability.PolyTime.Graph.RotationSystem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured

/-!
# Native ternary scope alignment and certificate conjugation

The programs retain binary variables, successor entries and arithmetic indices. Only actual
list positions are generated in unary and converted to binary before lookup. In particular,
a malformed successor entry of arbitrary binary magnitude never funds an iteration.

These certificates cover every raw scope and table. Acceptance of the reordered output is
a separate geometric and positional correctness result for the exact ternary base source.
-/

public section

namespace Cslib.Complexity.CSP.OneHot3

open Cslib.Logic.PL Graph Turing.MultiTapeTM

/-- Framed binary CSP followed by its supplied binary successor table. -/
abbrev encOrderInput := encPair (encCSP encUnit encNat) encRotationCertificate

/-- A binary rotation table followed by a binary index, with no unary clock conversion. -/
abbrev encTableIndex := encPair encRotationCertificate encNat

private theorem swapTail3_tidy :
    ComputableTidilyInPolyTime swapTail3 (encList encNat) (encList encNat) := by
  have he (xs : List ℕ) : swapTail3 xs =
      if 3 ≤ xs.length then xs.getD 0 0 :: xs.getD 2 0 :: xs.getD 1 0 :: xs.drop 3 else xs := by
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs =>
        cases xs with
        | nil => rfl
        | cons c tail => simp only [swapTail3, List.length_cons, List.getD_cons_zero,
            List.getD_cons_succ, List.drop_succ_cons, List.drop_zero,
            show 3 ≤ tail.length + 1 + 1 + 1 by omega, ↓reduceIte]
  simp_rw [he]
  fun_prop

private theorem forward_tidy :
    ComputableTidilyInPolyTime (fun p : RotationCertificate × ℕ => forward p.1 p.2)
      encTableIndex encBool := by
  have hs := RotationCertificate.computableInPolyTime_successor.tidy
  have hidx : ComputableTidilyInPolyTime (fun p : RotationCertificate × ℕ => 6 * p.2 + 1)
      encTableIndex encNat := by
    unfold encTableIndex
    fun_prop
  have hlookup := ComputableTidilyInPolyTime.listGetD_binary 0
    (hs.comp (ComputableTidilyInPolyTime.fst _ _)) hidx
  unfold forward encTableIndex at *
  fun_prop

/-- The exact conditional scope exchange is native polynomial time on all raw input lists. -/
theorem computableInPolyTime_orderedConstraints :
    ComputableInPolyTime (fun p : CSP Unit ℕ × RotationCertificate =>
      orderedConstraints p.1 p.2) encOrderInput (encCSP encUnit encNat) := by
  apply ComputableInPolyTime.of_tidy
  have hz : ComputableTidilyInPolyTime (fun p : CSP Unit ℕ × RotationCertificate => p.1.zipIdx)
      encOrderInput (encList (encPair (encConstraint encUnit encNat) encUnary)) :=
    (ComputableTidilyInPolyTime.zipIdx _).comp (ComputableTidilyInPolyTime.fst _ _)
  simp only [orderedConstraints, List.mapIdx_eq_zipIdx_map]
  apply ComputableTidilyInPolyTime.mapWithInput hz
  have hi := ComputableTidilyInPolyTime.unary_to_binary.comp
    (g := fun p : (CSP Unit ℕ × RotationCertificate) × (Constraint Unit ℕ × ℕ) => p.2.2)
    (by unfold encOrderInput; fun_prop)
  have hf := forward_tidy.comp
    ((by unfold encOrderInput; fun_prop).prod hi)
  have hswap := swapTail3_tidy.comp
    (g := fun p : (CSP Unit ℕ × RotationCertificate) × (Constraint Unit ℕ × ℕ) => p.2.1.scope)
    (by unfold encOrderInput; fun_prop)
  exact (encConstraint_mk_polyTime
    (by unfold encOrderInput; fun_prop)
    (ComputableInPolyTime.of_tidy (by fun_prop))).tidy

private theorem dartReindex_tidy :
    ComputableTidilyInPolyTime (fun p : RotationCertificate × ℕ => dartReindex p.1 p.2)
      encTableIndex encNat := by
  have hrow : ComputableTidilyInPolyTime (fun p : RotationCertificate × ℕ => p.2 / 6)
      encTableIndex encNat := by unfold encTableIndex; fun_prop
  have hf := forward_tidy.comp ((ComputableTidilyInPolyTime.fst _ _).prod hrow)
  unfold dartReindex encTableIndex at *
  fun_prop

/-- Conjugating the supplied binary table executes a polynomial-time program on all raw
inputs, even when lookups or table entries have enormous binary indices. -/
theorem computableInPolyTime_orderedCertificate :
    ComputableInPolyTime (fun p : CSP Unit ℕ × RotationCertificate =>
      orderedCertificate p.1 p.2) encOrderInput encRotationCertificate := by
  have hg := (computableInPolyTime_incidenceGraph encUnit encNat).tidy.comp
    (ComputableTidilyInPolyTime.fst (encCSP encUnit encNat) encRotationCertificate)
  have hword : ComputableTidilyInPolyTime
      (fun p : CSP Unit ℕ × RotationCertificate =>
        (List.range (2 * (incidenceGraph p.1).edges.length)).map fun a =>
          dartReindex p.2 (p.2.successor.getD (dartReindex p.2 a) 0))
      encOrderInput (encList encNat) := by
    apply ComputableTidilyInPolyTime.mapWithInput (encA := encUnary)
      (by unfold encOrderInput encGraph; fun_prop)
    have ha := ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.snd encOrderInput encUnary)
    have hc : ComputableTidilyInPolyTime
        (fun p : (CSP Unit ℕ × RotationCertificate) × ℕ => p.1.2)
        (encPair encOrderInput encUnary) encRotationCertificate := by
      unfold encOrderInput
      fun_prop
    have hi := dartReindex_tidy.comp (hc.prod ha)
    have hs := RotationCertificate.computableInPolyTime_successor.tidy.comp hc
    have hn := ComputableTidilyInPolyTime.listGetD_binary 0 hs hi
    exact dartReindex_tidy.comp (hc.prod hn)
  exact encRotationCertificate_mk_deg.computableInPolyTime.comp hword.computableInPolyTime

end Cslib.Complexity.CSP.OneHot3
