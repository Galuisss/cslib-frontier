/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.ClassicalDensity
public import CslibFrontier.Computability.Circuit.Quantum.Uniform
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec

/-!
# Reversible equality of two recorded bits

`GateCode.compareBits` replaces the guess wire by its equality with a distinct hidden-bit wire,
using one CNOT followed by one NOT. Every other wire is retained. Its readout theorem holds for
mixed states with an arbitrary reference, so a reduction can compare a guess with a private
challenge bit after the adversary has finished.

The retained native generator takes both wire positions in unary. Its certificate includes the
complete generated transition table, all-input output correctness, and separate time/workspace
maps; the installed program is charged by `NativeCompiler.staticBits` exactly once.

## Main definitions

* `Cslib.Quantum.GateCode.compareBits`: the two-gate equality suffix.
* `Cslib.Quantum.GateCode.compareBitsCompiler`: retained generation from unary wire positions.

## Main results

* `Cslib.Quantum.GateCode.readBit_classicalRun_compareBits`: the target becomes the equality bit.
* `Cslib.Quantum.measureDensity_compareBits`: final readout is the original equality event.

This is an original construction for hidden-bit reductions, not a security theorem.
-/

public section

namespace Cslib.Quantum

open Matrix Turing.MultiTapeTM
open scoped Kronecker

namespace GateCode

/-- Compare two distinct wires in place: CNOT from the hidden bit to the guess, then NOT the
guess. The hidden bit and every other non-target wire are unchanged. -/
@[expose] def compareBits (hidden guess : ℕ) : List GateCode :=
  [(false, guess, [hidden]), (false, guess, [])]

/-- The comparison consists of two well-formed classical gates. -/
theorem isClassical_compareBits {hidden guess width : ℕ} (hne : hidden ≠ guess)
    (hh : hidden < width) (hg : guess < width) : IsClassical width (compareBits hidden guess) := by
  simp [IsClassical, compareBits, WellFormed, Ne.symm hne, hh, hg]

/-- The guess wire after comparison equals the equality of the original recorded bits. -/
theorem readBit_classicalRun_compareBits {hidden guess width : ℕ} (hg : guess < width)
    (x : Fin width → Bool) :
    readBit (classicalRun (compareBits hidden guess) x) guess =
      (readBit x guess == readBit x hidden) := by
  simp only [compareBits, classicalRun_cons, classicalRun_nil, readBit_classicalStep,
    List.all_cons, List.all_nil, Bool.and_true, decide_true, Bool.true_and, hg,
    and_self, Bool.xor_true]
  cases readBit x guess <;> cases readBit x hidden <;> rfl

/-- All wires other than the comparison's target keep their original basis value. -/
theorem readBit_classicalRun_compareBits_of_ne {hidden guess wire width : ℕ}
    (hne : guess ≠ wire) (x : Fin width → Bool) :
    readBit (classicalRun (compareBits hidden guess) x) wire = readBit x wire := by
  exact readBit_classicalRun_of_forall_ne (by simp [compareBits, hne]) x

/-- Generate the two comparison gates with an actual retained machine. Input is the standard
pair of unary hidden-bit and guess-wire positions; output uses the standard framed gate list. -/
@[expose] def compareBitsCompiler :
    Internal.NativeCompiler (fun input : ℕ × ℕ => compareBits input.1 input.2)
      (encPair encUnary encUnary) (encList encGateCode) := by
  let inputEncoding := encPair encUnary encUnary
  let hidden := Internal.NativeCompiler.first encUnary encUnary
  let guess := Internal.NativeCompiler.second encUnary encUnary
  let flag := Internal.NativeCompiler.const inputEncoding encBool false
  let controls : Internal.NativeCompiler (fun input : ℕ × ℕ => [input.1])
      inputEncoding (encList encUnary) :=
    ((Internal.NativeCompiler.framedValue encUnary).comp hidden).ofOutputEq fun _ => by
      simp [encFramed_apply, encList_cons]
  let noControls := Internal.NativeCompiler.const inputEncoding (encList encUnary) []
  let cnot := flag.pair (guess.pair controls)
  let negation := flag.pair (guess.pair noControls)
  exact (((Internal.NativeCompiler.encodeFrame encGateCode).comp cnot).append
    ((Internal.NativeCompiler.encodeFrame encGateCode).comp negation)).ofOutputEq fun _ => by
      simp [compareBits, encList_cons, encBits_apply]

/-- Exact clock of the retained generator, including projections, framing and composition. -/
theorem time_compareBitsCompiler (input : ℕ × ℕ) :
    compareBitsCompiler.time input = 48 * input.1 + 60 * input.2 + 248 := by
  simp [compareBitsCompiler, Internal.NativeCompiler.first, Internal.NativeCompiler.second,
    Internal.NativeCompiler.ofTransducer, Internal.NativeCompiler.framedValue,
    Internal.NativeCompiler.ofOutputEq, Internal.NativeCompiler.const,
    Internal.NativeCompiler.pair, Internal.NativeCompiler.comp, Internal.NativeCompiler.append,
    Internal.NativeCompiler.encodeFrame, encPair_apply, encBool_apply, encUnary_apply,
    encList_cons, length_frame]
  omega

/-- Exact independent workspace bound recorded by the retained generator. -/
theorem workspace_compareBitsCompiler (input : ℕ × ℕ) :
    compareBitsCompiler.workspace input = 15 * input.1 + 30 * input.2 + 243 := by
  simp [compareBitsCompiler, Internal.NativeCompiler.first, Internal.NativeCompiler.second,
    Internal.NativeCompiler.ofTransducer, Internal.NativeCompiler.framedValue,
    Internal.NativeCompiler.ofOutputEq, Internal.NativeCompiler.const,
    Internal.NativeCompiler.pair, Internal.NativeCompiler.comp, Internal.NativeCompiler.append,
    Internal.NativeCompiler.encodeFrame, encPair_apply, encBool_apply, encUnary_apply,
    encList_cons, length_frame]
  omega

end GateCode

/-- Measuring the target after the comparison gives exactly the original equality event,
including for mixed states entangled with an arbitrary inaccessible reference. -/
theorem measureDensity_compareBits {hidden guess width : ℕ} (hne : hidden ≠ guess)
    (hh : hidden < width) (hg : guess < width)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Matrix ((Fin width → Bool) × κ) ((Fin width → Bool) × κ) ℂ)
    (hρ : IsDensityMatrix ρ) :
    (POVM.basis.measureDensity
      (densityConj
        ((Circuit.matrix (Circuit.ofCodes width (GateCode.compareBits hidden guess)) :
          Matrix (Fin width → Bool) (Fin width → Bool) ℂ) ⊗ₖ
          (1 : Matrix κ κ ℂ)) ρ)
      (hρ.densityConj_kronecker
        (V := (Circuit.matrix (Circuit.ofCodes width (GateCode.compareBits hidden guess)) :
          Matrix (Fin width → Bool) (Fin width → Bool) ℂ))
        (by
          exact UnitaryGroup.star_mul_self
            (Circuit.matrix (Circuit.ofCodes width (GateCode.compareBits hidden guess)))))).map
        (fun p => readBit p.1 guess) =
      (POVM.basis.measureDensity ρ hρ).map
        (fun p => readBit p.1 guess == readBit p.1 hidden) := by
  rw [Circuit.measureDensity_basis_ofCodes (GateCode.isClassical_compareBits hne hh hg) ρ hρ,
    PMF.map_comp]
  congr 1
  funext p
  exact GateCode.readBit_classicalRun_compareBits hg p.1

end Cslib.Quantum
