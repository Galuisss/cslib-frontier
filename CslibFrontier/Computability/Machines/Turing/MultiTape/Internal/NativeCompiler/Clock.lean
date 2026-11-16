/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Replicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamResourceBounds

/-!
# Retained unary polynomial clocks

This module constructs the unary clock `c * (n + 1) ^ d` from retained compiler tables. The
degree and coefficient are fixed when the table is assembled: no transition function is selected
from an existential computability proof, and no proof-level clock is evaluated at runtime.

The construction uses a private unary multiplier and exposes concrete polynomial upper bounds for
the actual retained clock compiler's time and workspace. Its output length is available directly
as `NativeCompiler.outputBits`; the coefficient is stored once in the generated table and the
emitted unary clock is a separate output artifact.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryPolynomialClock`: retained generation of the
  unary word of length `c * (n + 1) ^ d`.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryPolynomialClock_time_le`: an explicit
  polynomial upper bound for the retained table's actual running-time map.
* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryPolynomialClock_workspace_le`: an explicit
  polynomial upper bound for the retained table's actual workspace map.

The construction and bounds are original formalization infrastructure.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

private def unaryMulNext :
    NativeCompiler Prod.fst (encPair encUnary encBool) encUnary :=
  first encUnary encBool

private def unaryMulEmit :
    NativeCompiler (fun input : ℕ × Bool => encUnary input.1)
      (encPair encUnary encBool) encBits :=
  (first encUnary encBool).ofOutputEq fun _ => rfl

private def unaryMulFold :
    NativeCompiler (fun input : ℕ × List Bool => input.1 * input.2.length)
      (encPair encUnary (encList encBool)) encUnary := by
  apply listFoldEmitCompiler encUnary encBool encUnary unaryMulNext unaryMulEmit
  rintro ⟨value, bits⟩
  induction bits with
  | nil => simp [streamEmit]
  | cons bit bits ih =>
      rw [streamEmit, ← ih]
      simp only [encUnary_apply, List.length_cons, Nat.mul_add, Nat.mul_one,
        List.replicate_add, Nat.add_comm]

private def unaryMulMarshal :
    NativeCompiler (fun input : ℕ × ℕ => (input.1, List.replicate input.2 true))
      (encPair encUnary encUnary) (encPair encUnary (encList encBool)) :=
  (first encUnary encUnary).pair (unaryTrueListCompiler.comp (second encUnary encUnary))

private def unaryMul :
    NativeCompiler (fun input : ℕ × ℕ => input.1 * input.2)
      (encPair encUnary encUnary) encUnary :=
  (unaryMulFold.comp unaryMulMarshal).ofOutputEq fun input => by
    simp only [List.length_replicate]

private def unarySucc : NativeCompiler (fun n : ℕ => n + 1) encUnary encUnary :=
  unaryAdd.comp ((identity encUnary).pair (const encUnary encUnary 1))

private theorem unaryTrueListCompiler_tapeCount_eq :
    unaryTrueListCompiler.tapeCount = 2 := by
  rfl

private theorem unaryMulMarshal_tapeCount_eq : unaryMulMarshal.tapeCount = 4 := by
  rfl

private theorem unaryMulFold_tapeCount_eq : unaryMulFold.tapeCount = 15 := by
  rfl

private theorem streamState_unaryMul (value : ℕ) (bits : List Bool) (j : ℕ) :
    streamState value Prod.fst bits j = value := by
  simp [streamState]

private theorem unaryTrueListCompiler_time_le (count : ℕ) :
    unaryTrueListCompiler.time count ≤ 100 * (count + 1) := by
  let seedCompiler : NativeCompiler unaryFrameSeed encUnary encBits :=
    ofTransducer unaryFrameSeedT unitStateEncoding fun count => by
      simpa only [encBits_apply] using unaryFrameSeedT_run count
  have hseed : (unaryFrameSeed count).length ≤ seedCompiler.time count := by
    simpa only [encBits_apply] using (seedCompiler.computes count).length_output_le
  simp only [unaryTrueListCompiler, ofOutputEq, comp, ofTransducer, encUnary_apply,
    List.length_replicate, encBits_apply]
  simp only [seedCompiler, ofTransducer, encUnary_apply, List.length_replicate] at hseed
  nlinarith

private theorem unaryMulMarshal_time_le (left right : ℕ) :
    unaryMulMarshal.time (left, right) ≤ 200 * (left + 1) * (right + 1) := by
  simp only [unaryMulMarshal, pair, comp, first, second, ofTransducer, encodeFrame,
    encUnary_apply, List.length_replicate, encPair_apply, List.length_append, length_frame]
  nlinarith [unaryTrueListCompiler_time_le right]

private theorem unaryMulFold_time_le (value : ℕ) (bits : List Bool) :
    unaryMulFold.time (value, bits) ≤
      400 * (value + bits.length + 1) * (bits.length + 1) := by
  change streamFoldPairTime unaryMulNext unaryMulEmit (const encUnary encBits [])
    (value, bits) ≤ _
  let lengthBound := 3 * (value + bits.length + 1)
  have hinput : (encPair encUnary (encList encBool) (value, bits)).length ≤ lengthBound := by
    simp [lengthBound, encUnary_apply, length_encList, encBool_apply, Nat.mul_comm]
    omega
  have hstate : ∀ j, j ≤ bits.length →
      (encUnary (streamState value Prod.fst bits j)).length ≤ lengthBound := by
    intro j hj
    simp only [streamState_unaryMul, encUnary_apply, List.length_replicate, lengthBound]
    omega
  have helem : ∀ j (hj : j < bits.length),
      (encBool bits[j]).length ≤ lengthBound := by
    intro j hj
    simp only [encBool_apply, List.length_singleton, lengthBound]
    omega
  have hemit : ∀ j (hj : j < bits.length),
      unaryMulEmit.time (streamState value Prod.fst bits j, bits[j]) ≤ 8 * value + 16 := by
    intro j hj
    simp only [unaryMulEmit, ofOutputEq, first, ofTransducer, streamState_unaryMul,
      encPair_apply, List.length_append, length_frame, encUnary_apply, List.length_replicate,
      encBool_apply, List.length_singleton]
    omega
  have hnext : ∀ j (hj : j < bits.length),
      unaryMulNext.time (streamState value Prod.fst bits j, bits[j]) ≤ 8 * value + 16 := by
    intro j hj
    simp only [unaryMulNext, first, ofTransducer, streamState_unaryMul,
      encPair_apply, List.length_append, length_frame, encUnary_apply, List.length_replicate,
      encBool_apply, List.length_singleton]
    omega
  have hfinish : (const encUnary encBits []).time
      (streamState value Prod.fst bits bits.length) ≤ 1 := by
    simp only [const, encBits_apply, List.length_nil]
    omega
  have h := streamFoldPairTime_le unaryMulNext unaryMulEmit (const encUnary encBits [])
    (value, bits) (8 * value + 16) (8 * value + 16) 1 lengthBound
    hinput hstate helem hemit hnext hfinish
  dsimp only [lengthBound] at h
  nlinarith

private def unaryMulFoldSMax (input : ℕ × List Bool) : ℕ :=
  let K := streamFoldPairTapeCount unaryMulNext unaryMulEmit (const encUnary encBits [])
  (Finset.range input.2.length).sup fun j =>
    if hj : j < input.2.length then
      let pair := (streamState input.1 Prod.fst input.2 j, input.2[j])
      inputFromWordWorkspace K unaryMulEmit pair +
        onWordsWorkspace K (streamFramedNext unaryMulNext) pair
    else 0

private def unaryMulFoldLMax (input : ℕ × List Bool) : ℕ :=
  max
    ((Finset.range (input.2.length + 1)).sup fun j =>
      if hj : j ≤ input.2.length then
        (encUnary (streamState input.1 Prod.fst input.2 j)).length
      else 0)
    ((Finset.range input.2.length).sup fun j =>
      if hj : j < input.2.length then (encBool input.2[j]).length else 0)

private theorem unaryMulFold_workspace_le (value : ℕ) (bits : List Bool) :
    unaryMulFold.workspace (value, bits) ≤ 10000 * (value + 1) := by
  change streamFoldPairWorkspace unaryMulNext unaryMulEmit (const encUnary encBits [])
    unaryMulFoldSMax unaryMulFoldLMax (value, bits) ≤ _
  have hsMax : unaryMulFoldSMax (value, bits) ≤ 100 * (value + 1) := by
    apply Finset.sup_le
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [hj', dite_true, streamState_unaryMul,
      inputFromWordWorkspace, onWordsWorkspace, streamFoldPairTapeCount,
      streamFramedNext, streamUnframedFinish, unaryMulNext, unaryMulEmit, ofOutputEq,
      first, ofTransducer, encodeFrame, unframeValue, comp, const, encUnary_apply,
      List.length_replicate, encBool_apply, List.length_singleton, encBits_apply,
      encPair_apply, List.length_append, length_frame]
    omega
  have hlMax : unaryMulFoldLMax (value, bits) ≤ value + 1 := by
    apply max_le
    · apply Finset.sup_le
      intro j hj
      have hj' : j ≤ bits.length := by
        have hj' := Finset.mem_range.mp hj
        change j < bits.length + 1 at hj'
        omega
      simp only [hj', dite_true, streamState_unaryMul,
        encUnary_apply, List.length_replicate]
      omega
    · apply Finset.sup_le
      intro j hj
      have hj' := Finset.mem_range.mp hj
      change j < bits.length at hj'
      simp only [hj', dite_true, encBool_apply, List.length_singleton]
      omega
  have h := streamFoldPairWorkspace_le unaryMulNext unaryMulEmit
    (const encUnary encBits []) unaryMulFoldSMax unaryMulFoldLMax (value, bits)
    (100 * (value + 1)) (value + 1) 0 hsMax hlMax
    (by simp only [encUnary_apply, List.length_replicate]; omega)
    (by simp only [streamState_unaryMul, encUnary_apply, List.length_replicate]; omega)
    (by simp [const])
  refine h.trans ?_
  simp [streamFoldPairTapeCount, unaryMulNext, unaryMulEmit, ofOutputEq, first,
    ofTransducer, streamFramedNext, streamUnframedFinish, encodeFrame, unframeValue, comp,
    const]
  nlinarith

private theorem unaryTrueListCompiler_workspace_le (count : ℕ) :
    unaryTrueListCompiler.workspace count ≤ 100 * (count + 1) := by
  let seedCompiler : NativeCompiler unaryFrameSeed encUnary encBits :=
    ofTransducer unaryFrameSeedT unitStateEncoding fun count => by
      simpa only [encBits_apply] using unaryFrameSeedT_run count
  have hseed : (unaryFrameSeed count).length ≤ seedCompiler.time count := by
    simpa only [encBits_apply] using (seedCompiler.computes count).length_output_le
  simp only [unaryTrueListCompiler, ofOutputEq, comp, ofTransducer, encUnary_apply,
    List.length_replicate, encBits_apply]
  simp only [seedCompiler, ofTransducer, encUnary_apply, List.length_replicate] at hseed
  have hscaled := Nat.mul_le_mul_left 5 hseed
  omega

private theorem unaryMulMarshal_workspace_le (left right : ℕ) :
    unaryMulMarshal.workspace (left, right) ≤ 500 * (left + right + 1) := by
  have hworkspace := unaryTrueListCompiler_workspace_le right
  simp [unaryMulMarshal, pair, comp, first, second, ofTransducer, encodeFrame,
    unaryTrueListCompiler_tapeCount_eq, encUnary_apply, List.length_replicate,
    encPair_apply, List.length_append, length_frame]
  omega

private theorem unaryMul_workspace_le (left right : ℕ) :
    unaryMul.workspace (left, right) ≤ 20000 * (left + right + 1) := by
  simp [unaryMul, ofOutputEq, comp, encPair_apply, length_frame, encUnary_apply,
    length_encList, encBool_apply, unaryMulMarshal_tapeCount_eq,
    unaryMulFold_tapeCount_eq, Nat.mul_comm]
  nlinarith [unaryMulMarshal_workspace_le left right,
    unaryMulFold_workspace_le left (List.replicate right true)]

private theorem unarySucc_workspace_le (n : ℕ) :
    unarySucc.workspace n ≤ 100 * (n + 1) := by
  simp only [unarySucc, unaryAdd, ofOutputEq, comp, pair, append, identity, const,
    first, second, ofTransducer, encodeFrame, encUnary_apply, List.length_replicate,
    encPair_apply, List.length_append, length_frame, id_eq, Function.const_apply]
  omega

private theorem unaryMul_tapeCount_eq : unaryMul.tapeCount = 17 := by
  rfl

private theorem unarySucc_tapeCount_eq : unarySucc.tapeCount = 4 := by
  rfl

private theorem unaryMul_time_le (left right : ℕ) :
    unaryMul.time (left, right) ≤ 1000 * (left + right + 1) * (right + 1) := by
  have hmarshal := unaryMulMarshal_time_le left right
  have hfold := unaryMulFold_time_le left (List.replicate right true)
  simp only [List.length_replicate] at hfold
  have hproduct : left + right + 1 ≤ (left + right + 1) * (right + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hfactor : (left + 1) * (right + 1) ≤
      (left + right + 1) * (right + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hoverhead : (left * 2 + 1 + right * 3) * 4 + 9 ≤
      100 * ((left + right + 1) * (right + 1)) := by
    nlinarith
  simp [unaryMul, ofOutputEq, comp, encPair_apply, length_frame, encUnary_apply,
    length_encList, encBool_apply, Nat.mul_comm]
  nlinarith

private theorem unarySucc_time_eq (n : ℕ) :
    unarySucc.time n = 34 * n + 72 := by
  simp only [unarySucc, unaryAdd, ofOutputEq, comp, pair, append, identity, const,
    first, second, ofTransducer, encodeFrame, encUnary_apply, List.length_replicate,
    encPair_apply, List.length_append, length_frame, id_eq, Function.const_apply]
  omega

/-- Retained generation of the unary polynomial clock `c * (n + 1) ^ d`. The literals `c` and
`d` determine one finite transition table; the construction does not evaluate a proof-supplied
function or select a machine from an existential certificate. -/
noncomputable def unaryPolynomialClock (c : ℕ) :
    (d : ℕ) → NativeCompiler (fun n : ℕ => c * (n + 1) ^ d) encUnary encUnary
  | 0 => (const encUnary encUnary c).ofOutputEq fun _ => by simp
  | d + 1 =>
      (unaryMul.comp ((unaryPolynomialClock c d).pair unarySucc)).ofOutputEq fun n => by
        simp only [Nat.pow_succ]
        ac_rfl

private theorem unaryPolynomialClock_time_succ_le (c d n : ℕ) :
    (unaryPolynomialClock c (d + 1)).time n ≤
      (unaryPolynomialClock c d).time n +
        20000 * (c + 1) * (n + 1) ^ (d + 2) := by
  have hx : 1 ≤ n + 1 := by omega
  have hp : 1 ≤ (n + 1) ^ d := Nat.one_le_pow d (n + 1) hx
  have hmul := unaryMul_time_le (c * (n + 1) ^ d) (n + 1)
  have hscale : 1 ≤ (c + 1) * (n + 1) ^ d * (n + 1) := by
    exact Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) (by omega)
  have hcp : c * (n + 1) ^ d ≤ (c + 1) * (n + 1) ^ d * (n + 1) := by
    calc
      _ ≤ (c + 1) * (n + 1) ^ d := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (c + 1) * (n + 1) ^ d * (n + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
  have hbase : n + 1 ≤ (c + 1) * (n + 1) ^ d * (n + 1) := by
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))
  have ha : c * (n + 1) ^ d + (n + 1) + 1 ≤
      3 * ((c + 1) * (n + 1) ^ d * (n + 1)) := by
    omega
  have hb : n + 1 + 1 ≤ 2 * (n + 1) := by omega
  have hmul' :
      unaryMul.time (c * (n + 1) ^ d, n + 1) ≤
        6000 * (c + 1) * (n + 1) ^ d * (n + 1) ^ 2 := by
    calc
      _ ≤ 1000 * (c * (n + 1) ^ d + (n + 1) + 1) * (n + 1 + 1) := hmul
      _ ≤ 1000 * (3 * ((c + 1) * (n + 1) ^ d * (n + 1))) *
          (2 * (n + 1)) := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 ha) hb
      _ = 6000 * (c + 1) * (n + 1) ^ d * (n + 1) ^ 2 := by ring
  simp only [unaryPolynomialClock, ofOutputEq, comp, pair, encodeFrame,
    unarySucc_time_eq, encUnary_apply, List.length_replicate,
    encPair_apply, List.length_append, length_frame]
  rw [show (n + 1) ^ (d + 2) = (n + 1) ^ d * (n + 1) ^ 2 by ring]
  nlinarith

/-- Concrete running-time majorant for the actual retained clock table. The degree and
coefficient are literal construction parameters, not witnesses selected from a polynomial-time
existence proof. -/
theorem unaryPolynomialClock_time_le (c d n : ℕ) :
    (unaryPolynomialClock c d).time n ≤
      100000 * (c + 1) * (d + 1) * (n + 1) ^ (d + 2) := by
  induction d with
  | zero =>
      simp only [unaryPolynomialClock, ofOutputEq, const, encUnary_apply,
        List.length_replicate]
      calc
        c + 1 ≤ (c + 1) * (n + 1) ^ 2 :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
        _ ≤ 100000 * ((c + 1) * (n + 1) ^ 2) :=
          Nat.le_mul_of_pos_left _ (by decide)
        _ = 100000 * (c + 1) * (0 + 1) * (n + 1) ^ (0 + 2) := by ring
  | succ d ih =>
      refine (unaryPolynomialClock_time_succ_le c d n).trans ?_
      have hpow : (n + 1) ^ (d + 2) ≤ (n + 1) ^ (d + 1 + 2) := by
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hprevious :
          (unaryPolynomialClock c d).time n ≤
            100000 * (c + 1) * (d + 1) * (n + 1) ^ (d + 1 + 2) :=
        ih.trans (Nat.mul_le_mul_left _ hpow)
      have hoverhead :
          20000 * (c + 1) * (n + 1) ^ (d + 2) ≤
            20000 * (c + 1) * (n + 1) ^ (d + 1 + 2) :=
        Nat.mul_le_mul_left _ hpow
      calc
        _ ≤ 100000 * (c + 1) * (d + 1) * (n + 1) ^ (d + 1 + 2) +
              20000 * (c + 1) * (n + 1) ^ (d + 1 + 2) :=
          Nat.add_le_add hprevious hoverhead
        _ ≤ 100000 * (c + 1) * (d + 1 + 1) * (n + 1) ^ (d + 1 + 2) := by
          nlinarith

private theorem unaryPolynomialClock_tapeCount_le (c d : ℕ) :
    (unaryPolynomialClock c d).tapeCount ≤ 20 * (d + 1) := by
  induction d with
  | zero =>
      simp only [unaryPolynomialClock, ofOutputEq, const]
      omega
  | succ d ih =>
      simp only [unaryPolynomialClock, ofOutputEq, comp, pair, encodeFrame,
        unaryMul_tapeCount_eq, unarySucc_tapeCount_eq]
      have hpair : max ((unaryPolynomialClock c d).tapeCount + 2) 4 ≤
          (unaryPolynomialClock c d).tapeCount + 4 :=
        max_le (by omega) (by omega)
      have houter : max (max ((unaryPolynomialClock c d).tapeCount + 2) 4) 17 ≤
          (unaryPolynomialClock c d).tapeCount + 17 :=
        max_le (hpair.trans (by omega)) (by omega)
      omega

private theorem unaryPolynomialClock_workspace_succ_le (c d n : ℕ) :
    (unaryPolynomialClock c (d + 1)).workspace n ≤
      (unaryPolynomialClock c d).workspace n +
        100000 * (c + 1) * (d + 1) * (n + 1) ^ (d + 2) := by
  have hx : 1 ≤ n + 1 := by omega
  have hp : 1 ≤ (n + 1) ^ d := Nat.one_le_pow d (n + 1) hx
  have hpow : (n + 1) ^ d ≤ (n + 1) ^ (d + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hmul := unaryMul_workspace_le (c * (n + 1) ^ d) (n + 1)
  have hsucc := unarySucc_workspace_le n
  have htapes := unaryPolynomialClock_tapeCount_le c d
  have hpair : max ((unaryPolynomialClock c d).tapeCount + 2) 4 ≤
      (unaryPolynomialClock c d).tapeCount + 4 :=
    max_le (by omega) (by omega)
  have houter : max (max ((unaryPolynomialClock c d).tapeCount + 2) 4) 17 ≤
      (unaryPolynomialClock c d).tapeCount + 17 :=
    max_le (hpair.trans (by omega)) (by omega)
  have hone : 1 ≤ (c + 1) * (d + 1) * (n + 1) ^ (d + 2) := by
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (Nat.pow_pos (by omega))
  have hc : c ≤ (c + 1) * (d + 1) := by
    exact (by omega : c ≤ c + 1).trans (Nat.le_mul_of_pos_right _ (by omega))
  have ha : c * (n + 1) ^ d ≤
      (c + 1) * (d + 1) * (n + 1) ^ (d + 2) := by
    exact Nat.mul_le_mul hc hpow
  have hxn : n + 1 ≤ (c + 1) * (d + 1) * (n + 1) ^ (d + 2) := by
    have hxpow : n + 1 ≤ (n + 1) ^ (d + 2) :=
      Nat.le_self_pow (by omega) _
    exact hxpow.trans
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega)))
  have hd : d + 1 ≤ (c + 1) * (d + 1) * (n + 1) ^ (d + 2) := by
    calc
      _ ≤ ((c + 1) * (n + 1) ^ (d + 2)) * (d + 1) :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))
      _ = (c + 1) * (d + 1) * (n + 1) ^ (d + 2) := by ring
  have hk : (unaryPolynomialClock c d).tapeCount ≤
      20 * ((c + 1) * (d + 1) * (n + 1) ^ (d + 2)) :=
    htapes.trans (Nat.mul_le_mul_left 20 hd)
  have hmul' : unaryMul.workspace (c * (n + 1) ^ d, n + 1) ≤
      60000 * ((c + 1) * (d + 1) * (n + 1) ^ (d + 2)) := by
    calc
      _ ≤ 20000 * (c * (n + 1) ^ d + (n + 1) + 1) := hmul
      _ ≤ 60000 * ((c + 1) * (d + 1) * (n + 1) ^ (d + 2)) := by
        nlinarith
  have hsucc' : unarySucc.workspace n ≤
      100 * ((c + 1) * (d + 1) * (n + 1) ^ (d + 2)) := by
    exact hsucc.trans (Nat.mul_le_mul_left 100 hxn)
  simp only [unaryPolynomialClock, ofOutputEq, comp, pair, encodeFrame,
    unaryMul_tapeCount_eq, unarySucc_tapeCount_eq, encUnary_apply, List.length_replicate,
    encPair_apply, List.length_append, length_frame, Nat.max_eq_left (Nat.zero_le _)]
  nlinarith

/-- Concrete workspace majorant for the unchanged workspace map of the actual retained clock
table. Together with `unaryPolynomialClock_time_le`, this is the construction's explicit
time-and-space efficiency certificate. -/
theorem unaryPolynomialClock_workspace_le (c d n : ℕ) :
    (unaryPolynomialClock c d).workspace n ≤
      1000000 * (c + 1) * (d + 1) ^ 2 * (n + 1) ^ (d + 2) := by
  induction d with
  | zero =>
      simp only [unaryPolynomialClock, ofOutputEq, const]
      exact Nat.zero_le _
  | succ d ih =>
      refine (unaryPolynomialClock_workspace_succ_le c d n).trans ?_
      have hpow : (n + 1) ^ (d + 2) ≤ (n + 1) ^ (d + 1 + 2) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hprevious :
          (unaryPolynomialClock c d).workspace n ≤
            1000000 * (c + 1) * (d + 1) ^ 2 * (n + 1) ^ (d + 1 + 2) :=
        ih.trans (Nat.mul_le_mul_left _ hpow)
      have hoverhead :
          100000 * (c + 1) * (d + 1) * (n + 1) ^ (d + 2) ≤
            100000 * (c + 1) * (d + 1) * (n + 1) ^ (d + 1 + 2) :=
        Nat.mul_le_mul_left _ hpow
      calc
        _ ≤ 1000000 * (c + 1) * (d + 1) ^ 2 * (n + 1) ^ (d + 1 + 2) +
              100000 * (c + 1) * (d + 1) * (n + 1) ^ (d + 1 + 2) :=
          Nat.add_le_add hprevious hoverhead
        _ ≤ 1000000 * (c + 1) * (d + 1 + 1) ^ 2 *
              (n + 1) ^ (d + 1 + 2) := by
          nlinarith

end Turing.MultiTapeTM.Internal.NativeCompiler
