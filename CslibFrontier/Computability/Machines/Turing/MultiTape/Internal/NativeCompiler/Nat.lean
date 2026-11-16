/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Equality

/-!
# Named native binary-natural primitives

This module retains the existing streaming successor, predecessor and zero-test transducers as
`NativeCompiler`s. The wrappers name the concrete machines and their constructive state encodings;
they do not extract a witness from the existential complexity certificates.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryAdd`: retained unary addition by direct
  concatenation.
* `Turing.MultiTapeTM.Internal.NativeCompiler.unarySub`: retained truncated unary subtraction.
* `Turing.MultiTapeTM.Internal.NativeCompiler.natSucc`: retained binary successor.
* `Turing.MultiTapeTM.Internal.NativeCompiler.natPred`: retained saturating binary predecessor.
* `Turing.MultiTapeTM.Internal.NativeCompiler.natIsZeroBool`, `.natIsZeroTest`: retained binary
  zero tests in Boolean and branch-test encodings.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- Unary addition by emitting the two unary words consecutively. -/
@[expose] def unaryAdd :
    NativeCompiler (fun input : ℕ × ℕ => input.1 + input.2)
      (encPair encUnary encUnary) encUnary := by
  let inputEncoding := encPair encUnary encUnary
  let left : NativeCompiler (fun input : ℕ × ℕ => encUnary input.1)
      inputEncoding encBits :=
    (first encUnary encUnary).ofOutputEq fun _ => rfl
  let right : NativeCompiler (fun input : ℕ × ℕ => encUnary input.2)
      inputEncoding encBits :=
    (second encUnary encUnary).ofOutputEq fun _ => rfl
  exact (left.append right).ofOutputEq fun input => by
    simp only [encUnary_apply, encBits_apply, List.replicate_add]

/-- A unary zip scan emits one bit for each left symbol remaining after the right word ends. -/
def unarySubT : ZipTransducer Unit where
  q₀ := ()
  step _ symbols :=
    ((), if symbols.1.isSome && symbols.2.isNone then [true] else [])
  final _ := []
  length_step_le _ symbols := by cases symbols.1 <;> cases symbols.2 <;> simp
  length_final_le _ := by simp

/-- The unary subtraction transducer emits the truncated length difference. -/
theorem unarySubT_run (left right : ℕ) :
    unarySubT.run unarySubT.q₀ (encUnary left) (encUnary right) =
      encUnary (left - right) := by
  induction left generalizing right with
  | zero =>
      induction right with
      | zero =>
          simp only [encUnary_apply, List.replicate_zero, ZipTransducer.run_nil_nil,
            unarySubT, Nat.zero_sub]
      | succ right ih =>
          simpa [encUnary_apply, List.replicate_succ, ZipTransducer.run_nil_cons, unarySubT]
            using ih
  | succ left ih =>
      cases right with
      | zero =>
          simpa [encUnary_apply, List.replicate_succ, ZipTransducer.run_cons_nil, unarySubT]
            using ih 0
      | succ right =>
          simpa [encUnary_apply, List.replicate_succ, ZipTransducer.run_cons_cons, unarySubT]
            using ih right

/-- Truncated unary subtraction through one direct retained zip scan. -/
@[expose] def unarySub :
    NativeCompiler (fun input : ℕ × ℕ => input.1 - input.2)
      (encPair encUnary encUnary) encUnary :=
  ofZipTransducer encUnary encUnary encUnary unarySubT unitStateEncoding fun input =>
    unarySubT_run input.1 input.2

/-- Binary successor through the public carry transducer. -/
@[expose] def natSucc :
    NativeCompiler (fun n : ℕ => n + 1) encNat encNat :=
  ofTransducer NatSucc.succTransducer Universal.eBit fun n => by
    simpa only [encNat_apply] using NatSucc.run_succTransducer_q₀ n

/-- Saturating binary predecessor through the public borrow transducer. -/
@[expose] def natPred :
    NativeCompiler (fun n : ℕ => n - 1) encNat encNat :=
  ofTransducer NatPred.predTransducer (optionStateEncoding Universal.eBit) fun n => by
    simpa only [encNat_apply] using NatPred.run_predTransducer_q₀ n

/-- Binary zero test with one-bit Boolean output. -/
@[expose] def natIsZeroBool :
    NativeCompiler (fun n : ℕ => decide (n = 0)) encNat encBool :=
  ofTransducer NatPred.isZeroTransducer Universal.eBit fun n => by
    simpa only [encNat_apply, encBool_apply] using NatPred.run_isZeroTransducer_q₀ n

/-- Binary zero test in the empty/nonempty branch encoding, including the retained conversion. -/
@[expose] def natIsZeroTest :
    NativeCompiler (fun n : ℕ => decide (n = 0)) encNat encTest :=
  boolToTest.comp natIsZeroBool

end Turing.MultiTapeTM.Internal.NativeCompiler
