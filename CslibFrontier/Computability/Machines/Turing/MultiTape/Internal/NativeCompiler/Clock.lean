/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Replicate

/-!
# Concrete retained unary polynomial clocks

This module constructs the unary clock `c * (n + 1) ^ d` from retained compiler tables. The
degree and coefficient are fixed when the table is assembled: no transition function is selected
from an existential computability proof, and no proof-level clock is evaluated at runtime.

This concrete-only construction uses a private unary multiplier and retains the actual compiler's
time and workspace maps. Polynomial majorants for those maps remain open under issue #5281.
Its output length is available directly as `NativeCompiler.outputBits`; the coefficient is stored
in the generated table and the emitted unary clock is a separate output artifact.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryPolynomialClock`: retained generation of the
  unary word of length `c * (n + 1) ^ d`.

The construction is original formalization infrastructure. Its computation certificate proves
that the actual table emits the required unary clock; it does not yet prove polynomial bounds
for that table's execution.
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

end Turing.MultiTapeTM.Internal.NativeCompiler
