/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode
public import CslibFrontier.Computability.Circuit.Quantum.Parallel
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic

/-!
# Quantum interactive proofs

A verifier has a private register and a message register. A prover has its own private
register. An exchange applies a verifier circuit on the verifier's two registers, then
an arbitrary prover unitary on the message and the prover's own register. A final
verifier circuit decides by measuring the first verifier qubit. All registers begin
in the zero state except for the instance bits, placed in the verifier's private register.

This is the unitary presentation of [Watrous2008, §VI.1]. Prover operations can be
purified by retaining the extra qubits in its private register. The register width is
an unrestricted finite number, and a prover strategy can depend on the instance. A
prover-first protocol uses an empty initial verifier turn. Padding the message and
private registers gives fixed widths across turns for each input length. The verifier
keeps any workspace needed to implement its operations as unitary circuits.

## Main definitions

* `Cslib.Quantum.UniformInteractiveVerifier`: polynomial-time generation of a verifier's
  register widths and sequence of circuits.
* `Cslib.Quantum.UniformInteractiveVerifier.interaction`: alternating verifier and prover
  operations on the joint registers.
* `Cslib.Complexity.PromiseQIP` and `Cslib.Complexity.QIP`: quantum interactive proofs
  with completeness 2/3 and soundness 1/3.
-/

public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- Gate-code lists for each verifier turn before a prover response, followed by the final
verifier turn. The encoding makes the number and lengths of the turns explicit. -/
abbrev encInteractiveTurns :
    (List (List PhaseGateCode) × List PhaseGateCode) ↪ List Bool :=
  encPair (encList (encList encPhaseGateCode)) (encList encPhaseGateCode)

/-- Uniform verifier: widths and all circuit turns are computed in polynomial time from the
unary input length. Qubit zero belongs to the verifier's private register. -/
structure UniformInteractiveVerifier where
  /-- Verifier-private qubits, including the instance and any ancillas. -/
  privateWidth : ℕ → ℕ
  /-- Qubits exchanged between the parties on every turn. -/
  messageWidth : ℕ → ℕ
  /-- The verifier turns preceding a prover response and the final verifier turn. -/
  turns : ℕ → List (List PhaseGateCode) × List PhaseGateCode
  computableInPolyTime_privateWidth : ComputableInPolyTime privateWidth encUnary encUnary
  computableInPolyTime_messageWidth : ComputableInPolyTime messageWidth encUnary encUnary
  computableInPolyTime_turns : ComputableInPolyTime turns encUnary encInteractiveTurns
  le_privateWidth : ∀ n, n ≤ privateWidth n
  privateWidth_pos : ∀ n, 0 < privateWidth n
  wellFormed : ∀ n, ∀ gates ∈ ((turns n).1 ++ [(turns n).2]),
    ∀ g ∈ gates, g.WellFormed (privateWidth n + messageWidth n)

namespace UniformInteractiveVerifier

variable (V : UniformInteractiveVerifier)

/-- A prover's strategy consists of a unitary for each response, acting only on the message
and its own `p` qubits. -/
abbrev Strategy (n p : ℕ) := Fin (V.turns n).1.length → Gate (V.messageWidth n + p)

/-- Verifier-private and message qubits are the initial block of the joint register. -/
@[expose] def verifierWires (n p : ℕ) :
    Fin (V.privateWidth n + V.messageWidth n) ↪ Fin (V.privateWidth n + V.messageWidth n + p) :=
  Fin.castAddEmb p

/-- Message and prover-private qubits are the final block of the joint register. -/
@[expose] def proverWires (n p : ℕ) :
    Fin (V.messageWidth n + p) ↪ Fin (V.privateWidth n + V.messageWidth n + p) :=
  blockEmb (V.privateWidth n) (Nat.add_assoc _ _ _).ge

/-- Execute the protocol using one shared message register. Each earlier verifier circuit
is followed by the corresponding prover response; the final verifier circuit comes last. -/
@[expose] noncomputable def interaction (n : ℕ) {p : ℕ} (strategy : V.Strategy n p) :
    Circuit (V.privateWidth n + V.messageWidth n + p) :=
  let verifierTurn := fun gs => (Circuit.ofPhaseCodes _ gs).mapWires (V.verifierWires n p)
  (List.ofFn fun i : Fin (V.turns n).1.length =>
    verifierTurn (V.turns n).1[i] ++ [⟨_, strategy i, V.proverWires n p⟩]).flatten ++
    verifierTurn (V.turns n).2

/-- Measure the verifier's first private qubit after the interaction. -/
@[expose] noncomputable def acceptProb (x : List Bool) {p : ℕ}
    (strategy : V.Strategy x.length p) : ℝ :=
  measureProb ((V.interaction x.length strategy).run (inputState _ x)) (accepting _)

/-- The measurement has nonnegative probability. -/
theorem acceptProb_nonneg (x : List Bool) {p : ℕ} (strategy : V.Strategy x.length p) :
    0 ≤ V.acceptProb x strategy :=
  measureProb_nonneg _ _

/-- The joint circuit starts in a basis state and preserves its norm. -/
theorem acceptProb_le_one (x : List Bool) {p : ℕ} (strategy : V.Strategy x.length p) :
    V.acceptProb x strategy ≤ 1 := by
  refine (measureProb_le_measureProb_univ _ _).trans_eq ?_
  rw [measureProb_univ, Circuit.norm_run, one_pow]

end UniformInteractiveVerifier
end Cslib.Quantum

namespace Cslib.Complexity

open Cslib.Quantum

/-- Polynomial-round quantum interactive proofs for promise problems. The verifier works
against every finite-dimensional prover strategy on no-instances. -/
@[expose] def PromiseQIP {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {X | ∃ V : UniformInteractiveVerifier,
    (∀ a ∈ X.yes, ∃ (p : ℕ) (strategy : V.Strategy (enc a).length p),
      2 / 3 ≤ V.acceptProb (enc a) strategy) ∧
    (∀ a ∈ X.no, ∀ (p : ℕ) (strategy : V.Strategy (enc a).length p),
      V.acceptProb (enc a) strategy ≤ 1 / 3)}

/-- Quantum interactive proofs for languages, with soundness on the complement. -/
@[expose] def QIP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseQIP enc}

end Cslib.Complexity
