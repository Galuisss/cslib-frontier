/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Code

/-!
# Erasing calls to the all-zero quantum oracle

`OracleCircuit.zeroOraclePhaseCodes` retains every elementary phase-gate code and erases every
oracle-query instruction.  This is semantics preserving when the interpreted XOR oracle returns
zero on every input: a zero-response query is the identity on arbitrary quantum states, not only
on basis inputs.  The resulting equality of linear isometries rewrites directly under joint
density evolution with an arbitrary reference register.

The construction is used when a native quantum test is compiled into a genuinely query-free
reduction.  It does not restrict the input test to descriptions that were already query-free.

## Main definitions

* `Cslib.Quantum.OracleCircuit.zeroOraclePhaseCodes`: retain elementary instructions and erase
  all calls to the all-zero oracle.

## Main results

* `Cslib.Quantum.OracleCircuit.eval_toCircuit_zeroOracle_eq_ofPhaseCodes`: erasure preserves
  execution on every quantum state.
-/

public section

namespace Cslib.Quantum

namespace OracleCircuit

/-- Retain the elementary phase-gate codes and erase every oracle-query instruction. -/
@[expose] def zeroOraclePhaseCodes (instructions : OracleCircuit) : List PhaseGateCode :=
  instructions.filterMap fun
    | .gate code => some code
    | .query => none

/-- Erasing zero-oracle calls retains exactly the elementary-gate count. -/
@[simp] theorem length_zeroOraclePhaseCodes (instructions : OracleCircuit) :
    instructions.zeroOraclePhaseCodes.length = instructions.gateCount := by
  induction instructions with
  | nil => rfl
  | cons instruction instructions ih =>
      cases instruction with
      | gate code =>
          change (code :: zeroOraclePhaseCodes instructions).length =
            gateCount (OracleGateCode.gate code :: instructions)
          simp [gateCount, OracleGateCode.isQuery, ih]
      | query =>
          change (zeroOraclePhaseCodes instructions).length =
            gateCount (OracleGateCode.query :: instructions)
          simpa [gateCount, OracleGateCode.isQuery] using ih

/-- Rewrapping the retained phase codes gives a circuit with no query instructions. -/
@[simp] theorem queryCount_map_gate_zeroOraclePhaseCodes (instructions : OracleCircuit) :
    queryCount (instructions.zeroOraclePhaseCodes.map OracleGateCode.gate) = 0 := by
  simp [queryCount, OracleGateCode.isQuery]

private theorem xorQuery_zero_eval {a b m : ℕ} (A : Fin (a + b) ↪ Fin m)
    (ψ : Qubits m) :
    (xorQuery (fun _ : Fin a → Bool => fun _ : Fin b => false) A).eval ψ = ψ := by
  ext z
  obtain ⟨⟨x, y, w⟩, rfl⟩ := (queryRegisters A).symm.surjective z
  rw [xorQuery_eval_apply]
  have hy : y + (fun _ : Fin b => false) = y := by
    funext i
    exact Bool.xor_false (y i)
  rw [hy]

/-- **All-zero oracle erasure is semantics preserving on arbitrary states.** Every elementary
instruction is retained, and each well-formed zero-response XOR query acts as the identity;
malformed queries were already skipped by the total interpreter. -/
theorem eval_toCircuit_zeroOracle_eq_ofPhaseCodes {a b m : ℕ}
    (instructions : OracleCircuit) :
    Circuit.eval (toCircuit m (fun _ : Fin a → Bool => fun _ : Fin b => false) instructions) =
      Circuit.eval (Circuit.ofPhaseCodes m instructions.zeroOraclePhaseCodes) := by
  induction instructions with
  | nil => rfl
  | cons instruction instructions ih =>
      cases instruction with
      | gate code =>
          ext ψ
          rw [show zeroOraclePhaseCodes (OracleGateCode.gate code :: instructions) =
              code :: zeroOraclePhaseCodes instructions by rfl,
            Circuit.ofPhaseCodes_cons]
          rw [show OracleGateCode.gate code :: instructions =
              [OracleGateCode.gate code] ++ instructions by rfl,
            toCircuit_append, Circuit.eval_append, Circuit.eval_append, ih]
          have hsingle :
              toCircuit m (fun _ : Fin a → Bool => fun _ : Fin b => false)
                  [OracleGateCode.gate code] =
                Circuit.ofPhaseCodes m [code] :=
            toCircuit_map_gate (m := m)
              (fun _ : Fin a → Bool => fun _ : Fin b => false) [code]
          rw [hsingle]
      | query =>
          ext ψ
          rw [show zeroOraclePhaseCodes (OracleGateCode.query :: instructions) =
              zeroOraclePhaseCodes instructions by rfl]
          rw [show OracleGateCode.query :: instructions =
              [OracleGateCode.query] ++ instructions by rfl,
            toCircuit_append, Circuit.eval_append, ih]
          by_cases h : a + b ≤ m
          · simp [toCircuit, OracleGateCode.toPlacedGate?, h, xorQuery_zero_eval]
          · simp [toCircuit, OracleGateCode.toPlacedGate?, h]

end OracleCircuit

end Cslib.Quantum
