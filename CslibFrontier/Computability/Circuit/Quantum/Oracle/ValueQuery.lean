/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Basic
public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQuery

/-!
# Placed XOR queries and the quantum value-query model

A placed coherent XOR query agrees with the existing `valueOracle addStep` after reindexing its
query, response and unused registers. This bridge includes arbitrary superpositions and workspace
states. The circuit code layer does not depend on the abstract value-query simulation machinery.

## Main results

* `Cslib.Quantum.xorQuery_eq_valueOracle`: agreement of the placed and value-query semantics.
* `Cslib.Quantum.lookupXor_cleanLookupState`: implement a placed lookup with two calls to a
  separate XOR oracle, restoring its scratch registers for the next instruction.
-/

public section

namespace Cslib.Quantum

variable {a b m : ℕ}

/-- Reindexing the placed gate into its three registers gives the existing value oracle.
This equality covers arbitrary superpositions and arbitrary states of the unused wires. -/
theorem xorQuery_eq_valueOracle (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) (ψ : Qubits m) :
    let reindex := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (queryRegisters A)
    reindex ((xorQuery H A).eval ψ) = valueOracle addStep H (reindex ψ) := by
  intro reindex
  ext ⟨x, y, w⟩
  change ((xorQuery H A).eval ψ).ofLp ((queryRegisters A).symm (x, y, w)) = _
  rw [xorQuery_eval_apply, valueOracle_apply, addStep_apply]
  have hsub : y - H x = y + H x := by
    funext i
    exact BooleanRing.sub_eq_add _ _
  simp [reindex, hsub]

section Lookup

variable {n d : ℕ}

private def cleanBasis : BitString m ↪ BitString n × BitString d × BitString m :=
  ⟨fun z => (0, 0, z), fun _ _ h => congrArg (fun p => p.2.2) h⟩

/-- Embed a native register alongside two zero work registers for the lookup address and value. -/
noncomputable def cleanLookupState :
    Qubits m →ₗᵢ[ℂ] ValueState (BitString n) (BitString d) (BitString m) :=
  LinearIsometry.piLpExtendByZero 2 ℂ ℂ cleanBasis

private theorem cleanLookupState_apply (ψ : Qubits m) (i : BitString n) (v : BitString d)
    (z : BitString m) :
    (cleanLookupState ψ).ofLp (i, v, z) = if i = 0 ∧ v = 0 then ψ.ofLp z else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact (cleanBasis (n := n) (d := d)).injective.extend_apply ψ.ofLp 0 z
  · apply LinearIsometry.piLpExtendByZero_apply_eq_zero
    rintro ⟨_, eq⟩
    cases eq
    exact h ⟨rfl, rfl⟩

/-- A placed query compiled onto two fixed scratch registers. The digest-table query occurs
twice. The wire routing and the reversible response computation are independent of the table. -/
@[expose] noncomputable def lookupXor (wires : Fin (a + b) ↪ Fin m)
    (select : BitString a → BitString n) (reply : BitString a → BitString d → BitString b)
    (D : BitString n → BitString d) :
    ValueState (BitString n) (BitString d) (BitString m) ≃ₗᵢ[ℂ]
      ValueState (BitString n) (BitString d) (BitString m) :=
  let address (z : BitString m) := select (queryRegisters wires z).1
  let route : Equiv.Perm (BitString n × BitString d × BitString m) :=
    { toFun := fun (i, v, z) => (i + address z, v, z)
      invFun := fun (i, v, z) => (i - address z, v, z)
      left_inv := by rintro ⟨i, v, z⟩; simp
      right_inv := by rintro ⟨i, v, z⟩; simp }
  let post : Equiv.Perm (BitString n × BitString d × BitString m) :=
    { toFun := fun (i, v, z) => (i, v, (queryRegisters wires).symm
        (let (x, y, w) := queryRegisters wires z; (x, y + reply x v, w)))
      invFun := fun (i, v, z) => (i, v, (queryRegisters wires).symm
        (let (x, y, w) := queryRegisters wires z; (x, y - reply x v, w)))
      left_inv := by
        rintro ⟨i, v, z⟩
        obtain ⟨⟨x, y, w⟩, rfl⟩ := (queryRegisters wires).symm.surjective z
        simp only [Equiv.apply_symm_apply, add_sub_cancel_right]
      right_inv := by
        rintro ⟨i, v, z⟩
        obtain ⟨⟨x, y, w⟩, rfl⟩ := (queryRegisters wires).symm.surjective z
        simp only [Equiv.apply_symm_apply, sub_add_cancel] }
  let routing := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ route
  let response := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ post
  routing.trans ((valueOracle addStep D).trans (response.trans
    ((valueOracle addStep D).trans routing.symm)))

private theorem double_sub {k : ℕ} (u v : BitString k) : u - v - v = u := by
  funext j
  change u j - v j - v j = u j
  rw [sub_sub, BooleanRing.add_self, sub_zero]

/-- The compiled query implements the native placed XOR gate and restores both scratch
registers, with the same encoding for all choices of wires. -/
theorem lookupXor_cleanLookupState (wires : Fin (a + b) ↪ Fin m)
    (select : BitString a → BitString n) (reply : BitString a → BitString d → BitString b)
    (D : BitString n → BitString d) (ψ : Qubits m) :
    lookupXor wires select reply D (cleanLookupState ψ) =
      cleanLookupState ((xorQuery (fun x => reply x (D (select x))) wires).eval ψ) := by
  ext ⟨i, v, z⟩
  obtain ⟨⟨x, y, w⟩, rfl⟩ := (queryRegisters wires).symm.surjective z
  simp only [lookupXor, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, Equiv.symm_symm,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Equiv.apply_symm_apply,
    valueOracle_apply, addStep_apply, add_sub_cancel_right, double_sub, cleanLookupState_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    have xor_sub {k : ℕ} (u v : BitString k) : u - v = u + v :=
      funext fun j => BooleanRing.sub_eq_add (u j) (v j)
    simp only [zero_add, xor_sub, xorQuery_eval_apply]
  · rfl

end Lookup

end Cslib.Quantum
