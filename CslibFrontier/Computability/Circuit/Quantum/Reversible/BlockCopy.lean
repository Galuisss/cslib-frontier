/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Classical

/-!
# Copying a contiguous classical register

`GateCode.blockCopyCodes source target count` emits one CNOT for each pair of corresponding
wires in two contiguous blocks. The source and target blocks may occur in either order.
Disjointness makes their joint action the parallel XOR copy stated below and keeps every source
wire unchanged.

## Main definitions

* `Cslib.Quantum.GateCode.blockCopyCodes`: CNOTs from one contiguous block to another.

## Main results

* `Cslib.Quantum.GateCode.readBit_classicalRun_blockCopyCodes`: every target bit becomes its
  previous value XOR the corresponding source bit.

## References

This register-layout construction is original formalization infrastructure.
-/

public section

namespace Cslib.Quantum.GateCode

/-- XOR `count` consecutive source wires into the corresponding target wires with CNOTs. This
is a literal copy when the target block starts in the all-zero state. -/
@[expose] def blockCopyCodes (source target count : ℕ) : List GateCode :=
  (List.range count).map fun offset => (false, target + offset, [source + offset])

@[simp] theorem length_blockCopyCodes (source target count : ℕ) :
    (blockCopyCodes source target count).length = count := by
  simp [blockCopyCodes]

/-- A contiguous block copy is classical and well formed when the source and target blocks are
disjoint and both fit in the register. -/
theorem isClassical_blockCopyCodes {source target count width : ℕ}
    (hdisjoint : source + count ≤ target ∨ target + count ≤ source)
    (hsource : source + count ≤ width) (htarget : target + count ≤ width) :
    IsClassical width (blockCopyCodes source target count) := by
  intro gate hgate
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hgate
  have hoffset' := List.mem_range.mp hoffset
  refine ⟨rfl, ?_⟩
  simp only [WellFormed, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.succ_le_succ_iff, Nat.zero_le, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, List.nodup_nil, not_false_eq_true, and_true,
    true_and, forall_eq_or_imp, forall_eq]
  constructor
  · rcases hdisjoint with hdisjoint | hdisjoint
    · exact ne_of_gt (((Nat.add_lt_add_left hoffset' source).trans_le hdisjoint).trans_le
        (Nat.le_add_right target offset))
    · exact ne_of_lt (((Nat.add_lt_add_left hoffset' target).trans_le hdisjoint).trans_le
        (Nat.le_add_right source offset))
  · exact ⟨(Nat.add_lt_add_left hoffset' target).trans_le htarget,
      (Nat.add_lt_add_left hoffset' source).trans_le hsource⟩

/-- Each target of a disjoint block copy is XORed with the corresponding source bit. This
describes the exact basis-state action without assuming that the target block starts at zero. -/
theorem readBit_classicalRun_blockCopyCodes {source target count width : ℕ}
    (hdisjoint : source + count ≤ target ∨ target + count ≤ source)
    (hsource : source + count ≤ width) (htarget : target + count ≤ width)
    (x : Fin width → Bool) {offset : ℕ} (hoffset : offset < count) :
    readBit (classicalRun (blockCopyCodes source target count) x) (target + offset) =
      (readBit x (target + offset) ^^ readBit x (source + offset)) := by
  have hclass := isClassical_blockCopyCodes hdisjoint hsource htarget
  have hlt : ∀ gate ∈ blockCopyCodes source target count, gate.2.1 < width := by
    intro gate hgate
    obtain ⟨phase, target, controls⟩ := gate
    obtain ⟨hphase, hwellFormed⟩ := hclass (phase, target, controls) hgate
    change phase = false at hphase
    subst phase
    exact hwellFormed.2.2 target (List.mem_cons_self ..)
  have hnd : ((blockCopyCodes source target count).map fun gate => gate.2.1).Nodup := by
    rw [blockCopyCodes, List.map_map]
    exact List.nodup_range.map fun left right h => by
      simp only [Function.comp_apply] at h
      omega
  have hread : ∀ gate ∈ blockCopyCodes source target count,
      ∀ gate' ∈ blockCopyCodes source target count, gate.2.1 ∉ gate'.2.2 := by
    intro gate hgate gate' hgate'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hgate
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hgate'
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hdisjoint with hdisjoint | hdisjoint <;> omega
  have hmem : ((false, target + offset, [source + offset]) : GateCode) ∈
      blockCopyCodes source target count := by
    rw [blockCopyCodes, List.mem_map]
    exact ⟨offset, List.mem_range.mpr hoffset, rfl⟩
  simpa using readBit_classicalRun_of_mem hlt hnd hread x hmem

end Cslib.Quantum.GateCode
