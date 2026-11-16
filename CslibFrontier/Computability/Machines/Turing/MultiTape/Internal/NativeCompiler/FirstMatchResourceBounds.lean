/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.FirstMatch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamResourceBounds
import CslibFrontier.Tactic.EncLen

/-!
# Resource bounds for retained first-match lookup

This module bounds the actual time map of `firstMatchCompiler`. The proof controls every encoded
stream state and table occurrence, then applies the construction-derived stream and composition
bounds. It does not select a machine from an existential computability certificate.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.firstMatchCompiler_time_le`: a concrete quadratic
  time majorant for the retained first-match compiler.

The construction and bound are original formalization infrastructure.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

private theorem firstMatch_streamState_query {Key Value : Type*} [DecidableEq Key]
    (query : Key) (found : Bool) (table : List (Key × Value)) (j : ℕ)
    (hj : j ≤ table.length) :
    (streamState (query, found) firstMatchNext table j).1 = query := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [streamState_succ _ _ _ (by omega : j < table.length)]
      generalize hstate : streamState (query, found) firstMatchNext table j = state
      obtain ⟨stateQuery, stateFound⟩ := state
      obtain ⟨entryKey, entryValue⟩ := table[j]
      have hquery : stateQuery = query := by
        simpa only [hstate] using ih (by omega)
      subst stateQuery
      rfl

private theorem firstMatchNextCompiler_time_le {Key Value : Type*} [DecidableEq Key]
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : FirstMatchState Key × (Key × Value)) :
    (firstMatchNextCompiler encKey encValue).time input ≤
      10000 * ((encPair (encPair encKey encBool) (encPair encKey encValue) input).length + 1) := by
  obtain ⟨⟨query, found⟩, entryKey, value⟩ := input
  cases found <;>
    simp [firstMatchNextCompiler, first, second, wordEqBool, ofZipTransducer, boolToTest,
      ofTransducer, comp, pair, ite, const, encodeFrame, ofOutputEq, encTest_false,
      encTest_true] <;>
    omega

private theorem firstMatchNextCompiler_workspace_le {Key Value : Type*} [DecidableEq Key]
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : FirstMatchState Key × (Key × Value)) :
    (firstMatchNextCompiler encKey encValue).workspace input ≤
      10000 * ((encPair (encPair encKey encBool) (encPair encKey encValue) input).length + 1) := by
  obtain ⟨⟨query, found⟩, entryKey, value⟩ := input
  cases found <;>
    simp [firstMatchNextCompiler, first, second, wordEqBool, ofZipTransducer, boolToTest,
      ofTransducer, comp, pair, ite, const, encodeFrame, ofOutputEq, encTest_false,
      encTest_true] <;>
    omega

private theorem firstMatchEmitCompiler_time_le {Key Value : Type*} [DecidableEq Key]
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : FirstMatchState Key × (Key × Value)) :
    (firstMatchEmitCompiler encKey encValue).time input ≤
      20000 * ((encPair (encPair encKey encBool) (encPair encKey encValue) input).length + 1) := by
  obtain ⟨⟨query, found⟩, entryKey, value⟩ := input
  cases found <;> by_cases hkeys : entryKey = query <;>
    simp [firstMatchEmitCompiler, first, second, wordEqBool, wordEqTest, ofZipTransducer,
      boolToTest, optionSome, ofTransducer, comp, pair, ite, const, encodeFrame,
      hkeys, encKey.injective.eq_iff, ofOutputEq, encTest_false, encTest_true] <;>
    omega

private theorem firstMatchEmitCompiler_workspace_le {Key Value : Type*} [DecidableEq Key]
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : FirstMatchState Key × (Key × Value)) :
    (firstMatchEmitCompiler encKey encValue).workspace input ≤
      20000 * ((encPair (encPair encKey encBool) (encPair encKey encValue) input).length + 1) := by
  obtain ⟨⟨query, found⟩, entryKey, value⟩ := input
  cases found <;> by_cases hkeys : entryKey = query <;>
    simp [firstMatchEmitCompiler, first, second, wordEqBool, wordEqTest, ofZipTransducer,
      boolToTest, optionSome, ofTransducer, comp, pair, ite, const, encodeFrame,
      hkeys, encKey.injective.eq_iff, ofOutputEq, encTest_false, encTest_true] <;>
    omega

/-- The actual retained first-match compiler has quadratic time in the complete encoded table and
query. Its installed program description remains a separate static coordinate. -/
theorem firstMatchCompiler_time_le {Key Value : Type*} [DecidableEq Key]
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : List (Key × Value) × Key) :
    (firstMatchCompiler encKey encValue).time input ≤
      100000000 *
        ((encPair (encList (encPair encKey encValue)) encKey input).length + 1) ^ 2 := by
  let L := (encPair (encList (encPair encKey encValue)) encKey input).length
  let encState := encPair encKey encBool
  let encEntry := encPair encKey encValue
  let nextCompiler := firstMatchNextCompiler encKey encValue
  let emitCompiler := firstMatchEmitCompiler encKey encValue
  let finishCompiler := firstMatchFinishCompiler encKey encValue
  let streamInput : FirstMatchState Key × List (Key × Value) :=
    ((input.2, false), input.1)
  have hquery : (encKey input.2).length ≤ L := by
    exact (length_le_encPair_right (encList encEntry) encKey input).trans le_rfl
  have htable : (encList encEntry input.1).length ≤ L := by
    exact (length_le_encPair_left (encList encEntry) encKey input).trans le_rfl
  have htable' : (encList (encPair encKey encValue) input.1).length ≤ L := by
    simpa only [encEntry] using htable
  have hinput : (encPair encState (encList encEntry) streamInput).length ≤ 10 * (L + 1) := by
    simp only [streamInput, encState, encEntry]
    enc_len at hquery htable' ⊢
  have hstate : ∀ j, j ≤ input.1.length →
      (encState (streamState streamInput.1 firstMatchNext streamInput.2 j)).length ≤
        10 * (L + 1) := by
    intro j hj
    have hq := firstMatch_streamState_query input.2 false input.1 j hj
    generalize hstateEq : streamState streamInput.1 firstMatchNext streamInput.2 j = state at hq ⊢
    obtain ⟨stateQuery, stateFound⟩ := state
    change stateQuery = input.2 at hq
    subst stateQuery
    cases stateFound <;>
      simp only [encState, length_encPair, encBool_apply, List.length_singleton] <;>
      omega
  have helem : ∀ j (hj : j < input.1.length),
      (encEntry input.1[j]).length ≤ 10 * (L + 1) := by
    intro j hj
    have hmem : input.1[j] ∈ input.1 := List.getElem_mem hj
    have hmember := SizedListEncoding.length_elem_le
      (encA := encPair encKey encValue) (encL := encList (encPair encKey encValue))
      input.1 input.1[j] hmem
    simpa only [encEntry] using (hmember.trans htable').trans (by omega)
  have hpair : ∀ j (hj : j < input.1.length),
      (encPair (encPair encKey encBool) (encPair encKey encValue)
        (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j])).length ≤
          40 * (L + 1) := by
    intro j hj
    have hs := hstate j hj.le
    have he := helem j hj
    enc_len [encState, encEntry] at hs he ⊢
  have hnext : ∀ j (hj : j < input.1.length),
      nextCompiler.time
        (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j]) ≤
          500000 * (L + 1) := by
    intro j hj
    have h := firstMatchNextCompiler_time_le encKey encValue
      (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j])
    have hp := hpair j hj
    simp only [nextCompiler] at h ⊢
    omega
  have hemit : ∀ j (hj : j < input.1.length),
      emitCompiler.time
        (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j]) ≤
          1000000 * (L + 1) := by
    intro j hj
    have h := firstMatchEmitCompiler_time_le encKey encValue
      (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j])
    have hp := hpair j hj
    simp only [emitCompiler] at h ⊢
    omega
  have hfinish : finishCompiler.time
      (streamState streamInput.1 firstMatchNext streamInput.2 input.1.length) ≤ 1 := by
    simp [finishCompiler, firstMatchFinishCompiler, const]
  have hstream := streamFoldPairTime_le nextCompiler emitCompiler finishCompiler streamInput
    (1000000 * (L + 1)) (500000 * (L + 1)) 1 (10 * (L + 1))
    hinput hstate helem hemit hnext hfinish
  have hstream' :
      (firstMatchStreamCompiler encKey encValue).time streamInput ≤
        input.1.length *
          (1000000 * (L + 1) + 500000 * (L + 1) + 46 * (10 * (L + 1)) + 60) +
          1 + 24 * (10 * (L + 1)) + 40 := by
    change streamFoldPairTime nextCompiler emitCompiler finishCompiler streamInput ≤ _
    exact hstream
  simp only [streamInput] at hstream'
  have hcount : input.1.length ≤ L :=
    (length_le_length_encList encEntry input.1).trans htable
  have hround :
      1000000 * (L + 1) + 500000 * (L + 1) + 46 * (10 * (L + 1)) + 60 ≤
        2000000 * (L + 1) := by omega
  have hmul := Nat.mul_le_mul hcount hround
  have hquad : L * (2000000 * (L + 1)) ≤ 2000000 * (L + 1) ^ 2 := by
    nlinarith
  have hrounds := hmul.trans hquad
  have hlinear : L + 1 ≤ (L + 1) ^ 2 := by
    nlinarith
  have hstreamBound :
      (firstMatchStreamCompiler encKey encValue).time ((input.2, false), input.1) ≤
        3000000 * (L + 1) ^ 2 := by
    omega
  have hmarshal :
      (firstMatchMarshalCompiler encKey encValue).time input ≤ 10000 * (L + 1) := by
    simp [firstMatchMarshalCompiler, first, second, ofTransducer, pair, comp, encodeFrame,
      const, L]
    omega
  have hcomp := time_comp_le (firstMatchStreamCompiler encKey encValue)
    (firstMatchMarshalCompiler encKey encValue) input
  change ((firstMatchStreamCompiler encKey encValue).comp
    (firstMatchMarshalCompiler encKey encValue)).time input ≤
      100000000 * (L + 1) ^ 2
  omega

end Turing.MultiTapeTM.Internal.NativeCompiler
