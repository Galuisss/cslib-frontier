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

This module bounds the actual time and workspace maps of `firstMatchCompiler`. The proofs control
every encoded stream state and table occurrence, then apply the construction-derived stream and
composition bounds. They do not select a machine from an existential computability certificate.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.firstMatchCompiler_time_le`: a concrete quadratic
  time majorant for the retained first-match compiler.
* `Turing.MultiTapeTM.Internal.NativeCompiler.firstMatchCompiler_workspace_le`: an independent
  concrete quadratic workspace majorant for the same compiler.
* `Turing.MultiTapeTM.Internal.NativeCompiler.firstMatchCompiler_tapeCount_le`: a static
  tape-count majorant for the retained construction.

The construction and bounds are original formalization infrastructure.
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

private theorem firstMatch_state_length_le {Key Value : Type*} [DecidableEq Key]
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : List (Key × Value) × Key) (j : ℕ) (hj : j ≤ input.1.length) :
    ((encPair encKey encBool)
      (streamState (input.2, false) firstMatchNext input.1 j)).length ≤
        10 * ((encPair (encList (encPair encKey encValue)) encKey input).length + 1) := by
  have hq := firstMatch_streamState_query input.2 false input.1 j hj
  have hquery := length_le_encPair_right
    (encList (encPair encKey encValue)) encKey input
  generalize hstateEq : streamState (input.2, false) firstMatchNext input.1 j = state at hq ⊢
  obtain ⟨stateQuery, stateFound⟩ := state
  change stateQuery = input.2 at hq
  subst stateQuery
  cases stateFound <;>
    simp only [length_encPair, encBool_apply, List.length_singleton] <;>
    omega

private theorem firstMatch_element_length_le {Key Value : Type*}
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : List (Key × Value) × Key) (j : ℕ) (hj : j < input.1.length) :
    ((encPair encKey encValue) input.1[j]).length ≤
      10 * ((encPair (encList (encPair encKey encValue)) encKey input).length + 1) := by
  have hmem : input.1[j] ∈ input.1 := List.getElem_mem hj
  have hmember := SizedListEncoding.length_elem_le
    (encA := encPair encKey encValue) (encL := encList (encPair encKey encValue))
    input.1 input.1[j] hmem
  have htable := length_le_encPair_left
    (encList (encPair encKey encValue)) encKey input
  omega

private theorem firstMatchStreamCompiler_tapeCount_le {Key Value : Type*} [DecidableEq Key]
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool) :
    (firstMatchStreamCompiler encKey encValue).tapeCount ≤ 1000 := by
  change streamFoldPairTapeCount (firstMatchNextCompiler encKey encValue)
    (firstMatchEmitCompiler encKey encValue) (firstMatchFinishCompiler encKey encValue) ≤ 1000
  simp [streamFoldPairTapeCount, streamFramedNext, streamUnframedFinish,
    firstMatchNextCompiler, firstMatchEmitCompiler, firstMatchFinishCompiler,
    first, second, wordEqBool, wordEqTest, boolToTest, optionSome, ofZipTransducer,
    ofTransducer, comp, pair, ite, const, encodeFrame, unframeValue, ofOutputEq]

private theorem firstMatchMarshalCompiler_time_le {Key Value : Type*}
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : List (Key × Value) × Key) :
    (firstMatchMarshalCompiler encKey encValue).time input ≤
      10000 * ((encPair (encList (encPair encKey encValue)) encKey input).length + 1) := by
  simp [firstMatchMarshalCompiler, first, second, ofTransducer, pair, comp, encodeFrame, const]
  omega

private theorem firstMatchMarshalCompiler_tapeCount_le {Key Value : Type*}
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool) :
    (firstMatchMarshalCompiler encKey encValue).tapeCount ≤ 100 := by
  simp [firstMatchMarshalCompiler, first, second, ofTransducer, pair, comp, encodeFrame,
    const]

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
    simpa only [encState, streamInput, L] using
      firstMatch_state_length_le encKey encValue input j hj
  have helem : ∀ j (hj : j < input.1.length),
      (encEntry input.1[j]).length ≤ 10 * (L + 1) := by
    intro j hj
    simpa only [encEntry, L] using
      firstMatch_element_length_le encKey encValue input j hj
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
    simpa only [L] using firstMatchMarshalCompiler_time_le encKey encValue input
  have hcomp := time_comp_le (firstMatchStreamCompiler encKey encValue)
    (firstMatchMarshalCompiler encKey encValue) input
  change ((firstMatchStreamCompiler encKey encValue).comp
    (firstMatchMarshalCompiler encKey encValue)).time input ≤
      100000000 * (L + 1) ^ 2
  omega

/-- A construction-derived static tape-count bound for the retained first-match lookup. -/
theorem firstMatchCompiler_tapeCount_le {Key Value : Type*} [DecidableEq Key]
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool) :
    (firstMatchCompiler encKey encValue).tapeCount ≤ 1002 := by
  have hstream := firstMatchStreamCompiler_tapeCount_le encKey encValue
  have hmarshal := firstMatchMarshalCompiler_tapeCount_le encKey encValue
  change ((firstMatchStreamCompiler encKey encValue).comp
    (firstMatchMarshalCompiler encKey encValue)).tapeCount ≤ 1002
  simp only [comp]
  omega

/-- The actual retained first-match compiler has quadratic workspace in the complete encoded
table and query, independently of its time coordinate. Its installed program description remains
a separate static coordinate. -/
theorem firstMatchCompiler_workspace_le {Key Value : Type*} [DecidableEq Key]
    (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : List (Key × Value) × Key) :
    (firstMatchCompiler encKey encValue).workspace input ≤
      10000000000000 *
        ((encPair (encList (encPair encKey encValue)) encKey input).length + 1) ^ 2 := by
  let L := (encPair (encList (encPair encKey encValue)) encKey input).length
  let encState := encPair encKey encBool
  let encEntry := encPair encKey encValue
  let nextCompiler := firstMatchNextCompiler encKey encValue
  let emitCompiler := firstMatchEmitCompiler encKey encValue
  let finishCompiler := firstMatchFinishCompiler encKey encValue
  let streamInput : FirstMatchState Key × List (Key × Value) :=
    ((input.2, false), input.1)
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  have hstate : ∀ j, j ≤ input.1.length →
      (encState (streamState streamInput.1 firstMatchNext streamInput.2 j)).length ≤
        10 * (L + 1) := by
    intro j hj
    simpa only [encState, streamInput, L] using
      firstMatch_state_length_le encKey encValue input j hj
  have helem : ∀ j (hj : j < input.1.length),
      (encEntry input.1[j]).length ≤ 10 * (L + 1) := by
    intro j hj
    simpa only [encEntry, L] using
      firstMatch_element_length_le encKey encValue input j hj
  have hpair : ∀ j (hj : j < input.1.length),
      (encPair (encPair encKey encBool) (encPair encKey encValue)
        (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j])).length ≤
          40 * (L + 1) := by
    intro j hj
    have hs := hstate j hj.le
    have he := helem j hj
    enc_len [encState, encEntry] at hs he ⊢
  have hnext : ∀ j (hj : j < input.1.length),
      nextCompiler.workspace
        (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j]) ≤
          500000 * (L + 1) := by
    intro j hj
    have h := firstMatchNextCompiler_workspace_le encKey encValue
      (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j])
    have hp := hpair j hj
    simp only [nextCompiler] at h ⊢
    omega
  have hemit : ∀ j (hj : j < input.1.length),
      emitCompiler.workspace
        (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j]) ≤
          1000000 * (L + 1) := by
    intro j hj
    have h := firstMatchEmitCompiler_workspace_le encKey encValue
      (streamState streamInput.1 firstMatchNext streamInput.2 j, input.1[j])
    have hp := hpair j hj
    simp only [emitCompiler] at h ⊢
    omega
  have hK : K ≤ 1000 := by
    have h := firstMatchStreamCompiler_tapeCount_le encKey encValue
    change streamFoldPairTapeCount (firstMatchNextCompiler encKey encValue)
      (firstMatchEmitCompiler encKey encValue) (firstMatchFinishCompiler encKey encValue) ≤
        1000 at h
    simpa only [K, nextCompiler, emitCompiler, finishCompiler] using h
  have hkn : nextCompiler.tapeCount ≤ K := by
    simp only [K, streamFoldPairTapeCount, streamFramedNext, comp, encodeFrame]
    omega
  have hke : emitCompiler.tapeCount ≤ K := by
    simp only [K, streamFoldPairTapeCount]
    omega
  have hsMax : firstMatchSMax encKey encValue streamInput ≤
      10000000 * (L + 1) := by
    simp only [K, nextCompiler, emitCompiler, finishCompiler] at hK hkn hke
    simp only [firstMatchSMax, streamInput]
    apply Finset.sup_le
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hs := hstate j hj'.le
    have hs' := hstate (j + 1) (by omega)
    rw [streamState_succ _ _ _ hj'] at hs'
    have ha := helem j hj'
    have hn := hnext j hj'
    have he := hemit j hj'
    simp only [streamInput] at hs hs' hn he
    simp only [encState, length_encPair] at hs hs'
    simp only [encEntry, length_encPair] at ha
    simp only [nextCompiler] at hn
    simp only [emitCompiler] at he
    simp only [hj', dite_true, inputFromWordWorkspace, onWordsWorkspace,
      streamFramedNext, comp, encodeFrame, length_encPair, encBits_apply, length_frame]
    omega
  have hlMax : firstMatchLMax encKey encValue streamInput ≤ 10 * (L + 1) := by
    simp only [firstMatchLMax, streamInput]
    apply max_le
    · apply Finset.sup_le
      intro j hj
      have hj' : j ≤ input.1.length := by
        have := Finset.mem_range.mp hj
        omega
      simpa only [hj', dite_true] using hstate j hj'
    · apply Finset.sup_le
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simpa only [hj', dite_true] using helem j hj'
  have hfinish : finishCompiler.workspace
      (streamState streamInput.1 firstMatchNext streamInput.2 input.1.length) ≤ 0 := by
    simp [finishCompiler, firstMatchFinishCompiler, const]
  have hstream := streamFoldPairWorkspace_le nextCompiler emitCompiler finishCompiler
    (firstMatchSMax encKey encValue) (firstMatchLMax encKey encValue) streamInput
    (10000000 * (L + 1)) (10 * (L + 1)) 0 hsMax hlMax
    (hstate 0 (Nat.zero_le _)) (hstate input.1.length le_rfl) hfinish
  change streamFoldPairWorkspace nextCompiler emitCompiler finishCompiler
      (firstMatchSMax encKey encValue) (firstMatchLMax encKey encValue) streamInput ≤
        2 * K * (10000000 * (L + 1) + 16 * (10 * (L + 1)) + 4 * K + 26) + 0 +
          13 * (10 * (L + 1)) + 8 * finishCompiler.tapeCount + 5 * K + 43 at hstream
  have hinner : 10000000 * (L + 1) + 16 * (10 * (L + 1)) + 4 * K + 26 ≤
      10005000 * (L + 1) := by
    omega
  have htwice : 2 * K ≤ 2000 := by omega
  have hbulk := Nat.mul_le_mul htwice hinner
  have htail : 13 * (10 * (L + 1)) + 8 * finishCompiler.tapeCount + 5 * K + 43 ≤
      6000 * (L + 1) := by
    simp only [finishCompiler, firstMatchFinishCompiler, const]
    omega
  have hstreamBound :
      (firstMatchStreamCompiler encKey encValue).workspace streamInput ≤
        1000000000000 * (L + 1) ^ 2 := by
    change streamFoldPairWorkspace nextCompiler emitCompiler finishCompiler
      (firstMatchSMax encKey encValue) (firstMatchLMax encKey encValue) streamInput ≤ _
    have hB : 1 ≤ L + 1 := by omega
    exact hstream.trans (by nlinarith)
  have hmarshalTime :
      (firstMatchMarshalCompiler encKey encValue).time input ≤ 10000 * (L + 1) := by
    simpa only [L] using firstMatchMarshalCompiler_time_le encKey encValue input
  have hmarshalSpace :
      (firstMatchMarshalCompiler encKey encValue).workspace input ≤ 10000 * (L + 1) := by
    simp [firstMatchMarshalCompiler, first, second, ofTransducer, pair, comp, encodeFrame,
      const, L]
    omega
  have hmarshalTapes := firstMatchMarshalCompiler_tapeCount_le encKey encValue
  have hmax : max (firstMatchMarshalCompiler encKey encValue).tapeCount
      (firstMatchStreamCompiler encKey encValue).tapeCount ≤ 1000 :=
    max_le (hmarshalTapes.trans (by omega))
      (firstMatchStreamCompiler_tapeCount_le encKey encValue)
  have hcomp := workspace_comp_le (firstMatchStreamCompiler encKey encValue)
    (firstMatchMarshalCompiler encKey encValue) input
  change ((firstMatchStreamCompiler encKey encValue).comp
    (firstMatchMarshalCompiler encKey encValue)).workspace input ≤
      10000000000000 * (L + 1) ^ 2
  exact hcomp.trans (by nlinarith)

end Turing.MultiTapeTM.Internal.NativeCompiler
