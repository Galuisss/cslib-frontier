/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamResourceBounds

/-!
# Resource bounds for retained binary-indexed list access

This module bounds the actual retained `listGet?NatCompiler encUnary`. Its single-pass scan keeps
a binary countdown and an optional selected unary natural. The proof bounds every intermediate
state from the original encoded `(list, index)`, then applies the construction-derived stream and
composition inequalities. The program description and its static bits remain separate from these
per-input resource maps.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.time_listGetNatOptionCompiler_le`: a concrete
  quadratic time majorant for the retained optional lookup.
* `Turing.MultiTapeTM.Internal.NativeCompiler.workspace_listGetNatOptionCompiler_le`: the
  analogous concrete workspace majorant.

The construction and bounds are original formalization infrastructure.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Encodings

private theorem listGetNat_streamState_invariant (list : List ℕ) (index : ℕ) :
    ∀ j, j ≤ list.length →
      let state := streamState (index, none) listGetNatNext list j
      state.1 ≤ index ∧ ∀ value, state.2 = some value → value ∈ list := by
  intro j hj
  induction j with
  | zero =>
      simp only [streamState_zero]
      constructor
      · exact le_rfl
      · intro value hvalue
        simp at hvalue
  | succ j ih =>
      have hj' : j < list.length := by omega
      rw [show j + 1 = j + 1 by rfl, streamState_succ (index, none) listGetNatNext list hj']
      have hprevious := ih (by omega)
      generalize hstate : streamState (index, none) listGetNatNext list j = state at hprevious ⊢
      rcases state with ⟨remaining, selected⟩
      cases selected with
      | none =>
          cases remaining with
          | zero =>
              simp only [listGetNatNext, Option.isSome_none, Bool.false_eq_true, ite_false,
                ite_true]
              constructor
              · exact Nat.zero_le _
              · intro value hvalue
                have heq : list[j] = value := Option.some.inj hvalue
                subst value
                exact List.getElem_mem hj'
          | succ remaining =>
              simp only [listGetNatNext, Option.isSome_none, Bool.false_eq_true, ite_false,
                Nat.succ_ne_zero, Nat.succ_sub_one]
              constructor
              · omega
              · intro value hvalue
                simp at hvalue
      | some selected =>
          simpa only [listGetNatNext, Option.isSome_some, ite_true] using hprevious

private theorem listGetNat_state_length_le (list : List ℕ) (index j : ℕ)
    (hj : j ≤ list.length) :
    ((encPair encNat (encOption encUnary))
      (streamState (index, none) listGetNatNext list j)).length ≤
        4 * ((encPair (encList encUnary) encNat (list, index)).length + 1) := by
  let state := streamState (index, none) listGetNatNext list j
  have hinvariant := listGetNat_streamState_invariant list index j hj
  change ((encPair encNat (encOption encUnary)) state).length ≤ _
  have hindex : (encNat index).length ≤
      (encPair (encList encUnary) encNat (list, index)).length :=
    length_le_encPair_right (encList encUnary) encNat (list, index)
  have hremaining : (encNat state.1).length ≤ (encNat index).length := by
    simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hinvariant.1
  have hselected : ((encOption encUnary) state.2).length ≤
      (encPair (encList encUnary) encNat (list, index)).length + 1 := by
    cases hoption : state.2 with
    | none => simp only [encOption_none, List.length_nil]; omega
    | some value =>
        have hmem := hinvariant.2 value hoption
        have hvalue := (length_le_encList_of_mem encUnary hmem).trans
          (length_le_encPair_left (encList encUnary) encNat (list, index))
        simp only [encOption_some, List.length_cons]
        omega
  rw [length_encPair]
  omega

private theorem listGetNat_element_length_le (list : List ℕ) (index j : ℕ)
    (hj : j < list.length) :
    (encUnary list[j]).length ≤
      (encPair (encList encUnary) encNat (list, index)).length + 1 := by
  have hvalue := (length_le_encList_of_mem encUnary (List.getElem_mem hj)).trans
    (length_le_encPair_left (encList encUnary) encNat (list, index))
  omega

private theorem encNat_pred_length_le (n : ℕ) :
    (encNat (n - 1)).length ≤ (encNat n).length := by
  simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size (Nat.sub_le n 1)

private theorem listGetNatNextCompiler_time_le
    (input : (ListGetNatState ℕ) × ℕ) :
    (listGetNatNextCompiler encUnary).time input ≤
      10000 * (((encPair (encPair encNat (encOption encUnary)) encUnary) input).length + 1) := by
  rcases input with ⟨⟨remaining, selected⟩, element⟩
  have hpred := encNat_pred_length_le remaining
  cases selected <;> cases remaining <;>
    simp [listGetNatNextCompiler, ofOutputEq, ofInputEq, ite, pair, comp,
      first, second,
      optionIsSomeTest, optionIsSomeBool, boolToTest, natIsZeroTest, natIsZeroBool,
      boolDecoder, natPred, optionSome, const, ofTransducer, encodeFrame, encPair_apply,
      length_frame, encNat_apply, encUnary_apply, encTest_true, encTest_false] at hpred ⊢
    <;> omega

private theorem listGetNatNextCompiler_workspace_le
    (input : (ListGetNatState ℕ) × ℕ) :
    (listGetNatNextCompiler encUnary).workspace input ≤
      10000 * (((encPair (encPair encNat (encOption encUnary)) encUnary) input).length + 1) := by
  rcases input with ⟨⟨remaining, selected⟩, element⟩
  have hpred := encNat_pred_length_le remaining
  cases selected <;> cases remaining <;>
    simp [listGetNatNextCompiler, ofOutputEq, ofInputEq, ite, pair, comp,
      first, second,
      optionIsSomeTest, optionIsSomeBool, boolToTest, natIsZeroTest, natIsZeroBool,
      boolDecoder, natPred, optionSome, const, ofTransducer, encodeFrame, encPair_apply,
      length_frame, encNat_apply, encUnary_apply, encTest_true, encTest_false] at hpred ⊢
    <;> omega

private theorem listGetNatNextCompiler_tapeCount_le :
    (listGetNatNextCompiler encUnary).tapeCount ≤ 100 := by
  simp [listGetNatNextCompiler, ofOutputEq, ofInputEq, ite, pair, comp, first, second,
    optionIsSomeTest, optionIsSomeBool, boolToTest, natIsZeroTest, natIsZeroBool,
    boolDecoder, natPred, optionSome, const, ofTransducer, encodeFrame]

private theorem listGetNatOptionStreamCompiler_tapeCount_le :
    (listGetNatOptionStreamCompiler encUnary).tapeCount ≤ 200 := by
  change streamFoldPairTapeCount (listGetNatNextCompiler encUnary)
    (listGetNatEmitCompiler encUnary) (listGetNatOptionFinishCompiler encUnary) ≤ 200
  have hnext := listGetNatNextCompiler_tapeCount_le
  simp only [streamFoldPairTapeCount, streamFramedNext, streamUnframedFinish,
    listGetNatEmitCompiler, listGetNatOptionFinishCompiler, const, comp, encodeFrame,
    unframeValue, second, ofTransducer]
  omega

private theorem listGetNatMarshalCompiler_tapeCount_le :
    (listGetNatMarshalCompiler encUnary).tapeCount ≤ 20 := by
  simp [listGetNatMarshalCompiler, pair, comp, first, second, const, ofTransducer, encodeFrame]

private theorem listGetNatMarshalCompiler_time_le (input : List ℕ × ℕ) :
    (listGetNatMarshalCompiler encUnary).time input ≤
      1000 * ((encPair (encList encUnary) encNat input).length + 1) := by
  change ((((second (encList encUnary) encNat).pair
    (const (encPair (encList encUnary) encNat) (encOption encUnary) none)).pair
      (first (encList encUnary) encNat)).time input) ≤ _
  simp [pair, comp, first, second, const, ofTransducer, encodeFrame,
    encPair_apply, length_frame]
  omega

private theorem listGetNatMarshalCompiler_workspace_le (input : List ℕ × ℕ) :
    (listGetNatMarshalCompiler encUnary).workspace input ≤
      1000 * ((encPair (encList encUnary) encNat input).length + 1) := by
  change ((((second (encList encUnary) encNat).pair
    (const (encPair (encList encUnary) encNat) (encOption encUnary) none)).pair
      (first (encList encUnary) encNat)).workspace input) ≤ _
  simp [pair, comp, first, second, const, ofTransducer, encodeFrame,
    encPair_apply, length_frame]
  omega

private theorem listGetNatLMax_le (list : List ℕ) (index : ℕ) :
    listGetNatLMax encUnary ((index, none), list) ≤
      4 * ((encPair (encList encUnary) encNat (list, index)).length + 1) := by
  simp only [listGetNatLMax]
  apply max_le
  · apply Finset.sup_le
    intro j hj
    have hj' : j ≤ list.length := by
      have := Finset.mem_range.mp hj
      omega
    simp only [hj', dite_true]
    exact listGetNat_state_length_le list index j hj'
  · apply Finset.sup_le
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [hj', dite_true]
    exact (listGetNat_element_length_le list index j hj').trans (by omega)

private theorem listGetNatOptionSMax_le (list : List ℕ) (index : ℕ) :
    listGetNatOptionSMax encUnary ((index, none), list) ≤
      1000000 * ((encPair (encList encUnary) encNat (list, index)).length + 1) := by
  apply Finset.sup_le
  intro j hj
  have hj' := Finset.mem_range.mp hj
  change j < list.length at hj'
  let state := streamState (index, none) listGetNatNext list j
  let pair : (ListGetNatState ℕ) × ℕ := (state, list[j])
  have hstate := listGetNat_state_length_le list index j hj'.le
  have helement := listGetNat_element_length_le list index j hj'
  have hpair :
      ((encPair (encPair encNat (encOption encUnary)) encUnary) pair).length ≤
        10 * ((encPair (encList encUnary) encNat (list, index)).length + 1) := by
    dsimp only [pair, state]
    rw [length_encPair]
    omega
  have hnext := listGetNatNextCompiler_workspace_le pair
  have hnextState := listGetNat_state_length_le list index (j + 1) (by omega)
  have hnextTapes := listGetNatNextCompiler_tapeCount_le
  rw [streamState_succ (index, none) listGetNatNext list hj'] at hnextState
  simp only [hj', dite_true,
    inputFromWordWorkspace, onWordsWorkspace, streamFoldPairTapeCount,
    streamFramedNext, streamUnframedFinish, listGetNatEmitCompiler,
    listGetNatOptionFinishCompiler, const, comp, encodeFrame, unframeValue,
    second, ofTransducer]
  dsimp only [pair, state] at hnext hpair ⊢
  simp only [encBits_apply, length_frame] at hnextState ⊢
  omega

private theorem listGetNatOptionStreamCompiler_time_le (list : List ℕ) (index : ℕ) :
    (listGetNatOptionStreamCompiler encUnary).time ((index, none), list) ≤
      1000000 * ((encPair (encList encUnary) encNat (list, index)).length + 1) ^ 2 := by
  change streamFoldPairTime (listGetNatNextCompiler encUnary)
    (listGetNatEmitCompiler encUnary) (listGetNatOptionFinishCompiler encUnary)
      ((index, none), list) ≤ _
  let B := (encPair (encList encUnary) encNat (list, index)).length + 1
  let lengthBound := 10 * B
  have hinput :
      ((encPair (encPair encNat (encOption encUnary)) (encList encUnary))
        ((index, none), list)).length ≤ lengthBound := by
    have hstate := listGetNat_state_length_le list index 0 (Nat.zero_le _)
    have hlist := length_le_encPair_left (encList encUnary) encNat (list, index)
    simp only [lengthBound, B, length_encPair, encOption_none, List.length_nil] at hstate ⊢
    omega
  have hstate : ∀ j, j ≤ list.length →
      ((encPair encNat (encOption encUnary))
        (streamState (index, none) listGetNatNext list j)).length ≤ lengthBound := by
    intro j hj
    exact (listGetNat_state_length_le list index j hj).trans (by
      dsimp only [lengthBound, B]
      omega)
  have helem : ∀ j (hj : j < list.length),
      (encUnary list[j]).length ≤ lengthBound := by
    intro j hj
    exact (listGetNat_element_length_le list index j hj).trans (by
      dsimp only [lengthBound, B]
      omega)
  have hemit : ∀ j (hj : j < list.length),
      (listGetNatEmitCompiler encUnary).time
        (streamState (index, none) listGetNatNext list j, list[j]) ≤ 1 := by
    intro j hj
    simp [listGetNatEmitCompiler, const]
  have hnext : ∀ j (hj : j < list.length),
      (listGetNatNextCompiler encUnary).time
        (streamState (index, none) listGetNatNext list j, list[j]) ≤ 200000 * B := by
    intro j hj
    have h := listGetNatNextCompiler_time_le
      (streamState (index, none) listGetNatNext list j, list[j])
    have hs := listGetNat_state_length_le list index j hj.le
    have he := listGetNat_element_length_le list index j hj
    have hp :
        ((encPair (encPair encNat (encOption encUnary)) encUnary)
          (streamState (index, none) listGetNatNext list j, list[j])).length ≤ 10 * B := by
      rw [length_encPair]
      dsimp only [B] at hs he ⊢
      omega
    omega
  have hfinish :
      (listGetNatOptionFinishCompiler encUnary).time
        (streamState (index, none) listGetNatNext list list.length) ≤ 100 * B := by
    have hs := hstate list.length le_rfl
    simp only [listGetNatOptionFinishCompiler, second, ofTransducer]
    simp only [lengthBound] at hs
    omega
  have h := streamFoldPairTime_le (listGetNatNextCompiler encUnary)
    (listGetNatEmitCompiler encUnary) (listGetNatOptionFinishCompiler encUnary)
    ((index, none), list) 1 (200000 * B) (100 * B) lengthBound
    hinput hstate helem hemit hnext hfinish
  have hcount : list.length ≤ B := by
    have hl := length_le_length_encList encUnary list
    have hp := length_le_encPair_left (encList encUnary) encNat (list, index)
    change (encList encUnary list).length ≤
      (encPair (encList encUnary) encNat (list, index)).length at hp
    change list.length ≤ (encPair (encList encUnary) encNat (list, index)).length + 1
    omega
  have hB : 1 ≤ B := by dsimp only [B]; omega
  dsimp only [lengthBound] at h
  have hround : 1 + 200000 * B + 46 * (10 * B) + 60 ≤ 201000 * B := by
    omega
  have hmain :
      list.length * (1 + 200000 * B + 46 * (10 * B) + 60) ≤
        201000 * B ^ 2 := by
    calc
      _ ≤ B * (201000 * B) := Nat.mul_le_mul hcount hround
      _ = 201000 * B ^ 2 := by ring
  have htail : 100 * B + 24 * (10 * B) + 40 ≤ 1000 * B ^ 2 := by
    nlinarith
  dsimp only [B] at h hmain htail hB ⊢
  nlinarith

private theorem listGetNatOptionStreamCompiler_workspace_le (list : List ℕ) (index : ℕ) :
    (listGetNatOptionStreamCompiler encUnary).workspace ((index, none), list) ≤
      1000000000 * ((encPair (encList encUnary) encNat (list, index)).length + 1) ^ 2 := by
  change streamFoldPairWorkspace (listGetNatNextCompiler encUnary)
    (listGetNatEmitCompiler encUnary) (listGetNatOptionFinishCompiler encUnary)
      (listGetNatOptionSMax encUnary) (listGetNatLMax encUnary) ((index, none), list) ≤ _
  let B := (encPair (encList encUnary) encNat (list, index)).length + 1
  have hsMax := listGetNatOptionSMax_le list index
  have hlMax := listGetNatLMax_le list index
  have hinitial := listGetNat_state_length_le list index 0 (Nat.zero_le _)
  have hfinal := listGetNat_state_length_le list index list.length le_rfl
  have hfinish :
      (listGetNatOptionFinishCompiler encUnary).workspace
        (streamState (index, none) listGetNatNext list list.length) ≤ 0 := by
    simp [listGetNatOptionFinishCompiler, second, ofTransducer]
  have h := streamFoldPairWorkspace_le (listGetNatNextCompiler encUnary)
    (listGetNatEmitCompiler encUnary) (listGetNatOptionFinishCompiler encUnary)
    (listGetNatOptionSMax encUnary) (listGetNatLMax encUnary) ((index, none), list)
    (1000000 * B) (4 * B) 0 (by simpa only [B] using hsMax)
    (by simpa only [B] using hlMax) (by simpa only [B, streamState_zero] using hinitial)
    (by simpa only [B] using hfinal) hfinish
  let K := streamFoldPairTapeCount (listGetNatNextCompiler encUnary)
    (listGetNatEmitCompiler encUnary) (listGetNatOptionFinishCompiler encUnary)
  have hK : K ≤ 200 := by
    dsimp only [K]
    have hnext := listGetNatNextCompiler_tapeCount_le
    simp only [streamFoldPairTapeCount, streamFramedNext, streamUnframedFinish,
      listGetNatEmitCompiler, listGetNatOptionFinishCompiler, const, comp, encodeFrame,
      unframeValue, second, ofTransducer]
    omega
  refine h.trans ?_
  change 2 * K * (1000000 * B + 16 * (4 * B) + 4 * K + 26) + 0 +
      13 * (4 * B) + 8 * (listGetNatOptionFinishCompiler encUnary).tapeCount +
        5 * K + 43 ≤ _
  simp only [listGetNatOptionFinishCompiler, second, ofTransducer]
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hinner : 1000000 * B + 16 * (4 * B) + 4 * K + 26 ≤
      1001000 * B := by omega
  have htwice : 2 * K ≤ 400 := by omega
  have hbulk : 2 * K * (1000000 * B + 16 * (4 * B) + 4 * K + 26) ≤
      400 * (1001000 * B) := Nat.mul_le_mul htwice hinner
  have htail : 13 * (4 * B) + 8 * 0 + 5 * K + 43 ≤ 1100 * B := by omega
  dsimp only [B]
  nlinarith

/-- Concrete quadratic running-time majorant for the actual retained optional binary-indexed
lookup. The bound concerns the generated program's per-input time map; its description size is
accounted for separately by generator certificates. -/
theorem time_listGetNatOptionCompiler_le (input : List ℕ × ℕ) :
    (listGet?NatCompiler encUnary).time input ≤
      10000000 * ((encPair (encList encUnary) encNat input).length + 1) ^ 2 := by
  have hcomp := time_comp_le (listGetNatOptionStreamCompiler encUnary)
    (listGetNatMarshalCompiler encUnary) input
  have hmarshal := listGetNatMarshalCompiler_time_le input
  have hstream := listGetNatOptionStreamCompiler_time_le input.1 input.2
  have hone : 1 ≤ (encPair (encList encUnary) encNat input).length + 1 := by omega
  exact hcomp.trans (by nlinarith)

/-- Concrete quadratic workspace majorant for the actual retained optional binary-indexed
lookup. The retained compiler's original workspace map is bounded rather than replaced. -/
theorem workspace_listGetNatOptionCompiler_le (input : List ℕ × ℕ) :
    (listGet?NatCompiler encUnary).workspace input ≤
      10000000000 * ((encPair (encList encUnary) encNat input).length + 1) ^ 2 := by
  have hcomp := workspace_comp_le (listGetNatOptionStreamCompiler encUnary)
    (listGetNatMarshalCompiler encUnary) input
  have hmarshalTime := listGetNatMarshalCompiler_time_le input
  have hmarshalSpace := listGetNatMarshalCompiler_workspace_le input
  have hstream := listGetNatOptionStreamCompiler_workspace_le input.1 input.2
  have hone : 1 ≤ (encPair (encList encUnary) encNat input).length + 1 := by omega
  have hmarshalTapes := listGetNatMarshalCompiler_tapeCount_le
  have hstreamTapes := listGetNatOptionStreamCompiler_tapeCount_le
  have hmax : max (listGetNatMarshalCompiler encUnary).tapeCount
      (listGetNatOptionStreamCompiler encUnary).tapeCount ≤ 200 :=
    max_le (hmarshalTapes.trans (by omega)) hstreamTapes
  exact hcomp.trans (by nlinarith)

end Turing.MultiTapeTM.Internal.NativeCompiler
