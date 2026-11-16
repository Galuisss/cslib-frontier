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
      simp only [streamState_zero, Prod.fst, Prod.snd]
      exact ⟨le_rfl, fun _ h => Option.noConfusion h⟩
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
              simp only [listGetNatNext, Option.isSome_none, Bool.false_eq_true, if_false,
                if_pos rfl, Prod.fst, Prod.snd]
              constructor
              · exact Nat.zero_le _
              · intro value hvalue
                have heq : list[j] = value := Option.some.inj hvalue
                subst value
                exact List.getElem_mem hj'
          | succ remaining =>
              simp only [listGetNatNext, Option.isSome_none, Bool.false_eq_true, if_false,
                Nat.succ_ne_zero, Nat.succ_sub_one, Prod.fst, Prod.snd]
              constructor
              · omega
              · intro value hvalue
                exact Option.noConfusion hvalue
      | some selected =>
          simpa only [listGetNatNext, Option.isSome_some, if_true] using hprevious

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
    | none => simp only [hoption, encOption_none, List.length_nil]; omega
    | some value =>
        have hmem := hinvariant.2 value hoption
        have hvalue := (length_le_encList_of_mem encUnary hmem).trans
          (length_le_encPair_left (encList encUnary) encNat (list, index))
        simp only [hoption, encOption_some, List.length_cons]
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

private theorem listGetNatNextCompiler_time_le
    (input : (ListGetNatState ℕ) × ℕ) :
    (listGetNatNextCompiler encUnary).time input ≤
      10000 * (((encPair (encPair encNat (encOption encUnary)) encUnary) input).length + 1) := by
  rcases input with ⟨⟨remaining, selected⟩, element⟩
  cases selected <;> cases remaining <;>
    simp [listGetNatNextCompiler, listGetNatNext, ite, pair, comp, first, second,
      optionIsSomeTest, optionIsSomeBool, boolToTest, natIsZeroTest, natIsZeroBool,
      natPred, optionSome, const, ofTransducer, encodeFrame, encPair_apply, length_frame,
      encNat_apply, encUnary_apply]
    <;> omega

private theorem listGetNatNextCompiler_workspace_le
    (input : (ListGetNatState ℕ) × ℕ) :
    (listGetNatNextCompiler encUnary).workspace input ≤
      10000 * (((encPair (encPair encNat (encOption encUnary)) encUnary) input).length + 1) := by
  rcases input with ⟨⟨remaining, selected⟩, element⟩
  cases selected <;> cases remaining <;>
    simp [listGetNatNextCompiler, listGetNatNext, ite, pair, comp, first, second,
      optionIsSomeTest, optionIsSomeBool, boolToTest, natIsZeroTest, natIsZeroBool,
      natPred, optionSome, const, ofTransducer, encodeFrame, encPair_apply, length_frame,
      encNat_apply, encUnary_apply]
    <;> omega

private theorem listGetNatMarshalCompiler_time_le (input : List ℕ × ℕ) :
    (listGetNatMarshalCompiler encUnary).time input ≤
      1000 * ((encPair (encList encUnary) encNat input).length + 1) := by
  simp [listGetNatMarshalCompiler, pair, first, second, const, ofTransducer, encodeFrame,
    encPair_apply, length_frame]
  omega

private theorem listGetNatMarshalCompiler_workspace_le (input : List ℕ × ℕ) :
    (listGetNatMarshalCompiler encUnary).workspace input ≤
      1000 * ((encPair (encList encUnary) encNat input).length + 1) := by
  simp [listGetNatMarshalCompiler, pair, first, second, const, ofTransducer, encodeFrame,
    encPair_apply, length_frame]
  omega

private theorem listGetNatLMax_le (list : List ℕ) (index : ℕ) :
    listGetNatLMax encUnary ((index, none), list) ≤
      4 * ((encPair (encList encUnary) encNat (list, index)).length + 1) := by
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
  let state := streamState (index, none) listGetNatNext list j
  let pair : (ListGetNatState ℕ) × ℕ := (state, list[j])
  have hstate := listGetNat_state_length_le list index j hj'.le
  have helement := listGetNat_element_length_le list index j hj'
  have hpair :
      ((encPair (encPair encNat (encOption encUnary)) encUnary) pair).length ≤
        9 * ((encPair (encList encUnary) encNat (list, index)).length + 1) := by
    simp only [pair, length_encPair]
    omega
  have hnext := listGetNatNextCompiler_workspace_le pair
  simp only [listGetNatOptionSMax, hj', dite_true, pair, state,
    inputFromWordWorkspace, onWordsWorkspace, streamFoldPairTapeCount,
    streamFramedNext, streamUnframedFinish, listGetNatEmitCompiler,
    listGetNatOptionFinishCompiler, ofOutputEq, const, comp, encodeFrame, unframeValue,
    second, ofTransducer]
  simp only [pair, state] at hnext hpair ⊢
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
    exact (listGetNat_state_length_le list index j hj).trans (by simp [lengthBound, B]; omega)
  have helem : ∀ j (hj : j < list.length),
      (encUnary list[j]).length ≤ lengthBound := by
    intro j hj
    exact (listGetNat_element_length_le list index j hj).trans (by simp [lengthBound, B]; omega)
  have hemit : ∀ j (hj : j < list.length),
      (listGetNatEmitCompiler encUnary).time
        (streamState (index, none) listGetNatNext list j, list[j]) ≤ 1 := by
    intro j hj
    simp [listGetNatEmitCompiler, const]
  have hnext : ∀ j (hj : j < list.length),
      (listGetNatNextCompiler encUnary).time
        (streamState (index, none) listGetNatNext list j, list[j]) ≤ 100000 * B := by
    intro j hj
    have h := listGetNatNextCompiler_time_le
      (streamState (index, none) listGetNatNext list j, list[j])
    have hs := hstate j hj.le
    have he := helem j hj
    have hp :
        ((encPair (encPair encNat (encOption encUnary)) encUnary)
          (streamState (index, none) listGetNatNext list j, list[j])).length ≤ 21 * B := by
      simp only [length_encPair]
      simp only [lengthBound] at hs he
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
    ((index, none), list) 1 (100000 * B) (100 * B) lengthBound
    hinput hstate helem hemit hnext hfinish
  have hcount : list.length ≤ B := by
    have hl := length_le_length_encList encUnary list
    have hp := length_le_encPair_left (encList encUnary) encNat (list, index)
    simp only [B]
    omega
  dsimp only [lengthBound] at h
  nlinarith

private theorem listGetNatOptionStreamCompiler_workspace_le (list : List ℕ) (index : ℕ) :
    (listGetNatOptionStreamCompiler encUnary).workspace ((index, none), list) ≤
      100000000 * ((encPair (encList encUnary) encNat (list, index)).length + 1) ^ 2 := by
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
    (by simpa only [B] using hlMax) (by simpa only [B] using hinitial)
    (by simpa only [B] using hfinal) hfinish
  refine h.trans ?_
  simp only [streamFoldPairTapeCount, streamFramedNext, streamUnframedFinish,
    listGetNatNextCompiler, listGetNatEmitCompiler, listGetNatOptionFinishCompiler,
    ofOutputEq, ite, pair, comp, first, second, optionIsSomeTest, optionIsSomeBool,
    boolToTest, natIsZeroTest, natIsZeroBool, natPred, optionSome, const, ofTransducer,
    encodeFrame, unframeValue]
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
      1000000000 * ((encPair (encList encUnary) encNat input).length + 1) ^ 2 := by
  have hcomp := workspace_comp_le (listGetNatOptionStreamCompiler encUnary)
    (listGetNatMarshalCompiler encUnary) input
  have hmarshalTime := listGetNatMarshalCompiler_time_le input
  have hmarshalSpace := listGetNatMarshalCompiler_workspace_le input
  have hstream := listGetNatOptionStreamCompiler_workspace_le input.1 input.2
  have hone : 1 ≤ (encPair (encList encUnary) encNat input).length + 1 := by omega
  simp only [listGetNatMarshalCompiler, pair, first, second, const, ofTransducer,
    encodeFrame, comp, Nat.max_eq_left (Nat.zero_le _)] at hcomp
  exact hcomp.trans (by nlinarith)

end Turing.MultiTapeTM.Internal.NativeCompiler
