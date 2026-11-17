/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Conditional
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Equality
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamResourceBounds

/-!
# Named native deterministic-universal primitives

This module retains the concrete machines used by encoded deterministic and probabilistic
universal steps. Each construction is assembled from named native projections, streaming codecs,
arithmetic machines and conditionals; no semantic function is installed as an opaque machine.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.inputSymbol`: retained binary-position input lookup.
* `Turing.MultiTapeTM.Internal.NativeCompiler.moveInput`: retained boundary-aware input-head move.
* `Turing.MultiTapeTM.Internal.NativeCompiler.actInputMove`, `.actWorkActions`, `.actOutput`,
  `.actState`: retained ordinary-action projections.
* `Turing.MultiTapeTM.Internal.NativeCompiler.actProjectionResources_le`: concrete resource
  bounds for those retained action projections.
* `Turing.MultiTapeTM.Internal.NativeCompiler.tapeRead`, `.tapeApply`, `.reads`, `.applyTapes`:
  retained work-tape reads and updates.
* `Turing.MultiTapeTM.Internal.NativeCompiler.tapeRead_time_le`, `.tapeRead_workspace_le`:
  concrete bounds for the actual retained head-read compiler.
* `Turing.MultiTapeTM.Internal.NativeCompiler.tapeApply_time_le`, `.tapeApply_workspace_le`,
  `.tapeApply_tapeCount_le`: concrete resource bounds for the actual retained tape-action compiler.
* `Turing.MultiTapeTM.Internal.NativeCompiler.applyTapes_time_le`, `.applyTapes_workspace_le`,
  `.applyTapes_tapeCount_le`: concrete resource bounds for the actual retained list-action compiler.
* `Turing.MultiTapeTM.Internal.NativeCompiler.intUnaryPayload`, `.intUnaryNonnegativeTest`:
  retained signed-unary tag and payload access.
* `Turing.MultiTapeTM.Internal.NativeCompiler.intSucc`, `.intPred`, `.intMove`: retained
  signed-unary successor, predecessor and sign-directed movement.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM.Universal

/-- Retained projection of the ordinary input-head movement. -/
noncomputable def actInputMove : NativeCompiler Act.inputTape eAct encSign :=
  (first encSign (encPair (encList eTA) (encPair eSym eSym))).ofInputEq
    (fun action : Act => (action.inputTape, action.workTapes, action.output, action.state))
    fun _ => rfl

/-- Retained projection of the ordinary-action tail after input movement. -/
noncomputable def actTail₃ :
    NativeCompiler (fun action : Act => (action.workTapes, action.output, action.state))
      eAct (encPair (encList eTA) (encPair eSym eSym)) :=
  (second encSign (encPair (encList eTA) (encPair eSym eSym))).ofInputEq
    (fun action : Act => (action.inputTape, action.workTapes, action.output, action.state))
    fun _ => rfl

/-- Retained projection of work-tape actions. -/
noncomputable def actWorkActions :
    NativeCompiler Act.workTapes eAct (encList eTA) :=
  (first (encList eTA) (encPair eSym eSym)).comp actTail₃

/-- Retained ordinary-action output and successor tail. -/
noncomputable def actTail₂ :
    NativeCompiler (fun action : Act => (action.output, action.state)) eAct (encPair eSym eSym) :=
  (second (encList eTA) (encPair eSym eSym)).comp actTail₃

/-- Retained projection of the optional ordinary output symbol. -/
noncomputable def actOutput : NativeCompiler Act.output eAct eSym :=
  (first eSym eSym).comp actTail₂

/-- Retained projection of the optional ordinary successor tag. -/
noncomputable def actState : NativeCompiler Act.state eAct eSym :=
  (second eSym eSym).comp actTail₂

/-- The four retained ordinary-action projections have linear actual time and workspace, with a
uniform construction-derived static tape-count bound. -/
theorem actProjectionResources_le (input : Act) :
    actInputMove.time input ≤ 1000000 * ((eAct input).length + 1) ∧
      actInputMove.workspace input ≤ 1000000 * ((eAct input).length + 1) ∧
      actInputMove.tapeCount ≤ 100 ∧
      actWorkActions.time input ≤ 1000000 * ((eAct input).length + 1) ∧
      actWorkActions.workspace input ≤ 1000000 * ((eAct input).length + 1) ∧
      actWorkActions.tapeCount ≤ 100 ∧
      actOutput.time input ≤ 1000000 * ((eAct input).length + 1) ∧
      actOutput.workspace input ≤ 1000000 * ((eAct input).length + 1) ∧
      actOutput.tapeCount ≤ 100 ∧
      actState.time input ≤ 1000000 * ((eAct input).length + 1) ∧
      actState.workspace input ≤ 1000000 * ((eAct input).length + 1) ∧
      actState.tapeCount ≤ 100 := by
  simp [actInputMove, actWorkActions, actOutput, actState, actTail₂, actTail₃,
    first, second, comp, ofInputEq, ofTransducer]
  omega

/-- Payload stored after the signed-unary tag bit. The negative branch is used only when clients
explicitly accept that constructor. -/
@[expose] def intUnaryPayload : ℤ → ℕ
  | .ofNat value => value
  | .negSucc value => value

/-- Retained removal of the signed-unary tag bit. -/
@[expose] noncomputable def intUnaryPayloadCompiler :
    NativeCompiler intUnaryPayload encIntUnary encUnary :=
  (tailDecoder.ofInputEq (fun value => encIntUnary value) fun _ => rfl).ofOutputEq
    fun value => by cases value <;> simp [intUnaryPayload, encBits_apply, encUnary_apply]

/-- Retained nonnegative signed-unary constructor test. -/
@[expose] noncomputable def intUnaryNonnegativeTest :
    NativeCompiler (fun value : ℤ => decide (0 ≤ value)) encIntUnary encTest := by
  let sign : NativeCompiler (fun value : ℤ => (encIntUnary value).headD false)
      encIntUnary encBool :=
    boolDecoder.ofInputEq (fun value : ℤ => encIntUnary value) fun _ => by
      simp only [encBits_apply]
  let negative := boolToTest.comp sign
  let yes := const encIntUnary encTest true
  let no := const encIntUnary encTest false
  exact (ite negative no yes).ofOutputEq fun value => by cases value <;> rfl

/-- Retained signed-unary successor through the existing concrete transducer. -/
@[expose] noncomputable def intSucc :
    NativeCompiler (fun value : ℤ => value + 1) encIntUnary encIntUnary :=
  ofTransducer EncIntUnary.succT Fin.valEmbedding fun value => by
    exact (EncIntUnary.run_succT value).symm

/-- Retained signed-unary predecessor through the existing concrete transducer. -/
@[expose] noncomputable def intPred :
    NativeCompiler (fun value : ℤ => value - 1) encIntUnary encIntUnary :=
  ofTransducer EncIntUnary.predT Fin.valEmbedding fun value => by
    exact (EncIntUnary.run_predT value).symm

/-- Retained sign-directed integer movement. -/
@[expose] noncomputable def intMove :
    NativeCompiler (fun input : ℤ × SignType => input.1 + input.2)
      (encPair encIntUnary encSign) encIntUnary := by
  let value := first encIntUnary encSign
  let movement := second encIntUnary encSign
  let signIs (sign : SignType) := (wordEqTest encSign).comp
    (movement.pair (const (encPair encIntUnary encSign) encSign sign))
  let stay := value
  let positive := intSucc.comp value
  let negative := intPred.comp value
  refine (ite (signIs .zero) stay (ite (signIs .neg) negative positive)).ofOutputEq ?_
  rintro ⟨value, movement⟩
  cases movement <;> simp [sub_eq_add_neg]

/-- Retained projection of a zipper's two cell lists. -/
noncomputable def tapeTail :
    NativeCompiler (fun tape : Tape => (tape.left, tape.right)) eTape
      (encPair (encList eSym) (encList eSym)) :=
  (second encIntUnary (encPair (encList eSym) (encList eSym))).ofInputEq
    (fun tape : Tape => (tape.head, tape.left, tape.right)) fun _ => rfl

/-- Retained projection of a zipper's signed head position. -/
noncomputable def tapeHead : NativeCompiler Tape.head eTape encIntUnary :=
  (first encIntUnary (encPair (encList eSym) (encList eSym))).ofInputEq
    (fun tape : Tape => (tape.head, tape.left, tape.right)) fun _ => rfl

/-- Retained projection of cells left of the work-tape head. -/
noncomputable def tapeLeft : NativeCompiler Tape.left eTape (encList eSym) :=
  (first (encList eSym) (encList eSym)).comp tapeTail

/-- Retained projection of the cells at and right of the work-tape head. -/
noncomputable def tapeRight :
    NativeCompiler Tape.right eTape (encList eSym) :=
  (second (encList eSym) (encList eSym)).comp tapeTail

/-- Retained work-tape head read, returning blank on an empty right half. -/
@[expose] noncomputable def tapeRead : NativeCompiler Tape.read eTape eSym :=
  ((listHeadD none eSym).comp tapeRight).ofOutputEq fun tape => by
    rfl

/-- The actual retained work-head reader runs in time linear in the encoded zipper. -/
theorem tapeRead_time_le (tape : Tape) :
    tapeRead.time tape ≤ 1000 * ((eTape tape).length + 1) := by
  obtain ⟨head, left, right⟩ := tape
  cases right <;>
    simp [tapeRead, tapeRight, tapeTail, listHeadD, listIsEmpty, listHeadPayload,
      second, boolToTest, isEmpty, unframeDecoder, ofTransducer, comp, ite, const,
      ofInputEq, ofOutputEq, encTest_false, encTest_true] <;>
    omega

/-- The actual retained work-head reader uses workspace linear in the encoded zipper,
independently of its time coordinate. -/
theorem tapeRead_workspace_le (tape : Tape) :
    tapeRead.workspace tape ≤ 1000 * ((eTape tape).length + 1) := by
  obtain ⟨head, left, right⟩ := tape
  have hread := length_eSym_read_le ⟨head, left, right⟩
  cases right <;>
    simp [tapeRead, tapeRight, tapeTail, listHeadD, listIsEmpty, listHeadPayload,
      boolToTest, isEmpty, unframeDecoder, ofTransducer, comp, ite, const, ofInputEq, ofOutputEq,
      encTest_false, encTest_true] at hread ⊢ <;>
    simp only [second, ofTransducer] <;>
    omega

/-- A construction-derived static tape-count bound for the retained work-head reader. -/
theorem tapeRead_tapeCount_le : tapeRead.tapeCount ≤ 100 := by
  simp [tapeRead, tapeRight, tapeTail, listHeadD, listIsEmpty, listHeadPayload,
    second, boolToTest, isEmpty, unframeDecoder, ofTransducer, comp, ite, const,
    ofInputEq, ofOutputEq]

/-- Retained work-tape write, rebuilding the zipper from named field/list machines. -/
@[expose] noncomputable def tapeWrite :
    NativeCompiler (fun input : Tape × Option ℕ => input.1.write input.2)
      (encPair eTape eSym) eTape := by
  let tape := first eTape eSym
  let symbol := second eTape eSym
  let head := tapeHead.comp tape
  let left := tapeLeft.comp tape
  let right := tapeRight.comp tape
  let rightTail := (listTailCompiler eSym).comp right
  let newRight := (listConsCompiler eSym).comp (symbol.pair rightTail)
  exact head.pair (left.pair newRight) |>.ofOutputEq fun _ => rfl

private theorem tapeWrite_time_le (input : Tape × Option ℕ) :
    tapeWrite.time input ≤
      1000000 * ((encPair eTape eSym input).length + 1) := by
  rcases input with ⟨⟨head, left, right⟩, symbol⟩
  have htail := SizedListEncoding.length_drop_le (encA := eSym)
    (encL := encList eSym) right 1
  simp [tapeWrite, tapeHead, tapeLeft, tapeRight, tapeTail, listTailCompiler,
    listConsCompiler, dropFrameDecoder, pair, append, comp, first, second, encodeFrame,
    ofInputEq, ofOutputEq, ofTransducer, eTape_apply] at htail ⊢
  omega

private theorem tapeWrite_workspace_le (input : Tape × Option ℕ) :
    tapeWrite.workspace input ≤
      1000000 * ((encPair eTape eSym input).length + 1) := by
  rcases input with ⟨⟨head, left, right⟩, symbol⟩
  have htail := SizedListEncoding.length_drop_le (encA := eSym)
    (encL := encList eSym) right 1
  simp [tapeWrite, tapeHead, tapeLeft, tapeRight, tapeTail, listTailCompiler,
    listConsCompiler, dropFrameDecoder, pair, append, comp, first, second, encodeFrame,
    ofInputEq, ofOutputEq, ofTransducer, eTape_apply] at htail ⊢
  omega

private theorem tapeWrite_tapeCount_le : tapeWrite.tapeCount ≤ 100 := by
  simp [tapeWrite, tapeHead, tapeLeft, tapeRight, tapeTail, listTailCompiler,
    listConsCompiler, dropFrameDecoder, pair, append, comp, first, second, encodeFrame,
    ofInputEq, ofOutputEq, ofTransducer]

/-- Retained positive work-tape move. -/
@[expose] noncomputable def tapeMovePos :
    NativeCompiler (fun tape : Tape => tape.move .pos) eTape eTape := by
  let head := intSucc.comp tapeHead
  let left := (listConsCompiler eSym).comp (tapeRead.pair tapeLeft)
  let right := (listTailCompiler eSym).comp tapeRight
  exact head.pair (left.pair right) |>.ofOutputEq fun _ => rfl

private theorem tapeMovePos_time_le (tape : Tape) :
    tapeMovePos.time tape ≤ 1000000 * ((eTape tape).length + 1) := by
  obtain ⟨head, left, right⟩ := tape
  have hhead := length_encIntUnary_add_one_le head
  have hread := length_eSym_read_le ⟨head, left, right⟩
  cases right <;>
    simp [tapeMovePos, intSucc, tapeHead, tapeLeft, tapeRight, tapeTail, tapeRead,
      listHeadD, listIsEmpty, listHeadPayload, listTailCompiler, listConsCompiler,
      boolToTest, isEmpty, unframeDecoder, dropFrameDecoder, pair, append, comp, first,
      second, const, ite, encodeFrame, ofInputEq, ofOutputEq, ofTransducer,
      encTest_false, encTest_true, eTape_apply] at hhead hread ⊢ <;>
    omega

private theorem tapeMovePos_workspace_le (tape : Tape) :
    tapeMovePos.workspace tape ≤ 1000000 * ((eTape tape).length + 1) := by
  obtain ⟨head, left, right⟩ := tape
  have hhead := length_encIntUnary_add_one_le head
  have hread := length_eSym_read_le ⟨head, left, right⟩
  cases right <;>
    simp [tapeMovePos, intSucc, tapeHead, tapeLeft, tapeRight, tapeTail, tapeRead,
      listHeadD, listIsEmpty, listHeadPayload, listTailCompiler, listConsCompiler,
      boolToTest, isEmpty, unframeDecoder, dropFrameDecoder, pair, append, comp, first,
      second, const, ite, encodeFrame, ofInputEq, ofOutputEq, ofTransducer,
      encTest_false, encTest_true, eTape_apply] at hhead hread ⊢ <;>
    omega

private theorem tapeMovePos_tapeCount_le : tapeMovePos.tapeCount ≤ 100 := by
  simp [tapeMovePos, intSucc, tapeHead, tapeLeft, tapeRight, tapeTail, tapeRead,
    listHeadD, listIsEmpty, listHeadPayload, listTailCompiler, listConsCompiler,
    boolToTest, isEmpty, unframeDecoder, dropFrameDecoder, pair, append, comp, first,
    second, const, ite, encodeFrame, ofInputEq, ofOutputEq, ofTransducer]

/-- Retained negative work-tape move. -/
@[expose] noncomputable def tapeMoveNeg :
    NativeCompiler (fun tape : Tape => tape.move .neg) eTape eTape := by
  let head := intPred.comp tapeHead
  let left := (listTailCompiler eSym).comp tapeLeft
  let leftHead := (listHeadD none eSym).comp tapeLeft
  let right := (listConsCompiler eSym).comp (leftHead.pair tapeRight)
  exact head.pair (left.pair right) |>.ofOutputEq fun _ => rfl

private theorem tapeMoveNeg_time_le (tape : Tape) :
    tapeMoveNeg.time tape ≤ 1000000 * ((eTape tape).length + 1) := by
  obtain ⟨head, left, right⟩ := tape
  have hhead := length_encIntUnary_sub_one_le head
  cases left <;>
    simp [tapeMoveNeg, intPred, tapeHead, tapeLeft, tapeRight, tapeTail, listTailCompiler,
      listHeadD, listIsEmpty, listHeadPayload, listConsCompiler, boolToTest, isEmpty,
      unframeDecoder, dropFrameDecoder, pair, append, comp, first, second, const, ite,
      encodeFrame, ofInputEq, ofOutputEq, ofTransducer, encTest_false, encTest_true,
      eTape_apply] at hhead ⊢ <;>
    omega

private theorem tapeMoveNeg_workspace_le (tape : Tape) :
    tapeMoveNeg.workspace tape ≤ 1000000 * ((eTape tape).length + 1) := by
  obtain ⟨head, left, right⟩ := tape
  have hhead := length_encIntUnary_sub_one_le head
  cases left <;>
    simp [tapeMoveNeg, intPred, tapeHead, tapeLeft, tapeRight, tapeTail, listTailCompiler,
      listHeadD, listIsEmpty, listHeadPayload, listConsCompiler, boolToTest, isEmpty,
      unframeDecoder, dropFrameDecoder, pair, append, comp, first, second, const, ite,
      encodeFrame, ofInputEq, ofOutputEq, ofTransducer, encTest_false, encTest_true,
      eTape_apply] at hhead ⊢ <;>
    omega

private theorem tapeMoveNeg_tapeCount_le : tapeMoveNeg.tapeCount ≤ 100 := by
  simp [tapeMoveNeg, intPred, tapeHead, tapeLeft, tapeRight, tapeTail, listTailCompiler,
    listHeadD, listIsEmpty, listHeadPayload, listConsCompiler, boolToTest, isEmpty,
    unframeDecoder, dropFrameDecoder, pair, append, comp, first, second, const, ite,
    encodeFrame, ofInputEq, ofOutputEq, ofTransducer]

/-- Retained signed work-tape movement. -/
@[expose] noncomputable def tapeMove :
    NativeCompiler (fun input : Tape × SignType => input.1.move input.2)
      (encPair eTape encSign) eTape := by
  let tape := first eTape encSign
  let movement := second eTape encSign
  let signIs (sign : SignType) := (wordEqTest encSign).comp
    (movement.pair (const (encPair eTape encSign) encSign sign))
  let stay := tape
  let positive := tapeMovePos.comp tape
  let negative := tapeMoveNeg.comp tape
  refine (ite (signIs .zero) stay (ite (signIs .neg) negative positive)).ofOutputEq ?_
  rintro ⟨tape, movement⟩
  cases movement <;> rfl

private theorem tapeMove_time_le (input : Tape × SignType) :
    tapeMove.time input ≤
      1000000000 * ((encPair eTape encSign input).length + 1) := by
  let B := (encPair eTape encSign input).length
  let tape := first eTape encSign
  let movement := second eTape encSign
  let signIs (sign : SignType) := (wordEqTest encSign).comp
    (movement.pair (const (encPair eTape encSign) encSign sign))
  let stay := tape
  let positive := tapeMovePos.comp tape
  let negative := tapeMoveNeg.comp tape
  have htape : tape.time input ≤ 100 * (B + 1) := by
    simp [tape, first, ofTransducer, B]
    omega
  have hstay : stay.time input ≤ 100 * (B + 1) := by
    simpa only [stay] using htape
  have hcondition (sign : SignType) :
      (signIs sign).time input ≤ 100000 * (B + 1) := by
    have hsign : (encSign sign).length ≤ 1 := by cases sign <;> simp [encSign]
    simp [signIs, movement, wordEqTest, wordEqBool, boolToTest, pair, comp, second,
      const, encodeFrame, ofZipTransducer, ofTransducer, B] at hsign ⊢
    omega
  have hconditionNeg := hcondition .neg
  have hconditionZero := hcondition .zero
  have hpositiveRaw := time_comp_le tapeMovePos tape input
  have hpositiveOuter := tapeMovePos_time_le input.1
  have hpositive : positive.time input ≤ 10000000 * (B + 1) := by
    simp only [positive]
    exact hpositiveRaw.trans (by
      have htapeLength := length_le_encPair_left eTape encSign input
      omega)
  have hnegativeRaw := time_comp_le tapeMoveNeg tape input
  have hnegativeOuter := tapeMoveNeg_time_le input.1
  have hnegative : negative.time input ≤ 10000000 * (B + 1) := by
    simp only [negative]
    exact hnegativeRaw.trans (by
      have htapeLength := length_le_encPair_left eTape encSign input
      omega)
  have hinner := time_ite_le (signIs .neg) negative positive input
  have hinnerTime : (ite (signIs .neg) negative positive).time input ≤
      30000000 * (B + 1) := hinner.trans (by omega)
  have houter := time_ite_le (signIs .zero) stay
    (ite (signIs .neg) negative positive) input
  change (ite (signIs .zero) stay (ite (signIs .neg) negative positive)).time input ≤ _
  exact houter.trans (by omega)

private theorem tapeMove_tapeCount_stages :
    let tape := first eTape encSign
    let movement := second eTape encSign
    let signIs (sign : SignType) := (wordEqTest encSign).comp
      (movement.pair (const (encPair eTape encSign) encSign sign))
    let positive := tapeMovePos.comp tape
    let negative := tapeMoveNeg.comp tape
    tape.tapeCount ≤ 1 ∧ (∀ sign, (signIs sign).tapeCount ≤ 100) ∧
      positive.tapeCount ≤ 102 ∧ negative.tapeCount ≤ 102 := by
  dsimp only
  have htapeCount : (first eTape encSign).tapeCount ≤ 1 := by
    simp [first, ofTransducer]
  have hconditionCount (sign : SignType) :
      ((wordEqTest encSign).comp
        ((second eTape encSign).pair
          (const (encPair eTape encSign) encSign sign))).tapeCount ≤ 100 := by
    simp [wordEqTest, wordEqBool, boolToTest, pair, comp, second, const,
      encodeFrame, ofZipTransducer, ofTransducer]
  have hpositiveCount : (tapeMovePos.comp (first eTape encSign)).tapeCount ≤ 102 := by
    simp only [comp]
    have hmax : max (first eTape encSign).tapeCount tapeMovePos.tapeCount ≤ 100 :=
      max_le (htapeCount.trans (by omega)) tapeMovePos_tapeCount_le
    omega
  have hnegativeCount : (tapeMoveNeg.comp (first eTape encSign)).tapeCount ≤ 102 := by
    simp only [comp]
    have hmax : max (first eTape encSign).tapeCount tapeMoveNeg.tapeCount ≤ 100 :=
      max_le (htapeCount.trans (by omega)) tapeMoveNeg_tapeCount_le
    omega
  exact ⟨htapeCount, hconditionCount, hpositiveCount, hnegativeCount⟩

private theorem tapeMove_workspace_le (input : Tape × SignType) :
    tapeMove.workspace input ≤
      1000000000 * ((encPair eTape encSign input).length + 1) := by
  let B := (encPair eTape encSign input).length
  let tape := first eTape encSign
  let movement := second eTape encSign
  let signIs (sign : SignType) := (wordEqTest encSign).comp
    (movement.pair (const (encPair eTape encSign) encSign sign))
  let stay := tape
  let positive := tapeMovePos.comp tape
  let negative := tapeMoveNeg.comp tape
  have htapeTime : tape.time input ≤ 100 * (B + 1) := by
    simp [tape, first, ofTransducer, B]
    omega
  have htapeSpace : tape.workspace input ≤ 100 * (B + 1) := by
    simp [tape, first, ofTransducer, B]
  have hcountStages := tapeMove_tapeCount_stages
  change tape.tapeCount ≤ 1 ∧ (∀ sign, (signIs sign).tapeCount ≤ 100) ∧
    positive.tapeCount ≤ 102 ∧ negative.tapeCount ≤ 102 at hcountStages
  obtain ⟨htapeCount, hconditionCount, hpositiveCount, hnegativeCount⟩ := hcountStages
  have hstaySpace : stay.workspace input ≤ 100 * (B + 1) := by
    simpa only [stay] using htapeSpace
  have hcondition (sign : SignType) :
      (signIs sign).workspace input ≤ 100000 * (B + 1) := by
    have hsign : (encSign sign).length ≤ 1 := by cases sign <;> simp [encSign]
    simp [signIs, movement, wordEqTest, wordEqBool, boolToTest, pair, comp, second,
      const, encodeFrame, ofZipTransducer, ofTransducer, B] at hsign ⊢
    omega
  have hconditionNeg := hcondition .neg
  have hconditionZero := hcondition .zero
  have hpositiveRaw := workspace_comp_le tapeMovePos tape input
  have hpositiveOuter := tapeMovePos_workspace_le input.1
  have hpositive : positive.workspace input ≤ 10000000 * (B + 1) := by
    simp only [positive]
    exact hpositiveRaw.trans (by
      have htapeLength := length_le_encPair_left eTape encSign input
      have hmax : max tape.tapeCount tapeMovePos.tapeCount ≤ 100 :=
        max_le (htapeCount.trans (by omega)) tapeMovePos_tapeCount_le
      omega)
  have hnegativeRaw := workspace_comp_le tapeMoveNeg tape input
  have hnegativeOuter := tapeMoveNeg_workspace_le input.1
  have hnegative : negative.workspace input ≤ 10000000 * (B + 1) := by
    simp only [negative]
    exact hnegativeRaw.trans (by
      have htapeLength := length_le_encPair_left eTape encSign input
      have hmax : max tape.tapeCount tapeMoveNeg.tapeCount ≤ 100 :=
        max_le (htapeCount.trans (by omega)) tapeMoveNeg_tapeCount_le
      omega)
  have hinnerCount :
      max (signIs .neg).tapeCount (max negative.tapeCount positive.tapeCount) ≤ 102 :=
    max_le (hconditionCount .neg |>.trans (by omega))
      (max_le hnegativeCount hpositiveCount)
  have hinner := workspace_ite_le (signIs .neg) negative positive input
  have hinnerSpace :
      (ite (signIs .neg) negative positive).workspace input ≤
        30000000 * (B + 1) := hinner.trans (by omega)
  have hinnerTapeCount : (ite (signIs .neg) negative positive).tapeCount ≤ 103 := by
    simp only [ite]
    omega
  have houterCount :
      max (signIs .zero).tapeCount
        (max stay.tapeCount (ite (signIs .neg) negative positive).tapeCount) ≤ 103 :=
    max_le (hconditionCount .zero |>.trans (by omega))
      (max_le (htapeCount.trans (by omega)) hinnerTapeCount)
  have houter := workspace_ite_le (signIs .zero) stay
    (ite (signIs .neg) negative positive) input
  change (ite (signIs .zero) stay (ite (signIs .neg) negative positive)).workspace input ≤ _
  exact houter.trans (by omega)

private theorem tapeMove_tapeCount_le : tapeMove.tapeCount ≤ 104 := by
  let tape := first eTape encSign
  let movement := second eTape encSign
  let signIs (sign : SignType) := (wordEqTest encSign).comp
    (movement.pair (const (encPair eTape encSign) encSign sign))
  let stay := tape
  let positive := tapeMovePos.comp tape
  let negative := tapeMoveNeg.comp tape
  have hcountStages := tapeMove_tapeCount_stages
  change tape.tapeCount ≤ 1 ∧ (∀ sign, (signIs sign).tapeCount ≤ 100) ∧
    positive.tapeCount ≤ 102 ∧ negative.tapeCount ≤ 102 at hcountStages
  obtain ⟨htapeCount, hconditionCount, hpositiveCount, hnegativeCount⟩ := hcountStages
  have hstayCount : stay.tapeCount ≤ 1 := by simpa only [stay] using htapeCount
  have hconditionNeg := hconditionCount .neg
  have hconditionZero := hconditionCount .zero
  change (ite (signIs .zero) stay (ite (signIs .neg) negative positive)).tapeCount ≤ 104
  simp only [ite]
  omega

/-- Retained optional write followed by retained signed movement. -/
@[expose] noncomputable def tapeApply :
    NativeCompiler (fun input : Tape × TapeAct => input.1.apply input.2)
      (encPair eTape eTA) eTape := by
  let encInput := encPair eTape eTA
  let tape := first eTape eTA
  let action := second eTape eTA
  let write := (first (encOption eSym) encSign).comp action
  let movement := (second (encOption eSym) encSign).comp action
  let hasWrite := (optionIsSomeTest eSym).comp write
  let symbol := (optionGetD none eSym).comp write
  let written := ite hasWrite (tapeWrite.comp (tape.pair symbol)) tape
  refine (tapeMove.comp (written.pair movement)).ofOutputEq ?_
  rintro ⟨tape, ⟨write, movement⟩⟩
  cases write <;> rfl

private theorem tapeApply_moveInput_length_le (input : Tape × TapeAct) :
    (encPair eTape encSign
      ((if input.2.1.isSome then input.1.write (input.2.1.getD none) else input.1),
        input.2.2)).length ≤
      32 * ((encPair eTape eTA input).length + 1) := by
  let B := (encPair eTape eTA input).length
  have htape := length_le_encPair_left eTape eTA input
  have haction := length_le_encPair_right eTape eTA input
  have hsign : (encSign input.2.2).length ≤ 1 := by
    cases input.2.2 <;> simp [encSign]
  have hzeroAction : (eTA (input.2.1, .zero)).length ≤ (eTA input.2).length := by
    cases input.2.2 <;> simp [eTA, encSign]
  have hwrittenRaw := length_eTape_apply input.1 (input.2.1, .zero)
  have hwrittenEq :
      (if input.2.1.isSome then input.1.write (input.2.1.getD none) else input.1) =
        input.1.apply (input.2.1, .zero) := by
    cases input.2.1 <;> rfl
  rw [hwrittenEq, length_encPair]
  simp only
  omega

private theorem tapeApply_time_stages (input : Tape × TapeAct) :
    let B := (encPair eTape eTA input).length
    let tape := first eTape eTA
    let action := second eTape eTA
    let write := (first (encOption eSym) encSign).comp action
    let movement := (second (encOption eSym) encSign).comp action
    let hasWrite := (optionIsSomeTest eSym).comp write
    let symbol := (optionGetD none eSym).comp write
    let writeInput := tape.pair symbol
    let writeCompiler := tapeWrite.comp writeInput
    let written := ite hasWrite writeCompiler tape
    let moveInput := written.pair movement
    tape.time input ≤ 100 * (B + 1) ∧
      movement.time input ≤ 10000 * (B + 1) ∧
      hasWrite.time input ≤ 1000000 * (B + 1) ∧
      symbol.time input ≤ 1000000 * (B + 1) ∧
      writeInput.time input ≤ 10000000 * (B + 1) ∧
      writeCompiler.time input ≤ 100000000000000 * (B + 1) ∧
      written.time input ≤ 1000000000000000 * (B + 1) ∧
      moveInput.time input ≤ 10000000000000000 * (B + 1) := by
  dsimp only
  let B := (encPair eTape eTA input).length
  let tape := first eTape eTA
  let action := second eTape eTA
  let write := (first (encOption eSym) encSign).comp action
  let movement := (second (encOption eSym) encSign).comp action
  let hasWrite := (optionIsSomeTest eSym).comp write
  let symbol := (optionGetD none eSym).comp write
  let writeInput := tape.pair symbol
  let writeCompiler := tapeWrite.comp writeInput
  let written := ite hasWrite writeCompiler tape
  let moveInput := written.pair movement
  have htape : tape.time input ≤ 100 * (B + 1) := by
    simp [tape, first, ofTransducer, B]
    omega
  have hmovement : movement.time input ≤ 10000 * (B + 1) := by
    simp [movement, action, second, comp, ofTransducer, B]
    omega
  have hhasWrite : hasWrite.time input ≤ 1000000 * (B + 1) := by
    cases h : input.2.1 <;>
      simp [hasWrite, write, action, optionIsSomeTest, optionIsSomeBool, boolDecoder,
        boolToTest, first, second, comp, ofInputEq, ofOutputEq, ofTransducer, B, h] <;>
      omega
  have hsymbol : symbol.time input ≤ 1000000 * (B + 1) := by
    have htestFalse : (encTest false).length ≤ 1 := by simp [encTest_false]
    have htestTrue : (encTest true).length ≤ 1 := by simp [encTest_true]
    cases h : input.2.1 <;>
      simp [symbol, write, action, optionGetD, optionIsSomeTest, optionIsSomeBool,
        boolDecoder, optionPayload, boolToTest, tailDecoder, first, second, const, ite,
        comp, ofInputEq, ofOutputEq, ofTransducer, B, h] <;>
      omega
  have hwriteInputRaw := time_pair_le tape symbol input
  have hwriteInput : writeInput.time input ≤ 10000000 * (B + 1) := by
    simp only [writeInput]
    exact hwriteInputRaw.trans (by omega)
  have hwriteCompilerRaw := time_comp_le tapeWrite writeInput input
  have hwriteOuter := tapeWrite_time_le (input.1, input.2.1.getD none)
  have hwriteCompiler : writeCompiler.time input ≤
      100000000000000 * (B + 1) := by
    simp only [writeCompiler]
    have hlength := (writeInput.computes input).length_output_le
    exact hwriteCompilerRaw.trans (by omega)
  have hwrittenRaw := time_ite_le hasWrite writeCompiler tape input
  have hwritten : written.time input ≤ 1000000000000000 * (B + 1) := by
    simp only [written]
    exact hwrittenRaw.trans (by omega)
  have hmoveInputRaw := time_pair_le written movement input
  have hmoveInput : moveInput.time input ≤ 10000000000000000 * (B + 1) := by
    simp only [moveInput]
    exact hmoveInputRaw.trans (by omega)
  exact ⟨htape, hmovement, hhasWrite, hsymbol, hwriteInput, hwriteCompiler, hwritten,
    hmoveInput⟩

private theorem tapeApply_tapeCount_stages :
    let tape := first eTape eTA
    let action := second eTape eTA
    let write := (first (encOption eSym) encSign).comp action
    let movement := (second (encOption eSym) encSign).comp action
    let hasWrite := (optionIsSomeTest eSym).comp write
    let symbol := (optionGetD none eSym).comp write
    let writeInput := tape.pair symbol
    let writeCompiler := tapeWrite.comp writeInput
    let written := ite hasWrite writeCompiler tape
    let moveInput := written.pair movement
    tape.tapeCount ≤ 1 ∧ movement.tapeCount ≤ 10 ∧
      hasWrite.tapeCount ≤ 100 ∧ symbol.tapeCount ≤ 100 ∧
      writeInput.tapeCount ≤ 102 ∧ writeCompiler.tapeCount ≤ 104 ∧
      written.tapeCount ≤ 105 ∧ moveInput.tapeCount ≤ 107 := by
  dsimp only
  let tape := first eTape eTA
  let action := second eTape eTA
  let write := (first (encOption eSym) encSign).comp action
  let movement := (second (encOption eSym) encSign).comp action
  let hasWrite := (optionIsSomeTest eSym).comp write
  let symbol := (optionGetD none eSym).comp write
  let writeInput := tape.pair symbol
  let writeCompiler := tapeWrite.comp writeInput
  let written := ite hasWrite writeCompiler tape
  let moveInput := written.pair movement
  have htapeCount : tape.tapeCount ≤ 1 := by simp [tape, first, ofTransducer]
  have hmovementCount : movement.tapeCount ≤ 10 := by
    simp [movement, action, second, comp, ofTransducer]
  have hhasWriteCount : hasWrite.tapeCount ≤ 100 := by
    simp [hasWrite, write, action, optionIsSomeTest, optionIsSomeBool, boolDecoder,
      boolToTest, first, second, comp, ofInputEq, ofOutputEq, ofTransducer]
  have hsymbolCount : symbol.tapeCount ≤ 100 := by
    simp [symbol, write, action, optionGetD, optionIsSomeTest, optionIsSomeBool,
      boolDecoder, optionPayload, boolToTest, tailDecoder, first, second, const, ite,
      comp, ofInputEq, ofOutputEq, ofTransducer]
  have hwriteInputCount : writeInput.tapeCount ≤ 102 := by
    simp only [writeInput, pair, comp, encodeFrame]
    omega
  have hwriteCompilerCount : writeCompiler.tapeCount ≤ 104 := by
    simp only [writeCompiler, comp]
    have hmax : max writeInput.tapeCount tapeWrite.tapeCount ≤ 102 :=
      max_le hwriteInputCount (tapeWrite_tapeCount_le.trans (by omega))
    omega
  have hwrittenCount : written.tapeCount ≤ 105 := by
    simp only [written, ite]
    omega
  have hmoveInputCount : moveInput.tapeCount ≤ 107 := by
    simp only [moveInput, pair, comp, encodeFrame]
    omega
  exact ⟨htapeCount, hmovementCount, hhasWriteCount, hsymbolCount, hwriteInputCount,
    hwriteCompilerCount, hwrittenCount, hmoveInputCount⟩

/-- The actual retained single-tape action compiler has a linear construction-derived clock in
the encoded tape/action pair. -/
theorem tapeApply_time_le (input : Tape × TapeAct) :
    tapeApply.time input ≤
      100000000000000000 * ((encPair eTape eTA input).length + 1) := by
  let B := (encPair eTape eTA input).length
  let tape := first eTape eTA
  let action := second eTape eTA
  let write := (first (encOption eSym) encSign).comp action
  let movement := (second (encOption eSym) encSign).comp action
  let hasWrite := (optionIsSomeTest eSym).comp write
  let symbol := (optionGetD none eSym).comp write
  let writeInput := tape.pair symbol
  let writeCompiler := tapeWrite.comp writeInput
  let written := ite hasWrite writeCompiler tape
  let moveInput := written.pair movement
  have htimeStages := tapeApply_time_stages input
  change tape.time input ≤ 100 * (B + 1) ∧
    movement.time input ≤ 10000 * (B + 1) ∧
    hasWrite.time input ≤ 1000000 * (B + 1) ∧
    symbol.time input ≤ 1000000 * (B + 1) ∧
    writeInput.time input ≤ 10000000 * (B + 1) ∧
    writeCompiler.time input ≤ 100000000000000 * (B + 1) ∧
    written.time input ≤ 1000000000000000 * (B + 1) ∧
    moveInput.time input ≤ 10000000000000000 * (B + 1) at htimeStages
  obtain ⟨_, _, _, _, _, _, _, hmoveInput⟩ := htimeStages
  have hmoveOuter := tapeMove_time_le
    ((if input.2.1.isSome then input.1.write (input.2.1.getD none) else input.1), input.2.2)
  have hmoveLength := tapeApply_moveInput_length_le input
  have hcomp := time_comp_le tapeMove moveInput input
  simp only at hcomp
  change (tapeMove.comp moveInput).time input ≤ _
  exact hcomp.trans (by omega)

/-- The actual retained single-tape action compiler has an independent linear workspace bound in
the encoded tape/action pair. -/
theorem tapeApply_workspace_le (input : Tape × TapeAct) :
    tapeApply.workspace input ≤
      100000000000000000 * ((encPair eTape eTA input).length + 1) := by
  let B := (encPair eTape eTA input).length
  let tape := first eTape eTA
  let action := second eTape eTA
  let write := (first (encOption eSym) encSign).comp action
  let movement := (second (encOption eSym) encSign).comp action
  let hasWrite := (optionIsSomeTest eSym).comp write
  let symbol := (optionGetD none eSym).comp write
  let writeInput := tape.pair symbol
  let writeCompiler := tapeWrite.comp writeInput
  let written := ite hasWrite writeCompiler tape
  let moveInput := written.pair movement
  have htimeStages := tapeApply_time_stages input
  change tape.time input ≤ 100 * (B + 1) ∧
    movement.time input ≤ 10000 * (B + 1) ∧
    hasWrite.time input ≤ 1000000 * (B + 1) ∧
    symbol.time input ≤ 1000000 * (B + 1) ∧
    writeInput.time input ≤ 10000000 * (B + 1) ∧
    writeCompiler.time input ≤ 100000000000000 * (B + 1) ∧
    written.time input ≤ 1000000000000000 * (B + 1) ∧
    moveInput.time input ≤ 10000000000000000 * (B + 1) at htimeStages
  obtain ⟨htapeTime, hmovementTime, hhasWriteTime, hsymbolTime, hwriteInputTime,
      hwriteCompilerTime, hwrittenTime, hmoveInputTime⟩ := htimeStages
  have hcountStages := tapeApply_tapeCount_stages
  change tape.tapeCount ≤ 1 ∧ movement.tapeCount ≤ 10 ∧
    hasWrite.tapeCount ≤ 100 ∧ symbol.tapeCount ≤ 100 ∧
    writeInput.tapeCount ≤ 102 ∧ writeCompiler.tapeCount ≤ 104 ∧
    written.tapeCount ≤ 105 ∧ moveInput.tapeCount ≤ 107 at hcountStages
  obtain ⟨htapeCount, hmovementCount, hhasWriteCount, hsymbolCount, hwriteInputCount,
      hwriteCompilerCount, hwrittenCount, hmoveInputCount⟩ := hcountStages
  have htapeSpace : tape.workspace input ≤ 100 * (B + 1) := by
    simp [tape, first, ofTransducer, B]
  have hmovementSpace : movement.workspace input ≤ 10000 * (B + 1) := by
    simp [movement, action, second, comp, ofTransducer, B]
    omega
  have hhasWrite : hasWrite.workspace input ≤ 1000000 * (B + 1) := by
    cases h : input.2.1 <;>
      simp [hasWrite, write, action, optionIsSomeTest, optionIsSomeBool, boolDecoder,
        boolToTest, first, second, comp, ofInputEq, ofOutputEq, ofTransducer, B, h] <;>
      omega
  have hsymbolSpace : symbol.workspace input ≤ 1000000 * (B + 1) := by
    have htestFalse : (encTest false).length ≤ 1 := by simp [encTest_false]
    have htestTrue : (encTest true).length ≤ 1 := by simp [encTest_true]
    cases h : input.2.1 <;>
      simp [symbol, write, action, optionGetD, optionIsSomeTest, optionIsSomeBool,
        boolDecoder, optionPayload, boolToTest, tailDecoder, first, second, const, ite,
        comp, ofInputEq, ofOutputEq, ofTransducer, B, h] <;>
      omega
  have hwriteInputSpaceRaw := workspace_pair_le tape symbol input
  have hwriteInputSpace : writeInput.workspace input ≤ 10000000 * (B + 1) := by
    simp only [writeInput]
    exact hwriteInputSpaceRaw.trans (by omega)
  have hwriteCompilerSpaceRaw := workspace_comp_le tapeWrite writeInput input
  have hwriteOuterSpace := tapeWrite_workspace_le (input.1, input.2.1.getD none)
  have hwriteCompilerSpace : writeCompiler.workspace input ≤
      100000000000000 * (B + 1) := by
    simp only [writeCompiler]
    have hlength := (writeInput.computes input).length_output_le
    have hmax : max writeInput.tapeCount tapeWrite.tapeCount ≤ 102 :=
      max_le hwriteInputCount (tapeWrite_tapeCount_le.trans (by omega))
    exact hwriteCompilerSpaceRaw.trans (by omega)
  have hwrittenRaw := workspace_ite_le hasWrite writeCompiler tape input
  have hwrittenCountMax :
      max hasWrite.tapeCount (max writeCompiler.tapeCount tape.tapeCount) ≤ 104 :=
    max_le (hhasWriteCount.trans (by omega))
      (max_le hwriteCompilerCount (htapeCount.trans (by omega)))
  have hwritten : written.workspace input ≤ 1000000000000000 * (B + 1) := by
    simp only [written]
    exact hwrittenRaw.trans (by omega)
  have hmoveInputSpaceRaw := workspace_pair_le written movement input
  have hmoveInputSpace : moveInput.workspace input ≤ 10000000000000000 * (B + 1) := by
    simp only [moveInput]
    exact hmoveInputSpaceRaw.trans (by omega)
  have hmoveOuterSpace := tapeMove_workspace_le
    ((if input.2.1.isSome then input.1.write (input.2.1.getD none) else input.1), input.2.2)
  have hmoveLength := tapeApply_moveInput_length_le input
  have hcomp := workspace_comp_le tapeMove moveInput input
  simp only at hcomp
  have hmax : max moveInput.tapeCount tapeMove.tapeCount ≤ 107 :=
    max_le hmoveInputCount (tapeMove_tapeCount_le.trans (by omega))
  change (tapeMove.comp moveInput).workspace input ≤ _
  exact hcomp.trans (by omega)

/-- A construction-derived static bound for the retained single-tape action compiler. -/
theorem tapeApply_tapeCount_le : tapeApply.tapeCount ≤ 210 := by
  let tape := first eTape eTA
  let action := second eTape eTA
  let write := (first (encOption eSym) encSign).comp action
  let movement := (second (encOption eSym) encSign).comp action
  let hasWrite := (optionIsSomeTest eSym).comp write
  let symbol := (optionGetD none eSym).comp write
  let writeInput := tape.pair symbol
  let writeCompiler := tapeWrite.comp writeInput
  let written := ite hasWrite writeCompiler tape
  let moveInput := written.pair movement
  have hcountStages := tapeApply_tapeCount_stages
  change tape.tapeCount ≤ 1 ∧ movement.tapeCount ≤ 10 ∧
    hasWrite.tapeCount ≤ 100 ∧ symbol.tapeCount ≤ 100 ∧
    writeInput.tapeCount ≤ 102 ∧ writeCompiler.tapeCount ≤ 104 ∧
    written.tapeCount ≤ 105 ∧ moveInput.tapeCount ≤ 107 at hcountStages
  obtain ⟨_, _, _, _, _, _, _, hmoveInputCount⟩ := hcountStages
  have htapeMoveCount := tapeMove_tapeCount_le
  change (tapeMove.comp moveInput).tapeCount ≤ 210
  simp only [comp]
  omega

/-- Retained left-length application of work-tape actions. Missing actions use `(none, zero)` and
extra actions are ignored exactly as in the source interpreter. -/
@[expose] noncomputable def applyTapes :
    NativeCompiler (fun input : List Tape × List TapeAct =>
      Turing.MultiTapeTM.Universal.applyTapes input.1 input.2)
      (encPair (encList eTape) (encList eTA)) (encList eTape) := by
  let zipped := listZipWithLeftCompiler (none, .zero) eTape eTA eTape tapeApply
  refine zipped.ofOutputEq ?_
  intro input
  apply congrArg (encList eTape)
  obtain ⟨tapes, actions⟩ := input
  induction tapes generalizing actions with
  | nil => rfl
  | cons tape tapes ih =>
      cases actions with
      | nil =>
          have htail : tapes = listZipWithLeft (none, .zero)
              (fun input => input.1.apply input.2) tapes [] := by
            simpa only [Turing.MultiTapeTM.Universal.applyTapes_nil_right] using ih []
          change tape :: tapes =
            tape.apply (none, .zero) ::
              listZipWithLeft (none, .zero) (fun input => input.1.apply input.2) tapes []
          have hdefault : tape.apply (none, .zero) = tape := rfl
          rw [hdefault, ← htail]
      | cons action actions =>
          change tape.apply action :: Turing.MultiTapeTM.Universal.applyTapes tapes actions =
            tape.apply action ::
              listZipWithLeft (none, .zero) (fun input => input.1.apply input.2) tapes actions
          rw [ih actions]

private theorem applyTapes_streamState (actions : List TapeAct) (tapes : List Tape) (j : ℕ)
    (hj : j ≤ tapes.length) :
    streamState actions (fun pair : List TapeAct × Tape => pair.1.tail) tapes j =
      actions.drop j := by
  simp [streamState, List.foldl_const, List.tail_iterate, List.length_take, hj]

private theorem applyTapesNext_time_le (input : List TapeAct × Tape) :
    (listZipWithLeftNextCompiler eTape eTA).time input ≤
      10000 * ((encPair (encList eTA) eTape input).length + 1) := by
  simp [listZipWithLeftNextCompiler, listTailCompiler, dropFrameDecoder, comp, first,
    ofInputEq, ofOutputEq, ofTransducer]
  omega

private theorem applyTapesNext_workspace_le (input : List TapeAct × Tape) :
    (listZipWithLeftNextCompiler eTape eTA).workspace input ≤
      10000 * ((encPair (encList eTA) eTape input).length + 1) := by
  simp [listZipWithLeftNextCompiler, listTailCompiler, dropFrameDecoder, comp, first,
    ofInputEq, ofOutputEq, ofTransducer]
  omega

private theorem applyTapesNext_tapeCount_le :
    (listZipWithLeftNextCompiler eTape eTA).tapeCount ≤ 10 := by
  simp [listZipWithLeftNextCompiler, listTailCompiler, dropFrameDecoder, comp, first,
    ofInputEq, ofOutputEq, ofTransducer]

private theorem applyTapes_callbackInput_length_le (input : List TapeAct × Tape) :
    (encPair eTape eTA (input.2, input.1.headD (none, .zero))).length ≤
      4 * ((encPair (encList eTA) eTape input).length + 1) := by
  have htape := length_le_encPair_right (encList eTA) eTape input
  cases hactions : input.1 with
  | nil =>
      simp only [hactions, List.headD_nil, length_encPair] at htape ⊢
      simp [eTA, encSign]
      omega
  | cons action actions =>
      have haction : (eTA action).length ≤ (encList eTA input.1).length :=
        length_le_encList_of_mem eTA (by simp [hactions])
      have hactionsLength := length_le_encPair_left (encList eTA) eTape input
      calc
        (encPair eTape eTA (input.2, (action :: actions).headD (none, .zero))).length =
            2 * (eTape input.2).length + 1 + (eTA action).length := by
              simpa only [List.headD_cons] using
                length_encPair (enc₁ := eTape) (enc₂ := eTA) (input.2, action)
        _ ≤ 2 * ((encPair (encList eTA) eTape input).length) + 1 +
            (encPair (encList eTA) eTape input).length := by omega
        _ ≤ 4 * ((encPair (encList eTA) eTape input).length + 1) := by omega

private theorem applyTapesEmit_right_resources (input : List TapeAct × Tape) :
    let rights := first (encList eTA) eTape
    let right := (listHeadD (none, .zero) eTA).comp rights
    right.time input ≤
        1000000 * ((encPair (encList eTA) eTape input).length + 1) ∧
      right.workspace input ≤
        1000000 * ((encPair (encList eTA) eTape input).length + 1) := by
  let B := (encPair (encList eTA) eTape input).length
  let rights := first (encList eTA) eTape
  let right := (listHeadD (none, .zero) eTA).comp rights
  change right.time input ≤ 1000000 * (B + 1) ∧
    right.workspace input ≤ 1000000 * (B + 1)
  have htest : (encTest input.1.isEmpty).length ≤ 1 := by
    cases input.1 <;> simp [encTest_false, encTest_true]
  have hzeroSign : (encSign (.zero : SignType)).length ≤ 1 := by simp [encSign]
  have hzeroSignNat : (encSign (0 : SignType)).length ≤ 1 := by simp [encSign]
  cases h : input.1 <;>
    simp [right, rights, listHeadD, listIsEmpty, listHeadPayload, boolToTest,
      isEmpty, unframeDecoder, first, const, ite, comp, ofInputEq, ofOutputEq,
      ofTransducer, B, h] at htest ⊢ <;>
    omega

private theorem applyTapesEmit_tapeCount_stages :
    let rights := first (encList eTA) eTape
    let left := second (encList eTA) eTape
    let right := (listHeadD (none, .zero) eTA).comp rights
    let callbackInput := left.pair right
    let applied := tapeApply.comp callbackInput
    left.tapeCount ≤ 1 ∧ right.tapeCount ≤ 100 ∧ callbackInput.tapeCount ≤ 102 ∧
      applied.tapeCount ≤ 212 := by
  let rights := first (encList eTA) eTape
  let left := second (encList eTA) eTape
  let right := (listHeadD (none, .zero) eTA).comp rights
  let callbackInput := left.pair right
  let applied := tapeApply.comp callbackInput
  change left.tapeCount ≤ 1 ∧ right.tapeCount ≤ 100 ∧ callbackInput.tapeCount ≤ 102 ∧
    applied.tapeCount ≤ 212
  have hleftCount : left.tapeCount ≤ 1 := by simp [left, second, ofTransducer]
  have hrightCount : right.tapeCount ≤ 100 := by
    simp [right, rights, listHeadD, listIsEmpty, listHeadPayload, boolToTest,
      isEmpty, unframeDecoder, first, const, ite, comp, ofInputEq, ofOutputEq,
      ofTransducer]
  have hcallbackInputCount : callbackInput.tapeCount ≤ 102 := by
    simp only [callbackInput, pair, comp, encodeFrame]
    omega
  have happliedCount : applied.tapeCount ≤ 212 := by
    simp only [applied, comp]
    have hmax : max callbackInput.tapeCount tapeApply.tapeCount ≤ 210 :=
      max_le (hcallbackInputCount.trans (by omega)) tapeApply_tapeCount_le
    omega
  exact ⟨hleftCount, hrightCount, hcallbackInputCount, happliedCount⟩

private theorem applyTapesEmit_time_stages (input : List TapeAct × Tape) :
    let B := (encPair (encList eTA) eTape input).length
    let rights := first (encList eTA) eTape
    let left := second (encList eTA) eTape
    let right := (listHeadD (none, .zero) eTA).comp rights
    let callbackInput := left.pair right
    let applied := tapeApply.comp callbackInput
    callbackInput.time input ≤ 10000000 * (B + 1) ∧
      applied.time input ≤ 600000000000000000 * (B + 1) := by
  let B := (encPair (encList eTA) eTape input).length
  let rights := first (encList eTA) eTape
  let left := second (encList eTA) eTape
  let right := (listHeadD (none, .zero) eTA).comp rights
  let callbackInput := left.pair right
  let applied := tapeApply.comp callbackInput
  change callbackInput.time input ≤ 10000000 * (B + 1) ∧
    applied.time input ≤ 600000000000000000 * (B + 1)
  have hleft : left.time input ≤ 100 * (B + 1) := by
    simp [left, second, ofTransducer, B]
    omega
  have hrightStages := applyTapesEmit_right_resources input
  change right.time input ≤ 1000000 * (B + 1) ∧
    right.workspace input ≤ 1000000 * (B + 1) at hrightStages
  obtain ⟨hright, _⟩ := hrightStages
  have hcallbackInputRaw := time_pair_le left right input
  have hcallbackInput : callbackInput.time input ≤ 10000000 * (B + 1) := by
    simp only [callbackInput]
    exact hcallbackInputRaw.trans (by omega)
  have hcallbackLength := applyTapes_callbackInput_length_le input
  have happliedRaw := time_comp_le tapeApply callbackInput input
  have happliedOuter := tapeApply_time_le (input.2, input.1.headD (none, .zero))
  have happlied : applied.time input ≤ 600000000000000000 * (B + 1) := by
    simp only [applied]
    exact happliedRaw.trans (by nlinarith)
  exact ⟨hcallbackInput, happlied⟩

private theorem applyTapesEmit_time_le (input : List TapeAct × Tape) :
    (listZipWithLeftEmitCompiler (none, .zero) eTape eTA eTape tapeApply).time input ≤
      4000000000000000000 * ((encPair (encList eTA) eTape input).length + 1) := by
  let B := (encPair (encList eTA) eTape input).length
  let rights := first (encList eTA) eTape
  let left := second (encList eTA) eTape
  let right := (listHeadD (none, .zero) eTA).comp rights
  let callbackInput := left.pair right
  let applied := tapeApply.comp callbackInput
  let framed := (framedValue eTape).comp applied
  have htimeStages := applyTapesEmit_time_stages input
  change callbackInput.time input ≤ 10000000 * (B + 1) ∧
    applied.time input ≤ 600000000000000000 * (B + 1) at htimeStages
  obtain ⟨_, happlied⟩ := htimeStages
  have hcallbackLength := applyTapes_callbackInput_length_le input
  have houtputRaw := length_eTape_apply input.2 (input.1.headD (none, .zero))
  have htape := length_le_encPair_right (encList eTA) eTape input
  have haction := (length_le_encPair_right eTape eTA
    (input.2, input.1.headD (none, .zero))).trans hcallbackLength
  have houtput : (eTape (input.2.apply (input.1.headD (none, .zero)))).length ≤
      20 * (B + 1) := houtputRaw.trans (by nlinarith)
  have hframedRaw := time_comp_le (framedValue eTape) applied input
  change framed.time input ≤ _
  exact hframedRaw.trans (by
    simp only [framedValue, ofOutputEq, encodeFrame]
    nlinarith)

private theorem applyTapesEmit_workspace_le (input : List TapeAct × Tape) :
    (listZipWithLeftEmitCompiler (none, .zero) eTape eTA eTape tapeApply).workspace input ≤
      4000000000000000000 * ((encPair (encList eTA) eTape input).length + 1) := by
  let B := (encPair (encList eTA) eTape input).length
  let rights := first (encList eTA) eTape
  let left := second (encList eTA) eTape
  let right := (listHeadD (none, .zero) eTA).comp rights
  let callbackInput := left.pair right
  let applied := tapeApply.comp callbackInput
  let framed := (framedValue eTape).comp applied
  have hleftTime : left.time input ≤ 100 * (B + 1) := by
    simp [left, second, ofTransducer, B]
    omega
  have hleftSpace : left.workspace input ≤ 100 * (B + 1) := by
    simp [left, second, ofTransducer, B]
  have hrightStages := applyTapesEmit_right_resources input
  change right.time input ≤ 1000000 * (B + 1) ∧
    right.workspace input ≤ 1000000 * (B + 1) at hrightStages
  obtain ⟨hrightTime, hrightSpace⟩ := hrightStages
  have hcountStages := applyTapesEmit_tapeCount_stages
  change left.tapeCount ≤ 1 ∧ right.tapeCount ≤ 100 ∧ callbackInput.tapeCount ≤ 102 ∧
    applied.tapeCount ≤ 212 at hcountStages
  obtain ⟨_, _, hcallbackInputCount, happliedCount⟩ := hcountStages
  have htimeStages := applyTapesEmit_time_stages input
  change callbackInput.time input ≤ 10000000 * (B + 1) ∧
    applied.time input ≤ 600000000000000000 * (B + 1) at htimeStages
  obtain ⟨hcallbackInputTime, happliedTime⟩ := htimeStages
  have hcallbackInputSpaceRaw := workspace_pair_le left right input
  have hcallbackInputSpace : callbackInput.workspace input ≤ 10000000 * (B + 1) := by
    simp only [callbackInput]
    exact hcallbackInputSpaceRaw.trans (by omega)
  have hcallbackLength := applyTapes_callbackInput_length_le input
  have happliedSpaceRaw := workspace_comp_le tapeApply callbackInput input
  have happliedOuterSpace := tapeApply_workspace_le
    (input.2, input.1.headD (none, .zero))
  have happliedSpace : applied.workspace input ≤
      600000000000000000 * (B + 1) := by
    simp only [applied]
    have hmax : max callbackInput.tapeCount tapeApply.tapeCount ≤ 210 :=
      max_le (hcallbackInputCount.trans (by omega)) tapeApply_tapeCount_le
    exact happliedSpaceRaw.trans (by nlinarith)
  have hframedRaw := workspace_comp_le (framedValue eTape) applied input
  simp only [framedValue, ofOutputEq, encodeFrame] at hframedRaw
  simp only [Nat.max_eq_left (Nat.zero_le _)] at hframedRaw
  change framed.workspace input ≤ _
  exact hframedRaw.trans (by omega)

private theorem applyTapesEmit_tapeCount_le :
    (listZipWithLeftEmitCompiler (none, .zero) eTape eTA eTape tapeApply).tapeCount ≤ 214 := by
  let rights := first (encList eTA) eTape
  let left := second (encList eTA) eTape
  let right := (listHeadD (none, .zero) eTA).comp rights
  let callbackInput := left.pair right
  let applied := tapeApply.comp callbackInput
  let framed := (framedValue eTape).comp applied
  have hcountStages := applyTapesEmit_tapeCount_stages
  change left.tapeCount ≤ 1 ∧ right.tapeCount ≤ 100 ∧ callbackInput.tapeCount ≤ 102 ∧
    applied.tapeCount ≤ 212 at hcountStages
  obtain ⟨_, _, _, happliedCount⟩ := hcountStages
  change framed.tapeCount ≤ 214
  simp only [framed, comp, framedValue, ofOutputEq, encodeFrame]
  omega

private theorem applyTapesStreamPair_tapeCount_le :
    streamFoldPairTapeCount (listZipWithLeftNextCompiler eTape eTA)
      (listZipWithLeftEmitCompiler (none, .zero) eTape eTA eTape tapeApply)
      (listZipWithLeftFinishCompiler eTA) ≤ 250 := by
  let nextCompiler := listZipWithLeftNextCompiler eTape eTA
  let emitCompiler :=
    listZipWithLeftEmitCompiler (none, .zero) eTape eTA eTape tapeApply
  let finishCompiler := listZipWithLeftFinishCompiler eTA
  change streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler ≤ 250
  have hnext := applyTapesNext_tapeCount_le
  have hemit := applyTapesEmit_tapeCount_le
  simp only [streamFoldPairTapeCount, streamFramedNext, streamUnframedFinish,
    nextCompiler, emitCompiler, finishCompiler, listZipWithLeftFinishCompiler,
    comp, encodeFrame, unframeValue, const, ofTransducer]
  omega

private theorem applyTapes_tapes_length_le (input : List Tape × List TapeAct) :
    (encList eTape input.1).length ≤
      (encPair (encList eTape) (encList eTA) input).length + 1 := by
  exact (length_le_encPair_left (encList eTape) (encList eTA) input).trans (by omega)

private theorem applyTapes_actions_length_le (input : List Tape × List TapeAct) :
    (encList eTA input.2).length ≤
      (encPair (encList eTape) (encList eTA) input).length + 1 := by
  exact (length_le_encPair_right (encList eTape) (encList eTA) input).trans (by omega)

private theorem applyTapes_streamInput_length_le (input : List Tape × List TapeAct) :
    (encPair (encList eTA) (encList eTape) (input.2, input.1)).length ≤
      2 * ((encPair (encList eTape) (encList eTA) input).length + 1) := by
  simp only [length_encPair]
  omega

private theorem applyTapes_streamState_length_le (input : List Tape × List TapeAct) (j : ℕ)
    (hj : j ≤ input.1.length) :
    (encList eTA
      (streamState input.2 (fun pair : List TapeAct × Tape => pair.1.tail) input.1 j)).length ≤
        (encPair (encList eTape) (encList eTA) input).length + 1 := by
  rw [applyTapes_streamState input.2 input.1 j hj]
  exact (SizedListEncoding.length_drop_le (encA := eTA) (encL := encList eTA)
    input.2 j).trans (applyTapes_actions_length_le input)

private theorem applyTapes_streamElem_length_le (input : List Tape × List TapeAct) (j : ℕ)
    (hj : j < input.1.length) :
    (eTape input.1[j]).length ≤
      (encPair (encList eTape) (encList eTA) input).length + 1 := by
  exact (length_le_encList_of_mem eTape (List.getElem_mem hj)).trans
    (applyTapes_tapes_length_le input)

private theorem applyTapes_streamPair_length_le (input : List Tape × List TapeAct) (j : ℕ)
    (hj : j < input.1.length) :
    ((encPair (encList eTA) eTape)
      (streamState input.2 (fun pair : List TapeAct × Tape => pair.1.tail) input.1 j,
        input.1[j])).length + 1 ≤
      4 * ((encPair (encList eTape) (encList eTA) input).length + 1) := by
  have hs := applyTapes_streamState_length_le input j hj.le
  have he := applyTapes_streamElem_length_le input j hj
  have hB : 2 ≤ (encPair (encList eTape) (encList eTA) input).length + 1 := by
    simp only [length_encPair]
    omega
  rw [length_encPair (enc₁ := encList eTA) (enc₂ := eTape)]
  change 2 * (encList eTA
      (streamState input.2 (fun pair : List TapeAct × Tape => pair.1.tail) input.1 j)).length +
        1 + (eTape input.1[j]).length + 1 ≤
      4 * ((encPair (encList eTape) (encList eTA) input).length + 1)
  omega

private theorem applyTapesMarshal_time_le (input : List Tape × List TapeAct) :
    ((second (encList eTape) (encList eTA)).pair
      (first (encList eTape) (encList eTA))).time input ≤
        1000 * ((encPair (encList eTape) (encList eTA) input).length + 1) := by
  have h := time_pair_le (second (encList eTape) (encList eTA))
    (first (encList eTape) (encList eTA)) input
  exact h.trans (by simp only [first, second, ofTransducer]; omega)

private theorem applyTapesMarshal_workspace_le (input : List Tape × List TapeAct) :
    ((second (encList eTape) (encList eTA)).pair
      (first (encList eTape) (encList eTA))).workspace input ≤
        1000 * ((encPair (encList eTape) (encList eTA) input).length + 1) := by
  have h := workspace_pair_le (second (encList eTape) (encList eTA))
    (first (encList eTape) (encList eTA)) input
  exact h.trans (by simp only [first, second, ofTransducer]; omega)

private theorem applyTapesMarshal_tapeCount_le :
    ((second (encList eTape) (encList eTA)).pair
      (first (encList eTape) (encList eTA))).tapeCount ≤ 10 := by
  simp [pair, first, second, encodeFrame, comp, ofTransducer]

/-- The actual retained left-length tape-action compiler has a quadratic construction-derived
clock in the complete encoded pair of tape and action lists. Extra actions remain charged even
though the source semantics ignores them. -/
theorem applyTapes_time_le (input : List Tape × List TapeAct) :
    applyTapes.time input ≤
      200000000000000000000 *
        ((encPair (encList eTape) (encList eTA) input).length + 1) ^ 2 := by
  let B := (encPair (encList eTape) (encList eTA) input).length + 1
  let streamInput : List TapeAct × List Tape := (input.2, input.1)
  let nextCompiler := listZipWithLeftNextCompiler eTape eTA
  let emitCompiler :=
    listZipWithLeftEmitCompiler (none, .zero) eTape eTA eTape tapeApply
  let finishCompiler := listZipWithLeftFinishCompiler eTA
  let streamCompiler :=
    listZipWithLeftStreamCompiler (none, .zero) eTape eTA eTape tapeApply
  let marshal := (second (encList eTape) (encList eTA)).pair
    (first (encList eTape) (encList eTA))
  have htapes : (encList eTape input.1).length ≤ B := by
    simpa only [B] using applyTapes_tapes_length_le input
  have hinput :
      (encPair (encList eTA) (encList eTape) streamInput).length ≤ 2 * B := by
    simpa only [streamInput, B] using applyTapes_streamInput_length_le input
  have hstate : ∀ j, j ≤ streamInput.2.length →
      (encList eTA
        (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
          streamInput.2 j)).length ≤ B := by
    intro j hj
    simpa only [streamInput, B] using
      applyTapes_streamState_length_le input j (by simpa only [streamInput] using hj)
  have helem : ∀ j (hj : j < streamInput.2.length),
      (eTape streamInput.2[j]).length ≤ B := by
    intro j hj
    simpa only [streamInput, B] using
      applyTapes_streamElem_length_le input j (by simpa only [streamInput] using hj)
  have hpair : ∀ j (hj : j < streamInput.2.length),
      ((encPair (encList eTA) eTape)
        (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
          streamInput.2 j, streamInput.2[j])).length + 1 ≤ 4 * B := by
    intro j hj
    simpa only [streamInput, B] using
      applyTapes_streamPair_length_le input j (by simpa only [streamInput] using hj)
  have hemit : ∀ j (hj : j < streamInput.2.length),
      emitCompiler.time
        (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
          streamInput.2 j, streamInput.2[j]) ≤
        20000000000000000000 * B := by
    intro j hj
    have h := applyTapesEmit_time_le
      (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
        streamInput.2 j, streamInput.2[j])
    simp only [emitCompiler]
    exact h.trans (by have := hpair j hj; omega)
  have hnext : ∀ j (hj : j < streamInput.2.length),
      nextCompiler.time
        (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
          streamInput.2 j, streamInput.2[j]) ≤ 100000 * B := by
    intro j hj
    have h := applyTapesNext_time_le
      (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
        streamInput.2 j, streamInput.2[j])
    simp only [nextCompiler]
    exact h.trans (by have := hpair j hj; omega)
  have hfinish : finishCompiler.time
      (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
        streamInput.2 streamInput.2.length) ≤ 1 := by
    simp [finishCompiler, listZipWithLeftFinishCompiler, const]
  have hstreamRaw := streamFoldPairTime_le nextCompiler emitCompiler finishCompiler streamInput
    (20000000000000000000 * B) (100000 * B) 1 (2 * B)
    hinput (fun j hj => (hstate j hj).trans (by omega))
    (fun j hj => (helem j hj).trans (by omega)) hemit hnext hfinish
  have hcount : streamInput.2.length ≤ B := by
    have h := length_le_length_encList eTape input.1
    simpa only [streamInput] using h.trans htapes
  have hB : 1 ≤ B := by simp [B]
  have hround :
      20000000000000000000 * B + 100000 * B + 46 * (2 * B) + 60 ≤
        30000000000000000000 * B := by omega
  have hrounds := Nat.mul_le_mul hcount hround
  have hstream : streamCompiler.time streamInput ≤
      100000000000000000000 * B ^ 2 := by
    change streamFoldPairTime nextCompiler emitCompiler finishCompiler streamInput ≤ _
    exact hstreamRaw.trans (by nlinarith)
  have hmarshal : marshal.time input ≤ 1000 * B := by
    simpa only [marshal, B] using applyTapesMarshal_time_le input
  have hcomp := time_comp_le streamCompiler marshal input
  change (streamCompiler.comp marshal).time input ≤
    200000000000000000000 * B ^ 2
  exact hcomp.trans (by nlinarith)

/-- The actual retained left-length tape-action compiler has an independent linear workspace bound
in the complete encoded pair of tape and action lists, including empty and mismatched lists. -/
theorem applyTapes_workspace_le (input : List Tape × List TapeAct) :
    applyTapes.workspace input ≤
      30000000000000000000000 *
        ((encPair (encList eTape) (encList eTA) input).length + 1) := by
  let B := (encPair (encList eTape) (encList eTA) input).length + 1
  let streamInput : List TapeAct × List Tape := (input.2, input.1)
  let nextCompiler := listZipWithLeftNextCompiler eTape eTA
  let emitCompiler :=
    listZipWithLeftEmitCompiler (none, .zero) eTape eTA eTape tapeApply
  let emitBits : NativeCompiler
      (fun input : List TapeAct × Tape =>
        frame (eTape (input.2.apply (input.1.headD (none, .zero)))))
      (encPair (encList eTA) eTape) encBits :=
    emitCompiler.ofOutputEq (g := fun input =>
      frame (eTape (input.2.apply (input.1.headD (none, .zero))))) fun _ => rfl
  let streamCompiler :=
    listZipWithLeftStreamCompiler (none, .zero) eTape eTA eTape tapeApply
  let marshal := (second (encList eTape) (encList eTA)).pair
    (first (encList eTape) (encList eTA))
  have hstate : ∀ j, j ≤ streamInput.2.length →
      (encList eTA
        (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
          streamInput.2 j)).length ≤ B := by
    intro j hj
    simpa only [streamInput, B] using
      applyTapes_streamState_length_le input j (by simpa only [streamInput] using hj)
  have helem : ∀ j (hj : j < streamInput.2.length),
      (eTape streamInput.2[j]).length ≤ B := by
    intro j hj
    simpa only [streamInput, B] using
      applyTapes_streamElem_length_le input j (by simpa only [streamInput] using hj)
  have hpair : ∀ j (hj : j < streamInput.2.length),
      ((encPair (encList eTA) eTape)
        (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
          streamInput.2 j, streamInput.2[j])).length + 1 ≤ 4 * B := by
    intro j hj
    simpa only [streamInput, B] using
      applyTapes_streamPair_length_le input j (by simpa only [streamInput] using hj)
  have hemit : ∀ j (hj : j < streamInput.2.length),
      emitBits.workspace
        (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
          streamInput.2 j, streamInput.2[j]) ≤ 16000000000000000000 * B := by
    intro j hj
    have h := applyTapesEmit_workspace_le
      (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
        streamInput.2 j, streamInput.2[j])
    simp only [emitBits, emitCompiler, ofOutputEq]
    exact h.trans (by have := hpair j hj; omega)
  have hnext : ∀ j (hj : j < streamInput.2.length),
      nextCompiler.workspace
        (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
          streamInput.2 j, streamInput.2[j]) ≤ 40000 * B := by
    intro j hj
    have h := applyTapesNext_workspace_le
      (streamState streamInput.1 (fun pair : List TapeAct × Tape => pair.1.tail)
        streamInput.2 j, streamInput.2[j])
    simp only [nextCompiler]
    exact h.trans (by have := hpair j hj; omega)
  have hresult : ∀ streamInput : List TapeAct × List Tape,
      encBits (streamEmit (fun pair : List TapeAct × Tape => pair.1.tail)
        (fun pair => frame (eTape (pair.2.apply (pair.1.headD (none, .zero)))))
        streamInput.1 streamInput.2) =
      streamEmit (fun pair : List TapeAct × Tape => pair.1.tail)
        (fun pair => frame (eTape (pair.2.apply (pair.1.headD (none, .zero)))))
        streamInput.1 streamInput.2 := fun _ => rfl
  let K := streamFoldPairTapeCount nextCompiler emitBits (const (encList eTA) encBits [])
  have hstreamRaw :
      (listFoldEmitCompiler (encList eTA) eTape encBits nextCompiler emitBits
        hresult).workspace streamInput ≤
          2 * K * (16000000000000000000 * B + 40000 * B + 48 * B + 20 * K + 90) +
            13 * B + 5 * K + 43 := by
    simpa only [K] using listFoldEmitCompiler_workspace_le nextCompiler emitBits hresult
      streamInput (16000000000000000000 * B) (40000 * B) B hstate helem hemit hnext
  have hK : K ≤ 250 := by
    have hKRaw : streamFoldPairTapeCount nextCompiler emitCompiler
        (listZipWithLeftFinishCompiler eTA) ≤ 250 := by
      simpa only [nextCompiler, emitCompiler] using applyTapesStreamPair_tapeCount_le
    have hKExact : K =
          streamFoldPairTapeCount nextCompiler emitCompiler
            (listZipWithLeftFinishCompiler eTA) := rfl
    exact hKExact.trans_le hKRaw
  have hB : 1 ≤ B := by simp [B]
  have hstream : streamCompiler.workspace streamInput ≤
      20000000000000000000000 * B := by
    change (listFoldEmitCompiler (encList eTA) eTape encBits nextCompiler emitBits
      hresult).workspace streamInput ≤ _
    have hinner :
        16000000000000000000 * B + 40000 * B + 48 * B +
            20 * K + 90 ≤
          30000000000000000000 * B := by
      omega
    have hbulk :
        2 * K * (16000000000000000000 * B + 40000 * B + 48 * B + 20 * K + 90) ≤
          2 * 250 * (30000000000000000000 * B) := Nat.mul_le_mul
      (Nat.mul_le_mul_left 2 hK) hinner
    have htail :
        13 * B + 5 * K + 43 ≤ 2000 * B := by
      omega
    have hsum :
        2 * K * (16000000000000000000 * B + 40000 * B + 48 * B + 20 * K + 90) +
            13 * B + 5 * K + 43 ≤
          2 * 250 * (30000000000000000000 * B) + 2000 * B := by
      simpa only [Nat.add_assoc] using Nat.add_le_add hbulk htail
    have hcoarse :
        2 * 250 * (30000000000000000000 * B) + 2000 * B ≤
          20000000000000000000000 * B := by
      calc
        2 * 250 * (30000000000000000000 * B) + 2000 * B =
            15000000000000000002000 * B := by ring
        _ ≤ 20000000000000000000000 * B :=
          Nat.mul_le_mul_right B (by norm_num)
    exact hstreamRaw.trans (hsum.trans hcoarse)
  have hmarshalTime : marshal.time input ≤ 1000 * B := by
    simpa only [marshal, B] using applyTapesMarshal_time_le input
  have hmarshalSpace : marshal.workspace input ≤ 1000 * B := by
    simpa only [marshal, B] using applyTapesMarshal_workspace_le input
  have hmarshalCount : marshal.tapeCount ≤ 10 := by
    simpa only [marshal] using applyTapesMarshal_tapeCount_le
  have hcomp := workspace_comp_le streamCompiler marshal input
  have hstreamCount : streamCompiler.tapeCount ≤ 250 := by
    change streamFoldPairTapeCount (listZipWithLeftNextCompiler eTape eTA)
      (listZipWithLeftEmitCompiler (none, .zero) eTape eTA eTape tapeApply)
      (listZipWithLeftFinishCompiler eTA) ≤ 250
    exact applyTapesStreamPair_tapeCount_le
  have hmax : max marshal.tapeCount streamCompiler.tapeCount ≤ 250 :=
    max_le (hmarshalCount.trans (by omega)) hstreamCount
  have hstream' : streamCompiler.workspace (input.2, input.1) ≤
      20000000000000000000000 * B := by
    simpa only [streamInput] using hstream
  change (streamCompiler.comp marshal).workspace input ≤
    30000000000000000000000 * B
  exact hcomp.trans (by omega)

/-- A construction-derived static tape-count bound for the retained left-length tape-action
compiler. -/
theorem applyTapes_tapeCount_le : applyTapes.tapeCount ≤ 252 := by
  let streamCompiler :=
    listZipWithLeftStreamCompiler (none, .zero) eTape eTA eTape tapeApply
  let marshal := (second (encList eTape) (encList eTA)).pair
    (first (encList eTape) (encList eTA))
  have hmarshal : marshal.tapeCount ≤ 10 := by
    simpa only [marshal] using applyTapesMarshal_tapeCount_le
  have hstream : streamCompiler.tapeCount ≤ 250 := by
    change streamFoldPairTapeCount (listZipWithLeftNextCompiler eTape eTA)
      (listZipWithLeftEmitCompiler (none, .zero) eTape eTA eTape tapeApply)
      (listZipWithLeftFinishCompiler eTA) ≤ 250
    exact applyTapesStreamPair_tapeCount_le
  change (streamCompiler.comp marshal).tapeCount ≤ 252
  simp only [comp]
  omega

/-- Retained work-head reads, executing the named tape-read callback once per zipper. -/
@[expose] noncomputable def reads :
    NativeCompiler (List.map Tape.read) (encList eTape) (encList eSym) :=
  listMapCompiler eTape eSym tapeRead

/-- Retained input-symbol lookup. Position zero is the left blank; positive positions use a
binary predecessor followed by the charged binary-indexed list scan. -/
@[expose] noncomputable def inputSymbol :
    NativeCompiler (fun input : List ℕ × ℕ =>
      Turing.MultiTapeTM.Universal.inputSymbol input.1 input.2)
      (encPair (encList encUnary) encNat) eSym := by
  let encInput := encPair (encList encUnary) encNat
  let word := first (encList encUnary) encNat
  let position := second (encList encUnary) encNat
  let atLeftBoundary := natIsZeroTest.comp position
  let blank := const encInput eSym none
  let index := natPred.comp position
  let lookup := (listGet?NatCompiler encUnary).comp (word.pair index)
  refine (ite atLeftBoundary blank lookup).ofOutputEq ?_
  rintro ⟨word, position⟩
  cases position <;> simp [Turing.MultiTapeTM.Universal.inputSymbol, List.head?_drop]

/-- Retained boundary-aware input-head movement. The positive branch tests binary zero and the
standard option tag explicitly before selecting the concrete successor or identity machines. -/
@[expose] noncomputable def moveInput :
    NativeCompiler (fun (position, symbol, movement) =>
      Turing.MultiTapeTM.Universal.moveInput position symbol movement)
      (encPair encNat (encPair eSym encSign)) encNat := by
  let position := first encNat (encPair eSym encSign)
  let tail := second encNat (encPair eSym encSign)
  let symbol := (first eSym encSign).comp tail
  let movement := (second eSym encSign).comp tail
  let signIs (sign : SignType) := (wordEqTest encSign).comp
    (movement.pair (const (encPair encNat (encPair eSym encSign)) encSign sign))
  let stay := position
  let predecessor := natPred.comp position
  let successor := natSucc.comp position
  let atLeftBoundary := natIsZeroTest.comp position
  let readsSymbol := (optionIsSomeTest encUnary).comp symbol
  let positive := ite atLeftBoundary successor (ite readsSymbol successor stay)
  let assembled := ite (signIs .zero) stay (ite (signIs .neg) predecessor positive)
  refine assembled.ofOutputEq ?_
  rintro ⟨position, symbol, movement⟩
  cases movement <;> cases position <;> cases symbol <;>
    simp [Turing.MultiTapeTM.Universal.moveInput]

end Turing.MultiTapeTM.Internal.NativeCompiler
