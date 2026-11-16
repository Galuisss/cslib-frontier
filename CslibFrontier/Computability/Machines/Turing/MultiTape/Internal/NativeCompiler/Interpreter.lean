/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Replicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ReplicateResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Output
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.BitLength

/-!
# Concrete retained bounded interpretation

This concrete-only component installs an actual deterministic interpreter for a fixed description
and a unary clock. It streams emitted symbols instead of retaining and repeatedly copying the
output prefix. The clock controls simulated steps; the returned compiler charges the interpreter's
own native execution and workspace separately. Its complete installed description includes the
interpreted program.

Polynomial majorants for this exact interpreter, and its use with the adversary certificate's
dominating polynomial clock, remain part of the open certificate bridge in issue #5281.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.simulateOutputCompiler`: retained bounded simulation
  with exact output semantics and construction-derived time and workspace maps.
* `Turing.MultiTapeTM.Internal.NativeCompiler.simulateBitOutputCompiler`: bit input and output
  adapters retained in the installed interpreter.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM.Universal

private noncomputable def contextStepCompiler :
    NativeCompiler (fun c : Ctx => Universal.step c.desc c.input c.cfg)
      eCtx (encPair eCfg eSym) := by
  let original := first (encPair eDesc (encList encUnary)) eCfg
  let description := (first eDesc (encList encUnary)).comp original
  let word := (second eDesc (encList encUnary)).comp original
  let cfg := second (encPair eDesc (encList encUnary)) eCfg
  exact stepCompiler.comp (description.pair (word.pair cfg))

private theorem contextStepCompiler_time_le (ctx : Ctx) :
    contextStepCompiler.time ctx ≤
      stepCompiler.time (ctx.desc, ctx.input, ctx.cfg) + 128 * ((eCtx ctx).length + 1) := by
  simp only [contextStepCompiler, comp, pair, first, second, ofTransducer, encodeFrame,
    eCtx, length_encPair, Ctx.desc, Ctx.input, Ctx.cfg]
  omega

private theorem contextStepCompiler_workspace_le (ctx : Ctx) :
    contextStepCompiler.workspace ctx ≤
      stepCompiler.workspace (ctx.desc, ctx.input, ctx.cfg) +
        256 * ((eCtx ctx).length + 1) + 6 * max 4 stepCompiler.tapeCount := by
  simp only [contextStepCompiler, comp, pair, first, second, ofTransducer, encodeFrame,
    eCtx, length_encPair, Ctx.desc, Ctx.input, Ctx.cfg]
  omega

private def interpreterNext (input : Ctx × Bool) : Ctx :=
  ((input.1.desc, input.1.input), (Universal.step input.1.desc input.1.input input.1.cfg).1)

private def interpreterEmit (input : Ctx × Bool) : List Bool :=
  encList encUnary (Universal.step input.1.desc input.1.input input.1.cfg).2.toList

private noncomputable def interpreterNextCompiler :
    NativeCompiler interpreterNext (encPair eCtx encBool) eCtx := by
  let ctx := first eCtx encBool
  let fixed := (first (encPair eDesc (encList encUnary)) eCfg).comp ctx
  let advanced := (first eCfg eSym).comp (contextStepCompiler.comp ctx)
  exact (fixed.pair advanced).ofOutputEq fun _ => rfl

private noncomputable def interpreterEmitCompiler :
    NativeCompiler interpreterEmit (encPair eCtx encBool) encBits := by
  let ctx := first eCtx encBool
  let emitted := (second eCfg eSym).comp (contextStepCompiler.comp ctx)
  exact ((optionToListCompiler encUnary).comp emitted).ofOutputEq fun _ => rfl

private theorem interpreterNextCompiler_time_le (input : Ctx × Bool) :
    interpreterNextCompiler.time input ≤ contextStepCompiler.time input.1 +
      256 * ((eCtx input.1).length +
        (encPair eCfg eSym (Universal.step input.1.desc input.1.input input.1.cfg)).length +
        1) := by
  simp only [interpreterNextCompiler, ofOutputEq, comp, pair, first, ofTransducer,
    encodeFrame, eCtx, length_encPair, encBool_apply, List.length_singleton,
    Ctx.desc, Ctx.input, Ctx.cfg]
  omega

private theorem interpreterNextCompiler_workspace_le (input : Ctx × Bool) :
    interpreterNextCompiler.workspace input ≤ contextStepCompiler.workspace input.1 +
      256 * ((eCtx input.1).length +
        (encPair eCfg eSym (Universal.step input.1.desc input.1.input input.1.cfg)).length + 1) +
      256 * (contextStepCompiler.tapeCount + 1) := by
  simp only [interpreterNextCompiler, ofOutputEq, comp, pair, first, ofTransducer,
    encodeFrame, eCtx, length_encPair, encBool_apply, List.length_singleton,
    Ctx.desc, Ctx.input, Ctx.cfg]
  omega

private theorem interpreterEmitCompiler_time_le (input : Ctx × Bool) :
    interpreterEmitCompiler.time input ≤ contextStepCompiler.time input.1 +
      256 * ((eCtx input.1).length +
        (encPair eCfg eSym (Universal.step input.1.desc input.1.input input.1.cfg)).length +
        1) := by
  cases hsymbol : (Universal.step input.1.desc input.1.input input.1.cfg).2 <;>
    simp only [interpreterEmitCompiler, ofOutputEq, comp, optionToListCompiler,
      optionIsSomeTest, boolToTest, optionIsSomeBool, boolDecoder, optionPayload, tailDecoder,
      ofInputEq, ite, first, second, ofTransducer, encodeFrame, const, eCtx,
      length_encPair, encBool_apply,
      Ctx.desc, Ctx.input, Ctx.cfg, eSym, hsymbol, encOption_none, encOption_some,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte,
      encBits_apply, encTest_false, encTest_true, List.length_nil, List.length_cons,
      List.tail_cons]
  all_goals omega

private theorem interpreterEmitCompiler_workspace_le (input : Ctx × Bool) :
    interpreterEmitCompiler.workspace input ≤ contextStepCompiler.workspace input.1 +
      256 * ((eCtx input.1).length +
        (encPair eCfg eSym (Universal.step input.1.desc input.1.input input.1.cfg)).length + 1) +
      256 * (contextStepCompiler.tapeCount + 1) := by
  cases hsymbol : (Universal.step input.1.desc input.1.input input.1.cfg).2 <;>
    simp only [interpreterEmitCompiler, ofOutputEq, comp, optionToListCompiler,
      optionIsSomeTest, boolToTest, optionIsSomeBool, boolDecoder, optionPayload, tailDecoder,
      ofInputEq, ite, first, second, ofTransducer, encodeFrame, const, eCtx,
      length_encPair, encBool_apply,
      Ctx.desc, Ctx.input, Ctx.cfg, eSym, hsymbol, encOption_none, encOption_some,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte,
      encBits_apply, encTest_false, encTest_true, List.length_nil, List.length_cons,
      List.tail_cons]
  all_goals omega

private theorem interpreterEmit_eq (ctx : Ctx) (tokens : List Bool) :
    streamEmit interpreterNext interpreterEmit ctx tokens =
      encList encUnary ((stepOut ctx.desc ctx.input)^[tokens.length] (ctx.cfg, [])).2 := by
  induction tokens generalizing ctx with
  | nil => rfl
  | cons bit tokens ih =>
      rw [streamEmit, ih, List.length_cons, Function.iterate_succ_apply]
      simp only [interpreterNext, interpreterEmit, Ctx.desc, Ctx.input, Ctx.cfg, stepOut,
        List.nil_append]
      rw [stepOut_iterate_append ctx.desc ctx.input tokens.length
        (Universal.step ctx.desc ctx.input ctx.cfg).1
        (Universal.step ctx.desc ctx.input ctx.cfg).2.toList, encList_append]

private theorem interpreter_state (description : Desc) (word : List ℕ)
    (tokens : List Bool) (j : ℕ) (hj : j ≤ tokens.length) :
    streamState ((description, word), Universal.init description) interpreterNext tokens j =
      ((description, word),
        ((stepOut description word)^[j] (Universal.init description, [])).1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [streamState_succ _ _ _ (by omega), ih (by omega),
        Function.iterate_succ_apply']
      rfl

private theorem interpreter_state_length_le (description : Desc) (word : List ℕ)
    (tokens : List Bool) (j : ℕ) (hj : j ≤ tokens.length) :
    (eCtx (streamState ((description, word), Universal.init description)
      interpreterNext tokens j)).length ≤
        ctxBound (descLen description) (encList encUnary word).length tokens.length := by
  rw [interpreter_state description word tokens j hj]
  exact (length_eCtx_le description word (inv_iterate description word j).1).trans
    (ctxBound_mono hj)

private theorem interpreter_step_output_length_le (description : Desc) (word : List ℕ)
    (tokens : List Bool) (j : ℕ) (hj : j < tokens.length) :
    let ctx : Ctx := streamState ((description, word), Universal.init description)
      interpreterNext tokens j
    (encPair eCfg eSym (Universal.step ctx.desc ctx.input ctx.cfg)).length ≤
      2 * ctxBound (descLen description) (encList encUnary word).length tokens.length +
        descLen description + 2 := by
  dsimp only
  have hnext := interpreter_state_length_le description word tokens (j + 1) (by omega)
  rw [streamState_succ _ _ _ hj] at hnext
  rw [interpreter_state description word tokens j hj.le] at hnext ⊢
  have hsymbol := length_eSym_le ((inv_iterate description word j).1.step description).2
  simp only [interpreterNext, eCtx, length_encPair, Ctx.desc, Ctx.input, Ctx.cfg] at hnext ⊢
  omega

private noncomputable def interpreterStreamCompiler :
    NativeCompiler
      (fun input : Ctx × List Bool =>
        ((stepOut input.1.desc input.1.input)^[input.2.length] (input.1.cfg, [])).2)
      (encPair eCtx (encList encBool)) (encList encUnary) :=
  listFoldEmitCompiler eCtx encBool (encList encUnary)
    interpreterNextCompiler interpreterEmitCompiler fun input =>
      (interpreterEmit_eq input.1 input.2).symm

private theorem interpreterStreamCompiler_time_le (description : Desc) (word : List ℕ)
    (tokens : List Bool) (stepTime : ℕ)
    (hstep : ∀ j, j < tokens.length →
      stepCompiler.time (description, word,
        ((stepOut description word)^[j] (Universal.init description, [])).1) ≤ stepTime) :
    let lengthBound := ctxBound (descLen description) (encList encUnary word).length tokens.length
    interpreterStreamCompiler.time (((description, word), Universal.init description), tokens) ≤
      tokens.length * (2 * stepTime +
        5000 * (lengthBound + descLen description + tokens.length + 1)) +
      100 * (lengthBound + descLen description + tokens.length + 1) := by
  let L := ctxBound (descLen description) (encList encUnary word).length tokens.length
  let B := 2 * L + 3 * tokens.length + 1
  let input : Ctx × List Bool := (((description, word), Universal.init description), tokens)
  let callbackTime := stepTime + 1024 * (L + descLen description + 1)
  have hinput : (encPair eCtx (encList encBool) input).length ≤ B := by
    have hinitial := interpreter_state_length_le description word tokens 0 (Nat.zero_le _)
    rw [streamState_zero] at hinitial
    simp only [eCtx, length_encPair] at hinitial
    have hlist : (encList encBool tokens).length = 3 * tokens.length := by
      simp [length_encList, encBool_apply, Nat.mul_comm]
    simp only [input, length_encPair, hlist]
    dsimp only [B, L]
    omega
  have hstate : ∀ j, j ≤ input.2.length →
      (eCtx (streamState input.1 interpreterNext input.2 j)).length ≤ B := by
    intro j hj
    have h := interpreter_state_length_le description word tokens j hj
    dsimp only [input, B, L]
    omega
  have helem : ∀ j (hj : j < input.2.length), (encBool input.2[j]).length ≤ B := by
    intro j hj
    simp only [encBool_apply, List.length_singleton]
    dsimp only [B]
    omega
  have hcallbacks : ∀ j (hj : j < input.2.length),
      interpreterNextCompiler.time (streamState input.1 interpreterNext input.2 j,
        input.2[j]) ≤ callbackTime ∧
      interpreterEmitCompiler.time (streamState input.1 interpreterNext input.2 j,
        input.2[j]) ≤ callbackTime := by
    intro j hj
    let ctx : Ctx := streamState input.1 interpreterNext input.2 j
    have hl := interpreter_state_length_le description word tokens j hj.le
    have ho := interpreter_step_output_length_le description word tokens j hj
    have hm := contextStepCompiler_time_le ctx
    have hn := interpreterNextCompiler_time_le (ctx, input.2[j])
    have he := interpreterEmitCompiler_time_le (ctx, input.2[j])
    have ht : stepCompiler.time (ctx.desc, ctx.input, ctx.cfg) ≤ stepTime := by
      dsimp only [ctx, input]
      rw [interpreter_state description word tokens j hj.le]
      exact hstep j hj
    change (eCtx ctx).length ≤ L at hl
    change (encPair eCfg eSym (Universal.step ctx.desc ctx.input ctx.cfg)).length ≤
      2 * L + descLen description + 2 at ho
    change interpreterNextCompiler.time (ctx, input.2[j]) ≤ callbackTime ∧
      interpreterEmitCompiler.time (ctx, input.2[j]) ≤ callbackTime
    have hcontext : contextStepCompiler.time ctx ≤ stepTime + 128 * (L + 1) :=
      hm.trans (Nat.add_le_add ht (Nat.mul_le_mul_left 128 (Nat.add_le_add_right hl 1)))
    have hlength : (eCtx ctx).length +
        (encPair eCfg eSym (Universal.step ctx.desc ctx.input ctx.cfg)).length + 1 ≤
          L + (2 * L + descLen description + 2) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add hl ho) 1
    have hcommon : contextStepCompiler.time ctx +
        256 * ((eCtx ctx).length +
          (encPair eCfg eSym (Universal.step ctx.desc ctx.input ctx.cfg)).length + 1) ≤
        callbackTime := by
      refine (Nat.add_le_add hcontext (Nat.mul_le_mul_left 256 hlength)).trans ?_
      dsimp only [callbackTime]
      omega
    exact ⟨hn.trans hcommon, he.trans hcommon⟩
  have hfinish : (const eCtx encBits []).time
      (streamState input.1 interpreterNext input.2 input.2.length) ≤ 1 := by
    simp [const, encBits_apply]
  have h := streamFoldPairTime_le interpreterNextCompiler interpreterEmitCompiler
    (const eCtx encBits []) input callbackTime callbackTime 1 B hinput hstate helem
    (fun j hj => (hcallbacks j hj).2) (fun j hj => (hcallbacks j hj).1) hfinish
  change streamFoldPairTime interpreterNextCompiler interpreterEmitCompiler
    (const eCtx encBits []) input ≤ _
  have hround : callbackTime + callbackTime + 46 * B + 60 ≤
      2 * stepTime + 5000 * (L + descLen description + tokens.length + 1) := by
    dsimp only [callbackTime, B]
    omega
  have htail : 1 + 24 * B + 40 ≤
      100 * (L + descLen description + tokens.length + 1) := by
    dsimp only [B]
    omega
  calc
    _ ≤ tokens.length * (callbackTime + callbackTime + 46 * B + 60) +
        (1 + 24 * B + 40) := by
      simpa only [input, Nat.add_assoc] using h
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left tokens.length hround) htail

private theorem interpreterStreamCompiler_workspace_le (description : Desc) (word : List ℕ)
    (tokens : List Bool) (stepSpace : ℕ)
    (hstep : ∀ j, j < tokens.length →
      stepCompiler.workspace (description, word,
        ((stepOut description word)^[j] (Universal.init description, [])).1) ≤ stepSpace) :
    let L := ctxBound (descLen description) (encList encUnary word).length tokens.length
    let K := streamFoldPairTapeCount interpreterNextCompiler interpreterEmitCompiler
      (const eCtx encBits [])
    let callbackSpace := stepSpace + 1024 * (L + descLen description + 1) +
      256 * (contextStepCompiler.tapeCount + 1) + 6 * max 4 stepCompiler.tapeCount
    interpreterStreamCompiler.workspace
        (((description, word), Universal.init description), tokens) ≤
      2 * K * (callbackSpace + callbackSpace + 48 * (L + 1) + 20 * K + 90) +
        13 * (L + 1) + 5 * K + 43 := by
  let L := ctxBound (descLen description) (encList encUnary word).length tokens.length
  let input : Ctx × List Bool := (((description, word), Universal.init description), tokens)
  let callbackSpace := stepSpace + 1024 * (L + descLen description + 1) +
    256 * (contextStepCompiler.tapeCount + 1) + 6 * max 4 stepCompiler.tapeCount
  have hstate : ∀ j, j ≤ input.2.length →
      (eCtx (streamState input.1 interpreterNext input.2 j)).length ≤ L + 1 := by
    intro j hj
    exact (interpreter_state_length_le description word tokens j hj).trans (Nat.le_succ L)
  have helem : ∀ j (hj : j < input.2.length), (encBool input.2[j]).length ≤ L + 1 := by
    intro j hj
    simp only [encBool_apply, List.length_singleton]
    omega
  have hcallbacks : ∀ j (hj : j < input.2.length),
      interpreterNextCompiler.workspace (streamState input.1 interpreterNext input.2 j,
        input.2[j]) ≤ callbackSpace ∧
      interpreterEmitCompiler.workspace (streamState input.1 interpreterNext input.2 j,
        input.2[j]) ≤ callbackSpace := by
    intro j hj
    let ctx : Ctx := streamState input.1 interpreterNext input.2 j
    have hl := interpreter_state_length_le description word tokens j hj.le
    have ho := interpreter_step_output_length_le description word tokens j hj
    have hm := contextStepCompiler_workspace_le ctx
    have hn := interpreterNextCompiler_workspace_le (ctx, input.2[j])
    have he := interpreterEmitCompiler_workspace_le (ctx, input.2[j])
    have hs : stepCompiler.workspace (ctx.desc, ctx.input, ctx.cfg) ≤ stepSpace := by
      dsimp only [ctx, input]
      rw [interpreter_state description word tokens j hj.le]
      exact hstep j hj
    change (eCtx ctx).length ≤ L at hl
    change (encPair eCfg eSym (Universal.step ctx.desc ctx.input ctx.cfg)).length ≤
      2 * L + descLen description + 2 at ho
    change interpreterNextCompiler.workspace (ctx, input.2[j]) ≤ callbackSpace ∧
      interpreterEmitCompiler.workspace (ctx, input.2[j]) ≤ callbackSpace
    have hcontext : contextStepCompiler.workspace ctx ≤
        stepSpace + 256 * (L + 1) + 6 * max 4 stepCompiler.tapeCount :=
      hm.trans (Nat.add_le_add_right
        (Nat.add_le_add hs (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hl 1))) _)
    have hlength : (eCtx ctx).length +
        (encPair eCfg eSym (Universal.step ctx.desc ctx.input ctx.cfg)).length + 1 ≤
          L + (2 * L + descLen description + 2) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add hl ho) 1
    have hcommon : contextStepCompiler.workspace ctx +
        256 * ((eCtx ctx).length +
          (encPair eCfg eSym (Universal.step ctx.desc ctx.input ctx.cfg)).length + 1) +
        256 * (contextStepCompiler.tapeCount + 1) ≤ callbackSpace := by
      refine (Nat.add_le_add_right
        (Nat.add_le_add hcontext (Nat.mul_le_mul_left 256 hlength)) _).trans ?_
      have hscalar (a b : ℕ) :
          stepSpace + 256 * (L + 1) + a +
            256 * (L + (2 * L + descLen description + 2) + 1) + b ≤
          stepSpace + 1024 * (L + descLen description + 1) + b + a := by omega
      exact hscalar _ _
    exact ⟨hn.trans hcommon, he.trans hcommon⟩
  exact listFoldEmitCompiler_workspace_le interpreterNextCompiler interpreterEmitCompiler
    (fun input => (interpreterEmit_eq input.1 input.2).symm) input
    callbackSpace callbackSpace (L + 1) hstate helem
    (fun j hj => (hcallbacks j hj).2) (fun j hj => (hcallbacks j hj).1)

private noncomputable def interpreterInputCompiler (description : Desc) :
    NativeCompiler
      (fun input : List ℕ × ℕ =>
        (((description, input.1), Universal.init description), List.replicate input.2 true))
      (encPair (encList encUnary) encUnary) (encPair eCtx (encList encBool)) := by
  let encInput := encPair (encList encUnary) encUnary
  let word := first (encList encUnary) encUnary
  let ticks := unaryTrueListCompiler.comp (second (encList encUnary) encUnary)
  let fixed := (const encInput eDesc description).pair word
  let ctx := fixed.pair (const encInput eCfg (Universal.init description))
  exact ctx.pair ticks

private theorem interpreterInputCompiler_time_le (description : Desc) (word : List ℕ)
    (count : ℕ) :
    (interpreterInputCompiler description).time (word, count) ≤
      1000 * (descLen description + (eCfg (Universal.init description)).length +
        (encList encUnary word).length + count + 1) := by
  have ht := unaryTrueListCompiler_time_le count
  simp only [interpreterInputCompiler, pair, comp, first, second, const, ofTransducer,
    encodeFrame, length_encPair, encUnary_apply, List.length_replicate, descLen,
    Function.const_apply] at ht ⊢
  omega

private theorem interpreterInputCompiler_workspace_le (description : Desc) (word : List ℕ)
    (count : ℕ) :
    (interpreterInputCompiler description).workspace (word, count) ≤
      1000 * (descLen description + (eCfg (Universal.init description)).length +
        (encList encUnary word).length + count + 1) := by
  have hs := unaryTrueListCompiler_workspace_le count
  have hk : unaryTrueListCompiler.tapeCount = 2 := rfl
  simp only [interpreterInputCompiler, pair, comp, first, second, const, ofTransducer,
    encodeFrame, hk, length_encPair, encUnary_apply, List.length_replicate,
    length_encList, descLen, Function.const_apply]
  omega

private theorem interpreterInput_length_le (description : Desc) (word : List ℕ) (count : ℕ) :
    (encPair eCtx (encList encBool)
      (((description, word), Universal.init description), List.replicate count true)).length ≤
      8 * (descLen description + (eCfg (Universal.init description)).length +
        (encList encUnary word).length + count + 1) := by
  have ht := length_encList_le encBool (List.replicate count true) (b := 1)
    (by intro bit hbit; simp [encBool_apply])
  simp only [List.length_replicate] at ht
  simp only [eCtx, length_encPair, descLen]
  omega

/-- Install a fixed deterministic description and execute the supplied number of simulated steps.
The compiler's time and workspace fields charge its actual finite transition table, independently
of the simulated clock. The output is valid even if the simulated program has not yet halted. -/
noncomputable def simulateOutputCompiler (description : Desc) :
    NativeCompiler (fun input : List ℕ × ℕ => (simulate description input.1 input.2).1)
      (encPair (encList encUnary) encUnary) (encList encUnary) := by
  exact (interpreterStreamCompiler.comp (interpreterInputCompiler description)).ofOutputEq
    fun input => by
    simp only [simulate, List.length_replicate, Ctx.desc, Ctx.input, Ctx.cfg]

private theorem simulateOutputCompiler_time_le (description : Desc) (word : List ℕ)
    (count stepTime : ℕ)
    (hstep : ∀ j, j < count →
      stepCompiler.time (description, word,
        ((stepOut description word)^[j] (Universal.init description, [])).1) ≤ stepTime) :
    let L := ctxBound (descLen description) (encList encUnary word).length count
    (simulateOutputCompiler description).time (word, count) ≤
      count * (2 * stepTime + 5000 * (L + descLen description + count + 1)) +
        100 * (L + descLen description + count + 1) +
        1100 * (descLen description + (eCfg (Universal.init description)).length +
          (encList encUnary word).length + count + 1) := by
  let A := descLen description + (eCfg (Universal.init description)).length +
    (encList encUnary word).length + count + 1
  have hi := interpreterInputCompiler_time_le description word count
  have hm := interpreterInput_length_le description word count
  have hs := interpreterStreamCompiler_time_le description word (List.replicate count true)
    stepTime (by simpa only [List.length_replicate] using hstep)
  simp only [List.length_replicate] at hs
  have hscalar (a b m s : ℕ) (ha : a ≤ 1000 * A) (hb : b ≤ s) (hm : m ≤ 8 * A) :
      a + b + 4 * m + 9 ≤ s + 1100 * A := by
    dsimp only [A] at *
    omega
  change (interpreterInputCompiler description).time (word, count) +
    interpreterStreamCompiler.time
      (((description, word), Universal.init description), List.replicate count true) +
    4 * (encPair eCtx (encList encBool)
      (((description, word), Universal.init description), List.replicate count true)).length +
    9 ≤ _
  exact hscalar _ _ _ _ hi hs hm

private theorem simulateOutputCompiler_workspace_le (description : Desc) (word : List ℕ)
    (count stepSpace : ℕ)
    (hstep : ∀ j, j < count →
      stepCompiler.workspace (description, word,
        ((stepOut description word)^[j] (Universal.init description, [])).1) ≤ stepSpace) :
    let L := ctxBound (descLen description) (encList encUnary word).length count
    let K := streamFoldPairTapeCount interpreterNextCompiler interpreterEmitCompiler
      (const eCtx encBits [])
    let callbackSpace := stepSpace + 1024 * (L + descLen description + 1) +
      256 * (contextStepCompiler.tapeCount + 1) + 6 * max 4 stepCompiler.tapeCount
    (simulateOutputCompiler description).workspace (word, count) ≤
      (2 * K * (callbackSpace + callbackSpace + 48 * (L + 1) + 20 * K + 90) +
        13 * (L + 1) + 5 * K + 43) +
      1100 * (descLen description + (eCfg (Universal.init description)).length +
        (encList encUnary word).length + count + 1) +
      6 * max (interpreterInputCompiler description).tapeCount
        interpreterStreamCompiler.tapeCount := by
  let A := descLen description + (eCfg (Universal.init description)).length +
    (encList encUnary word).length + count + 1
  have hi := interpreterInputCompiler_workspace_le description word count
  have hm := interpreterInput_length_le description word count
  have hs := interpreterStreamCompiler_workspace_le description word (List.replicate count true)
    stepSpace (by simpa only [List.length_replicate] using hstep)
  simp only [List.length_replicate] at hs
  have hscalar (a b m s k : ℕ) (ha : a ≤ 1000 * A) (hb : b ≤ s) (hm : m ≤ 8 * A) :
      a + b + 5 * m + (6 * k + 20) ≤ s + 1100 * A + 6 * k := by
    dsimp only [A] at *
    omega
  change (interpreterInputCompiler description).workspace (word, count) +
    interpreterStreamCompiler.workspace
      (((description, word), Universal.init description), List.replicate count true) +
    5 * (encPair eCtx (encList encBool)
      (((description, word), Universal.init description), List.replicate count true)).length +
    (6 * max (interpreterInputCompiler description).tapeCount interpreterStreamCompiler.tapeCount +
      20) ≤ _
  exact hscalar _ _ _ _ _ hi hs hm

private def inputSymbolsCompiler :
    NativeCompiler (List.map Universal.eBit) encBits (encList encUnary) := by
  let doubled : NativeCompiler (id : List Bool → List Bool) encBits encTrueDoubled :=
    ofTransducer trueDoubleT unitStateEncoding fun word => trueDoubleT_run word
  let symbols : NativeCompiler (List.map Universal.eBit) encTrueDoubled (encList encUnary) :=
    ofTransducer symbolsT Universal.eBit fun word => symbolsT_run word
  exact symbols.comp doubled

private theorem inputSymbolsCompiler_resources_le (word : List Bool) :
    inputSymbolsCompiler.time word ≤ 100 * (word.length + 1) ∧
      inputSymbolsCompiler.workspace word ≤ 100 * (word.length + 1) := by
  have hd := (trueDoubleT.computesInTimeAndSpace_toTM word).length_output_le
  change (trueDoubleT.run () word).length ≤ 2 * word.length + 3 at hd
  rw [trueDoubleT_run] at hd
  simp only [inputSymbolsCompiler, comp, ofTransducer, encBits_apply]
  constructor <;> omega

private def bitInterpreterInputCompiler :
    NativeCompiler (fun input : List Bool × ℕ => (input.1.map Universal.eBit, input.2))
      (encPair encBits encUnary) (encPair (encList encUnary) encUnary) :=
  (inputSymbolsCompiler.comp (first encBits encUnary)).pair (second encBits encUnary)

private theorem bitInterpreterInputCompiler_resources_le (word : List Bool) (count : ℕ) :
    bitInterpreterInputCompiler.time (word, count) ≤ 2000 * (word.length + count + 1) ∧
      bitInterpreterInputCompiler.workspace (word, count) ≤
        2000 * (word.length + count + 1) := by
  have hs := inputSymbolsCompiler_resources_le word
  have hl := length_encList_map_eBit_le word
  have hk : inputSymbolsCompiler.tapeCount = 2 := rfl
  simp only [bitInterpreterInputCompiler, pair, comp, first, second, ofTransducer,
    encodeFrame, hk, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  constructor <;> norm_num [Nat.max_def] <;> omega

private def outputBitCompiler :
    NativeCompiler (fun symbol : ℕ => decide (symbol = 1)) encUnary encBool :=
  ((wordEqBool encUnary).comp
    ((identity encUnary).pair (const encUnary encUnary 1))).ofOutputEq fun symbol => by
      simp only [encUnary.injective.eq_iff, id_eq, Function.const_apply]

private theorem outputBitCompiler_resources_le (symbol : ℕ) :
    outputBitCompiler.time symbol ≤ 100 * (symbol + 1) ∧
      outputBitCompiler.workspace symbol ≤ 100 * (symbol + 1) := by
  simp only [outputBitCompiler, ofOutputEq, comp, wordEqBool, ofZipTransducer,
    pair, identity, const, encodeFrame, length_encPair, encUnary_apply,
    List.length_replicate, id_eq, Function.const_apply]
  constructor <;> omega

private def outputBitEmitCompiler :
    NativeCompiler (fun input : Unit × ℕ => [decide (input.2 = 1)])
      (encPair encUnit encUnary) encBits :=
  (outputBitCompiler.comp (second encUnit encUnary)).ofOutputEq fun _ => rfl

private def outputBitsStreamCompiler :
    NativeCompiler (fun input : Unit × List ℕ => input.2.map fun symbol => decide (symbol = 1))
      (encPair encUnit (encList encUnary)) encBits :=
  listFoldEmitCompiler encUnit encUnary encBits
    (first encUnit encUnary) outputBitEmitCompiler fun input => by
      induction input.2 with
      | nil => rfl
      | cons symbol rest ih => simpa [streamEmit, encBits_apply] using ih

private theorem outputBitsStreamCompiler_resources_le (symbols : List ℕ) :
    outputBitsStreamCompiler.time ((), symbols) ≤
        1000 * ((encList encUnary symbols).length + 1) ^ 2 ∧
      outputBitsStreamCompiler.workspace ((), symbols) ≤
        100000 * ((encList encUnary symbols).length + 1) := by
  let N := (encList encUnary symbols).length
  let input : Unit × List ℕ := ((), symbols)
  have hcount : symbols.length ≤ N := length_le_length_encList encUnary symbols
  have hstate : ∀ j, j ≤ input.2.length →
      (encUnit (streamState input.1 Prod.fst input.2 j)).length ≤ N + 1 := by
    simp [encUnit_apply]
  have helem : ∀ j (hj : j < input.2.length), (encUnary input.2[j]).length ≤ N + 1 := by
    intro j hj
    exact (SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
      symbols symbols[j] (List.getElem_mem hj)).trans (Nat.le_succ N)
  have hemit : ∀ j (hj : j < input.2.length),
      outputBitEmitCompiler.time (streamState input.1 Prod.fst input.2 j, input.2[j]) ≤
        200 * (N + 1) ∧
      outputBitEmitCompiler.workspace (streamState input.1 Prod.fst input.2 j, input.2[j]) ≤
        200 * (N + 1) := by
    intro j hj
    have hsymbol := SizedListEncoding.length_elem_le (encA := encUnary)
      (encL := encList encUnary) symbols symbols[j] (List.getElem_mem hj)
    have hb := outputBitCompiler_resources_le symbols[j]
    have hk : outputBitCompiler.tapeCount = 4 := rfl
    simp only [encUnary_apply, List.length_replicate] at hsymbol
    simp only [outputBitEmitCompiler, ofOutputEq, comp, second, ofTransducer, hk,
      length_encPair, encUnit_apply, List.length_nil, encUnary_apply, List.length_replicate]
    change symbols[j] ≤ N at hsymbol
    dsimp only [input]
    constructor <;> omega
  have hnext : ∀ j (hj : j < input.2.length),
      (first encUnit encUnary).time
        (streamState input.1 Prod.fst input.2 j, input.2[j]) ≤ 20 * (N + 1) := by
    intro j hj
    have h := helem j hj
    simp only [first, ofTransducer, length_encPair, encUnit_apply, List.length_nil]
    omega
  have ht := streamFoldPairTime_le (first encUnit encUnary) outputBitEmitCompiler
    (const encUnit encBits []) input (200 * (N + 1)) (20 * (N + 1)) 1 (N + 1)
    (by simp [input, encUnit_apply, N]) hstate helem
    (fun j hj => (hemit j hj).1) hnext (by simp [const, encBits_apply])
  have hs : outputBitsStreamCompiler.workspace input ≤
      2 * 21 * (200 * (N + 1) + 0 + 48 * (N + 1) + 20 * 21 + 90) +
        13 * (N + 1) + 5 * 21 + 43 := by
    apply listFoldEmitCompiler_workspace_le (first encUnit encUnary) outputBitEmitCompiler
    · exact hstate
    · exact helem
    · exact fun j hj => (hemit j hj).2
    · intro j hj
      simp [first, ofTransducer]
  change outputBitsStreamCompiler.time input ≤
    input.2.length * (200 * (N + 1) + 20 * (N + 1) + 46 * (N + 1) + 60) +
      1 + 24 * (N + 1) + 40 at ht
  change outputBitsStreamCompiler.time input ≤ 1000 * (N + 1) ^ 2 ∧
    outputBitsStreamCompiler.workspace input ≤ 100000 * (N + 1)
  constructor
  · refine ht.trans ?_
    have hm := Nat.mul_le_mul_right (200 * (N + 1) + 20 * (N + 1) + 46 * (N + 1) + 60) hcount
    change input.2.length * _ ≤ _ at hm
    nlinarith
  · omega

private def outputBitsCompiler :
    NativeCompiler (List.map fun symbol : ℕ => decide (symbol = 1))
      (encList encUnary) encBits :=
  (outputBitsStreamCompiler.comp
    ((const (encList encUnary) encUnit ()).pair (identity (encList encUnary)))).ofOutputEq
      fun _ => rfl

private theorem outputBitsCompiler_resources_le (symbols : List ℕ) :
    outputBitsCompiler.time symbols ≤ 2000 * ((encList encUnary symbols).length + 1) ^ 2 ∧
      outputBitsCompiler.workspace symbols ≤
        200000 * ((encList encUnary symbols).length + 1) := by
  have hs := outputBitsStreamCompiler_resources_le symbols
  have hk : outputBitsStreamCompiler.tapeCount = 21 := rfl
  simp only [outputBitsCompiler, ofOutputEq, comp, pair, const, identity, encodeFrame, hk,
    length_encPair, encUnit_apply, List.length_nil, Function.const_apply, id_eq]
  constructor <;> norm_num [Nat.max_def] <;> nlinarith

/-- Bounded interpretation with literal bit-symbol adapters. A simulated output symbol is read
as `true` exactly when it is `1`; callers claiming bit-output semantics must establish that the
simulated output is the image of a bit word under `Universal.eBit`. -/
noncomputable def simulateBitOutputCompiler (description : Desc) :
    NativeCompiler
      (fun input : List Bool × ℕ =>
        ((simulate description (input.1.map Universal.eBit) input.2).1).map
          fun symbol => decide (symbol = 1))
      (encPair encBits encUnary) encBits :=
  outputBitsCompiler.comp ((simulateOutputCompiler description).comp bitInterpreterInputCompiler)

private theorem simulateBitOutputCompiler_resources_le (description : Desc)
    (word : List Bool) (count simulationTime simulationSpace : ℕ)
    (htime : (simulateOutputCompiler description).time (word.map Universal.eBit, count) ≤
      simulationTime)
    (hspace : (simulateOutputCompiler description).workspace (word.map Universal.eBit, count) ≤
      simulationSpace) :
    let A := word.length + count + 1
    let O := count * (2 * descLen description + 1)
    let K₁ := max bitInterpreterInputCompiler.tapeCount
      (simulateOutputCompiler description).tapeCount
    let K₂ := max ((simulateOutputCompiler description).comp bitInterpreterInputCompiler).tapeCount
      outputBitsCompiler.tapeCount
    (simulateBitOutputCompiler description).time (word, count) ≤
        simulationTime + 10000 * A + 10000 * (O + 1) ^ 2 ∧
      (simulateBitOutputCompiler description).workspace (word, count) ≤
        simulationSpace + 10000 * A + 300000 * (O + 1) + 6 * K₁ + 6 * K₂ := by
  let A := word.length + count + 1
  let O := count * (2 * descLen description + 1)
  let output := (simulate description (word.map Universal.eBit) count).1
  have hi := bitInterpreterInputCompiler_resources_le word count
  have hbits := length_encList_map_eBit_le word
  have hm : (encPair (encList encUnary) encUnary (word.map Universal.eBit, count)).length ≤
      7 * A := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    dsimp only [A]
    omega
  have hinv := inv_iterate description (word.map Universal.eBit) count
  have ho : (encList encUnary output).length ≤ O := by
    have hsymbols : ∀ symbol ∈ output, (encUnary symbol).length ≤ descLen description := by
      simpa only [output, simulate, encUnary_apply, List.length_replicate] using hinv.2.2
    have hlength : output.length ≤ count := by
      simpa only [output, simulate] using hinv.2.1
    exact (length_encList_le encUnary output hsymbols).trans
      (Nat.mul_le_mul_right (2 * descLen description + 1) hlength)
  have hd := outputBitsCompiler_resources_le output
  have hdTime : outputBitsCompiler.time output ≤ 2000 * (O + 1) ^ 2 :=
    hd.1.trans (Nat.mul_le_mul_left 2000
      (Nat.pow_le_pow_left (Nat.add_le_add_right ho 1) 2))
  have hdSpace : outputBitsCompiler.workspace output ≤ 200000 * (O + 1) :=
    hd.2.trans (Nat.mul_le_mul_left 200000 (Nat.add_le_add_right ho 1))
  constructor
  · have hscalar (i t d m o : ℕ) (hi : i ≤ 2000 * A) (ht : t ≤ simulationTime)
        (hd : d ≤ 2000 * (O + 1) ^ 2) (hm : m ≤ 7 * A) (ho : o ≤ O) :
        i + t + 4 * m + 9 + d + 4 * o + 9 ≤
          simulationTime + 10000 * A + 10000 * (O + 1) ^ 2 := by
      have hO : O ≤ (O + 1) ^ 2 := by nlinarith
      dsimp only [A] at *
      omega
    change bitInterpreterInputCompiler.time (word, count) +
      (simulateOutputCompiler description).time (word.map Universal.eBit, count) +
      4 * (encPair (encList encUnary) encUnary (word.map Universal.eBit, count)).length + 9 +
      outputBitsCompiler.time output + 4 * (encList encUnary output).length + 9 ≤ _
    exact hscalar _ _ _ _ _ hi.1 htime hdTime hm ho
  · have hscalar (i s d m o k₁ k₂ : ℕ) (hi : i ≤ 2000 * A)
        (hs : s ≤ simulationSpace) (hd : d ≤ 200000 * (O + 1))
        (hm : m ≤ 7 * A) (ho : o ≤ O) :
        i + s + 5 * m + (6 * k₁ + 20) + d + 5 * o + (6 * k₂ + 20) ≤
          simulationSpace + 10000 * A + 300000 * (O + 1) + 6 * k₁ + 6 * k₂ := by
      dsimp only [A] at *
      omega
    change bitInterpreterInputCompiler.workspace (word, count) +
      (simulateOutputCompiler description).workspace (word.map Universal.eBit, count) +
      5 * (encPair (encList encUnary) encUnary (word.map Universal.eBit, count)).length +
      (6 * max bitInterpreterInputCompiler.tapeCount
        (simulateOutputCompiler description).tapeCount + 20) +
      outputBitsCompiler.workspace output + 5 * (encList encUnary output).length +
      (6 * max ((simulateOutputCompiler description).comp bitInterpreterInputCompiler).tapeCount
        outputBitsCompiler.tapeCount + 20) ≤ _
    exact hscalar _ _ _ _ _ _ _ hi.2 hspace hdSpace hm ho

private theorem interpreterStepInput_length_le (description : Desc) (word : List ℕ)
    (count j : ℕ) (hj : j ≤ count) :
    (encPair eDesc (encPair (encList encUnary) eCfg)
      (description, word,
        ((stepOut description word)^[j] (Universal.init description, [])).1)).length ≤
      ctxBound (descLen description) (encList encUnary word).length count := by
  have h := (length_eCtx_le description word (inv_iterate description word j).1).trans
    (ctxBound_mono hj)
  simp only [eCtx, length_encPair, descLen] at h ⊢
  omega

private theorem simulateBitOutputCompiler_time_le_of_stepBound (description : Desc)
    (coefficient degree : ℕ)
    (hstep : ∀ word cfg, stepCompiler.time (description, word, cfg) ≤
      coefficient *
        ((encPair eDesc (encPair (encList encUnary) eCfg) (description, word, cfg)).length +
          1) ^ degree)
    (word : List Bool) (count : ℕ) :
    let M := descLen description + (eCfg (Universal.init description)).length + 1
    let x := word.length + count + 1
    (simulateBitOutputCompiler description).time (word, count) ≤
      2 * coefficient * (101 * M ^ 2) ^ degree * x ^ (degree + 1) +
        1000000 * M ^ 2 * x ^ 2 := by
  let D := descLen description
  let I := (eCfg (Universal.init description)).length
  let M := D + I + 1
  let x := word.length + count + 1
  let raw := word.map Universal.eBit
  let N := (encList encUnary raw).length
  let L := ctxBound D N count
  let P := 101 * M ^ 2
  let stepTime := coefficient * (L + 1) ^ degree
  have hbits : N ≤ 3 * word.length := length_encList_map_eBit_le word
  have hx : 1 ≤ x := by dsimp only [x]; omega
  have hM : 1 ≤ M := by dsimp only [M]; omega
  have hcount : count ≤ x := by dsimp only [x]; omega
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by decide) M
  have hM2x : M ≤ M ^ 2 * x := hM2.trans (Nat.le_mul_of_pos_right _ hx)
  have hxx : x ≤ M ^ 2 * x :=
    Nat.le_mul_of_pos_left _ (Nat.pow_pos hM)
  have hD : D ≤ M := by dsimp only [M]; omega
  have hD2 : D ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hD 2
  have hDx : D ≤ M ^ 2 * x := hD.trans hM2x
  have hcountOne : count + 1 ≤ x := by dsimp only [x]; omega
  have hL : L ≤ 100 * M ^ 2 * x := by
    have hcoef : 24 * D ^ 2 + 40 * D ≤ 64 * M ^ 2 := by nlinarith
    have hmain := Nat.mul_le_mul hcoef hcount
    have hN : N ≤ 3 * x := by dsimp only [x]; omega
    have heq : L = (24 * D ^ 2 + 40 * D) * count + 15 * D + 4 * N + 9 := by
      dsimp only [L, ctxBound, cfgBound, tapeBound]
      ring
    rw [heq]
    nlinarith
  have hL1 : L + 1 ≤ P * x := by dsimp only [P]; nlinarith
  have hZ : L + D + count + 1 ≤ 102 * M ^ 2 * x := by nlinarith
  have hA : D + I + N + count + 1 ≤ 4 * M ^ 2 * x := by
    have hsmall : N + count ≤ 3 * x := by dsimp only [x]; omega
    have heq : D + I + N + count + 1 = M + (N + count) := by dsimp only [M]; omega
    rw [heq]
    nlinarith
  have hO : count * (2 * D + 1) + 1 ≤ 2 * M * x := by
    have hc := Nat.mul_le_mul_right (2 * D + 1) hcount
    have hD : D + 1 ≤ M := by dsimp only [M]; omega
    have hd := Nat.mul_le_mul_right x hD
    nlinarith
  have hstepTime : stepTime ≤ coefficient * P ^ degree * x ^ degree := by
    refine (Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left hL1 degree)).trans ?_
    rw [Nat.mul_pow]
    exact le_of_eq (Nat.mul_assoc _ _ _).symm
  have hs := simulateOutputCompiler_time_le description raw count stepTime (by
    intro j hj
    exact (hstep raw _).trans (Nat.mul_le_mul_left coefficient
      (Nat.pow_le_pow_left (Nat.add_le_add_right
        (interpreterStepInput_length_le description raw count j hj.le) 1) degree)))
  have hb := (simulateBitOutputCompiler_resources_le description word count _
    ((simulateOutputCompiler description).workspace (raw, count)) hs le_rfl).1
  have hmain : count * (2 * stepTime) ≤
      2 * coefficient * P ^ degree * x ^ (degree + 1) := by
    calc
      _ ≤ x * (2 * (coefficient * P ^ degree * x ^ degree)) :=
        Nat.mul_le_mul hcount (Nat.mul_le_mul_left 2 hstepTime)
      _ = _ := by rw [pow_succ]; ring
  have hZTime : count * (5000 * (L + D + count + 1)) ≤
      510000 * M ^ 2 * x ^ 2 := by
    calc
      _ ≤ x * (5000 * (102 * M ^ 2 * x)) :=
        Nat.mul_le_mul hcount (Nat.mul_le_mul_left 5000 hZ)
      _ = _ := by ring
  have hZ' : L + D + count + 1 ≤ 102 * M ^ 2 * x ^ 2 :=
    hZ.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) x))
  have hA' : D + I + N + count + 1 ≤ 4 * M ^ 2 * x ^ 2 :=
    hA.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) x))
  have hx' : x ≤ M ^ 2 * x ^ 2 :=
    hxx.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) x))
  have hO' : (count * (2 * D + 1) + 1) ^ 2 ≤ 4 * M ^ 2 * x ^ 2 := by
    exact (Nat.pow_le_pow_left hO 2).trans (le_of_eq (by ring))
  change _ ≤ 2 * coefficient * P ^ degree * x ^ (degree + 1) +
    1000000 * M ^ 2 * x ^ 2
  change (simulateBitOutputCompiler description).time (word, count) ≤
    count * (2 * stepTime + 5000 * (L + D + count + 1)) +
      100 * (L + D + count + 1) + 1100 * (D + I + N + count + 1) +
      10000 * x + 10000 * (count * (2 * D + 1) + 1) ^ 2 at hb
  rw [Nat.mul_add] at hb
  nlinarith

end Turing.MultiTapeTM.Internal.NativeCompiler
