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

/-- Install a fixed deterministic description and execute the supplied number of simulated steps.
The compiler's time and workspace fields charge its actual finite transition table, independently
of the simulated clock. The output is valid even if the simulated program has not yet halted. -/
noncomputable def simulateOutputCompiler (description : Desc) :
    NativeCompiler (fun input : List ℕ × ℕ => (simulate description input.1 input.2).1)
      (encPair (encList encUnary) encUnary) (encList encUnary) := by
  exact (interpreterStreamCompiler.comp (interpreterInputCompiler description)).ofOutputEq
    fun input => by
    simp only [simulate, List.length_replicate, Ctx.desc, Ctx.input, Ctx.cfg]

private def inputSymbolsCompiler :
    NativeCompiler (List.map Universal.eBit) encBits (encList encUnary) := by
  let doubled : NativeCompiler (id : List Bool → List Bool) encBits encTrueDoubled :=
    ofTransducer trueDoubleT unitStateEncoding fun word => trueDoubleT_run word
  let symbols : NativeCompiler (List.map Universal.eBit) encTrueDoubled (encList encUnary) :=
    ofTransducer symbolsT Universal.eBit fun word => symbolsT_run word
  exact symbols.comp doubled

private def outputBitCompiler :
    NativeCompiler (fun symbol : ℕ => decide (symbol = 1)) encUnary encBool :=
  ((wordEqBool encUnary).comp
    ((identity encUnary).pair (const encUnary encUnary 1))).ofOutputEq fun symbol => by
      simp only [encUnary.injective.eq_iff, id_eq, Function.const_apply]

private def outputBitsCompiler :
    NativeCompiler (List.map fun symbol : ℕ => decide (symbol = 1))
      (encList encUnary) encBits := by
  let encInput := encPair encUnit encUnary
  let emit : NativeCompiler
      (fun input : Unit × ℕ => [decide (input.2 = 1)]) encInput encBits :=
    (outputBitCompiler.comp (second encUnit encUnary)).ofOutputEq fun _ => rfl
  let stream := listFoldEmitCompiler encUnit encUnary encBits
    (first encUnit encUnary) emit
    (result := fun input : Unit × List ℕ => input.2.map fun symbol => decide (symbol = 1))
    (fun input => by
      induction input.2 with
      | nil => rfl
      | cons symbol rest ih => simpa [streamEmit, encBits_apply] using ih)
  exact (stream.comp
    ((const (encList encUnary) encUnit ()).pair (identity (encList encUnary)))).ofOutputEq
      fun _ => rfl

/-- Bounded interpretation with literal bit-symbol adapters. A simulated output symbol is read
as `true` exactly when it is `1`; callers claiming bit-output semantics must establish that the
simulated output is the image of a bit word under `Universal.eBit`. -/
noncomputable def simulateBitOutputCompiler (description : Desc) :
    NativeCompiler
      (fun input : List Bool × ℕ =>
        ((simulate description (input.1.map Universal.eBit) input.2).1).map
          fun symbol => decide (symbol = 1))
      (encPair encBits encUnary) encBits := by
  let word := inputSymbolsCompiler.comp (first encBits encUnary)
  let clock := second encBits encUnary
  exact outputBitsCompiler.comp ((simulateOutputCompiler description).comp (word.pair clock))

end Turing.MultiTapeTM.Internal.NativeCompiler
