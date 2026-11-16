/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.FirstMatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Universal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.FirstMatchResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ListResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ReadsResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ResourceBounds

/-!
# Retained deterministic universal steps

This module assembles the deterministic universal interpreter's `stepWith` and `step` from named
native projections, input/work-tape reads, first-match lookup and action application. The active
path captures one lookup result and reuses it for presence testing and action extraction.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.stepWithLookupCompiler`: retained key/table lookup.
* `Turing.MultiTapeTM.Internal.NativeCompiler.stepWithCompiler`: retained step with a supplied
  input-head symbol.
* `Turing.MultiTapeTM.Internal.NativeCompiler.stepCompiler`: retained complete deterministic step.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM.Universal

private abbrev DescTail₂ := ℕ × List (Key × Act)
private abbrev eDescTail₂ : DescTail₂ ↪ List Bool :=
  encPair encUnary (encList (encPair eKey eAct))
private abbrev CfgTail₂ := ℕ × List Tape
private abbrev eCfgTail₂ : CfgTail₂ ↪ List Bool := encPair encNat (encList eTape)

private abbrev StepWithInput := Desc × (SCfg × Option ℕ)
private abbrev eStepWithInput : StepWithInput ↪ List Bool :=
  encPair eDesc (encPair eCfg eSym)
private abbrev StepWithLookupInput := StepWithInput × Option Act
private abbrev eStepWithLookupInput : StepWithLookupInput ↪ List Bool :=
  encPair eStepWithInput (encOption eAct)

/-- Retained deterministic transition table projection. -/
private noncomputable def descTable :
    NativeCompiler Desc.table eDesc (encList (encPair eKey eAct)) := by
  let tail := (second encUnary eDescTail₂).ofInputEq
    (encIn := eDesc)
    (fun description : Desc => (description.tapes, description.q₀, description.table))
    fun _ => rfl
  exact (second encUnary (encList (encPair eKey eAct))).comp tail

/-- Retained deterministic configuration-state projection. -/
private noncomputable def cfgState : NativeCompiler SCfg.state eCfg eSym :=
  (first eSym eCfgTail₂).ofInputEq
    (encIn := eCfg)
    (fun cfg : SCfg => (cfg.state, cfg.inputPos, cfg.workTapes)) fun _ => rfl

/-- Retained deterministic configuration tail. -/
private noncomputable def cfgTail₂ :
    NativeCompiler (fun cfg : SCfg => (cfg.inputPos, cfg.workTapes)) eCfg eCfgTail₂ :=
  (second eSym eCfgTail₂).ofInputEq
    (encIn := eCfg)
    (fun cfg : SCfg => (cfg.state, cfg.inputPos, cfg.workTapes)) fun _ => rfl

/-- Retained deterministic input-position projection. -/
private noncomputable def cfgInputPos : NativeCompiler SCfg.inputPos eCfg encNat :=
  (first encNat (encList eTape)).comp cfgTail₂

/-- Retained deterministic work-tape projection. -/
private noncomputable def cfgWorkTapes :
    NativeCompiler SCfg.workTapes eCfg (encList eTape) :=
  (second encNat (encList eTape)).comp cfgTail₂

/-- Retained transition key on the `stepWith` layout. -/
private noncomputable def stepWithKeyCompiler :
    NativeCompiler
      (fun input : StepWithInput =>
        let (_description, cfg, symbol) := input
        ⟨cfg.state.getD 0, symbol, cfg.workTapes.map Tape.read⟩)
      eStepWithInput eKey := by
  let tail := second eDesc (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp tail
  let symbol := (second eCfg eSym).comp tail
  let state := (optionGetD 0 encUnary).comp (cfgState.comp cfg)
  let work := reads.comp (cfgWorkTapes.comp cfg)
  exact state.pair (symbol.pair work) |>.ofOutputEq fun _ => rfl

/-- Retained first-match table lookup on the `stepWith` layout. -/
noncomputable def stepWithLookupCompiler :
    NativeCompiler
      (fun input : Desc × (SCfg × Option ℕ) =>
        let (description, cfg, symbol) := input
        firstMatch (description.table,
          ⟨cfg.state.getD 0, symbol, cfg.workTapes.map Tape.read⟩))
      (encPair eDesc (encPair eCfg eSym)) (encOption eAct) := by
  let description := first eDesc (encPair eCfg eSym)
  let table := descTable.comp description
  exact (firstMatchCompiler eKey eAct).comp (table.pair stepWithKeyCompiler)

/-- Apply one retained deterministic action on a supplied input-head symbol. -/
private noncomputable def actApplyWithCompiler :
    NativeCompiler
      (fun input : Act × (SCfg × Option ℕ) =>
        let (action, cfg, symbol) := input
        ⟨action.state,
          Universal.moveInput cfg.inputPos symbol action.inputTape,
          Turing.MultiTapeTM.Universal.applyTapes cfg.workTapes action.workTapes⟩)
      (encPair eAct (encPair eCfg eSym)) eCfg := by
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let symbol := (second eCfg eSym).comp cfgSymbol
  let state := actState.comp action
  let position := cfgInputPos.comp cfg
  let movedInput := moveInput.comp
    (position.pair (symbol.pair (actInputMove.comp action)))
  let movedWork := applyTapes.comp
    ((cfgWorkTapes.comp cfg).pair (actWorkActions.comp action))
  exact state.pair (movedInput.pair movedWork) |>.ofOutputEq fun _ => rfl

/-- Interpret a captured deterministic lookup result without rescanning the table. -/
private def stepWithFromLookup : StepWithLookupInput → SCfg × Option ℕ
  | ((_description, cfg, symbol), lookup) =>
      match lookup with
      | none => ({ cfg with state := none }, none)
      | some action =>
          (⟨action.state,
            Universal.moveInput cfg.inputPos symbol action.inputTape,
            Turing.MultiTapeTM.Universal.applyTapes cfg.workTapes action.workTapes⟩,
            action.output)

/-- Retained post-lookup deterministic action/missing-transition stage. -/
private noncomputable def stepWithFromLookupCompiler :
    NativeCompiler stepWithFromLookup eStepWithLookupInput (encPair eCfg eSym) := by
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let hasAction := (optionIsSomeTest eAct).comp lookup
  let action := (optionGetD default eAct).comp lookup
  let applied := actApplyWithCompiler.comp (action.pair (cfg.pair symbol))
  let output := actOutput.comp action
  let successful := applied.pair output
  let haltedState := const eStepWithLookupInput eSym none
  let haltedCfg : NativeCompiler
      (fun input : StepWithLookupInput => { input.1.2.1 with state := none })
      eStepWithLookupInput eCfg :=
    (haltedState.pair ((cfgInputPos.comp cfg).pair (cfgWorkTapes.comp cfg))).ofOutputEq
      fun _ => rfl
  let missing := haltedCfg.pair (const eStepWithLookupInput eSym none)
  refine (ite hasAction successful missing).ofOutputEq ?_
  rintro ⟨⟨_, _, _⟩, lookup⟩
  cases lookup <;> rfl

/-- Retained active deterministic step with exactly one captured lookup result. -/
private noncomputable def stepWithActiveCompiler :
    NativeCompiler
      (fun input : StepWithInput =>
        let (description, cfg, symbol) := input
        let input := (description, cfg, symbol)
        stepWithFromLookup (input, firstMatch (description.table,
          ⟨cfg.state.getD 0, symbol, cfg.workTapes.map Tape.read⟩)))
      eStepWithInput (encPair eCfg eSym) :=
  stepWithFromLookupCompiler.comp
    ((identity eStepWithInput).pair stepWithLookupCompiler)

/-- Retained deterministic step with a supplied input-head symbol. Halted configurations bypass
the table scan; active configurations execute the single captured lookup stage. -/
noncomputable def stepWithCompiler :
    NativeCompiler
      (fun input : Desc × (SCfg × Option ℕ) =>
        let (description, cfg, symbol) := input
        Universal.stepWith description cfg symbol)
      (encPair eDesc (encPair eCfg eSym)) (encPair eCfg eSym) := by
  let tail := second eDesc (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp tail
  let hasState := (optionIsSomeTest encUnary).comp (cfgState.comp cfg)
  let halted := cfg.pair (const eStepWithInput eSym none)
  refine (ite hasState stepWithActiveCompiler halted).ofOutputEq ?_
  rintro ⟨description, cfg, symbol⟩
  cases hstate : cfg.state with
  | none => simp [Universal.stepWith, hstate]
  | some state =>
      generalize hlookup : description.table.find?
        (·.1 = ⟨state, symbol, cfg.workTapes.map Tape.read⟩) = lookup
      cases lookup <;>
        simp [Universal.stepWith, stepWithFromLookup, hstate, firstMatch, hlookup]

/-- Retained complete deterministic step. Input-symbol lookup is executed before the retained
`stepWith` controller. -/
noncomputable def stepCompiler :
    NativeCompiler
      (fun input : Desc × (List ℕ × SCfg) =>
        let (description, word, cfg) := input
        Universal.step description word cfg)
      (encPair eDesc (encPair (encList encUnary) eCfg)) (encPair eCfg eSym) := by
  let description := first eDesc (encPair (encList encUnary) eCfg)
  let tail := second eDesc (encPair (encList encUnary) eCfg)
  let word := (first (encList encUnary) eCfg).comp tail
  let cfg := (second (encList encUnary) eCfg).comp tail
  let symbol := inputSymbol.comp (word.pair (cfgInputPos.comp cfg))
  refine (stepWithCompiler.comp (description.pair (cfg.pair symbol))).ofOutputEq ?_
  intro input
  exact congrArg (encPair eCfg eSym) (Universal.step_eq_stepWith input.1 input.2.1 input.2.2)

/-! ### Actual resource bounds -/

private theorem inputSymbol_time_le (input : List ℕ × ℕ) :
    inputSymbol.time input ≤
      1000000000000 *
        ((encPair (encList encUnary) encNat input).length + 1) ^ 2 := by
  let L := (encPair (encList encUnary) encNat input).length
  let encInput := encPair (encList encUnary) encNat
  let word := first (encList encUnary) encNat
  let position := second (encList encUnary) encNat
  let atLeftBoundary := natIsZeroTest.comp position
  let blank := const encInput eSym none
  let index := natPred.comp position
  let lookupInput := word.pair index
  let lookup := (listGet?NatCompiler encUnary).comp lookupInput
  have hword : (encList encUnary input.1).length ≤ L := by
    exact (length_le_encPair_left (encList encUnary) encNat input).trans le_rfl
  have hposition : (encNat input.2).length ≤ L := by
    exact (length_le_encPair_right (encList encUnary) encNat input).trans le_rfl
  have hpred : (encNat (input.2 - 1)).length ≤ (encNat input.2).length :=
    length_encNat_mono (Nat.sub_le input.2 1)
  have hlookupInputSize :
      (encPair (encList encUnary) encNat (input.1, input.2 - 1)).length ≤ L := by
    simp only [L, length_encPair]
    omega
  have hcondition : atLeftBoundary.time input ≤ 1000 * (L + 1) := by
    simp [atLeftBoundary, position, natIsZeroTest, natIsZeroBool, boolToTest, second,
      comp, ofTransducer, L]
    omega
  have hblank : blank.time input ≤ 1000 * (L + 1) := by
    simp [blank, const, L]
    omega
  have hlookupInputTime : lookupInput.time input ≤ 100000 * (L + 1) := by
    simp [lookupInput, word, index, position, first, second, natPred, pair, comp, ofTransducer,
      encodeFrame, L]
    omega
  have hlookupOuter := time_listGetNatOptionCompiler_le (input.1, input.2 - 1)
  have hlookupComp := time_comp_le (listGet?NatCompiler encUnary) lookupInput input
  have hlookup : lookup.time input ≤ 100000000 * (L + 1) ^ 2 := by
    simp only [lookup]
    exact hlookupComp.trans (by nlinarith)
  have hite := time_ite_le atLeftBoundary blank lookup input
  change (ite atLeftBoundary blank lookup).time input ≤
    1000000000000 * (L + 1) ^ 2
  exact hite.trans (by nlinarith)

private theorem inputSymbol_workspace_le (input : List ℕ × ℕ) :
    inputSymbol.workspace input ≤
      1000000000000 *
        ((encPair (encList encUnary) encNat input).length + 1) ^ 2 := by
  let L := (encPair (encList encUnary) encNat input).length
  let encInput := encPair (encList encUnary) encNat
  let word := first (encList encUnary) encNat
  let position := second (encList encUnary) encNat
  let atLeftBoundary := natIsZeroTest.comp position
  let blank := const encInput eSym none
  let index := natPred.comp position
  let lookupInput := word.pair index
  let lookup := (listGet?NatCompiler encUnary).comp lookupInput
  have hword : (encList encUnary input.1).length ≤ L := by
    exact (length_le_encPair_left (encList encUnary) encNat input).trans le_rfl
  have hposition : (encNat input.2).length ≤ L := by
    exact (length_le_encPair_right (encList encUnary) encNat input).trans le_rfl
  have hpred : (encNat (input.2 - 1)).length ≤ (encNat input.2).length :=
    length_encNat_mono (Nat.sub_le input.2 1)
  have hlookupInputSize :
      (encPair (encList encUnary) encNat (input.1, input.2 - 1)).length ≤ L := by
    simp only [L, length_encPair]
    omega
  have hcondition : atLeftBoundary.workspace input ≤ 1000 * (L + 1) := by
    simp [atLeftBoundary, position, natIsZeroTest, natIsZeroBool, boolToTest, second,
      comp, ofTransducer, L]
    omega
  have hblank : blank.workspace input ≤ 1000 * (L + 1) := by
    simp [blank, const, L]
  have hlookupInputTime : lookupInput.time input ≤ 100000 * (L + 1) := by
    simp [lookupInput, word, index, position, first, second, natPred, pair, comp, ofTransducer,
      encodeFrame, L]
    omega
  have hlookupInputSpace : lookupInput.workspace input ≤ 100000 * (L + 1) := by
    simp [lookupInput, word, index, position, first, second, natPred, pair, comp, ofTransducer,
      encodeFrame, L]
    omega
  have hlookupInputTapes : lookupInput.tapeCount ≤ 20 := by
    simp [lookupInput, word, index, position, first, second, natPred, pair, comp, ofTransducer,
      encodeFrame]
  have hlookupCompilerTapes := listGetNatOptionCompiler_tapeCount_le
  have hlookupMax : max lookupInput.tapeCount
      (listGet?NatCompiler encUnary).tapeCount ≤ 202 :=
    max_le (hlookupInputTapes.trans (by omega)) hlookupCompilerTapes
  have hlookupOuter := workspace_listGetNatOptionCompiler_le (input.1, input.2 - 1)
  have hlookupComp := workspace_comp_le (listGet?NatCompiler encUnary) lookupInput input
  have hlookup : lookup.workspace input ≤ 100000000000 * (L + 1) ^ 2 := by
    simp only [lookup]
    exact hlookupComp.trans (by nlinarith)
  have hconditionTapes : atLeftBoundary.tapeCount ≤ 10 := by
    simp [atLeftBoundary, position, natIsZeroTest, natIsZeroBool, boolToTest, second,
      comp, ofTransducer]
  have hblankTapes : blank.tapeCount ≤ 10 := by
    simp [blank, const]
  have hlookupTapes : lookup.tapeCount ≤ 204 := by
    simp only [lookup, comp]
    omega
  have hstatic : max atLeftBoundary.tapeCount (max blank.tapeCount lookup.tapeCount) ≤ 204 :=
    max_le (hconditionTapes.trans (by omega))
      (max_le (hblankTapes.trans (by omega)) hlookupTapes)
  have hite := workspace_ite_le atLeftBoundary blank lookup input
  change (ite atLeftBoundary blank lookup).workspace input ≤
    1000000000000 * (L + 1) ^ 2
  exact hite.trans (by nlinarith)

private theorem stepWithKeyComponentTime_le (input : StepWithInput) :
    let L := (eStepWithInput input).length
    let tail := second eDesc (encPair eCfg eSym)
    let cfg := (first eCfg eSym).comp tail
    let symbol := (second eCfg eSym).comp tail
    let state := (optionGetD 0 encUnary).comp (cfgState.comp cfg)
    let workInput := cfgWorkTapes.comp cfg
    state.time input ≤ 1000000000 * (L + 1) ∧
      symbol.time input ≤ 1000000 * (L + 1) ∧
      workInput.time input ≤ 1000000000 * (L + 1) := by
  dsimp only
  let L := (eStepWithInput input).length
  let tail := second eDesc (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp tail
  let symbol := (second eCfg eSym).comp tail
  let state := (optionGetD 0 encUnary).comp (cfgState.comp cfg)
  let workInput := cfgWorkTapes.comp cfg
  change state.time input ≤ 1000000000 * (L + 1) ∧
    symbol.time input ≤ 1000000 * (L + 1) ∧
    workInput.time input ≤ 1000000000 * (L + 1)
  have hstateBits : ((encOption encUnary) input.2.1.state).length ≤ L := by
    change (eSym input.2.1.state).length ≤ L
    simp only [L, eCfg_apply, length_encPair]
    omega
  have hstate : state.time input ≤ 1000000000 * (L + 1) := by
    cases hoption : input.2.1.state <;>
      simp [state, cfg, tail, cfgState, first, second, optionGetD, optionPayload,
        tailDecoder, optionIsSomeTest, optionIsSomeBool, boolDecoder, boolToTest,
        ofTransducer, comp, ite, const, ofInputEq, ofOutputEq, encTest_false,
        encTest_true, hoption, L] at hstateBits ⊢ <;>
      omega
  have hsymbol : symbol.time input ≤ 1000000 * (L + 1) := by
    simp [symbol, tail, second, ofTransducer, comp, L]
    omega
  have hworkInput : workInput.time input ≤ 1000000000 * (L + 1) := by
    simp [workInput, cfg, tail, cfgWorkTapes, cfgTail₂, first, second, ofTransducer,
      comp, ofInputEq, L]
    omega
  exact ⟨hstate, hsymbol, hworkInput⟩

private theorem stepWithKeyComponentTapeCount_le :
    let tail := second eDesc (encPair eCfg eSym)
    let cfg := (first eCfg eSym).comp tail
    let symbol := (second eCfg eSym).comp tail
    let state := (optionGetD 0 encUnary).comp (cfgState.comp cfg)
    let workInput := cfgWorkTapes.comp cfg
    state.tapeCount ≤ 1000 ∧ symbol.tapeCount ≤ 100 ∧ workInput.tapeCount ≤ 100 := by
  dsimp only
  let tail := second eDesc (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp tail
  let symbol := (second eCfg eSym).comp tail
  let state := (optionGetD 0 encUnary).comp (cfgState.comp cfg)
  let workInput := cfgWorkTapes.comp cfg
  change state.tapeCount ≤ 1000 ∧ symbol.tapeCount ≤ 100 ∧
    workInput.tapeCount ≤ 100
  have hstate : state.tapeCount ≤ 1000 := by
    simp [state, cfg, tail, cfgState, first, second, optionGetD, optionPayload,
      tailDecoder, optionIsSomeTest, optionIsSomeBool, boolDecoder, boolToTest,
      ofTransducer, comp, ite, const, ofInputEq, ofOutputEq]
  have hsymbol : symbol.tapeCount ≤ 100 := by
    simp [symbol, tail, second, ofTransducer, comp]
  have hworkInput : workInput.tapeCount ≤ 100 := by
    simp [workInput, cfg, tail, cfgWorkTapes, cfgTail₂, first, second, ofTransducer,
      comp, ofInputEq]
  exact ⟨hstate, hsymbol, hworkInput⟩

private theorem stepWithKeyCompiler_time_le (input : StepWithInput) :
    stepWithKeyCompiler.time input ≤
      1000000000000000 * ((eStepWithInput input).length + 1) ^ 2 := by
  let L := (eStepWithInput input).length
  let tail := second eDesc (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp tail
  let symbol := (second eCfg eSym).comp tail
  let state := (optionGetD 0 encUnary).comp (cfgState.comp cfg)
  let workInput := cfgWorkTapes.comp cfg
  let work := reads.comp workInput
  have hworkBits : (encList eTape input.2.1.workTapes).length ≤ L := by
    simp only [L, eCfg_apply, length_encPair]
    omega
  have hcomponentTime := stepWithKeyComponentTime_le input
  obtain ⟨hstate, hsymbol, hworkInput⟩ := hcomponentTime
  have hreads := reads_time_le input.2.1.workTapes
  have hworkRaw := time_comp_le reads workInput input
  have hwork : work.time input ≤ 1000000000000 * (L + 1) ^ 2 := by
    simp only [work]
    exact hworkRaw.trans (by nlinarith)
  have htailPair := time_pair_le symbol work input
  have hfullPair := time_pair_le state (symbol.pair work) input
  change (state.pair (symbol.pair work)).time input ≤
    1000000000000000 * (L + 1) ^ 2
  exact hfullPair.trans (by nlinarith)

private theorem stepWithKeyCompiler_workspace_le (input : StepWithInput) :
    stepWithKeyCompiler.workspace input ≤
      1000000000000000 * ((eStepWithInput input).length + 1) ^ 2 := by
  let L := (eStepWithInput input).length
  let tail := second eDesc (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp tail
  let symbol := (second eCfg eSym).comp tail
  let state := (optionGetD 0 encUnary).comp (cfgState.comp cfg)
  let workInput := cfgWorkTapes.comp cfg
  let work := reads.comp workInput
  have hworkBits : (encList eTape input.2.1.workTapes).length ≤ L := by
    simp only [L, eCfg_apply, length_encPair]
    omega
  have hstateBits : ((encOption encUnary) input.2.1.state).length ≤ L := by
    change (eSym input.2.1.state).length ≤ L
    simp only [L, eCfg_apply, length_encPair]
    omega
  have hcomponentTime := stepWithKeyComponentTime_le input
  obtain ⟨hstateTime, hsymbolTime, hworkInputTime⟩ := hcomponentTime
  have hcomponentTapes := stepWithKeyComponentTapeCount_le
  have hstateTapes := hcomponentTapes.1
  change state.tapeCount ≤ 1000 at hstateTapes
  have hsymbolTapes := hcomponentTapes.2.1
  change symbol.tapeCount ≤ 100 at hsymbolTapes
  have hworkInputTapes := hcomponentTapes.2.2
  change workInput.tapeCount ≤ 100 at hworkInputTapes
  have hstateSpace : state.workspace input ≤ 1000000000 * (L + 1) := by
    cases hoption : input.2.1.state <;>
      simp [state, cfg, tail, cfgState, first, second, optionGetD, optionPayload,
        tailDecoder, optionIsSomeTest, optionIsSomeBool, boolDecoder, boolToTest,
        ofTransducer, comp, ite, const, ofInputEq, ofOutputEq, encTest_false,
        encTest_true, hoption, L] at hstateBits ⊢ <;>
      omega
  have hsymbolSpace : symbol.workspace input ≤ 1000000 * (L + 1) := by
    simp [symbol, tail, second, ofTransducer, comp, L]
    omega
  have hworkInputSpace : workInput.workspace input ≤ 1000000000 * (L + 1) := by
    simp [workInput, cfg, tail, cfgWorkTapes, cfgTail₂, first, second, ofTransducer,
      comp, ofInputEq, L]
    omega
  have hreadsSpace := reads_workspace_le input.2.1.workTapes
  have hreadsTapes := reads_tapeCount_le
  have hworkMax : max workInput.tapeCount reads.tapeCount ≤ 1002 :=
    max_le (hworkInputTapes.trans (by omega)) hreadsTapes
  have hworkRaw := workspace_comp_le reads workInput input
  have hworkSpace : work.workspace input ≤ 10000000000000 * (L + 1) ^ 2 := by
    simp only [work]
    exact hworkRaw.trans (by nlinarith)
  have hworkTapes : work.tapeCount ≤ 1004 := by
    simp only [work, comp]
    omega
  have htailMax : max (symbol.tapeCount + 2) work.tapeCount ≤ 1004 :=
    max_le (by omega) hworkTapes
  have htailRaw := workspace_pair_le symbol work input
  have htailSpace : (symbol.pair work).workspace input ≤
      100000000000000 * (L + 1) ^ 2 :=
    htailRaw.trans (by nlinarith)
  have hframedSymbolTapes : ((encodeFrame eSym).comp symbol).tapeCount ≤ 102 := by
    simp only [comp, encodeFrame]
    omega
  have htailTapes : (symbol.pair work).tapeCount ≤ 1006 := by
    simp only [pair]
    omega
  have hfullMax : max (state.tapeCount + 2) (symbol.pair work).tapeCount ≤ 1006 :=
    max_le (by omega) htailTapes
  have hfullRaw := workspace_pair_le state (symbol.pair work) input
  change (state.pair (symbol.pair work)).workspace input ≤
    1000000000000000 * (L + 1) ^ 2
  exact hfullRaw.trans (by nlinarith)

private theorem stepWithKeyCompiler_tapeCount_le : stepWithKeyCompiler.tapeCount ≤ 1008 := by
  let tail := second eDesc (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp tail
  let symbol := (second eCfg eSym).comp tail
  let state := (optionGetD 0 encUnary).comp (cfgState.comp cfg)
  let workInput := cfgWorkTapes.comp cfg
  let work := reads.comp workInput
  have hcomponentTapes := stepWithKeyComponentTapeCount_le
  have hstate := hcomponentTapes.1
  change state.tapeCount ≤ 1000 at hstate
  have hsymbol := hcomponentTapes.2.1
  change symbol.tapeCount ≤ 100 at hsymbol
  have hworkInput := hcomponentTapes.2.2
  change workInput.tapeCount ≤ 100 at hworkInput
  have hreads := reads_tapeCount_le
  change (state.pair (symbol.pair work)).tapeCount ≤ 1008
  simp only [pair, work, comp, encodeFrame]
  omega

private theorem stepWithLookupTable_tapeCount_le :
    let description := first eDesc (encPair eCfg eSym)
    (descTable.comp description).tapeCount ≤ 100 := by
  dsimp only
  let description := first eDesc (encPair eCfg eSym)
  let table := descTable.comp description
  change table.tapeCount ≤ 100
  simp [table, description, descTable, first, second, ofTransducer, comp, ofInputEq]

private theorem stepWithLookupInput_tapeCount_le :
    let description := first eDesc (encPair eCfg eSym)
    let table := descTable.comp description
    (table.pair stepWithKeyCompiler).tapeCount ≤ 1010 := by
  dsimp only
  let description := first eDesc (encPair eCfg eSym)
  let table := descTable.comp description
  have htable : table.tapeCount ≤ 100 := by
    simpa only [table, description] using stepWithLookupTable_tapeCount_le
  have hkey := stepWithKeyCompiler_tapeCount_le
  have hframedTable : ((encodeFrame (encList (encPair eKey eAct))).comp table).tapeCount ≤
      102 := by
    simp only [comp, encodeFrame]
    omega
  simp only [table, description] at hframedTable
  simp only [pair]
  omega

private theorem stepWithLookupInputResource_le (input : StepWithInput) :
    let L := (eStepWithInput input).length
    let description := first eDesc (encPair eCfg eSym)
    let table := descTable.comp description
    let lookupInput := table.pair stepWithKeyCompiler
    lookupInput.time input ≤ 2000000000000000 * (L + 1) ^ 2 ∧
      lookupInput.workspace input ≤ 2000000000000000 * (L + 1) ^ 2 ∧
      lookupInput.tapeCount ≤ 1010 := by
  dsimp only
  let L := (eStepWithInput input).length
  let description := first eDesc (encPair eCfg eSym)
  let table := descTable.comp description
  let lookupInput := table.pair stepWithKeyCompiler
  change lookupInput.time input ≤ 2000000000000000 * (L + 1) ^ 2 ∧
    lookupInput.workspace input ≤ 2000000000000000 * (L + 1) ^ 2 ∧
    lookupInput.tapeCount ≤ 1010
  have htableTime : table.time input ≤ 1000000000 * (L + 1) := by
    simp [table, description, descTable, first, second, ofTransducer, comp, ofInputEq, L]
    omega
  have htableSpace : table.workspace input ≤ 1000000000 * (L + 1) := by
    simp [table, description, descTable, first, second, ofTransducer, comp, ofInputEq, L]
    omega
  have htableTapes : table.tapeCount ≤ 100 := by
    simpa only [table, description] using stepWithLookupTable_tapeCount_le
  have hkeyTime : stepWithKeyCompiler.time input ≤
      1000000000000000 * (L + 1) ^ 2 := by
    simpa only [L] using stepWithKeyCompiler_time_le input
  have hkeySpace : stepWithKeyCompiler.workspace input ≤
      1000000000000000 * (L + 1) ^ 2 := by
    simpa only [L] using stepWithKeyCompiler_workspace_le input
  have hkeyTapes := stepWithKeyCompiler_tapeCount_le
  have htimeRaw := time_pair_le table stepWithKeyCompiler input
  have htime : lookupInput.time input ≤ 2000000000000000 * (L + 1) ^ 2 := by
    simp only [lookupInput]
    exact htimeRaw.trans (by nlinarith)
  have hmax : max (table.tapeCount + 2) stepWithKeyCompiler.tapeCount ≤ 1008 :=
    max_le (by omega) hkeyTapes
  have hspaceRaw := workspace_pair_le table stepWithKeyCompiler input
  have hspace : lookupInput.workspace input ≤ 2000000000000000 * (L + 1) ^ 2 := by
    simp only [lookupInput]
    exact hspaceRaw.trans (by nlinarith)
  have htapes : lookupInput.tapeCount ≤ 1010 := by
    simpa only [lookupInput, table, description] using stepWithLookupInput_tapeCount_le
  exact ⟨htime, hspace, htapes⟩

private theorem stepWithLookupSemanticLength_le (input : StepWithInput) :
    (encPair (encList (encPair eKey eAct)) eKey
      (input.1.table,
        ⟨input.2.1.state.getD 0, input.2.2, input.2.1.workTapes.map Tape.read⟩)).length ≤
      100 * ((eStepWithInput input).length + 1) := by
  let L := (eStepWithInput input).length
  have htable : (encList (encPair eKey eAct) input.1.table).length ≤ L := by
    simp only [L, eDesc_apply, eCfg_apply, length_encPair]
    omega
  have hwork : (encList eTape input.2.1.workTapes).length ≤ L := by
    simp only [L, eDesc_apply, eCfg_apply, length_encPair]
    omega
  have hsymbol : (eSym input.2.2).length ≤ L := by
    simp only [L, eDesc_apply, eCfg_apply, length_encPair]
    omega
  have hstateBits : (eSym input.2.1.state).length ≤ L := by
    simp only [L, eDesc_apply, eCfg_apply, length_encPair]
    omega
  have hstate := getD_le_length_eSym input.2.1.state
  have hreads := length_encList_map_read_le input.2.1.workTapes
  have hkey :
      (eKey ⟨input.2.1.state.getD 0, input.2.2,
        input.2.1.workTapes.map Tape.read⟩).length ≤ 16 * (L + 1) := by
    simp only [eKey_apply, length_encPair, encUnary_apply, List.length_replicate]
    omega
  change (encPair (encList (encPair eKey eAct)) eKey
    (input.1.table,
      ⟨input.2.1.state.getD 0, input.2.2, input.2.1.workTapes.map Tape.read⟩)).length ≤
        100 * (L + 1)
  simp only [length_encPair]
  omega

private theorem stepWithLookupCompiler_time_le (input : StepWithInput) :
    stepWithLookupCompiler.time input ≤
      (2 * 10 ^ 16) * ((eStepWithInput input).length + 1) ^ 2 := by
  let L := (eStepWithInput input).length
  let description := first eDesc (encPair eCfg eSym)
  let table := descTable.comp description
  let lookupInput := table.pair stepWithKeyCompiler
  have hinputResource := stepWithLookupInputResource_le input
  obtain ⟨hinputTime, _hinputSpace, _hinputTapes⟩ := hinputResource
  have hsemantic := stepWithLookupSemanticLength_le input
  have houter := firstMatchCompiler_time_le eKey eAct
    (input.1.table, ⟨input.2.1.state.getD 0, input.2.2, input.2.1.workTapes.map Tape.read⟩)
  have hcomp := time_comp_le (firstMatchCompiler eKey eAct) lookupInput input
  change ((firstMatchCompiler eKey eAct).comp lookupInput).time input ≤
    (2 * 10 ^ 16) * (L + 1) ^ 2
  nlinarith

private theorem stepWithLookupCompiler_workspace_le (input : StepWithInput) :
    stepWithLookupCompiler.workspace input ≤
      10 ^ 18 * ((eStepWithInput input).length + 1) ^ 2 := by
  let L := (eStepWithInput input).length
  let description := first eDesc (encPair eCfg eSym)
  let table := descTable.comp description
  let lookupInput := table.pair stepWithKeyCompiler
  have hinputResource := stepWithLookupInputResource_le input
  obtain ⟨hinputTime, hinputSpace, hinputTapes⟩ := hinputResource
  have hsemantic := stepWithLookupSemanticLength_le input
  have houterSpace := firstMatchCompiler_workspace_le eKey eAct
    (input.1.table, ⟨input.2.1.state.getD 0, input.2.2, input.2.1.workTapes.map Tape.read⟩)
  have houterTapes := firstMatchCompiler_tapeCount_le eKey eAct
  have hmax : max lookupInput.tapeCount (firstMatchCompiler eKey eAct).tapeCount ≤ 1010 :=
    max_le hinputTapes (houterTapes.trans (by omega))
  have hcomp := workspace_comp_le (firstMatchCompiler eKey eAct) lookupInput input
  change ((firstMatchCompiler eKey eAct).comp lookupInput).workspace input ≤
    10 ^ 18 * (L + 1) ^ 2
  nlinarith

private theorem stepWithLookupCompiler_tapeCount_le :
    stepWithLookupCompiler.tapeCount ≤ 1012 := by
  let description := first eDesc (encPair eCfg eSym)
  let table := descTable.comp description
  let lookupInput := table.pair stepWithKeyCompiler
  have hinput : lookupInput.tapeCount ≤ 1010 := by
    simpa only [lookupInput, table, description] using stepWithLookupInput_tapeCount_le
  have houter := firstMatchCompiler_tapeCount_le eKey eAct
  change ((firstMatchCompiler eKey eAct).comp lookupInput).tapeCount ≤ 1012
  simp only [comp]
  omega

end Turing.MultiTapeTM.Internal.NativeCompiler
