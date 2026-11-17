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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ControlResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.ListOption
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Input

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
* `Turing.MultiTapeTM.Internal.NativeCompiler.stepCompiler_time_le`, `.stepCompiler_workspace_le`,
  `.stepCompiler_tapeCount_le`: concrete resource bounds for that actual retained compiler.
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
private abbrev ActApplyInput := Act × (SCfg × Option ℕ)
private abbrev eActApplyInput : ActApplyInput ↪ List Bool :=
  encPair eAct (encPair eCfg eSym)

/-- Complete deterministic-step inputs encode the machine description first, followed by the
standard framed pair of the unary-symbol input word and universal configuration. -/
abbrev eDeterministicStepInput : (Desc × (List ℕ × SCfg)) ↪ List Bool :=
  encPair eDesc (encPair (encList encUnary) eCfg)

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
      eDeterministicStepInput (encPair eCfg eSym) := by
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

private theorem inputSymbolStaticTapeCounts_le :
    let encInput := encPair (encList encUnary) encNat
    let word := first (encList encUnary) encNat
    let position := second (encList encUnary) encNat
    let atLeftBoundary := natIsZeroTest.comp position
    let blank := const encInput eSym none
    let index := natPred.comp position
    let lookupInput := word.pair index
    let lookup := (listGet?NatCompiler encUnary).comp lookupInput
    max lookupInput.tapeCount (listGet?NatCompiler encUnary).tapeCount ≤ 202 ∧
      max atLeftBoundary.tapeCount (max blank.tapeCount lookup.tapeCount) ≤ 204 := by
  dsimp only
  have hcondition :
      (natIsZeroTest.comp (second (encList encUnary) encNat)).tapeCount ≤ 10 := by
    simp [natIsZeroTest, natIsZeroBool, boolToTest, second, comp, ofTransducer]
  have hblank :
      (const (encPair (encList encUnary) encNat) eSym none).tapeCount ≤ 10 := by
    simp [const]
  have hlookupInput :
      ((first (encList encUnary) encNat).pair
        (natPred.comp (second (encList encUnary) encNat))).tapeCount ≤ 20 := by
    simp [first, second, natPred, pair, comp, ofTransducer, encodeFrame]
  have hlookupCompiler := listGetNatOptionCompiler_tapeCount_le
  have hlookupMax :
      max ((first (encList encUnary) encNat).pair
          (natPred.comp (second (encList encUnary) encNat))).tapeCount
        (listGet?NatCompiler encUnary).tapeCount ≤ 202 :=
    max_le (hlookupInput.trans (by omega)) hlookupCompiler
  have hlookup :
      ((listGet?NatCompiler encUnary).comp
        ((first (encList encUnary) encNat).pair
          (natPred.comp (second (encList encUnary) encNat)))).tapeCount ≤ 204 := by
    change max
      ((first (encList encUnary) encNat).pair
        (natPred.comp (second (encList encUnary) encNat))).tapeCount
      (listGet?NatCompiler encUnary).tapeCount + 2 ≤ 204
    omega
  exact ⟨hlookupMax,
    max_le (hcondition.trans (by omega)) (max_le (hblank.trans (by omega)) hlookup)⟩

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
  have hstaticCounts := inputSymbolStaticTapeCounts_le
  change max lookupInput.tapeCount (listGet?NatCompiler encUnary).tapeCount ≤ 202 ∧
    max atLeftBoundary.tapeCount (max blank.tapeCount lookup.tapeCount) ≤ 204 at hstaticCounts
  obtain ⟨hlookupMax, hstatic⟩ := hstaticCounts
  have hlookupOuter := workspace_listGetNatOptionCompiler_le (input.1, input.2 - 1)
  have hlookupComp := workspace_comp_le (listGet?NatCompiler encUnary) lookupInput input
  have hlookup : lookup.workspace input ≤ 100000000000 * (L + 1) ^ 2 := by
    simp only [lookup]
    exact hlookupComp.trans (by nlinarith)
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

private theorem stepWithLookupOutput_length_le (input : StepWithInput) :
    (encOption eAct (firstMatch (input.1.table,
      ⟨input.2.1.state.getD 0, input.2.2, input.2.1.workTapes.map Tape.read⟩))).length ≤
        2 * ((eStepWithInput input).length + 1) := by
  let key : Key :=
    ⟨input.2.1.state.getD 0, input.2.2, input.2.1.workTapes.map Tape.read⟩
  have htable : (encList (encPair eKey eAct) input.1.table).length ≤
      (eStepWithInput input).length := by
    simp only [eStepWithInput, eDesc_apply, eCfg_apply, length_encPair]
    omega
  cases hfind : input.1.table.find? (·.1 = key) with
  | none => simp [firstMatch, key, hfind]
  | some entry =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hentry := length_le_encList_of_mem (encPair eKey eAct) hmem
      have hvalue := (length_le_encPair_right eKey eAct entry).trans hentry
      simp only [firstMatch, key, hfind, Option.map_some, encOption_some,
        List.length_cons]
      omega

private theorem stepWithActiveInput_length_le (input : StepWithInput) :
    (eStepWithLookupInput
      (input, firstMatch (input.1.table,
        ⟨input.2.1.state.getD 0, input.2.2, input.2.1.workTapes.map Tape.read⟩))).length ≤
        8 * ((eStepWithInput input).length + 1) := by
  have hlookup := stepWithLookupOutput_length_le input
  simp only [eStepWithLookupInput, length_encPair] at hlookup ⊢
  omega

private theorem length_eAct_default_le : (eAct (default : Act)).length ≤ 16 := by
  rw [show (default : Act) =
    { inputTape := .zero, workTapes := [], output := none, state := none } by rfl]
  simp [eAct_apply, eTA, encSign]

private theorem stepWithFromLookupActInput_length_le (input : StepWithLookupInput) :
    (eActApplyInput
      (input.2.getD default, input.1.2.1, input.1.2.2)).length ≤
        16 * ((eStepWithLookupInput input).length + 1) := by
  have haction := length_enc_getD_le (encC := eAct) input.2
  have hdefault := length_eAct_default_le
  simp only [eActApplyInput, eStepWithLookupInput, length_encPair] at haction ⊢
  omega

private theorem actApplyComponentTime_le (input : ActApplyInput) :
    let L := (eActApplyInput input).length
    let action := first eAct (encPair eCfg eSym)
    let cfgSymbol := second eAct (encPair eCfg eSym)
    let cfg := (first eCfg eSym).comp cfgSymbol
    let symbol := (second eCfg eSym).comp cfgSymbol
    let state := actState.comp action
    let position := cfgInputPos.comp cfg
    let movement := actInputMove.comp action
    let tapes := cfgWorkTapes.comp cfg
    let actions := actWorkActions.comp action
    state.time input ≤ 1000000000 * (L + 1) ∧
      position.time input ≤ 1000000000 * (L + 1) ∧
      symbol.time input ≤ 1000000000 * (L + 1) ∧
      movement.time input ≤ 1000000000 * (L + 1) ∧
      tapes.time input ≤ 1000000000 * (L + 1) ∧
      actions.time input ≤ 1000000000 * (L + 1) := by
  dsimp only
  let L := (eActApplyInput input).length
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let symbol := (second eCfg eSym).comp cfgSymbol
  let state := actState.comp action
  let position := cfgInputPos.comp cfg
  let movement := actInputMove.comp action
  let tapes := cfgWorkTapes.comp cfg
  let actions := actWorkActions.comp action
  change state.time input ≤ 1000000000 * (L + 1) ∧
    position.time input ≤ 1000000000 * (L + 1) ∧
    symbol.time input ≤ 1000000000 * (L + 1) ∧
    movement.time input ≤ 1000000000 * (L + 1) ∧
    tapes.time input ≤ 1000000000 * (L + 1) ∧
    actions.time input ≤ 1000000000 * (L + 1)
  have hactionBits : (eAct input.1).length ≤ L := by
    simp only [L, length_encPair]
    omega
  have hactionTime : action.time input ≤ 1000000 * (L + 1) := by
    simp [action, first, ofTransducer, L, eActApplyInput]
    omega
  have hprojections := actProjectionResources_le input.1
  obtain ⟨hmoveOuterTime, _hmoveOuterSpace, _hmoveOuterCount,
    hworkOuterTime, _hworkOuterSpace, _hworkOuterCount,
    _houtputOuterTime, _houtputOuterSpace, _houtputOuterCount,
    hstateOuterTime, _hstateOuterSpace, _hstateOuterCount⟩ := hprojections
  have hstateRaw := time_comp_le actState action input
  have hstate : state.time input ≤ 1000000000 * (L + 1) := by
    simp only [state]
    exact hstateRaw.trans (by omega)
  have hmovementRaw := time_comp_le actInputMove action input
  have hmovement : movement.time input ≤ 1000000000 * (L + 1) := by
    simp only [movement]
    exact hmovementRaw.trans (by omega)
  have hactionsRaw := time_comp_le actWorkActions action input
  have hactions : actions.time input ≤ 1000000000 * (L + 1) := by
    simp only [actions]
    exact hactionsRaw.trans (by omega)
  have hposition : position.time input ≤ 1000000000 * (L + 1) := by
    simp [position, cfg, cfgSymbol, cfgInputPos, cfgTail₂, first, second, comp,
      ofInputEq, ofTransducer, L, eActApplyInput]
    omega
  have hsymbol : symbol.time input ≤ 1000000000 * (L + 1) := by
    simp [symbol, cfgSymbol, second, comp, ofTransducer, L, eActApplyInput]
    omega
  have htapes : tapes.time input ≤ 1000000000 * (L + 1) := by
    simp [tapes, cfg, cfgSymbol, cfgWorkTapes, cfgTail₂, first, second, comp,
      ofInputEq, ofTransducer, L, eActApplyInput]
    omega
  exact ⟨hstate, hposition, hsymbol, hmovement, htapes, hactions⟩

private theorem actApplyComponentWorkspace_le (input : ActApplyInput) :
    let L := (eActApplyInput input).length
    let action := first eAct (encPair eCfg eSym)
    let cfgSymbol := second eAct (encPair eCfg eSym)
    let cfg := (first eCfg eSym).comp cfgSymbol
    let symbol := (second eCfg eSym).comp cfgSymbol
    let state := actState.comp action
    let position := cfgInputPos.comp cfg
    let movement := actInputMove.comp action
    let tapes := cfgWorkTapes.comp cfg
    let actions := actWorkActions.comp action
    state.workspace input ≤ 1000000000 * (L + 1) ∧
      position.workspace input ≤ 1000000000 * (L + 1) ∧
      symbol.workspace input ≤ 1000000000 * (L + 1) ∧
      movement.workspace input ≤ 1000000000 * (L + 1) ∧
      tapes.workspace input ≤ 1000000000 * (L + 1) ∧
      actions.workspace input ≤ 1000000000 * (L + 1) := by
  dsimp only
  let L := (eActApplyInput input).length
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let symbol := (second eCfg eSym).comp cfgSymbol
  let state := actState.comp action
  let position := cfgInputPos.comp cfg
  let movement := actInputMove.comp action
  let tapes := cfgWorkTapes.comp cfg
  let actions := actWorkActions.comp action
  change state.workspace input ≤ 1000000000 * (L + 1) ∧
    position.workspace input ≤ 1000000000 * (L + 1) ∧
    symbol.workspace input ≤ 1000000000 * (L + 1) ∧
    movement.workspace input ≤ 1000000000 * (L + 1) ∧
    tapes.workspace input ≤ 1000000000 * (L + 1) ∧
    actions.workspace input ≤ 1000000000 * (L + 1)
  have hactionBits : (eAct input.1).length ≤ L := by
    simp only [L, length_encPair]
    omega
  have hactionTime : action.time input ≤ 1000000 * (L + 1) := by
    simp [action, first, ofTransducer, L, eActApplyInput]
    omega
  have hactionSpace : action.workspace input ≤ 1000000 * (L + 1) := by
    simp [action, first, ofTransducer, L, eActApplyInput]
  have hactionCount : action.tapeCount ≤ 1 := by
    simp [action, first, ofTransducer]
  have hprojections := actProjectionResources_le input.1
  obtain ⟨hmoveOuterTime, hmoveOuterSpace, hmoveOuterCount,
    hworkOuterTime, hworkOuterSpace, hworkOuterCount,
    _houtputOuterTime, _houtputOuterSpace, _houtputOuterCount,
    hstateOuterTime, hstateOuterSpace, hstateOuterCount⟩ := hprojections
  have hstateMax : max action.tapeCount actState.tapeCount ≤ 100 :=
    max_le (hactionCount.trans (by omega)) hstateOuterCount
  have hstateRaw := workspace_comp_le actState action input
  have hstate : state.workspace input ≤ 1000000000 * (L + 1) := by
    simp only [state]
    exact hstateRaw.trans (by omega)
  have hmoveMax : max action.tapeCount actInputMove.tapeCount ≤ 100 :=
    max_le (hactionCount.trans (by omega)) hmoveOuterCount
  have hmovementRaw := workspace_comp_le actInputMove action input
  have hmovement : movement.workspace input ≤ 1000000000 * (L + 1) := by
    simp only [movement]
    exact hmovementRaw.trans (by omega)
  have hworkMax : max action.tapeCount actWorkActions.tapeCount ≤ 100 :=
    max_le (hactionCount.trans (by omega)) hworkOuterCount
  have hactionsRaw := workspace_comp_le actWorkActions action input
  have hactions : actions.workspace input ≤ 1000000000 * (L + 1) := by
    simp only [actions]
    exact hactionsRaw.trans (by omega)
  have hposition : position.workspace input ≤ 1000000000 * (L + 1) := by
    simp [position, cfg, cfgSymbol, cfgInputPos, cfgTail₂, first, second, comp,
      ofInputEq, ofTransducer, L, eActApplyInput]
    omega
  have hsymbol : symbol.workspace input ≤ 1000000000 * (L + 1) := by
    simp [symbol, cfgSymbol, second, comp, ofTransducer, L, eActApplyInput]
    omega
  have htapes : tapes.workspace input ≤ 1000000000 * (L + 1) := by
    simp [tapes, cfg, cfgSymbol, cfgWorkTapes, cfgTail₂, first, second, comp,
      ofInputEq, ofTransducer, L, eActApplyInput]
    omega
  exact ⟨hstate, hposition, hsymbol, hmovement, htapes, hactions⟩

private theorem actApplyComponentTapeCount_le :
    let action := first eAct (encPair eCfg eSym)
    let cfgSymbol := second eAct (encPair eCfg eSym)
    let cfg := (first eCfg eSym).comp cfgSymbol
    let symbol := (second eCfg eSym).comp cfgSymbol
    let state := actState.comp action
    let position := cfgInputPos.comp cfg
    let movement := actInputMove.comp action
    let tapes := cfgWorkTapes.comp cfg
    let actions := actWorkActions.comp action
    state.tapeCount ≤ 102 ∧ position.tapeCount ≤ 102 ∧ symbol.tapeCount ≤ 102 ∧
      movement.tapeCount ≤ 102 ∧ tapes.tapeCount ≤ 102 ∧ actions.tapeCount ≤ 102 := by
  dsimp only
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let symbol := (second eCfg eSym).comp cfgSymbol
  let state := actState.comp action
  let position := cfgInputPos.comp cfg
  let movement := actInputMove.comp action
  let tapes := cfgWorkTapes.comp cfg
  let actions := actWorkActions.comp action
  change state.tapeCount ≤ 102 ∧ position.tapeCount ≤ 102 ∧ symbol.tapeCount ≤ 102 ∧
    movement.tapeCount ≤ 102 ∧ tapes.tapeCount ≤ 102 ∧ actions.tapeCount ≤ 102
  have hactionCount : action.tapeCount ≤ 1 := by simp [action, first, ofTransducer]
  have hprojections := actProjectionResources_le (default : Act)
  obtain ⟨_hmoveTime, _hmoveSpace, hmoveCount,
    _hworkTime, _hworkSpace, hworkCount,
    _houtputTime, _houtputSpace, _houtputCount,
    _hstateTime, _hstateSpace, hstateCount⟩ := hprojections
  have hstate : state.tapeCount ≤ 102 := by
    simp only [state, comp]
    omega
  have hmovement : movement.tapeCount ≤ 102 := by
    simp only [movement, comp]
    omega
  have hactions : actions.tapeCount ≤ 102 := by
    simp only [actions, comp]
    omega
  have hposition : position.tapeCount ≤ 102 := by
    simp [position, cfg, cfgSymbol, cfgInputPos, cfgTail₂, first, second, comp,
      ofInputEq, ofTransducer]
  have hsymbol : symbol.tapeCount ≤ 102 := by
    simp [symbol, cfgSymbol, second, comp, ofTransducer]
  have htapes : tapes.tapeCount ≤ 102 := by
    simp [tapes, cfg, cfgSymbol, cfgWorkTapes, cfgTail₂, first, second, comp,
      ofInputEq, ofTransducer]
  exact ⟨hstate, hposition, hsymbol, hmovement, htapes, hactions⟩

private theorem actApplyMoveInput_length_le (input : ActApplyInput) :
    (encPair encNat (encPair eSym encSign)
      (input.2.1.inputPos, input.2.2, input.1.inputTape)).length ≤
        8 * ((eActApplyInput input).length + 1) := by
  simp only [eActApplyInput, eAct_apply, eCfg_apply, length_encPair]
  omega

private theorem actApplyWorkInput_length_le (input : ActApplyInput) :
    (encPair (encList eTape) (encList eTA)
      (input.2.1.workTapes, input.1.workTapes)).length ≤
        8 * ((eActApplyInput input).length + 1) := by
  simp only [eActApplyInput, eAct_apply, eCfg_apply, length_encPair]
  omega

private theorem actApplySubcompilerTapeCount_le :
    let action := first eAct (encPair eCfg eSym)
    let cfgSymbol := second eAct (encPair eCfg eSym)
    let cfg := (first eCfg eSym).comp cfgSymbol
    let symbol := (second eCfg eSym).comp cfgSymbol
    let position := cfgInputPos.comp cfg
    let movement := actInputMove.comp action
    let tapes := cfgWorkTapes.comp cfg
    let actions := actWorkActions.comp action
    let moveArgs := position.pair (symbol.pair movement)
    let movedInput := moveInput.comp moveArgs
    let workArgs := tapes.pair actions
    let movedWork := applyTapes.comp workArgs
    moveArgs.tapeCount ≤ 106 ∧ movedInput.tapeCount ≤ 1002 ∧
      workArgs.tapeCount ≤ 104 ∧ movedWork.tapeCount ≤ 254 := by
  dsimp only
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let symbol := (second eCfg eSym).comp cfgSymbol
  let position := cfgInputPos.comp cfg
  let movement := actInputMove.comp action
  let tapes := cfgWorkTapes.comp cfg
  let actions := actWorkActions.comp action
  let moveArgs := position.pair (symbol.pair movement)
  let movedInput := moveInput.comp moveArgs
  let workArgs := tapes.pair actions
  let movedWork := applyTapes.comp workArgs
  change moveArgs.tapeCount ≤ 106 ∧ movedInput.tapeCount ≤ 1002 ∧
    workArgs.tapeCount ≤ 104 ∧ movedWork.tapeCount ≤ 254
  have hcounts := actApplyComponentTapeCount_le
  obtain ⟨_hstateCount, hpositionCount, hsymbolCount, hmovementCount,
    htapesCount, hactionsCount⟩ := hcounts
  change position.tapeCount ≤ 102 at hpositionCount
  change symbol.tapeCount ≤ 102 at hsymbolCount
  change movement.tapeCount ≤ 102 at hmovementCount
  change tapes.tapeCount ≤ 102 at htapesCount
  change actions.tapeCount ≤ 102 at hactionsCount
  have hmoveCount := moveInput_tapeCount_le
  have hworkCount := applyTapes_tapeCount_le
  simp only [moveArgs, movedInput, workArgs, movedWork, pair, comp, encodeFrame]
  omega

private theorem actApplyMovedInputResource_le (input : ActApplyInput) :
    let L := (eActApplyInput input).length
    let action := first eAct (encPair eCfg eSym)
    let cfgSymbol := second eAct (encPair eCfg eSym)
    let cfg := (first eCfg eSym).comp cfgSymbol
    let symbol := (second eCfg eSym).comp cfgSymbol
    let position := cfgInputPos.comp cfg
    let movement := actInputMove.comp action
    let moveArgs := position.pair (symbol.pair movement)
    let movedInput := moveInput.comp moveArgs
    movedInput.time input ≤ 1000000000000 * (L + 1) ∧
      movedInput.workspace input ≤ 1000000000000 * (L + 1) ∧
      movedInput.tapeCount ≤ 1002 := by
  dsimp only
  let L := (eActApplyInput input).length
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let symbol := (second eCfg eSym).comp cfgSymbol
  let position := cfgInputPos.comp cfg
  let movement := actInputMove.comp action
  let moveArgs := position.pair (symbol.pair movement)
  let movedInput := moveInput.comp moveArgs
  change movedInput.time input ≤ 1000000000000 * (L + 1) ∧
    movedInput.workspace input ≤ 1000000000000 * (L + 1) ∧
    movedInput.tapeCount ≤ 1002
  have htime := actApplyComponentTime_le input
  obtain ⟨_hstateTime, hpositionTime, hsymbolTime, hmovementTime,
    _htapesTime, _hactionsTime⟩ := htime
  change position.time input ≤ 1000000000 * (L + 1) at hpositionTime
  change symbol.time input ≤ 1000000000 * (L + 1) at hsymbolTime
  change movement.time input ≤ 1000000000 * (L + 1) at hmovementTime
  have hspace := actApplyComponentWorkspace_le input
  obtain ⟨_hstateSpace, hpositionSpace, hsymbolSpace, hmovementSpace,
    _htapesSpace, _hactionsSpace⟩ := hspace
  change position.workspace input ≤ 1000000000 * (L + 1) at hpositionSpace
  change symbol.workspace input ≤ 1000000000 * (L + 1) at hsymbolSpace
  change movement.workspace input ≤ 1000000000 * (L + 1) at hmovementSpace
  have hcounts := actApplyComponentTapeCount_le
  obtain ⟨_hstateCount, hpositionCount, hsymbolCount, hmovementCount,
    _htapesCount, _hactionsCount⟩ := hcounts
  change position.tapeCount ≤ 102 at hpositionCount
  change symbol.tapeCount ≤ 102 at hsymbolCount
  change movement.tapeCount ≤ 102 at hmovementCount
  have hsubCounts := actApplySubcompilerTapeCount_le
  obtain ⟨hmoveArgsCount, hmovedInputCount, _hworkArgsCount, _hmovedWorkCount⟩ := hsubCounts
  change moveArgs.tapeCount ≤ 106 at hmoveArgsCount
  change movedInput.tapeCount ≤ 1002 at hmovedInputCount
  have hsymbolMovementTimeRaw := time_pair_le symbol movement input
  have hsymbolMovementTime : (symbol.pair movement).time input ≤
      20000000000 * (L + 1) := hsymbolMovementTimeRaw.trans (by omega)
  have hmoveArgsTimeRaw := time_pair_le position (symbol.pair movement) input
  have hmoveArgsTime : moveArgs.time input ≤ 100000000000 * (L + 1) := by
    simp only [moveArgs]
    exact hmoveArgsTimeRaw.trans (by omega)
  have hsymbolMovementSpaceRaw := workspace_pair_le symbol movement input
  have hsymbolMovementSpace : (symbol.pair movement).workspace input ≤
      10000000000 * (L + 1) := hsymbolMovementSpaceRaw.trans (by omega)
  have hsymbolMovementCount : (symbol.pair movement).tapeCount ≤ 104 := by
    simp only [pair, comp, encodeFrame]
    omega
  have hmoveArgsSpaceRaw := workspace_pair_le position (symbol.pair movement) input
  have hmoveArgsSpace : moveArgs.workspace input ≤ 100000000000 * (L + 1) := by
    simp only [moveArgs]
    exact hmoveArgsSpaceRaw.trans (by omega)
  have hmoveLength := actApplyMoveInput_length_le input
  have hmoveOuterTime := moveInput_time_le
    (input.2.1.inputPos, input.2.2, input.1.inputTape)
  have hmoveTimeRaw := time_comp_le moveInput moveArgs input
  have hmovedInputTime : movedInput.time input ≤ 1000000000000 * (L + 1) := by
    simp only [movedInput]
    exact hmoveTimeRaw.trans (by omega)
  have hmoveOuterSpace := moveInput_workspace_le
    (input.2.1.inputPos, input.2.2, input.1.inputTape)
  have hmoveCount := moveInput_tapeCount_le
  have hmoveMax : max moveArgs.tapeCount moveInput.tapeCount ≤ 1000 :=
    max_le (hmoveArgsCount.trans (by omega)) hmoveCount
  have hmoveSpaceRaw := workspace_comp_le moveInput moveArgs input
  have hmovedInputSpace : movedInput.workspace input ≤ 1000000000000 * (L + 1) := by
    simp only [movedInput]
    exact hmoveSpaceRaw.trans (by omega)
  exact ⟨hmovedInputTime, hmovedInputSpace, hmovedInputCount⟩

private theorem actApplyMovedWorkResource_le (input : ActApplyInput) :
    let L := (eActApplyInput input).length
    let action := first eAct (encPair eCfg eSym)
    let cfgSymbol := second eAct (encPair eCfg eSym)
    let cfg := (first eCfg eSym).comp cfgSymbol
    let tapes := cfgWorkTapes.comp cfg
    let actions := actWorkActions.comp action
    let workArgs := tapes.pair actions
    let movedWork := applyTapes.comp workArgs
    movedWork.time input ≤ 100000000000000000000000 * (L + 1) ^ 2 ∧
      movedWork.workspace input ≤ 1000000000000000000000000 * (L + 1) ^ 2 ∧
      movedWork.tapeCount ≤ 254 := by
  dsimp only
  let L := (eActApplyInput input).length
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let tapes := cfgWorkTapes.comp cfg
  let actions := actWorkActions.comp action
  let workArgs := tapes.pair actions
  let movedWork := applyTapes.comp workArgs
  change movedWork.time input ≤ 100000000000000000000000 * (L + 1) ^ 2 ∧
    movedWork.workspace input ≤ 1000000000000000000000000 * (L + 1) ^ 2 ∧
    movedWork.tapeCount ≤ 254
  have htime := actApplyComponentTime_le input
  obtain ⟨_hstateTime, _hpositionTime, _hsymbolTime, _hmovementTime,
    htapesTime, hactionsTime⟩ := htime
  change tapes.time input ≤ 1000000000 * (L + 1) at htapesTime
  change actions.time input ≤ 1000000000 * (L + 1) at hactionsTime
  have hspace := actApplyComponentWorkspace_le input
  obtain ⟨_hstateSpace, _hpositionSpace, _hsymbolSpace, _hmovementSpace,
    htapesSpace, hactionsSpace⟩ := hspace
  change tapes.workspace input ≤ 1000000000 * (L + 1) at htapesSpace
  change actions.workspace input ≤ 1000000000 * (L + 1) at hactionsSpace
  have hcounts := actApplyComponentTapeCount_le
  have htapesCount := hcounts.2.2.2.2.1
  have hactionsCount := hcounts.2.2.2.2.2
  change tapes.tapeCount ≤ 102 at htapesCount
  change actions.tapeCount ≤ 102 at hactionsCount
  have hsubCounts := actApplySubcompilerTapeCount_le
  obtain ⟨_hmoveArgsCount, _hmovedInputCount, hworkArgsCount, hmovedWorkCount⟩ := hsubCounts
  change workArgs.tapeCount ≤ 104 at hworkArgsCount
  change movedWork.tapeCount ≤ 254 at hmovedWorkCount
  have hworkArgsTimeRaw := time_pair_le tapes actions input
  have hworkArgsTime : workArgs.time input ≤ 20000000000 * (L + 1) := by
    simp only [workArgs]
    exact hworkArgsTimeRaw.trans (by omega)
  have hworkArgsSpaceRaw := workspace_pair_le tapes actions input
  have hworkPairMax : max (tapes.tapeCount + 2) actions.tapeCount ≤ 104 :=
    max_le (by omega) (hactionsCount.trans (by omega))
  have hworkArgsSpace : workArgs.workspace input ≤ 10000000000 * (L + 1) := by
    simp only [workArgs]
    exact hworkArgsSpaceRaw.trans (by omega)
  have hworkLength := actApplyWorkInput_length_le input
  have hworkOuterTime := applyTapes_time_le (input.2.1.workTapes, input.1.workTapes)
  have hworkTimeRaw := time_comp_le applyTapes workArgs input
  have hmovedWorkTime : movedWork.time input ≤
      100000000000000000000000 * (L + 1) ^ 2 := by
    simp only [movedWork]
    exact hworkTimeRaw.trans (by nlinarith)
  have hworkOuterSpace := applyTapes_workspace_le (input.2.1.workTapes, input.1.workTapes)
  have hworkCount := applyTapes_tapeCount_le
  have hworkMax : max workArgs.tapeCount applyTapes.tapeCount ≤ 252 :=
    max_le (hworkArgsCount.trans (by omega)) hworkCount
  have hworkSpaceRaw := workspace_comp_le applyTapes workArgs input
  have hmovedWorkSpace : movedWork.workspace input ≤
      1000000000000000000000000 * (L + 1) ^ 2 := by
    simp only [movedWork]
    exact hworkSpaceRaw.trans (by nlinarith)
  exact ⟨hmovedWorkTime, hmovedWorkSpace, hmovedWorkCount⟩

private theorem actApplyWithCompiler_time_le (input : ActApplyInput) :
    actApplyWithCompiler.time input ≤
      1000000000000000000000000 * ((eActApplyInput input).length + 1) ^ 2 := by
  let L := (eActApplyInput input).length
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let symbol := (second eCfg eSym).comp cfgSymbol
  let state := actState.comp action
  let position := cfgInputPos.comp cfg
  let movement := actInputMove.comp action
  let tapes := cfgWorkTapes.comp cfg
  let actions := actWorkActions.comp action
  let moveArgs := position.pair (symbol.pair movement)
  let movedInput := moveInput.comp moveArgs
  let workArgs := tapes.pair actions
  let movedWork := applyTapes.comp workArgs
  have hcomponentTime := actApplyComponentTime_le input
  have hstateTime := hcomponentTime.1
  change state.time input ≤ 1000000000 * (L + 1) at hstateTime
  have hmove := actApplyMovedInputResource_le input
  have hmovedInputTime := hmove.1
  have hwork := actApplyMovedWorkResource_le input
  have hmovedWorkTime := hwork.1
  change movedInput.time input ≤ 1000000000000 * (L + 1) at hmovedInputTime
  change movedWork.time input ≤
    100000000000000000000000 * (L + 1) ^ 2 at hmovedWorkTime
  have htailRaw := time_pair_le movedInput movedWork input
  have htail : (movedInput.pair movedWork).time input ≤
      200000000000000000000000 * (L + 1) ^ 2 := htailRaw.trans (by nlinarith)
  have hfullRaw := time_pair_le state (movedInput.pair movedWork) input
  change (state.pair (movedInput.pair movedWork)).time input ≤
    1000000000000000000000000 * (L + 1) ^ 2
  exact hfullRaw.trans (by nlinarith)

private theorem actApplyWithCompiler_workspace_le (input : ActApplyInput) :
    actApplyWithCompiler.workspace input ≤
      10000000000000000000000000 * ((eActApplyInput input).length + 1) ^ 2 := by
  let L := (eActApplyInput input).length
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let symbol := (second eCfg eSym).comp cfgSymbol
  let state := actState.comp action
  let position := cfgInputPos.comp cfg
  let movement := actInputMove.comp action
  let tapes := cfgWorkTapes.comp cfg
  let actions := actWorkActions.comp action
  let moveArgs := position.pair (symbol.pair movement)
  let movedInput := moveInput.comp moveArgs
  let workArgs := tapes.pair actions
  let movedWork := applyTapes.comp workArgs
  have hcomponentTime := actApplyComponentTime_le input
  have hstateTime := hcomponentTime.1
  change state.time input ≤ 1000000000 * (L + 1) at hstateTime
  have hcomponentSpace := actApplyComponentWorkspace_le input
  have hstateSpace := hcomponentSpace.1
  change state.workspace input ≤ 1000000000 * (L + 1) at hstateSpace
  have hcomponentCount := actApplyComponentTapeCount_le
  have hstateCount := hcomponentCount.1
  change state.tapeCount ≤ 102 at hstateCount
  have hmove := actApplyMovedInputResource_le input
  obtain ⟨hmovedInputTime, hmovedInputSpace, hmovedInputCount⟩ := hmove
  have hwork := actApplyMovedWorkResource_le input
  obtain ⟨_hmovedWorkTime, hmovedWorkSpace, hmovedWorkCount⟩ := hwork
  change movedInput.time input ≤ 1000000000000 * (L + 1) at hmovedInputTime
  change movedInput.workspace input ≤ 1000000000000 * (L + 1) at hmovedInputSpace
  change movedInput.tapeCount ≤ 1002 at hmovedInputCount
  change movedWork.workspace input ≤
    1000000000000000000000000 * (L + 1) ^ 2 at hmovedWorkSpace
  change movedWork.tapeCount ≤ 254 at hmovedWorkCount
  have htailMax : max (movedInput.tapeCount + 2) movedWork.tapeCount ≤ 1004 :=
    max_le (by omega) (hmovedWorkCount.trans (by omega))
  have htailRaw := workspace_pair_le movedInput movedWork input
  have htailSpace : (movedInput.pair movedWork).workspace input ≤
      2000000000000000000000000 * (L + 1) ^ 2 := htailRaw.trans (by nlinarith)
  have htailCount : (movedInput.pair movedWork).tapeCount ≤ 1006 := by
    simp only [pair, comp, encodeFrame]
    omega
  have hfullMax : max (state.tapeCount + 2)
      (movedInput.pair movedWork).tapeCount ≤ 1006 :=
    max_le (by omega) htailCount
  have hfullRaw := workspace_pair_le state (movedInput.pair movedWork) input
  change (state.pair (movedInput.pair movedWork)).workspace input ≤
    10000000000000000000000000 * (L + 1) ^ 2
  exact hfullRaw.trans (by nlinarith)

private theorem actApplyWithCompiler_tapeCount_le : actApplyWithCompiler.tapeCount ≤ 1008 := by
  let action := first eAct (encPair eCfg eSym)
  let cfgSymbol := second eAct (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp cfgSymbol
  let symbol := (second eCfg eSym).comp cfgSymbol
  let state := actState.comp action
  let position := cfgInputPos.comp cfg
  let movement := actInputMove.comp action
  let tapes := cfgWorkTapes.comp cfg
  let actions := actWorkActions.comp action
  let moveArgs := position.pair (symbol.pair movement)
  let movedInput := moveInput.comp moveArgs
  let workArgs := tapes.pair actions
  let movedWork := applyTapes.comp workArgs
  have hcomponentCount := actApplyComponentTapeCount_le
  have hstateCount := hcomponentCount.1
  change state.tapeCount ≤ 102 at hstateCount
  have hsubCounts := actApplySubcompilerTapeCount_le
  have hmovedInputCount := hsubCounts.2.1
  change movedInput.tapeCount ≤ 1002 at hmovedInputCount
  have hmovedWorkCount := hsubCounts.2.2.2
  change movedWork.tapeCount ≤ 254 at hmovedWorkCount
  change (state.pair (movedInput.pair movedWork)).tapeCount ≤ 1008
  simp only [pair, comp, encodeFrame]
  omega

private theorem stepWithFromLookupActionResource_le (input : StepWithLookupInput) :
    let L := (eStepWithLookupInput input).length
    let lookup := second eStepWithInput (encOption eAct)
    let action := (optionGetD default eAct).comp lookup
    action.time input ≤ 10000000000 * (L + 1) ∧
      action.workspace input ≤ 10000000000 * (L + 1) ∧
      action.tapeCount ≤ 100 := by
  dsimp only
  let L := (eStepWithLookupInput input).length
  let lookup := second eStepWithInput (encOption eAct)
  let action := (optionGetD default eAct).comp lookup
  change action.time input ≤ 10000000000 * (L + 1) ∧
    action.workspace input ≤ 10000000000 * (L + 1) ∧ action.tapeCount ≤ 100
  have hdefault := length_eAct_default_le
  cases hlookup : input.2 <;>
    simp [action, lookup, optionGetD, optionPayload, optionIsSomeTest,
      optionIsSomeBool, tailDecoder, boolDecoder, boolToTest, second, comp, ite,
      const, ofInputEq, ofOutputEq, ofTransducer, encTest_false, encTest_true,
      hlookup, L, eStepWithLookupInput] at hdefault ⊢ <;>
    omega

private theorem stepWithFromLookupComponentTime_le (input : StepWithLookupInput) :
    let L := (eStepWithLookupInput input).length
    let original := first eStepWithInput (encOption eAct)
    let lookup := second eStepWithInput (encOption eAct)
    let originalTail := (second eDesc (encPair eCfg eSym)).comp original
    let cfg := (first eCfg eSym).comp originalTail
    let symbol := (second eCfg eSym).comp originalTail
    let hasAction := (optionIsSomeTest eAct).comp lookup
    let action := (optionGetD default eAct).comp lookup
    let output := actOutput.comp action
    let position := cfgInputPos.comp cfg
    let tapes := cfgWorkTapes.comp cfg
    cfg.time input ≤ 1000000000000 * (L + 1) ∧
      symbol.time input ≤ 1000000000000 * (L + 1) ∧
      hasAction.time input ≤ 1000000000000 * (L + 1) ∧
      action.time input ≤ 1000000000000 * (L + 1) ∧
      output.time input ≤ 1000000000000 * (L + 1) ∧
      position.time input ≤ 1000000000000 * (L + 1) ∧
      tapes.time input ≤ 1000000000000 * (L + 1) := by
  dsimp only
  let L := (eStepWithLookupInput input).length
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let hasAction := (optionIsSomeTest eAct).comp lookup
  let action := (optionGetD default eAct).comp lookup
  let output := actOutput.comp action
  let position := cfgInputPos.comp cfg
  let tapes := cfgWorkTapes.comp cfg
  change cfg.time input ≤ 1000000000000 * (L + 1) ∧
    symbol.time input ≤ 1000000000000 * (L + 1) ∧
    hasAction.time input ≤ 1000000000000 * (L + 1) ∧
    action.time input ≤ 1000000000000 * (L + 1) ∧
    output.time input ≤ 1000000000000 * (L + 1) ∧
    position.time input ≤ 1000000000000 * (L + 1) ∧
    tapes.time input ≤ 1000000000000 * (L + 1)
  have hactionResource := stepWithFromLookupActionResource_le input
  obtain ⟨hactionTimeTight, _hactionSpace, _hactionCount⟩ := hactionResource
  change action.time input ≤ 10000000000 * (L + 1) at hactionTimeTight
  have hactionTime : action.time input ≤ 1000000000000 * (L + 1) := by omega
  have hbase : cfg.time input ≤ 1000000000000 * (L + 1) ∧
      symbol.time input ≤ 1000000000000 * (L + 1) ∧
      hasAction.time input ≤ 1000000000000 * (L + 1) ∧
      position.time input ≤ 1000000000000 * (L + 1) ∧
      tapes.time input ≤ 1000000000000 * (L + 1) := by
    cases hlookup : input.2 <;>
      simp [cfg, symbol, hasAction, position, tapes, originalTail, original, lookup,
        cfgInputPos, cfgWorkTapes, cfgTail₂, optionIsSomeTest, optionIsSomeBool,
        boolDecoder, boolToTest, first, second, comp, ofInputEq, ofOutputEq,
        ofTransducer, hlookup, L, eStepWithLookupInput] <;>
      omega
  obtain ⟨hcfgTime, hsymbolTime, hhasActionTime, hpositionTime, htapesTime⟩ := hbase
  have hactionBits := length_enc_getD_le (encC := eAct) input.2
  have hdefault := length_eAct_default_le
  have hoptionBits : ((encOption eAct) input.2).length ≤ L := by
    simp only [L, length_encPair]
    omega
  have hprojection := actProjectionResources_le (input.2.getD default)
  have houtputOuterTime := hprojection.2.2.2.2.2.2.1
  have houtputRaw := time_comp_le actOutput action input
  have houtputTime : output.time input ≤ 1000000000000 * (L + 1) := by
    simp only [output]
    exact houtputRaw.trans (by omega)
  exact ⟨hcfgTime, hsymbolTime, hhasActionTime, hactionTime, houtputTime,
    hpositionTime, htapesTime⟩

private theorem stepWithFromLookupComponentWorkspace_le (input : StepWithLookupInput) :
    let L := (eStepWithLookupInput input).length
    let original := first eStepWithInput (encOption eAct)
    let lookup := second eStepWithInput (encOption eAct)
    let originalTail := (second eDesc (encPair eCfg eSym)).comp original
    let cfg := (first eCfg eSym).comp originalTail
    let symbol := (second eCfg eSym).comp originalTail
    let hasAction := (optionIsSomeTest eAct).comp lookup
    let action := (optionGetD default eAct).comp lookup
    let output := actOutput.comp action
    let position := cfgInputPos.comp cfg
    let tapes := cfgWorkTapes.comp cfg
    cfg.workspace input ≤ 1000000000000 * (L + 1) ∧
      symbol.workspace input ≤ 1000000000000 * (L + 1) ∧
      hasAction.workspace input ≤ 1000000000000 * (L + 1) ∧
      action.workspace input ≤ 1000000000000 * (L + 1) ∧
      output.workspace input ≤ 1000000000000 * (L + 1) ∧
      position.workspace input ≤ 1000000000000 * (L + 1) ∧
      tapes.workspace input ≤ 1000000000000 * (L + 1) := by
  dsimp only
  let L := (eStepWithLookupInput input).length
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let hasAction := (optionIsSomeTest eAct).comp lookup
  let action := (optionGetD default eAct).comp lookup
  let output := actOutput.comp action
  let position := cfgInputPos.comp cfg
  let tapes := cfgWorkTapes.comp cfg
  change cfg.workspace input ≤ 1000000000000 * (L + 1) ∧
    symbol.workspace input ≤ 1000000000000 * (L + 1) ∧
    hasAction.workspace input ≤ 1000000000000 * (L + 1) ∧
    action.workspace input ≤ 1000000000000 * (L + 1) ∧
    output.workspace input ≤ 1000000000000 * (L + 1) ∧
    position.workspace input ≤ 1000000000000 * (L + 1) ∧
    tapes.workspace input ≤ 1000000000000 * (L + 1)
  have hactionResource := stepWithFromLookupActionResource_le input
  obtain ⟨hactionTimeTight, hactionSpaceTight, hactionCount⟩ := hactionResource
  change action.time input ≤ 10000000000 * (L + 1) at hactionTimeTight
  change action.workspace input ≤ 10000000000 * (L + 1) at hactionSpaceTight
  have hactionSpace : action.workspace input ≤ 1000000000000 * (L + 1) := by omega
  change action.tapeCount ≤ 100 at hactionCount
  have hbase : cfg.workspace input ≤ 1000000000000 * (L + 1) ∧
      symbol.workspace input ≤ 1000000000000 * (L + 1) ∧
      hasAction.workspace input ≤ 1000000000000 * (L + 1) ∧
      position.workspace input ≤ 1000000000000 * (L + 1) ∧
      tapes.workspace input ≤ 1000000000000 * (L + 1) := by
    cases hlookup : input.2 <;>
      simp [cfg, symbol, hasAction, position, tapes, originalTail, original, lookup,
        cfgInputPos, cfgWorkTapes, cfgTail₂, optionIsSomeTest, optionIsSomeBool,
        boolDecoder, boolToTest, first, second, comp, ofInputEq, ofOutputEq,
        ofTransducer, hlookup, L, eStepWithLookupInput] <;>
      omega
  obtain ⟨hcfgSpace, hsymbolSpace, hhasActionSpace, hpositionSpace, htapesSpace⟩ := hbase
  have hactionBits := length_enc_getD_le (encC := eAct) input.2
  have hdefault := length_eAct_default_le
  have hoptionBits : ((encOption eAct) input.2).length ≤ L := by
    simp only [L, length_encPair]
    omega
  have hprojection := actProjectionResources_le (input.2.getD default)
  have houtputOuterTime := hprojection.2.2.2.2.2.2.1
  have houtputOuterSpace := hprojection.2.2.2.2.2.2.2.1
  have houtputOuterCount := hprojection.2.2.2.2.2.2.2.2.1
  have houtputMax : max action.tapeCount actOutput.tapeCount ≤ 100 :=
    max_le hactionCount houtputOuterCount
  have houtputRaw := workspace_comp_le actOutput action input
  have houtputSpace : output.workspace input ≤ 1000000000000 * (L + 1) := by
    simp only [output]
    exact houtputRaw.trans (by omega)
  exact ⟨hcfgSpace, hsymbolSpace, hhasActionSpace, hactionSpace, houtputSpace,
    hpositionSpace, htapesSpace⟩

private theorem stepWithFromLookupComponentTapeCount_le :
    let original := first eStepWithInput (encOption eAct)
    let lookup := second eStepWithInput (encOption eAct)
    let originalTail := (second eDesc (encPair eCfg eSym)).comp original
    let cfg := (first eCfg eSym).comp originalTail
    let symbol := (second eCfg eSym).comp originalTail
    let hasAction := (optionIsSomeTest eAct).comp lookup
    let action := (optionGetD default eAct).comp lookup
    let output := actOutput.comp action
    let position := cfgInputPos.comp cfg
    let tapes := cfgWorkTapes.comp cfg
    cfg.tapeCount ≤ 1000 ∧ symbol.tapeCount ≤ 1000 ∧ hasAction.tapeCount ≤ 1000 ∧
      action.tapeCount ≤ 1000 ∧ output.tapeCount ≤ 1000 ∧
      position.tapeCount ≤ 1000 ∧ tapes.tapeCount ≤ 1000 := by
  dsimp only
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let hasAction := (optionIsSomeTest eAct).comp lookup
  let action := (optionGetD default eAct).comp lookup
  let output := actOutput.comp action
  let position := cfgInputPos.comp cfg
  let tapes := cfgWorkTapes.comp cfg
  change cfg.tapeCount ≤ 1000 ∧ symbol.tapeCount ≤ 1000 ∧
    hasAction.tapeCount ≤ 1000 ∧ action.tapeCount ≤ 1000 ∧
    output.tapeCount ≤ 1000 ∧ position.tapeCount ≤ 1000 ∧ tapes.tapeCount ≤ 1000
  have hactionResource := stepWithFromLookupActionResource_le (default : StepWithLookupInput)
  have hactionCount := hactionResource.2.2
  change action.tapeCount ≤ 100 at hactionCount
  have hprojection := actProjectionResources_le (default : Act)
  have houtputOuterCount := hprojection.2.2.2.2.2.2.2.2.1
  have houtputCount : output.tapeCount ≤ 1000 := by
    simp only [output, comp]
    omega
  have hbase : cfg.tapeCount ≤ 1000 ∧ symbol.tapeCount ≤ 1000 ∧
      hasAction.tapeCount ≤ 1000 ∧ position.tapeCount ≤ 1000 ∧
      tapes.tapeCount ≤ 1000 := by
    simp [cfg, symbol, hasAction, position, tapes, originalTail, original, lookup,
      cfgInputPos, cfgWorkTapes, cfgTail₂, optionIsSomeTest, optionIsSomeBool,
      boolDecoder, boolToTest, first, second, comp,
      ofInputEq, ofOutputEq, ofTransducer]
  obtain ⟨hcfgCount, hsymbolCount, hhasActionCount, hpositionCount, htapesCount⟩ := hbase
  exact ⟨hcfgCount, hsymbolCount, hhasActionCount, hactionCount.trans (by omega),
    houtputCount, hpositionCount, htapesCount⟩

private theorem stepWithFromLookupActionArgsResource_le (input : StepWithLookupInput) :
    let L := (eStepWithLookupInput input).length
    let original := first eStepWithInput (encOption eAct)
    let lookup := second eStepWithInput (encOption eAct)
    let originalTail := (second eDesc (encPair eCfg eSym)).comp original
    let cfg := (first eCfg eSym).comp originalTail
    let symbol := (second eCfg eSym).comp originalTail
    let action := (optionGetD default eAct).comp lookup
    let actionArgs := action.pair (cfg.pair symbol)
    actionArgs.time input ≤ 30000000000000 * (L + 1) ∧
      actionArgs.workspace input ≤ 20000000000000 * (L + 1) ∧
      actionArgs.tapeCount ≤ 1002 := by
  dsimp only
  let L := (eStepWithLookupInput input).length
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let action := (optionGetD default eAct).comp lookup
  let actionArgs := action.pair (cfg.pair symbol)
  change actionArgs.time input ≤ 30000000000000 * (L + 1) ∧
    actionArgs.workspace input ≤ 20000000000000 * (L + 1) ∧
    actionArgs.tapeCount ≤ 1002
  have htime := stepWithFromLookupComponentTime_le input
  obtain ⟨hcfgTime, hsymbolTime, _hhasActionTime, hactionTime,
    _houtputTime, _hpositionTime, _htapesTime⟩ := htime
  change cfg.time input ≤ 1000000000000 * (L + 1) at hcfgTime
  change symbol.time input ≤ 1000000000000 * (L + 1) at hsymbolTime
  change action.time input ≤ 1000000000000 * (L + 1) at hactionTime
  have hspace := stepWithFromLookupComponentWorkspace_le input
  obtain ⟨hcfgSpace, hsymbolSpace, _hhasActionSpace, hactionSpace,
    _houtputSpace, _hpositionSpace, _htapesSpace⟩ := hspace
  change cfg.workspace input ≤ 1000000000000 * (L + 1) at hcfgSpace
  change symbol.workspace input ≤ 1000000000000 * (L + 1) at hsymbolSpace
  change action.workspace input ≤ 1000000000000 * (L + 1) at hactionSpace
  have hcounts := stepWithFromLookupComponentTapeCount_le
  obtain ⟨hcfgCount, hsymbolCount, _hhasActionCount, hactionCount,
    _houtputCount, _hpositionCount, _htapesCount⟩ := hcounts
  change cfg.tapeCount ≤ 1000 at hcfgCount
  change symbol.tapeCount ≤ 1000 at hsymbolCount
  change action.tapeCount ≤ 1000 at hactionCount
  have hcfgSymbolTimeRaw := time_pair_le cfg symbol input
  have hcfgSymbolTime : (cfg.pair symbol).time input ≤
      20000000000000 * (L + 1) := hcfgSymbolTimeRaw.trans (by omega)
  have hactionArgsTimeRaw := time_pair_le action (cfg.pair symbol) input
  have hactionArgsTime : actionArgs.time input ≤ 30000000000000 * (L + 1) := by
    simp only [actionArgs]
    exact hactionArgsTimeRaw.trans (by omega)
  have hcfgSymbolMax : max (cfg.tapeCount + 2) symbol.tapeCount ≤ 1002 :=
    max_le (by omega) (hsymbolCount.trans (by omega))
  have hcfgSymbolSpaceRaw := workspace_pair_le cfg symbol input
  have hcfgSymbolSpace : (cfg.pair symbol).workspace input ≤
      10000000000000 * (L + 1) := hcfgSymbolSpaceRaw.trans (by omega)
  have hcfgSymbolCount : (cfg.pair symbol).tapeCount ≤ 1002 := by
    simp only [pair, comp, encodeFrame]
    omega
  have hactionArgsMax : max (action.tapeCount + 2)
      (cfg.pair symbol).tapeCount ≤ 1002 :=
    max_le (by omega) hcfgSymbolCount
  have hactionArgsSpaceRaw := workspace_pair_le action (cfg.pair symbol) input
  have hactionArgsSpace : actionArgs.workspace input ≤ 20000000000000 * (L + 1) := by
    simp only [actionArgs]
    exact hactionArgsSpaceRaw.trans (by omega)
  have hactionArgsCount : actionArgs.tapeCount ≤ 1002 := by
    simp only [actionArgs, pair, comp, encodeFrame]
    omega
  exact ⟨hactionArgsTime, hactionArgsSpace, hactionArgsCount⟩

private theorem stepWithFromLookupAppliedResource_le (input : StepWithLookupInput) :
    let L := (eStepWithLookupInput input).length
    let original := first eStepWithInput (encOption eAct)
    let lookup := second eStepWithInput (encOption eAct)
    let originalTail := (second eDesc (encPair eCfg eSym)).comp original
    let cfg := (first eCfg eSym).comp originalTail
    let symbol := (second eCfg eSym).comp originalTail
    let action := (optionGetD default eAct).comp lookup
    let actionArgs := action.pair (cfg.pair symbol)
    let applied := actApplyWithCompiler.comp actionArgs
    applied.time input ≤ 1000000000000000000000000000 * (L + 1) ^ 2 ∧
      applied.workspace input ≤ 10000000000000000000000000000 * (L + 1) ^ 2 ∧
      applied.tapeCount ≤ 1010 := by
  dsimp only
  let L := (eStepWithLookupInput input).length
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let action := (optionGetD default eAct).comp lookup
  let actionArgs := action.pair (cfg.pair symbol)
  let applied := actApplyWithCompiler.comp actionArgs
  change applied.time input ≤ 1000000000000000000000000000 * (L + 1) ^ 2 ∧
    applied.workspace input ≤ 10000000000000000000000000000 * (L + 1) ^ 2 ∧
    applied.tapeCount ≤ 1010
  have hargs := stepWithFromLookupActionArgsResource_le input
  obtain ⟨hactionArgsTime, hactionArgsSpace, hactionArgsCount⟩ := hargs
  change actionArgs.time input ≤ 30000000000000 * (L + 1) at hactionArgsTime
  change actionArgs.workspace input ≤ 20000000000000 * (L + 1) at hactionArgsSpace
  change actionArgs.tapeCount ≤ 1002 at hactionArgsCount
  have hactionArgsLength := stepWithFromLookupActInput_length_le input
  have happliedOuterTime := actApplyWithCompiler_time_le
    (input.2.getD default, input.1.2.1, input.1.2.2)
  have happliedTimeRaw := time_comp_le actApplyWithCompiler actionArgs input
  have happliedTime : applied.time input ≤
      1000000000000000000000000000 * (L + 1) ^ 2 := by
    simp only [applied]
    exact happliedTimeRaw.trans (by nlinarith)
  have happliedOuterSpace := actApplyWithCompiler_workspace_le
    (input.2.getD default, input.1.2.1, input.1.2.2)
  have happliedCountOuter := actApplyWithCompiler_tapeCount_le
  have happliedMax : max actionArgs.tapeCount actApplyWithCompiler.tapeCount ≤ 1008 :=
    max_le (hactionArgsCount.trans (by omega)) happliedCountOuter
  have happliedSpaceRaw := workspace_comp_le actApplyWithCompiler actionArgs input
  have happliedSpace : applied.workspace input ≤
      10000000000000000000000000000 * (L + 1) ^ 2 := by
    simp only [applied]
    exact happliedSpaceRaw.trans (by nlinarith)
  have happliedCount : applied.tapeCount ≤ 1010 := by
    simp only [applied, comp]
    omega
  exact ⟨happliedTime, happliedSpace, happliedCount⟩

private theorem stepWithFromLookupSuccessfulResource_le (input : StepWithLookupInput) :
    let L := (eStepWithLookupInput input).length
    let original := first eStepWithInput (encOption eAct)
    let lookup := second eStepWithInput (encOption eAct)
    let originalTail := (second eDesc (encPair eCfg eSym)).comp original
    let cfg := (first eCfg eSym).comp originalTail
    let symbol := (second eCfg eSym).comp originalTail
    let action := (optionGetD default eAct).comp lookup
    let actionArgs := action.pair (cfg.pair symbol)
    let applied := actApplyWithCompiler.comp actionArgs
    let output := actOutput.comp action
    let successful := applied.pair output
    successful.time input ≤ 10000000000000000000000000000 * (L + 1) ^ 2 ∧
      successful.workspace input ≤ 20000000000000000000000000000 * (L + 1) ^ 2 ∧
      successful.tapeCount ≤ 1012 := by
  dsimp only
  let L := (eStepWithLookupInput input).length
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let action := (optionGetD default eAct).comp lookup
  let actionArgs := action.pair (cfg.pair symbol)
  let applied := actApplyWithCompiler.comp actionArgs
  let output := actOutput.comp action
  let successful := applied.pair output
  change successful.time input ≤ 10000000000000000000000000000 * (L + 1) ^ 2 ∧
    successful.workspace input ≤ 20000000000000000000000000000 * (L + 1) ^ 2 ∧
    successful.tapeCount ≤ 1012
  have htime := stepWithFromLookupComponentTime_le input
  have houtputTime := htime.2.2.2.2.1
  change output.time input ≤ 1000000000000 * (L + 1) at houtputTime
  have hspace := stepWithFromLookupComponentWorkspace_le input
  have houtputSpace := hspace.2.2.2.2.1
  change output.workspace input ≤ 1000000000000 * (L + 1) at houtputSpace
  have hcounts := stepWithFromLookupComponentTapeCount_le
  have houtputCount := hcounts.2.2.2.2.1
  change output.tapeCount ≤ 1000 at houtputCount
  have happliedResource := stepWithFromLookupAppliedResource_le input
  obtain ⟨happliedTime, happliedSpace, happliedCount⟩ := happliedResource
  change applied.time input ≤
    1000000000000000000000000000 * (L + 1) ^ 2 at happliedTime
  change applied.workspace input ≤
    10000000000000000000000000000 * (L + 1) ^ 2 at happliedSpace
  change applied.tapeCount ≤ 1010 at happliedCount
  have hsuccessfulTimeRaw := time_pair_le applied output input
  have hsuccessfulTime : successful.time input ≤
      10000000000000000000000000000 * (L + 1) ^ 2 := by
    simp only [successful]
    exact hsuccessfulTimeRaw.trans (by nlinarith)
  have hsuccessfulSpaceRaw := workspace_pair_le applied output input
  have hsuccessfulMax : max (applied.tapeCount + 2) output.tapeCount ≤ 1012 :=
    max_le (by omega) (houtputCount.trans (by omega))
  have hsuccessfulSpace : successful.workspace input ≤
      20000000000000000000000000000 * (L + 1) ^ 2 := by
    simp only [successful]
    exact hsuccessfulSpaceRaw.trans (by nlinarith)
  have hsuccessfulCount : successful.tapeCount ≤ 1012 := by
    simp only [successful, pair, comp, encodeFrame]
    omega
  exact ⟨hsuccessfulTime, hsuccessfulSpace, hsuccessfulCount⟩

private theorem stepWithFromLookupMissingResource_le (input : StepWithLookupInput) :
    let L := (eStepWithLookupInput input).length
    let original := first eStepWithInput (encOption eAct)
    let originalTail := (second eDesc (encPair eCfg eSym)).comp original
    let cfg := (first eCfg eSym).comp originalTail
    let position := cfgInputPos.comp cfg
    let tapes := cfgWorkTapes.comp cfg
    let haltedState := const eStepWithLookupInput eSym none
    let haltedCfg : NativeCompiler
        (fun input : StepWithLookupInput => { input.1.2.1 with state := none })
        eStepWithLookupInput eCfg :=
      (haltedState.pair (position.pair tapes)).ofOutputEq fun _ => rfl
    let missing := haltedCfg.pair (const eStepWithLookupInput eSym none)
    missing.time input ≤ 1000000000000000 * (L + 1) ∧
      missing.workspace input ≤ 1000000000000000 * (L + 1) ∧
      missing.tapeCount ≤ 1004 := by
  dsimp only
  let L := (eStepWithLookupInput input).length
  let original := first eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let position := cfgInputPos.comp cfg
  let tapes := cfgWorkTapes.comp cfg
  let haltedState := const eStepWithLookupInput eSym none
  let haltedCfg : NativeCompiler
      (fun input : StepWithLookupInput => { input.1.2.1 with state := none })
      eStepWithLookupInput eCfg :=
    (haltedState.pair (position.pair tapes)).ofOutputEq fun _ => rfl
  let missingOutput := const eStepWithLookupInput eSym none
  let missing := haltedCfg.pair missingOutput
  change missing.time input ≤ 1000000000000000 * (L + 1) ∧
    missing.workspace input ≤ 1000000000000000 * (L + 1) ∧
    missing.tapeCount ≤ 1004
  have htime := stepWithFromLookupComponentTime_le input
  have hpositionTime := htime.2.2.2.2.2.1
  have htapesTime := htime.2.2.2.2.2.2
  change position.time input ≤ 1000000000000 * (L + 1) at hpositionTime
  change tapes.time input ≤ 1000000000000 * (L + 1) at htapesTime
  have hspace := stepWithFromLookupComponentWorkspace_le input
  have hpositionSpace := hspace.2.2.2.2.2.1
  have htapesSpace := hspace.2.2.2.2.2.2
  change position.workspace input ≤ 1000000000000 * (L + 1) at hpositionSpace
  change tapes.workspace input ≤ 1000000000000 * (L + 1) at htapesSpace
  have hcounts := stepWithFromLookupComponentTapeCount_le
  have hpositionCount := hcounts.2.2.2.2.2.1
  have htapesCount := hcounts.2.2.2.2.2.2
  change position.tapeCount ≤ 1000 at hpositionCount
  change tapes.tapeCount ≤ 1000 at htapesCount
  have hpositionTapesTimeRaw := time_pair_le position tapes input
  have hpositionTapesTime : (position.pair tapes).time input ≤
      20000000000000 * (L + 1) := hpositionTapesTimeRaw.trans (by omega)
  have hpositionTapesSpaceRaw := workspace_pair_le position tapes input
  have hpositionTapesMax : max (position.tapeCount + 2) tapes.tapeCount ≤ 1002 :=
    max_le (by omega) (htapesCount.trans (by omega))
  have hpositionTapesSpace : (position.pair tapes).workspace input ≤
      10000000000000 * (L + 1) := hpositionTapesSpaceRaw.trans (by omega)
  have hpositionTapesCount : (position.pair tapes).tapeCount ≤ 1002 := by
    simp only [pair, comp, encodeFrame]
    omega
  have hhaltedStateTime : haltedState.time input ≤ 10 * (L + 1) := by
    simp [haltedState, const]
    omega
  have hhaltedStateSpace : haltedState.workspace input = 0 := by rfl
  have hhaltedStateCount : haltedState.tapeCount = 0 := rfl
  have hhaltedCfgTimeRaw := time_pair_le haltedState (position.pair tapes) input
  have hhaltedCfgTime : haltedCfg.time input ≤ 30000000000000 * (L + 1) := by
    simp only [haltedCfg]
    exact hhaltedCfgTimeRaw.trans (by omega)
  have hhaltedCfgSpaceRaw := workspace_pair_le haltedState (position.pair tapes) input
  have hhaltedMax : max (haltedState.tapeCount + 2)
      (position.pair tapes).tapeCount ≤ 1002 :=
    max_le (by omega) hpositionTapesCount
  have hhaltedCfgSpace : haltedCfg.workspace input ≤ 20000000000000 * (L + 1) := by
    simp only [haltedCfg]
    exact hhaltedCfgSpaceRaw.trans (by omega)
  have hhaltedCfgCount : haltedCfg.tapeCount ≤ 1002 := by
    simpa only [haltedCfg, ofOutputEq, pair, comp, encodeFrame,
      Nat.max_eq_left (Nat.zero_le _)] using hhaltedMax
  have hmissingOutputTime : missingOutput.time input ≤ 10 * (L + 1) := by
    simp [missingOutput, const]
    omega
  have hmissingOutputSpace : missingOutput.workspace input = 0 := by rfl
  have hmissingOutputCount : missingOutput.tapeCount = 0 := rfl
  have hmissingTimeRaw := time_pair_le haltedCfg missingOutput input
  have hmissingTime : missing.time input ≤ 1000000000000000 * (L + 1) := by
    simp only [missing]
    exact hmissingTimeRaw.trans (by omega)
  have hmissingSpaceRaw := workspace_pair_le haltedCfg missingOutput input
  have hmissingMax : max (haltedCfg.tapeCount + 2) missingOutput.tapeCount ≤ 1004 :=
    max_le (by omega) (by omega)
  have hmissingSpace : missing.workspace input ≤ 1000000000000000 * (L + 1) := by
    simp only [missing]
    exact hmissingSpaceRaw.trans (by omega)
  have hmissingCount : missing.tapeCount ≤ 1004 := by
    simpa only [missing, pair, comp, encodeFrame,
      Nat.max_eq_left (Nat.zero_le _)] using hmissingMax
  exact ⟨hmissingTime, hmissingSpace, hmissingCount⟩

private theorem stepWithFromLookupCompiler_time_le (input : StepWithLookupInput) :
    stepWithFromLookupCompiler.time input ≤
      100000000000000000000000000000 *
        ((eStepWithLookupInput input).length + 1) ^ 2 := by
  let L := (eStepWithLookupInput input).length
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let hasAction := (optionIsSomeTest eAct).comp lookup
  let action := (optionGetD default eAct).comp lookup
  let actionArgs := action.pair (cfg.pair symbol)
  let applied := actApplyWithCompiler.comp actionArgs
  let output := actOutput.comp action
  let successful := applied.pair output
  let haltedState := const eStepWithLookupInput eSym none
  let haltedCfg : NativeCompiler
      (fun input : StepWithLookupInput => { input.1.2.1 with state := none })
      eStepWithLookupInput eCfg :=
    (haltedState.pair ((cfgInputPos.comp cfg).pair (cfgWorkTapes.comp cfg))).ofOutputEq
      fun _ => rfl
  let missing := haltedCfg.pair (const eStepWithLookupInput eSym none)
  have hcomponent := stepWithFromLookupComponentTime_le input
  have hcondition := hcomponent.2.2.1
  change hasAction.time input ≤ 1000000000000 * (L + 1) at hcondition
  have hsuccessfulResource := stepWithFromLookupSuccessfulResource_le input
  have hsuccessful := hsuccessfulResource.1
  change successful.time input ≤
    10000000000000000000000000000 * (L + 1) ^ 2 at hsuccessful
  have hmissingResource := stepWithFromLookupMissingResource_le input
  have hmissing := hmissingResource.1
  change missing.time input ≤ 1000000000000000 * (L + 1) at hmissing
  have hite := time_ite_le hasAction successful missing input
  change (ite hasAction successful missing).time input ≤
    100000000000000000000000000000 * (L + 1) ^ 2
  exact hite.trans (by nlinarith)

private theorem stepWithFromLookupCompiler_workspace_le (input : StepWithLookupInput) :
    stepWithFromLookupCompiler.workspace input ≤
      1000000000000000000000000000000 *
        ((eStepWithLookupInput input).length + 1) ^ 2 := by
  let L := (eStepWithLookupInput input).length
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let hasAction := (optionIsSomeTest eAct).comp lookup
  let action := (optionGetD default eAct).comp lookup
  let actionArgs := action.pair (cfg.pair symbol)
  let applied := actApplyWithCompiler.comp actionArgs
  let output := actOutput.comp action
  let successful := applied.pair output
  let haltedState := const eStepWithLookupInput eSym none
  let haltedCfg : NativeCompiler
      (fun input : StepWithLookupInput => { input.1.2.1 with state := none })
      eStepWithLookupInput eCfg :=
    (haltedState.pair ((cfgInputPos.comp cfg).pair (cfgWorkTapes.comp cfg))).ofOutputEq
      fun _ => rfl
  let missing := haltedCfg.pair (const eStepWithLookupInput eSym none)
  have hcomponentSpace := stepWithFromLookupComponentWorkspace_le input
  have hconditionSpace := hcomponentSpace.2.2.1
  change hasAction.workspace input ≤ 1000000000000 * (L + 1) at hconditionSpace
  have hcomponentCount := stepWithFromLookupComponentTapeCount_le
  have hconditionCount := hcomponentCount.2.2.1
  change hasAction.tapeCount ≤ 1000 at hconditionCount
  have hsuccessfulResource := stepWithFromLookupSuccessfulResource_le input
  have hsuccessfulSpace := hsuccessfulResource.2.1
  change successful.workspace input ≤
    20000000000000000000000000000 * (L + 1) ^ 2 at hsuccessfulSpace
  have hsuccessfulCount := hsuccessfulResource.2.2
  change successful.tapeCount ≤ 1012 at hsuccessfulCount
  have hmissingResource := stepWithFromLookupMissingResource_le input
  have hmissingSpace := hmissingResource.2.1
  change missing.workspace input ≤ 1000000000000000 * (L + 1) at hmissingSpace
  have hmissingCount := hmissingResource.2.2
  change missing.tapeCount ≤ 1004 at hmissingCount
  have hbranchMax : max hasAction.tapeCount
      (max successful.tapeCount missing.tapeCount) ≤ 1012 :=
    max_le (hconditionCount.trans (by omega)) (max_le hsuccessfulCount (by omega))
  have hite := workspace_ite_le hasAction successful missing input
  change (ite hasAction successful missing).workspace input ≤
    1000000000000000000000000000000 * (L + 1) ^ 2
  exact hite.trans (by nlinarith)

private theorem stepWithFromLookupCompiler_tapeCount_le :
    stepWithFromLookupCompiler.tapeCount ≤ 1013 := by
  let original := first eStepWithInput (encOption eAct)
  let lookup := second eStepWithInput (encOption eAct)
  let originalTail := (second eDesc (encPair eCfg eSym)).comp original
  let cfg := (first eCfg eSym).comp originalTail
  let symbol := (second eCfg eSym).comp originalTail
  let hasAction := (optionIsSomeTest eAct).comp lookup
  let action := (optionGetD default eAct).comp lookup
  let actionArgs := action.pair (cfg.pair symbol)
  let applied := actApplyWithCompiler.comp actionArgs
  let output := actOutput.comp action
  let successful := applied.pair output
  let haltedState := const eStepWithLookupInput eSym none
  let haltedCfg : NativeCompiler
      (fun input : StepWithLookupInput => { input.1.2.1 with state := none })
      eStepWithLookupInput eCfg :=
    (haltedState.pair ((cfgInputPos.comp cfg).pair (cfgWorkTapes.comp cfg))).ofOutputEq
      fun _ => rfl
  let missing := haltedCfg.pair (const eStepWithLookupInput eSym none)
  have hcomponentCount := stepWithFromLookupComponentTapeCount_le
  have hconditionCount := hcomponentCount.2.2.1
  change hasAction.tapeCount ≤ 1000 at hconditionCount
  have hsuccessfulResource :=
    stepWithFromLookupSuccessfulResource_le (default : StepWithLookupInput)
  have hsuccessfulCount := hsuccessfulResource.2.2
  change successful.tapeCount ≤ 1012 at hsuccessfulCount
  have hmissingResource :=
    stepWithFromLookupMissingResource_le (default : StepWithLookupInput)
  have hmissingCount := hmissingResource.2.2
  change missing.tapeCount ≤ 1004 at hmissingCount
  change (ite hasAction successful missing).tapeCount ≤ 1013
  simp only [ite]
  omega

private theorem stepCompilerInput_length_le (input : Desc × (List ℕ × SCfg)) :
    (eStepWithInput
      (input.1, input.2.2, Universal.inputSymbol input.2.1 input.2.2.inputPos)).length ≤
        16 *
          ((eDeterministicStepInput input).length + 1) := by
  have hsymbol :=
    Turing.MultiTapeTM.Universal.length_inputSymbol_le input.2.1 input.2.2.inputPos
  simp only [eStepWithInput, eCfg_apply, eSym, length_encPair] at hsymbol ⊢
  omega

private theorem inputSymbol_tapeCount_le : inputSymbol.tapeCount ≤ 205 := by
  let encInput := encPair (encList encUnary) encNat
  let word := first (encList encUnary) encNat
  let position := second (encList encUnary) encNat
  let atLeftBoundary := natIsZeroTest.comp position
  let blank := const encInput eSym none
  let index := natPred.comp position
  let lookupInput := word.pair index
  let lookup := (listGet?NatCompiler encUnary).comp lookupInput
  have hstaticCounts := inputSymbolStaticTapeCounts_le
  change max lookupInput.tapeCount (listGet?NatCompiler encUnary).tapeCount ≤ 202 ∧
    max atLeftBoundary.tapeCount (max blank.tapeCount lookup.tapeCount) ≤ 204 at hstaticCounts
  change (ite atLeftBoundary blank lookup).tapeCount ≤ 205
  simp only [ite]
  omega

private theorem stepWithActiveCompilerResources_le (input : StepWithInput) :
    stepWithActiveCompiler.time input ≤
        10 ^ 32 * ((eStepWithInput input).length + 1) ^ 2 ∧
      stepWithActiveCompiler.workspace input ≤
        10 ^ 33 * ((eStepWithInput input).length + 1) ^ 2 ∧
      stepWithActiveCompiler.tapeCount ≤ 1015 := by
  let L := (eStepWithInput input).length
  let original := identity eStepWithInput
  let lookup := stepWithLookupCompiler
  let combined := original.pair lookup
  let activeInput : StepWithLookupInput :=
    (id input, match input with
      | (description, cfg, symbol) =>
          firstMatch (description.table,
            ⟨cfg.state.getD 0, symbol, cfg.workTapes.map Tape.read⟩))
  have hN : 1 ≤ (L + 1) ^ 2 := by
    simpa using Nat.pow_le_pow_left (by omega : 1 ≤ L + 1) 2
  have horiginalTime : original.time input ≤ 10 * (L + 1) := by
    simp [original, identity, L]
    omega
  have horiginalSpace : original.workspace input = 0 := by rfl
  have horiginalCount : original.tapeCount = 0 := by rfl
  have hlookupTime := stepWithLookupCompiler_time_le input
  have hlookupSpace := stepWithLookupCompiler_workspace_le input
  have hlookupCount := stepWithLookupCompiler_tapeCount_le
  have hcombinedTimeRaw := time_pair_le original lookup input
  have hcombinedTime : combined.time input ≤ 10 ^ 18 * (L + 1) ^ 2 := by
    simp only [combined]
    exact hcombinedTimeRaw.trans (by nlinarith)
  have hcombinedSpaceRaw := workspace_pair_le original lookup input
  have hcombinedMax : max (original.tapeCount + 2) lookup.tapeCount ≤ 1012 :=
    max_le (by omega) hlookupCount
  have hcombinedSpace : combined.workspace input ≤ 2 * 10 ^ 18 * (L + 1) ^ 2 := by
    simp only [combined]
    exact hcombinedSpaceRaw.trans (by nlinarith)
  have hcombinedCount : combined.tapeCount ≤ 1012 := by
    simp only [combined, pair, encodeFrame, comp]
    omega
  have hsemantic : (eStepWithLookupInput activeInput).length ≤ 8 * (L + 1) := by
    simpa only [activeInput, id_eq, L] using stepWithActiveInput_length_le input
  have houterTime := stepWithFromLookupCompiler_time_le activeInput
  have houterSpace := stepWithFromLookupCompiler_workspace_le activeInput
  have houterCount := stepWithFromLookupCompiler_tapeCount_le
  have hsemanticSquare :
      ((eStepWithLookupInput activeInput).length + 1) ^ 2 ≤
        81 * (L + 1) ^ 2 := by
    nlinarith
  have houterTimeBound :
      stepWithFromLookupCompiler.time activeInput ≤
          10 ^ 31 * (L + 1) ^ 2 := by
    calc
      _ ≤ 100000000000000000000000000000 * (81 * (L + 1) ^ 2) :=
        houterTime.trans (Nat.mul_le_mul_left _ hsemanticSquare)
      _ = 8100000000000000000000000000000 * (L + 1) ^ 2 := by ring
      _ ≤ 10 ^ 31 * (L + 1) ^ 2 :=
        Nat.mul_le_mul_right _ (by norm_num)
  have houterSpaceBound :
      stepWithFromLookupCompiler.workspace activeInput ≤
          10 ^ 32 * (L + 1) ^ 2 := by
    calc
      _ ≤ 1000000000000000000000000000000 * (81 * (L + 1) ^ 2) :=
        houterSpace.trans (Nat.mul_le_mul_left _ hsemanticSquare)
      _ = 81000000000000000000000000000000 * (L + 1) ^ 2 := by ring
      _ ≤ 10 ^ 32 * (L + 1) ^ 2 :=
        Nat.mul_le_mul_right _ (by norm_num)
  have htimeRaw := time_comp_le stepWithFromLookupCompiler combined input
  change (stepWithFromLookupCompiler.comp combined).time input ≤
    5 * combined.time input + stepWithFromLookupCompiler.time activeInput + 9 at htimeRaw
  have htime : stepWithActiveCompiler.time input ≤ 10 ^ 32 * (L + 1) ^ 2 := by
    change (stepWithFromLookupCompiler.comp combined).time input ≤ _
    exact htimeRaw.trans (by omega)
  have hspaceRaw := workspace_comp_le stepWithFromLookupCompiler combined input
  change (stepWithFromLookupCompiler.comp combined).workspace input ≤
    combined.workspace input + stepWithFromLookupCompiler.workspace activeInput +
      5 * combined.time input +
        (6 * max combined.tapeCount stepWithFromLookupCompiler.tapeCount + 20) at hspaceRaw
  have hmax : max combined.tapeCount stepWithFromLookupCompiler.tapeCount ≤ 1013 :=
    max_le (hcombinedCount.trans (by omega)) houterCount
  have hspace : stepWithActiveCompiler.workspace input ≤
      10 ^ 33 * (L + 1) ^ 2 := by
    change (stepWithFromLookupCompiler.comp combined).workspace input ≤ _
    exact hspaceRaw.trans (by omega)
  have hcount : stepWithActiveCompiler.tapeCount ≤ 1015 := by
    change (stepWithFromLookupCompiler.comp combined).tapeCount ≤ 1015
    simp only [comp]
    omega
  exact ⟨htime, hspace, hcount⟩

private theorem stepWithCompilerResources_le (input : StepWithInput) :
    stepWithCompiler.time input ≤
        10 ^ 33 * ((eStepWithInput input).length + 1) ^ 2 ∧
      stepWithCompiler.workspace input ≤
        10 ^ 34 * ((eStepWithInput input).length + 1) ^ 2 ∧
      stepWithCompiler.tapeCount ≤ 1016 := by
  let L := (eStepWithInput input).length
  let tail := second eDesc (encPair eCfg eSym)
  let cfg := (first eCfg eSym).comp tail
  let hasState := (optionIsSomeTest encUnary).comp (cfgState.comp cfg)
  let halted := cfg.pair (const eStepWithInput eSym none)
  have hstateBits : (eSym input.2.1.state).length ≤ L := by
    simp only [L, eCfg_apply, length_encPair]
    omega
  have hcondition : hasState.time input ≤ 10 ^ 12 * (L + 1) ∧
      hasState.workspace input ≤ 10 ^ 12 * (L + 1) ∧
      hasState.tapeCount ≤ 1000 := by
    cases hoption : input.2.1.state <;>
      simp [hasState, cfg, tail, cfgState, optionIsSomeTest, optionIsSomeBool,
        boolDecoder, boolToTest, first, second, comp, ofInputEq, ofOutputEq,
        ofTransducer, hoption, L] at hstateBits ⊢ <;>
      omega
  obtain ⟨hconditionTime, hconditionSpace, hconditionCount⟩ := hcondition
  have hhaltedTime : halted.time input ≤ 10 ^ 12 * (L + 1) := by
    simp [halted, cfg, tail, first, second, const, pair, comp,
      encodeFrame, ofTransducer, L]
    omega
  have hhaltedSpace : halted.workspace input ≤ 10 ^ 12 * (L + 1) := by
    simp [halted, cfg, tail, first, second, const, pair, comp,
      encodeFrame, ofTransducer, L]
    omega
  have hhaltedCount : halted.tapeCount ≤ 1000 := by
    simp [halted, cfg, tail, first, second, const, pair, comp,
      encodeFrame, ofTransducer]
  have hactive := stepWithActiveCompilerResources_le input
  have htimeRaw := time_ite_le hasState stepWithActiveCompiler halted input
  have htime : stepWithCompiler.time input ≤ 10 ^ 33 * (L + 1) ^ 2 := by
    change (ite hasState stepWithActiveCompiler halted).time input ≤ _
    exact htimeRaw.trans (by nlinarith [hactive.1])
  have hbranchMax : max hasState.tapeCount
      (max stepWithActiveCompiler.tapeCount halted.tapeCount) ≤ 1015 :=
    max_le (hconditionCount.trans (by omega))
      (max_le hactive.2.2 (hhaltedCount.trans (by omega)))
  have hspaceRaw := workspace_ite_le hasState stepWithActiveCompiler halted input
  have hspace : stepWithCompiler.workspace input ≤ 10 ^ 34 * (L + 1) ^ 2 := by
    change (ite hasState stepWithActiveCompiler halted).workspace input ≤ _
    exact hspaceRaw.trans (by nlinarith [hactive.2.1])
  have hcount : stepWithCompiler.tapeCount ≤ 1016 := by
    change (ite hasState stepWithActiveCompiler halted).tapeCount ≤ 1016
    simp only [ite]
    omega
  exact ⟨htime, hspace, hcount⟩

private theorem stepCompilerProjectionResources_le (input : Desc × (List ℕ × SCfg)) :
    let L := (eDeterministicStepInput input).length
    let description := first eDesc (encPair (encList encUnary) eCfg)
    let tail := second eDesc (encPair (encList encUnary) eCfg)
    let word := (first (encList encUnary) eCfg).comp tail
    let cfg := (second (encList encUnary) eCfg).comp tail
    let position := cfgInputPos.comp cfg
    description.time input ≤ 10 ^ 9 * (L + 1) ∧
      description.workspace input ≤ 10 ^ 9 * (L + 1) ∧
      description.tapeCount ≤ 100 ∧
      word.time input ≤ 10 ^ 9 * (L + 1) ∧
      word.workspace input ≤ 10 ^ 9 * (L + 1) ∧
      word.tapeCount ≤ 100 ∧
      cfg.time input ≤ 10 ^ 9 * (L + 1) ∧
      cfg.workspace input ≤ 10 ^ 9 * (L + 1) ∧
      cfg.tapeCount ≤ 100 ∧
      position.time input ≤ 10 ^ 9 * (L + 1) ∧
      position.workspace input ≤ 10 ^ 9 * (L + 1) ∧
      position.tapeCount ≤ 100 := by
  dsimp only
  let L := (eDeterministicStepInput input).length
  let description := first eDesc (encPair (encList encUnary) eCfg)
  let tail := second eDesc (encPair (encList encUnary) eCfg)
  let word := (first (encList encUnary) eCfg).comp tail
  let cfg := (second (encList encUnary) eCfg).comp tail
  let position := cfgInputPos.comp cfg
  change description.time input ≤ 10 ^ 9 * (L + 1) ∧
    description.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    description.tapeCount ≤ 100 ∧
    word.time input ≤ 10 ^ 9 * (L + 1) ∧
    word.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    word.tapeCount ≤ 100 ∧
    cfg.time input ≤ 10 ^ 9 * (L + 1) ∧
    cfg.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    cfg.tapeCount ≤ 100 ∧
    position.time input ≤ 10 ^ 9 * (L + 1) ∧
    position.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    position.tapeCount ≤ 100
  simp [description, word, position, cfg, tail, cfgInputPos, cfgTail₂,
    first, second, comp, ofInputEq, ofTransducer, L]
  omega

private theorem stepCompilerSymbolInput_length_le (input : Desc × (List ℕ × SCfg)) :
    (encPair (encList encUnary) encNat
      (input.2.1, input.2.2.inputPos)).length ≤
        2 * ((eDeterministicStepInput input).length + 1) := by
  simp only [eCfg_apply, length_encPair]
  omega

private theorem stepCompilerSymbolInputResources_le (input : Desc × (List ℕ × SCfg)) :
    let tail := second eDesc (encPair (encList encUnary) eCfg)
    let word := (first (encList encUnary) eCfg).comp tail
    let cfg := (second (encList encUnary) eCfg).comp tail
    let position := cfgInputPos.comp cfg
    let symbolInput := word.pair position
    symbolInput.time input ≤ 10 ^ 11 * ((eDeterministicStepInput input).length + 1) ∧
      symbolInput.workspace input ≤
        10 ^ 11 * ((eDeterministicStepInput input).length + 1) ∧
      symbolInput.tapeCount ≤ 102 := by
  dsimp only
  let L := (eDeterministicStepInput input).length
  let tail := second eDesc (encPair (encList encUnary) eCfg)
  let word := (first (encList encUnary) eCfg).comp tail
  let cfg := (second (encList encUnary) eCfg).comp tail
  let position := cfgInputPos.comp cfg
  let symbolInput := word.pair position
  change symbolInput.time input ≤ 10 ^ 11 * (L + 1) ∧
    symbolInput.workspace input ≤ 10 ^ 11 * (L + 1) ∧
    symbolInput.tapeCount ≤ 102
  have hcomponents := stepCompilerProjectionResources_le input
  change
    (first eDesc (encPair (encList encUnary) eCfg)).time input ≤ 10 ^ 9 * (L + 1) ∧
    (first eDesc (encPair (encList encUnary) eCfg)).workspace input ≤
      10 ^ 9 * (L + 1) ∧
    (first eDesc (encPair (encList encUnary) eCfg)).tapeCount ≤ 100 ∧
    word.time input ≤ 10 ^ 9 * (L + 1) ∧
    word.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    word.tapeCount ≤ 100 ∧
    cfg.time input ≤ 10 ^ 9 * (L + 1) ∧
    cfg.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    cfg.tapeCount ≤ 100 ∧
    position.time input ≤ 10 ^ 9 * (L + 1) ∧
    position.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    position.tapeCount ≤ 100 at hcomponents
  obtain ⟨_, _, _, hwordTime, hwordSpace, hwordCount, _, _, _,
    hpositionTime, hpositionSpace, hpositionCount⟩ := hcomponents
  have htimeRaw := time_pair_le word position input
  have htime : symbolInput.time input ≤ 10 ^ 11 * (L + 1) := by
    simp only [symbolInput]
    exact htimeRaw.trans (by omega)
  have hspaceRaw := workspace_pair_le word position input
  have hmax : max (word.tapeCount + 2) position.tapeCount ≤ 102 :=
    max_le (by omega) (hpositionCount.trans (by omega))
  have hspace : symbolInput.workspace input ≤ 10 ^ 11 * (L + 1) := by
    simp only [symbolInput]
    exact hspaceRaw.trans (by omega)
  have hcount : symbolInput.tapeCount ≤ 102 := by
    simp only [symbolInput, pair, comp, encodeFrame]
    omega
  exact ⟨htime, hspace, hcount⟩

private theorem stepCompilerSymbolResources_le (input : Desc × (List ℕ × SCfg)) :
    let tail := second eDesc (encPair (encList encUnary) eCfg)
    let word := (first (encList encUnary) eCfg).comp tail
    let cfg := (second (encList encUnary) eCfg).comp tail
    let position := cfgInputPos.comp cfg
    let symbolInput := word.pair position
    let symbol := inputSymbol.comp symbolInput
    symbol.time input ≤
        10 ^ 15 * ((eDeterministicStepInput input).length + 1) ^ 2 ∧
      symbol.workspace input ≤
        10 ^ 15 * ((eDeterministicStepInput input).length + 1) ^ 2 ∧
      symbol.tapeCount ≤ 207 := by
  dsimp only
  let L := (eDeterministicStepInput input).length
  let tail := second eDesc (encPair (encList encUnary) eCfg)
  let word := (first (encList encUnary) eCfg).comp tail
  let cfg := (second (encList encUnary) eCfg).comp tail
  let position := cfgInputPos.comp cfg
  let symbolInput := word.pair position
  let symbol := inputSymbol.comp symbolInput
  change symbol.time input ≤ 10 ^ 15 * (L + 1) ^ 2 ∧
    symbol.workspace input ≤ 10 ^ 15 * (L + 1) ^ 2 ∧
    symbol.tapeCount ≤ 207
  have hN : 1 ≤ (L + 1) ^ 2 := by
    simpa using Nat.pow_le_pow_left (by omega : 1 ≤ L + 1) 2
  have hlinear : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by omega) (L + 1)
  have hsymbolInputLength := stepCompilerSymbolInput_length_le input
  have hsymbolInputResource := stepCompilerSymbolInputResources_le input
  change symbolInput.time input ≤ 10 ^ 11 * (L + 1) ∧
    symbolInput.workspace input ≤ 10 ^ 11 * (L + 1) ∧
    symbolInput.tapeCount ≤ 102 at hsymbolInputResource
  obtain ⟨hsymbolInputTime, hsymbolInputSpace, hsymbolInputCount⟩ :=
    hsymbolInputResource
  have hsymbolSizeSquare :
      ((encPair (encList encUnary) encNat
        (input.2.1, input.2.2.inputPos)).length + 1) ^ 2 ≤
          9 * (L + 1) ^ 2 := by
    nlinarith
  have hsymbolOuterTime := inputSymbol_time_le (input.2.1, input.2.2.inputPos)
  have hsymbolOuterTimeBound : inputSymbol.time (input.2.1, input.2.2.inputPos) ≤
      9 * 10 ^ 12 * (L + 1) ^ 2 := by
    calc
      _ ≤ 10 ^ 12 * (9 * (L + 1) ^ 2) :=
        hsymbolOuterTime.trans (Nat.mul_le_mul_left _ hsymbolSizeSquare)
      _ = 9 * 10 ^ 12 * (L + 1) ^ 2 := by ring
  have hsymbolOuterSpace := inputSymbol_workspace_le (input.2.1, input.2.2.inputPos)
  have hsymbolOuterSpaceBound :
      inputSymbol.workspace (input.2.1, input.2.2.inputPos) ≤
        9 * 10 ^ 12 * (L + 1) ^ 2 := by
    calc
      _ ≤ 10 ^ 12 * (9 * (L + 1) ^ 2) :=
        hsymbolOuterSpace.trans (Nat.mul_le_mul_left _ hsymbolSizeSquare)
      _ = 9 * 10 ^ 12 * (L + 1) ^ 2 := by ring
  have hsymbolOuterCount := inputSymbol_tapeCount_le
  have hsymbolTimeRaw := time_comp_le inputSymbol symbolInput input
  have hsymbolTime : symbol.time input ≤ 10 ^ 15 * (L + 1) ^ 2 := by
    simp only [symbol]
    exact hsymbolTimeRaw.trans (by omega)
  have hsymbolMax : max symbolInput.tapeCount inputSymbol.tapeCount ≤ 205 :=
    max_le (hsymbolInputCount.trans (by omega)) hsymbolOuterCount
  have hsymbolSpaceRaw := workspace_comp_le inputSymbol symbolInput input
  have hsymbolSpace : symbol.workspace input ≤ 10 ^ 15 * (L + 1) ^ 2 := by
    simp only [symbol]
    exact hsymbolSpaceRaw.trans (by omega)
  have hsymbolCount : symbol.tapeCount ≤ 207 := by
    simp only [symbol, comp]
    omega
  exact ⟨hsymbolTime, hsymbolSpace, hsymbolCount⟩

private theorem stepCompilerInputResources_le (input : Desc × (List ℕ × SCfg)) :
    let description := first eDesc (encPair (encList encUnary) eCfg)
    let tail := second eDesc (encPair (encList encUnary) eCfg)
    let word := (first (encList encUnary) eCfg).comp tail
    let cfg := (second (encList encUnary) eCfg).comp tail
    let position := cfgInputPos.comp cfg
    let symbolInput := word.pair position
    let symbol := inputSymbol.comp symbolInput
    let assembled := description.pair (cfg.pair symbol)
    assembled.time input ≤
        10 ^ 18 * ((eDeterministicStepInput input).length + 1) ^ 2 ∧
      assembled.workspace input ≤
        10 ^ 18 * ((eDeterministicStepInput input).length + 1) ^ 2 ∧
      assembled.tapeCount ≤ 207 := by
  dsimp only
  let L := (eDeterministicStepInput input).length
  let description := first eDesc (encPair (encList encUnary) eCfg)
  let tail := second eDesc (encPair (encList encUnary) eCfg)
  let word := (first (encList encUnary) eCfg).comp tail
  let cfg := (second (encList encUnary) eCfg).comp tail
  let position := cfgInputPos.comp cfg
  let symbolInput := word.pair position
  let symbol := inputSymbol.comp symbolInput
  let cfgSymbol := cfg.pair symbol
  let assembled := description.pair cfgSymbol
  change assembled.time input ≤ 10 ^ 18 * (L + 1) ^ 2 ∧
    assembled.workspace input ≤ 10 ^ 18 * (L + 1) ^ 2 ∧
    assembled.tapeCount ≤ 207
  have hN : 1 ≤ (L + 1) ^ 2 := by
    simpa using Nat.pow_le_pow_left (by omega : 1 ≤ L + 1) 2
  have hlinear : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by omega) (L + 1)
  have hcomponents := stepCompilerProjectionResources_le input
  change description.time input ≤ 10 ^ 9 * (L + 1) ∧
    description.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    description.tapeCount ≤ 100 ∧
    word.time input ≤ 10 ^ 9 * (L + 1) ∧
    word.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    word.tapeCount ≤ 100 ∧
    cfg.time input ≤ 10 ^ 9 * (L + 1) ∧
    cfg.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    cfg.tapeCount ≤ 100 ∧
    position.time input ≤ 10 ^ 9 * (L + 1) ∧
    position.workspace input ≤ 10 ^ 9 * (L + 1) ∧
    position.tapeCount ≤ 100 at hcomponents
  obtain ⟨hdescriptionTime, hdescriptionSpace, hdescriptionCount,
    _, _, _, hcfgTime, hcfgSpace, hcfgCount, _, _, _⟩ := hcomponents
  have hsymbolResource := stepCompilerSymbolResources_le input
  change symbol.time input ≤ 10 ^ 15 * (L + 1) ^ 2 ∧
    symbol.workspace input ≤ 10 ^ 15 * (L + 1) ^ 2 ∧
    symbol.tapeCount ≤ 207 at hsymbolResource
  obtain ⟨hsymbolTime, hsymbolSpace, hsymbolCount⟩ := hsymbolResource
  have hcfgSymbolTimeRaw := time_pair_le cfg symbol input
  have hcfgSymbolTime : cfgSymbol.time input ≤ 10 ^ 16 * (L + 1) ^ 2 := by
    simp only [cfgSymbol]
    exact hcfgSymbolTimeRaw.trans (by omega)
  have hcfgSymbolMax : max (cfg.tapeCount + 2) symbol.tapeCount ≤ 207 :=
    max_le (by omega) hsymbolCount
  have hcfgSymbolSpaceRaw := workspace_pair_le cfg symbol input
  have hcfgSymbolSpace : cfgSymbol.workspace input ≤ 10 ^ 16 * (L + 1) ^ 2 := by
    simp only [cfgSymbol]
    exact hcfgSymbolSpaceRaw.trans (by omega)
  have hcfgSymbolCount : cfgSymbol.tapeCount ≤ 207 := by
    simp only [cfgSymbol, pair, comp, encodeFrame]
    omega
  have hassembledTimeRaw := time_pair_le description cfgSymbol input
  have hassembledTime : assembled.time input ≤ 10 ^ 18 * (L + 1) ^ 2 := by
    simp only [assembled]
    exact hassembledTimeRaw.trans (by omega)
  have hassembledMax : max (description.tapeCount + 2) cfgSymbol.tapeCount ≤ 207 :=
    max_le (by omega) hcfgSymbolCount
  have hassembledSpaceRaw := workspace_pair_le description cfgSymbol input
  have hassembledSpace : assembled.workspace input ≤ 10 ^ 18 * (L + 1) ^ 2 := by
    simp only [assembled]
    exact hassembledSpaceRaw.trans (by omega)
  have hassembledCount : assembled.tapeCount ≤ 207 := by
    simp only [assembled, pair, comp, encodeFrame]
    omega
  exact ⟨hassembledTime, hassembledSpace, hassembledCount⟩

private theorem stepCompilerOuterResources_le (input : Desc × (List ℕ × SCfg)) :
    let stepInput : StepWithInput :=
      (input.1, input.2.2, Universal.inputSymbol input.2.1 input.2.2.inputPos)
    stepWithCompiler.time stepInput ≤
        289 * 10 ^ 33 * ((eDeterministicStepInput input).length + 1) ^ 2 ∧
      stepWithCompiler.workspace stepInput ≤
        289 * 10 ^ 34 * ((eDeterministicStepInput input).length + 1) ^ 2 ∧
      stepWithCompiler.tapeCount ≤ 1016 := by
  dsimp only
  let L := (eDeterministicStepInput input).length
  let stepInput : StepWithInput :=
    (input.1, input.2.2, Universal.inputSymbol input.2.1 input.2.2.inputPos)
  change stepWithCompiler.time stepInput ≤ 289 * 10 ^ 33 * (L + 1) ^ 2 ∧
    stepWithCompiler.workspace stepInput ≤ 289 * 10 ^ 34 * (L + 1) ^ 2 ∧
    stepWithCompiler.tapeCount ≤ 1016
  have hsemantic := stepCompilerInput_length_le input
  have hsemanticSquare : (eStepWithInput stepInput).length.succ ^ 2 ≤
      289 * (L + 1) ^ 2 := by
    nlinarith
  have houter := stepWithCompilerResources_le stepInput
  have htime : stepWithCompiler.time stepInput ≤
      289 * 10 ^ 33 * (L + 1) ^ 2 := by
    calc
      _ ≤ 10 ^ 33 * (289 * (L + 1) ^ 2) :=
        houter.1.trans (Nat.mul_le_mul_left _ hsemanticSquare)
      _ = 289 * 10 ^ 33 * (L + 1) ^ 2 := by ring
  have hspace : stepWithCompiler.workspace stepInput ≤
      289 * 10 ^ 34 * (L + 1) ^ 2 := by
    calc
      _ ≤ 10 ^ 34 * (289 * (L + 1) ^ 2) :=
        houter.2.1.trans (Nat.mul_le_mul_left _ hsemanticSquare)
      _ = 289 * 10 ^ 34 * (L + 1) ^ 2 := by ring
  exact ⟨htime, hspace, houter.2.2⟩

/-- The actual retained complete deterministic-step compiler has quadratic time in the complete
encoded input length. The installed program size is the separate field `stepCompiler.staticBits`.
-/
theorem stepCompiler_time_le (input : Desc × (List ℕ × SCfg)) :
    stepCompiler.time input ≤
      10 ^ 36 * ((eDeterministicStepInput input).length + 1) ^ 2 := by
  let L := (eDeterministicStepInput input).length
  let description := first eDesc (encPair (encList encUnary) eCfg)
  let tail := second eDesc (encPair (encList encUnary) eCfg)
  let word := (first (encList encUnary) eCfg).comp tail
  let cfg := (second (encList encUnary) eCfg).comp tail
  let symbol := inputSymbol.comp (word.pair (cfgInputPos.comp cfg))
  let assembled := description.pair (cfg.pair symbol)
  let stepInput : StepWithInput :=
    (input.1, input.2.2, Universal.inputSymbol input.2.1 input.2.2.inputPos)
  have hN : 1 ≤ (L + 1) ^ 2 := by
    simpa using Nat.pow_le_pow_left (by omega : 1 ≤ L + 1) 2
  have hinner := stepCompilerInputResources_le input
  change assembled.time input ≤ 10 ^ 18 * (L + 1) ^ 2 ∧
    assembled.workspace input ≤ 10 ^ 18 * (L + 1) ^ 2 ∧
    assembled.tapeCount ≤ 207 at hinner
  have houter := stepCompilerOuterResources_le input
  change stepWithCompiler.time stepInput ≤ 289 * 10 ^ 33 * (L + 1) ^ 2 ∧
    stepWithCompiler.workspace stepInput ≤ 289 * 10 ^ 34 * (L + 1) ^ 2 ∧
    stepWithCompiler.tapeCount ≤ 1016 at houter
  have hraw := time_comp_le stepWithCompiler assembled input
  change (stepWithCompiler.comp assembled).time input ≤
    5 * assembled.time input + stepWithCompiler.time stepInput + 9 at hraw
  change (stepWithCompiler.comp assembled).time input ≤ 10 ^ 36 * (L + 1) ^ 2
  exact hraw.trans (by omega)

/-- The actual retained complete deterministic-step compiler has an independent quadratic
workspace bound in the complete encoded input length. The bound does not replace workspace by
time, and the installed program size remains the separate field `stepCompiler.staticBits`. -/
theorem stepCompiler_workspace_le (input : Desc × (List ℕ × SCfg)) :
    stepCompiler.workspace input ≤
      10 ^ 37 * ((eDeterministicStepInput input).length + 1) ^ 2 := by
  let L := (eDeterministicStepInput input).length
  let description := first eDesc (encPair (encList encUnary) eCfg)
  let tail := second eDesc (encPair (encList encUnary) eCfg)
  let word := (first (encList encUnary) eCfg).comp tail
  let cfg := (second (encList encUnary) eCfg).comp tail
  let symbol := inputSymbol.comp (word.pair (cfgInputPos.comp cfg))
  let assembled := description.pair (cfg.pair symbol)
  let stepInput : StepWithInput :=
    (input.1, input.2.2, Universal.inputSymbol input.2.1 input.2.2.inputPos)
  have hN : 1 ≤ (L + 1) ^ 2 := by
    simpa using Nat.pow_le_pow_left (by omega : 1 ≤ L + 1) 2
  have hinner := stepCompilerInputResources_le input
  change assembled.time input ≤ 10 ^ 18 * (L + 1) ^ 2 ∧
    assembled.workspace input ≤ 10 ^ 18 * (L + 1) ^ 2 ∧
    assembled.tapeCount ≤ 207 at hinner
  have houter := stepCompilerOuterResources_le input
  change stepWithCompiler.time stepInput ≤ 289 * 10 ^ 33 * (L + 1) ^ 2 ∧
    stepWithCompiler.workspace stepInput ≤ 289 * 10 ^ 34 * (L + 1) ^ 2 ∧
    stepWithCompiler.tapeCount ≤ 1016 at houter
  have hmax : max assembled.tapeCount stepWithCompiler.tapeCount ≤ 1016 :=
    max_le (hinner.2.2.trans (by omega)) houter.2.2
  have hraw := workspace_comp_le stepWithCompiler assembled input
  change (stepWithCompiler.comp assembled).workspace input ≤
    assembled.workspace input + stepWithCompiler.workspace stepInput +
      5 * assembled.time input +
        (6 * max assembled.tapeCount stepWithCompiler.tapeCount + 20) at hraw
  change (stepWithCompiler.comp assembled).workspace input ≤ 10 ^ 37 * (L + 1) ^ 2
  exact hraw.trans (by omega)

/-- A construction-derived static tape-count bound for the actual retained complete
deterministic-step compiler. -/
theorem stepCompiler_tapeCount_le : stepCompiler.tapeCount ≤ 1018 := by
  let description := first eDesc (encPair (encList encUnary) eCfg)
  let tail := second eDesc (encPair (encList encUnary) eCfg)
  let word := (first (encList encUnary) eCfg).comp tail
  let cfg := (second (encList encUnary) eCfg).comp tail
  let symbol := inputSymbol.comp (word.pair (cfgInputPos.comp cfg))
  let assembled := description.pair (cfg.pair symbol)
  have hinner := (stepCompilerInputResources_le
    (default : Desc × (List ℕ × SCfg))).2.2
  change assembled.tapeCount ≤ 207 at hinner
  have houter := (stepWithCompilerResources_le (default : StepWithInput)).2.2
  change (stepWithCompiler.comp assembled).tapeCount ≤ 1018
  simp only [comp]
  omega

end Turing.MultiTapeTM.Internal.NativeCompiler
