/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.FirstMatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Universal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ListResourceBounds
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

end Turing.MultiTapeTM.Internal.NativeCompiler
