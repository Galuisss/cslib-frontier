/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Same-input seed scheduler

The binary scheduler keeps its frame during each source scan. The callback reads the original
input. Only the false selector resumes the scheduler from a completed scan or advances a
skipped designated root.

## Main definitions

* `SeedSchedulerMachine.State`: pending skip, active scan, or finished search.
* `SeedSchedulerMachine.machine`: compose the scheduler transition with a supplied scan.
* `SeedSchedulerMachine.resume`: continue after a skipped root or a returned verdict.
* `SeedSchedulerMachine.reply`: observe exhaustion or the chosen seed rank and designated answer
  on a successful branch.

## Main results

* `SeedSchedulerMachine.enter_inSpace` and `SeedSchedulerMachine.init_budget`: enter a
  supplied scan or skip phase within the caller's workspace budget.
* `SeedSchedulerMachine.resume_inSpace`: process the scheduler's control result in space
  linear in the paired frame and verdict encoding.
* `SeedSchedulerMachine.next_inSpace`: advance the scheduler in space linear in its encoded
  state, read bit, and selector.
* `SeedSchedulerMachine.observations_inSpace`: query, halt, terminal reply, and acceptance
  use space linear in the encoded state.
* `SeedSchedulerMachine.step_liveScan`: a live scan takes the callback's step on the same input.
* `SeedSchedulerMachine.firstHalting_scan_iff`: split a successful scan and the resumed trace.
* `SeedSchedulerMachine.firstHalting_skip_iff`: split a skipped root's false selector and suffix.
-/

public section

namespace Cslib.Complexity.STCON.SeedSchedulerMachine

open Cslib.DoubleCounting
open _root_.Turing _root_.Turing.MultiTapeTM

/-- A selected binary seed and its designated reachability answer. -/
structure Answer where
  /-- Seed rank in increasing binary order. -/
  seed : ℕ
  /-- The answer returned by the designated scan. -/
  reachable : Bool
  deriving DecidableEq

/-- Encode the binary rank and the designated answer. -/
enc_structure encAnswer : Answer where
  seed : encNat, reachable : encBool

/-- The terminal payload records rejection, exhaustion, or a selected answer. -/
abbrev State (σ : Type) :=
  (SeedSchedulerFrame ⊕ (SeedSchedulerFrame × σ)) ⊕ Option (Option Answer)

/-- Frame the active scheduler and callback state, or encode the terminal payload. -/
def encState {σ : Type} (encScan : σ ↪ List Bool) : State σ ↪ List Bool :=
  encSum (encSum encSeedSchedulerFrame (encPair encSeedSchedulerFrame encScan))
    (encOption (encOption encAnswer))

/-- Start the requested scan if needed, or enter the deterministic skip phase. -/
@[expose] def enter {σ : Type} (start : SeedScanRequest → σ) (frame : SeedSchedulerFrame) :
    State σ :=
  if frame.needsScan then .inl (.inr (frame, start frame.request)) else .inl (.inl frame)

/-- Apply the local scheduler transition and enter its next frame or terminal state. -/
def resume {σ : Type} (start : SeedScanRequest → σ) (frame : SeedSchedulerFrame)
    (verdict : Option ControllerVerdict) : State σ :=
  match seedSchedulerStep frame verdict with
  | none => .inr none
  | some (.inl next) => enter start next
  | some (.inr answer) => .inr (some (answer.map fun bit => ⟨frame.request.seed, bit⟩))

/-- Read a successful terminal result. The outer option is absent for a live or rejected state.
An exhausted search has a present outer option and no answer. -/
@[expose] def reply {σ : Type} : State σ → Option (Option Answer)
  | .inl _ => none
  | .inr result => result

/-- Scan the designated source and then the indexed roots on the original read-only input.
Accept when the terminal result contains a positive designated answer. -/
def machine {σ : Type} (setup : SeedSearchSetup) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict) :
    NondeterministicQueryMachine (State σ) where
  init := (seedSchedulerCandidate setup 0).elim (.inr (some none)) (enter start)
  query
    | .inl (.inr (_, s)) => scan.query s
    | _ => 0
  next
    | (.inl (.inl frame), _, choice) =>
      if choice then .inr none else resume start frame none
    | (.inl (.inr (frame, s)), read, choice) =>
      if scan.halted s then
        if choice then .inr none else resume start frame (verdict s)
      else .inl (.inr (frame, scan.next (s, read, choice)))
    | (.inr result, _, _) => .inr result
  halted
    | .inl _ => false
    | .inr _ => true
  accept s := ((reply s).join.map Answer.reachable).getD false

open _root_.Turing.MultiTapeTM.ComputableInSpace in
/-- Enter a skipped root or an active scan within space linear in the encoded frame. -/
theorem enter_inSpace {σ : Type} (encScan : σ ↪ List Bool) (start : SeedScanRequest → σ)
    (hstart : ComputableInSpace start encSeedScanRequest encScan
      (fun r => (encSeedScanRequest r).length)) :
    ComputableInSpace (enter start) encSeedSchedulerFrame (encState encScan)
      (fun f => (encSeedSchedulerFrame f).length) := by
  let scanState := encPair encSeedSchedulerFrame encScan
  let live := encSum encSeedSchedulerFrame scanState
  let terminal := encOption (encOption encAnswer)
  have hframe := budget_id (enc := encSeedSchedulerFrame) (.refl _)
  have hentry := budget_comp_linear hstart (encSeedSchedulerFrame_request_budget hframe)
  have hscan := budget_comp_linear (of_inO (ComputableInO.inr encSeedSchedulerFrame scanState))
    (budget_prod hframe hentry)
  have hskip := of_inO (ComputableInO.inl encSeedSchedulerFrame scanState)
  have hlive := budget_ite (SeedSchedulerFrame.needsScan_budget hframe) hscan hskip
  exact (budget_comp_linear (of_inO (ComputableInO.inl live terminal)) hlive).of_enc_eq fun f => by
    change encState encScan (enter start f) = encState encScan
      (.inl (if f.needsScan then .inr (f, start f.request) else .inl f))
    unfold enter
    split <;> rfl

open _root_.Turing.MultiTapeTM.ComputableInSpace in
/-- Construct the scheduler's initial state under the setup producer's workspace budget. -/
theorem init_budget {α σ : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (encScan : σ ↪ List Bool) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict)
    (hstart : ComputableInSpace start encSeedScanRequest encScan
      (fun r => (encSeedScanRequest r).length))
    {setup : α → SeedSearchSetup} (hsetup : ComputableInSpace setup enc encSeedSearchSetup S) :
    ComputableInSpace (fun a => (machine (setup a) scan start verdict).init)
      enc (encState encScan) S := by
  have hzero := (constZero (encIn := enc) (encB := encNat) 0).mono_le (fun a => Nat.zero_le (S a))
  have hcandidate := seedSchedulerCandidate_budget hsetup hzero
  have hentry := optionElim (.inr (some none)) (enter_inSpace encScan start hstart)
  exact (budget_comp_linear hentry hcandidate).of_enc_eq fun _ => rfl

open _root_.Turing.MultiTapeTM.ComputableInSpace in
/-- Resume the scheduler in workspace linear in the paired frame and optional verdict.
A completed answer keeps the seed rank from the retained frame. -/
theorem resume_inSpace {σ : Type} (encScan : σ ↪ List Bool) (start : SeedScanRequest → σ)
    (hstart : ComputableInSpace start encSeedScanRequest encScan
      (fun r => (encSeedScanRequest r).length)) :
    let E := encPair encSeedSchedulerFrame
      (encOption _root_.Turing.DoubleCounting.SourceRoundLoop.encVerdict)
    ComputableInSpace (fun p => resume start p.1 p.2) E (encState encScan)
      (fun p => (E p).length) := by
  let F := encSeedSchedulerFrame
  let R := encState encScan
  let live := encSum F (encPair F encScan)
  let terminal := encOption (encOption encAnswer)
  let verdict := encOption _root_.Turing.DoubleCounting.SourceRoundLoop.encVerdict
  have hcontinue := budget_comp_linear (enter_inSpace encScan start hstart) (snd F F)
  have hframeWithBit := fst F encBool
  have hrank := encSeedScanRequest_seed_budget (encSeedSchedulerFrame_request_budget hframeWithBit)
  have hresult := encAnswer_mk_budget hrank (snd F encBool)
  have hnoAnswer := budget_const (encIn := F) (encB := encOption encAnswer) none (.refl _)
  have hanswer := optionElimSnd hnoAnswer (budget_optionSome hresult)
  have hfinish := budget_comp_linear (of_inO (ComputableInO.inr live terminal))
    (budget_optionSome hanswer)
  have hreject := budget_const (encIn := F) (encB := R) (.inr none) (.refl _)
  have hdispatch := optionElimSnd hreject (sumElimSnd hcontinue hfinish)
  have hinput := budget_prod (fst F verdict) seedSchedulerStep_inSpace
  exact (budget_comp_linear hdispatch hinput).of_enc_eq fun p => by
    unfold resume
    cases seedSchedulerStep p.1 p.2 with
    | none => rfl
    | some result =>
      cases result with
      | inl next => rfl
      | inr answer => cases answer <;> rfl

open _root_.Turing.MultiTapeTM.ComputableInSpace in
/-- Query, read the phase tag or terminal reply, and test acceptance in space linear in
the encoded scheduler state. Only the active scan's query uses a supplied certificate. -/
theorem observations_inSpace {σ : Type} (encScan : σ ↪ List Bool) (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict)
    (hquery : ComputableInSpace scan.query encScan encNat (fun s => (encScan s).length)) :
    let E := encState encScan
    let M := machine setup scan start verdict
    ComputableInSpace M.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace M.halted E encBool (fun s => (E s).length) ∧
      ComputableInSpace reply E (encOption (encOption encAnswer)) (fun s => (E s).length) ∧
      ComputableInSpace M.accept E encBool (fun s => (E s).length) := by
  intro E M
  let live := encSum encSeedSchedulerFrame (encPair encSeedSchedulerFrame encScan)
  let terminal := encOption (encOption encAnswer)
  have hquerySkip := budget_const (encIn := encSeedSchedulerFrame) (encB := encNat) 0 (.refl _)
  have hqueryScan := budget_comp_linear hquery (snd encSeedSchedulerFrame encScan)
  have hqueryTerminal := budget_const (encIn := terminal) (encB := encNat) 0 (.refl _)
  have hqueryMachine : ComputableInSpace M.query E encNat (fun s => (E s).length) :=
    (sumElim (sumElim hquerySkip hqueryScan) hqueryTerminal).of_enc_eq fun
      | .inl (.inl _) | .inl (.inr _) | .inr _ => rfl
  have hhaltLive := budget_const (encIn := live) (encB := encBool) false (.refl _)
  have hhaltTerminal := budget_const (encIn := terminal) (encB := encBool) true (.refl _)
  have hhalt : ComputableInSpace M.halted E encBool (fun s => (E s).length) :=
    (sumElim hhaltLive hhaltTerminal).of_enc_eq fun | .inl _ | .inr _ => rfl
  have hreplyLive := budget_const (encIn := live) (encB := terminal) none (.refl _)
  have hreplyTerminal := budget_id (enc := terminal) (.refl _)
  have hreply : ComputableInSpace reply E terminal (fun s => (E s).length) :=
    (sumElim hreplyLive hreplyTerminal).of_enc_eq fun | .inl _ | .inr _ => rfl
  have hanswer := encAnswer_reachable_budget (budget_id (enc := encAnswer) (.refl _))
  have haccept := budget_comp_linear (optionElim false (optionElim false hanswer)) hreply
  exact ⟨hqueryMachine, hhalt, hreply, haccept.of_enc_eq fun
    | .inl _ | .inr none | .inr (some none) | .inr (some (some _)) => rfl⟩

open _root_.Turing.MultiTapeTM.ComputableInSpace NondeterministicQueryMachine in
/-- Forward a live scanner transition or resume its caller, using workspace linear in the
encoded scheduler state and the read and selector bits. -/
theorem next_inSpace {σ : Type} (encScan : σ ↪ List Bool) (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict)
    (hstart : ComputableInSpace start encSeedScanRequest encScan
      (fun r => (encSeedScanRequest r).length))
    (hhalt : ComputableInSpace scan.halted encScan encBool (fun s => (encScan s).length))
    (hverdict : ComputableInSpace verdict encScan
      (encOption _root_.Turing.DoubleCounting.SourceRoundLoop.encVerdict)
      (fun s => (encScan s).length))
    (hnext : ComputableInSpace scan.next (encPair encScan encReadChoice) encScan
      (fun p => (encPair encScan encReadChoice p).length)) :
    let E := encState encScan
    let P := encPair E encReadChoice
    ComputableInSpace (machine setup scan start verdict).next P E (fun p => (P p).length) := by
  let F := encSeedSchedulerFrame
  let A := encPair F encScan
  let L := encSum F A
  let T := encOption (encOption encAnswer)
  let E := encState encScan
  let V := encOption _root_.Turing.DoubleCounting.SourceRoundLoop.encVerdict
  have hresume := resume_inSpace encScan start hstart
  have hskipFrame := fst F encReadChoice
  have hskipChoice := snd' (snd F encReadChoice)
  have hskipReject := budget_const (encIn := encPair F encReadChoice) (encB := E) (.inr none)
    (.refl _)
  have hnoVerdict := budget_const (encIn := encPair F encReadChoice) (encB := V) none (.refl _)
  have hskip := budget_ite hskipChoice hskipReject
    (budget_comp_linear hresume (budget_prod hskipFrame hnoVerdict))
  have hactive := fst A encReadChoice
  have hread := snd A encReadChoice
  have hsuspended := fst' hactive
  have hscan := snd' hactive
  have hreturn := budget_comp_linear hresume
    (budget_prod hsuspended (budget_comp_linear hverdict hscan))
  have hscanReject := budget_const (encIn := encPair A encReadChoice) (encB := E) (.inr none)
    (.refl _)
  have hliveState := budget_prod hsuspended (budget_comp_linear hnext (budget_prod hscan hread))
  have hlive := budget_comp_linear (of_inO (ComputableInO.inl L T))
    (budget_comp_linear (of_inO (ComputableInO.inr F A)) hliveState)
  have hrun := budget_ite (budget_comp_linear hhalt hscan)
    (budget_ite (snd' hread) hscanReject hreturn) hlive
  have hfinished := budget_comp_linear (of_inO (ComputableInO.inr L T)) (fst T encReadChoice)
  refine (sumElimFst (sumElimFst hskip hrun) hfinished).of_enc_eq ?_
  rintro ⟨(f | ⟨f, s⟩) | result, read, bit⟩
  · cases bit <;> rfl
  · cases scan.halted s <;> cases bit <;> rfl
  · rfl

/-- The live callback sees the original query answer and selector, and its caller frame
is unchanged by the step. -/
theorem step_liveScan {σ : Type} (setup : SeedSearchSetup) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict)
    (w : List Bool) (frame : SeedSchedulerFrame) (s : σ) (choice : Bool)
    (hlive : scan.halted s = false) :
    (machine setup scan start verdict).step w (.inl (.inr (frame, s))) choice =
      .inl (.inr (frame, scan.step w s choice)) := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, machine, hlive]

/-- A successful first halt from an active scan consumes its parsed verdict and then
first halts from the resumed scheduler, using the parser's unmodified suffix.
The frame must request a scan, as it does when `enter` selects the active phase. -/
theorem firstHalting_scan_iff {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (w : List Bool)
    (frame : SeedSchedulerFrame) (state : σ) (bits : List Bool) (answer : Option Answer)
    (hscan : frame.needsScan = true) :
    let M := machine setup scan start verdict
    let active : State σ := .inl (.inr (frame, state))
    M.FirstHalting w bits active ∧ M.replay w bits active = .inr (some answer) ↔
      ∃ value rest, scan.readReply verdict w state bits = some (value, rest) ∧
        M.FirstHalting w rest (resume start frame (some value)) ∧
        M.replay w rest (resume start frame (some value)) = .inr (some answer) := by
  intro M active
  refine NondeterministicQueryMachine.successful_call_iff M scan w
    (fun s => .inl (.inr (frame, s))) verdict (fun v => resume start frame (some v))
    (.inr none) (.inr (some answer)) rfl (by simp) rfl (fun _ => rfl)
    (step_liveScan setup scan start verdict w frame) ?_ state bits
  intro s selector hhalt
  have hstep : M.step w (.inl (.inr (frame, s))) selector =
      if selector then .inr none else resume start frame (verdict s) := by
    simp [M, NondeterministicQueryMachine.step, machine, hhalt]
  rw [hstep]
  cases hv : verdict s with
  | none => simp [resume, seedSchedulerStep_noReply_of_needsScan frame hscan]
  | some v => rfl

/-- A successful first halt from a skipped root consumes exactly one false selector
before continuing the search. -/
theorem firstHalting_skip_iff {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (w : List Bool)
    (frame : SeedSchedulerFrame) (bits : List Bool) (answer : Option Answer) :
    let M := machine setup scan start verdict
    let skip : State σ := .inl (.inl frame)
    M.FirstHalting w bits skip ∧ M.replay w bits skip = .inr (some answer) ↔
      ∃ rest, bits = false :: rest ∧ M.FirstHalting w rest (resume start frame none) ∧
        M.replay w rest (resume start frame none) = .inr (some answer) := by
  intro M skip
  cases bits with
  | nil => simp [skip]
  | cons selector bits =>
    have hskip : M.halted skip = false := rfl
    rw [M.firstHalting_cons_iff, M.replay_cons, hskip]
    cases selector
    · have hstep : M.step w skip false = resume start frame none := rfl
      simp [hstep]
    · have hstep : M.step w skip true = .inr none := rfl
      have hhalt : M.halted (.inr none) = true := rfl
      simp [hstep, M.replay_of_halted w hhalt]

end Cslib.Complexity.STCON.SeedSchedulerMachine
