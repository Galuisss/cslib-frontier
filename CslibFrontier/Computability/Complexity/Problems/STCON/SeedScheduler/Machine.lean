/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.HozaSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

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

* `SeedSchedulerMachine.observations_inSpace`: query, halt, terminal reply, and acceptance
  use space linear in the encoded state.
* `SeedSchedulerMachine.step_liveScan`: a live scan takes the callback's step on the same input.
* `SeedSchedulerMachine.firstHalting_scan_iff`: split a successful scan and the resumed trace.
* `SeedSchedulerMachine.firstHalting_skip_iff`: split a skipped root's false selector and suffix.
* `SeedSchedulerMachine.length_run_le`: bound the state size on every selector prefix.
-/

public section

namespace Cslib.Complexity.STCON.SeedSchedulerMachine

open Cslib.DoubleCounting Cslib.Reachability.Hoza
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

/-- The live callback sees the original query answer and selector, and its caller frame
is unchanged by the step. -/
theorem step_liveScan {σ : Type} (setup : SeedSearchSetup) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict)
    (w : List Bool) (frame : SeedSchedulerFrame) (s : σ) (choice : Bool)
    (hlive : scan.halted s = false) :
    (machine setup scan start verdict).step w (.inl (.inr (frame, s))) choice =
      .inl (.inr (frame, scan.step w s choice)) := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, machine, hlive]

private theorem step_haltedScan {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (input : List Bool)
    (frame : SeedSchedulerFrame) (s : σ) (selector : Bool) (hhalt : scan.halted s = true) :
    (machine setup scan start verdict).step input (.inl (.inr (frame, s))) selector =
      if selector then .inr none else resume start frame (verdict s) := by
  simp [NondeterministicQueryMachine.step, machine, hhalt]

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
  rw [step_haltedScan setup scan start verdict w frame s selector hhalt]
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

private def PrefixState {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (w : List Bool) : State σ → Prop
  | .inl (.inl f) => f.Valid ∧ f.request.setup = setup
  | .inl (.inr (f, state)) =>
    f.Valid ∧ f.request.setup = setup ∧ f.needsScan = true ∧
      ∃ bits, scan.replay w bits (start f.request) = state
  | .inr (some (some a)) => a.seed < setup.parameters.search.seedLimit
  | .inr none | .inr (some none) => True

private theorem prefixState_enter {σ : Type} {setup : SeedSearchSetup}
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (w : List Bool) {f : SeedSchedulerFrame} (hf : f.Valid) (hs : f.request.setup = setup) :
    PrefixState setup scan start w (enter start f) := by
  unfold enter
  split
  · exact ⟨hf, hs, ‹f.needsScan = true›, [], rfl⟩
  · exact ⟨hf, hs⟩

private theorem prefixState_resume {σ : Type} {setup : SeedSearchSetup}
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (w : List Bool) {f : SeedSchedulerFrame} (hf : f.Valid) (hs : f.request.setup = setup)
    (result : Option ControllerVerdict) :
    PrefixState setup scan start w (resume start f result) := by
  unfold resume
  split
  · trivial
  · rename_i next hnext
    obtain ⟨hv, he, _⟩ := seedSchedulerStep_progress hf hnext
    exact prefixState_enter scan start w hv (he.trans hs)
  · rename_i answer _
    cases answer
    · trivial
    · exact hs ▸ hf.seed_lt

private theorem prefixState_step {σ : Type} {setup : SeedSearchSetup}
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (w : List Bool)
    {state : State σ} (h : PrefixState setup scan start w state) (bit : Bool) :
    PrefixState setup scan start w ((machine setup scan start verdict).step w state bit) := by
  cases state with
  | inr result =>
    rw [NondeterministicQueryMachine.step_of_halted _ _ (by rfl)]
    exact h
  | inl frame =>
    cases frame with
    | inl f =>
      obtain ⟨hf, hs⟩ := h
      cases bit
      · exact prefixState_resume scan start w hf hs none
      · trivial
    | inr active =>
      obtain ⟨f, s⟩ := active
      obtain ⟨hf, hs, hscan, bits, rfl⟩ := h
      cases hh : scan.halted (scan.replay w bits (start f.request))
      · rw [step_liveScan _ _ _ _ _ _ _ _ hh]
        exact ⟨hf, hs, hscan, bits ++ [bit], scan.replay_append w bits [bit] _⟩
      · rw [step_haltedScan _ _ _ _ _ _ _ _ hh]
        cases bit
        · exact prefixState_resume scan start w hf hs
            (verdict (scan.replay w bits (start f.request)))
        · trivial

/-- Every selector prefix of the same-input scheduler, including rejecting branches,
uses at most the uniform scanner state bound plus a linear allowance for the retained
setup and frame. The scanner bound applies to valid frames that request a scan on the
original input. -/
theorem length_run_le {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (encScan : σ ↪ List Bool)
    (w : List Bool) (scanBound : ℕ)
    (hsource : setup.sourceID < setup.parameters.search.subdivision.vertexCount)
    (hroot : ∀ j < setup.parameters.search.subdivision.originalCount,
      setup.originalSourceID j < setup.parameters.search.subdivision.vertexCount)
    (hscan : ∀ f : SeedSchedulerFrame, f.request.setup = setup → f.Valid →
      f.needsScan = true → ∀ bits,
        (encScan (scan.replay w bits (start f.request))).length ≤ scanBound)
    (bits : List Bool) :
    (encState encScan ((machine setup scan start verdict).run w bits)).length ≤
      24 * (encSeedSearchSetup setup).length + scanBound + 21 := by
  let M := machine setup scan start verdict
  have hinit : PrefixState setup scan start w M.init := by
    change PrefixState setup scan start w
      ((seedSchedulerCandidate setup 0).elim (.inr (some none)) (enter start))
    cases hc : seedSchedulerCandidate setup 0 with
    | none => trivial
    | some f =>
      obtain ⟨hf, hs, _⟩ := seedSchedulerCandidate_valid hc
      exact prefixState_enter scan start w hf hs
  have hrun : PrefixState setup scan start w (M.run w bits) := by
    induction bits using List.reverseRecOn with
    | nil => exact hinit
    | append_singleton bits bit ih =>
      rw [M.run_append]
      exact prefixState_step scan start verdict w ih bit
  have frameLength {f : SeedSchedulerFrame} (hf : f.Valid) (hs : f.request.setup = setup) :
      (encSeedSchedulerFrame f).length ≤ 12 * (encSeedSearchSetup setup).length + 9 :=
    hs ▸ hf.length_le (hs.symm ▸ hsource) (hs.symm ▸ hroot)
  change (encState encScan (M.run w bits)).length ≤ _
  generalize M.run w bits = state at hrun ⊢
  cases state with
  | inl live =>
    cases live with
    | inl f =>
      obtain ⟨hf, hs⟩ := hrun
      have hframe := frameLength hf hs
      simp only [encState, encSum_inl, List.length_cons]
      omega
    | inr active =>
      obtain ⟨f, s⟩ := active
      obtain ⟨hf, hs, hneeds, choices, rfl⟩ := hrun
      have hframe := frameLength hf hs
      have hcallback := hscan f hs hf hneeds choices
      simp only [encState, encSum_inl, encSum_inr, List.length_cons, length_encPair]
      omega
  | inr result =>
    rcases result with _ | (_ | answer)
    · simp [encState]
    · simp [encState]
    · have hseed : answer.seed < setup.parameters.search.seedLimit := hrun
      have hlength := (length_encNat_mono hseed.le).trans
        ((encSeedSearchSize_seedLimit_length_le setup.parameters.search).trans
          ((encSeedSearchParameters_search_length_le setup.parameters).trans
            (encSeedSearchSetup_parameters_length_le setup)))
      simp only [encState, encSum_inr, encOption_some, encAnswer_apply, length_encPair,
        encBool_apply, List.length_cons, List.length_nil]
      omega

end Cslib.Complexity.STCON.SeedSchedulerMachine
