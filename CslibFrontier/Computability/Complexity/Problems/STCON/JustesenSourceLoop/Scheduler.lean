/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceContext.Scheduler
public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceLoop
public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler.Machine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Retain

/-!
# Justesen source loop for scheduler requests

The seed scheduler can start the retained source loop directly from a scan request and the
prepared field context. The entry uses the subdivision's vertex count as fuel and shares the
workspace budget of the request and field producers. A single scheduler machine carries the
prepared field in its state and uses it to start each scan on the original input.

## Main definitions

* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest`: enter the concrete source loop.
* `Cslib.Complexity.STCON.justesenSeedScheduler`: the scheduler with a retained field.
* `Cslib.Complexity.STCON.configurationJustesenSeedSchedulerEntry`: its entry for an original word.

## Main results

* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest_budget`: the full-fuel entry
  uses the shared workspace budget.
* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest_eq`: the scheduler and original-word
  initializers agree at any requested source.
* `Cslib.Complexity.STCON.justesenSeedScheduler_observations_inSpace`:
  query, halt and acceptance in linear workspace in the encoded state.
* `Cslib.Complexity.STCON.justesenSeedScheduler_next_inSpace`:
  a scheduler transition in linear workspace in the encoded state and read/selector input.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_replay`: re-entering the fixed
  scheduler agrees with the scheduler initialized for the original word.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_length_run_le_log`:
  logarithmic encoded state length on every selector prefix.
* `Cslib.Complexity.STCON.configurationJustesenSeedSchedulerEntry_inSpace`:
  construct the original-word entry within the logarithmic workspace budget.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_haltsWithin_clock`:
  a common polynomial selector clock for every branch.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily
open _root_.Turing _root_.Turing.DoubleCounting
open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

/-- Enter the concrete retained round or terminate immediately at zero fuel. -/
@[expose] def justesenSourceLoopEntryOfRequest (request : SeedScanRequest) (field : FieldContext) :
    JustesenSourceLoopState :=
  SourceRoundLoop.enterRound justesenRetainedSourceRoundEntry
    (justesenSourceRegistersOfRequest request field)

/-- The callback entry uses the shared workspace budget of the request and field producers. -/
theorem justesenSourceLoopEntryOfRequest_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {request : α → SeedScanRequest} {field : α → FieldContext}
    (hrequest : ComputableInSpace request enc encSeedScanRequest S)
    (hfield : ComputableInSpace field enc encFieldContext S) :
    ComputableInSpace (fun a => justesenSourceLoopEntryOfRequest (request a) (field a))
      enc encJustesenSourceLoopState S :=
  budget_comp_linear
    (SourceRoundLoop.enterRound_inSpace encJustesenSourceContext encJustesenRetainedSourceRoundState
      (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)
      justesenRetainedSourceRoundEntry justesenRetainedSourceRoundEntry_inSpace)
    (justesenSourceRegistersOfRequest_budget hrequest hfield)

/-- The scheduler's concrete entry agrees with the original-word initializer at any source. -/
theorem justesenSourceLoopEntryOfRequest_eq {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (rank source : ℕ) :
    let setup := configurationSeedSearchSetup ntm c w
    justesenSourceLoopEntryOfRequest ⟨setup, rank, source⟩ (configurationFieldContext ntm c w) =
      (justesenSourceLoop ntm c
        ⟨configurationJustesenSubdivisionContext ntm c w rank, source, setup.targetID⟩
        setup.parameters.search.subdivision.vertexCount).init :=
  congrArg (SourceRoundLoop.enterRound justesenRetainedSourceRoundEntry)
    (justesenSourceRegistersOfRequest_eq ntm c w rank source)

/-- The concrete scheduler's scanner uses the source loop's fixed transitions. -/
noncomputable def justesenSeedSchedulerScan {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    NondeterministicQueryMachine JustesenSourceLoopState :=
  justesenSourceLoop ntm c ⟨configurationJustesenSubdivisionContext ntm c [] 0, 0, 0⟩ 0

/-- Run the scheduler for a given setup and prepared field, re-entering the source loop
at the request-specific state for each scan. -/
noncomputable def justesenSeedSchedulerFor {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (setup : SeedSearchSetup) (field : FieldContext) :
    NondeterministicQueryMachine (SeedSchedulerMachine.State JustesenSourceLoopState) :=
  SeedSchedulerMachine.machine setup (justesenSeedSchedulerScan ntm c)
    (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply

/-- The scheduler retains the prepared field alongside its existing state. -/
abbrev JustesenSeedSchedulerState :=
  FieldContext × SeedSchedulerMachine.State JustesenSourceLoopState

/-- Frame the retained field before the scheduler state. -/
def encJustesenSeedSchedulerState : JustesenSeedSchedulerState ↪ List Bool :=
  encPair encFieldContext (SeedSchedulerMachine.encState encJustesenSourceLoopState)

/-- One query machine for every prepared field and setup. Re-entry supplies the data for
the actual input word. -/
noncomputable def justesenSeedScheduler {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    NondeterministicQueryMachine JustesenSeedSchedulerState :=
  NondeterministicQueryMachine.retain (Equiv.refl _)
    (justesenSeedSchedulerFor ntm c (configurationSeedSearchSetup ntm c []))
    (configurationFieldContext ntm c [])

/-- The fixed scheduler's query, halt and acceptance observations use workspace linear in
the encoded retained state. -/
theorem justesenSeedScheduler_observations_inSpace {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let E := encJustesenSeedSchedulerState
    let M := justesenSeedScheduler ntm c
    ComputableInSpace M.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace M.halted E encBool (fun s => (E s).length) ∧
      ComputableInSpace M.accept E encBool (fun s => (E s).length) := by
  intro E M
  let setup := configurationSeedSearchSetup ntm c []
  let field := configurationFieldContext ntm c []
  have hscan := (justesenSourceLoop_parts_inSpace ntm c
    ⟨configurationJustesenSubdivisionContext ntm c [] 0, 0, 0⟩ 0).1
  obtain ⟨hq, hh, _, ha⟩ := SeedSchedulerMachine.observations_inSpace
    encJustesenSourceLoopState setup (justesenSeedSchedulerScan ntm c)
    (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply hscan
  have hstate := snd encFieldContext (SeedSchedulerMachine.encState encJustesenSourceLoopState)
  refine ⟨(budget_comp_linear hq hstate).of_enc_eq ?_,
    (budget_comp_linear hh hstate).of_enc_eq ?_, (budget_comp_linear ha hstate).of_enc_eq ?_⟩ <;>
    rintro ⟨retained, state⟩ <;>
    obtain ⟨hquery, hhalted, haccept⟩ := SeedSchedulerMachine.observations_eq setup setup
      (justesenSeedSchedulerScan ntm c)
      (fun request => justesenSourceLoopEntryOfRequest request retained)
      (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply
  · exact congrArg encNat (congrFun hquery state)
  · exact congrArg encBool (congrFun hhalted state)
  · exact congrArg encBool (congrFun haccept state)

open NondeterministicQueryMachine in
/-- A step of the fixed scheduler uses linear workspace in the encoded state and read/selector
input. If it enters a scan, the scan uses the field stored in that state. -/
theorem justesenSeedScheduler_next_inSpace {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let E := encPair encJustesenSeedSchedulerState encReadChoice
    ComputableInSpace (justesenSeedScheduler ntm c).next E encJustesenSeedSchedulerState
      (fun p => (E p).length) := by
  let setup := configurationSeedSearchSetup ntm c []
  let scan := justesenSeedSchedulerScan ntm c
  let encState := SeedSchedulerMachine.encState encJustesenSourceLoopState
  have hstart := justesenSourceLoopEntryOfRequest_budget
    (fst encSeedScanRequest encFieldContext) (snd encSeedScanRequest encFieldContext)
  obtain ⟨_, hnext, hhalt, hreply⟩ := justesenSourceLoop_parts_inSpace ntm c
    ⟨configurationJustesenSubdivisionContext ntm c [] 0, 0, 0⟩ 0
  have hstep := SeedSchedulerMachine.next_withContext_inSpace encFieldContext
    encJustesenSourceLoopState setup scan (fun p => justesenSourceLoopEntryOfRequest p.1 p.2)
    SourceRoundLoop.reply hstart hhalt hreply hnext
  have hstate := fst encJustesenSeedSchedulerState encReadChoice
  have hfield := budget_comp_linear (fst encFieldContext encState) hstate
  have hinner := budget_comp_linear (snd encFieldContext encState) hstate
  have hinput := snd encJustesenSeedSchedulerState encReadChoice
  have hnextInner := budget_comp_linear hstep (budget_prod hinner (budget_prod hfield hinput))
  exact (budget_prod hfield hnextInner).of_enc_eq fun ⟨⟨_, _⟩, _⟩ => rfl

/-- Enter candidate zero with the setup and retained field computed on the original word. -/
noncomputable def configurationJustesenSeedSchedulerEntry {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    JustesenSeedSchedulerState :=
  let field := configurationFieldContext ntm c w
  (field, (justesenSeedSchedulerFor ntm c (configurationSeedSearchSetup ntm c w) field).init)

private theorem inSpace_of_logSpace_and_length {β : Type} {enc : β ↪ List Bool}
    {f : List Bool → β} (h : ComputableInLogSpace f encBits enc)
    (hlen : ∃ C, ∀ w, (enc (f w)).length ≤ C * (Nat.log2 w.length + 1)) :
    ComputableInSpace f encBits enc (fun w => Nat.log2 w.length + 1) := by
  obtain ⟨time, A, hwork⟩ := h
  obtain ⟨B, hlen⟩ := hlen
  refine ⟨time, max A B, hwork.mono (fun _ => le_rfl) (fun w => ?_), fun w => ?_⟩
  · simp only [encBits_apply]
    exact (Nat.mul_le_mul_right _ (le_max_left _ _)).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ _))
  · exact (hlen w).trans ((Nat.mul_le_mul_right _ (le_max_right _ _)).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ _)))

/-- The fixed scheduler's original-word entry uses logarithmic workspace and charges its
encoded output, including the retained field. -/
theorem configurationJustesenSeedSchedulerEntry_inSpace {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInSpace (configurationJustesenSeedSchedulerEntry ntm c)
      encBits encJustesenSeedSchedulerState (fun w => Nat.log2 w.length + 1) := by
  have hsetup := inSpace_of_logSpace_and_length (configurationSeedSearchSetup_inLogSpace ntm c)
    (length_configurationSeedSearchSetup_le_log ntm c)
  have hfield := inSpace_of_logSpace_and_length (configurationFieldContext_inLogSpace ntm c)
    (length_configurationFieldContext_le_log ntm c)
  have hstart := justesenSourceLoopEntryOfRequest_budget
    (fst encSeedScanRequest encFieldContext) (snd encSeedScanRequest encFieldContext)
  have hinit := SeedSchedulerMachine.init_withContext_budget encFieldContext
    encJustesenSourceLoopState (justesenSeedSchedulerScan ntm c)
    (fun p => justesenSourceLoopEntryOfRequest p.1 p.2) SourceRoundLoop.reply hstart hsetup hfield
  exact budget_prod hfield hinit

/-- Every selector replay from an original-word entry retains the field and agrees with
the scheduler initialized directly for that word, including rejected replays. -/
theorem configurationJustesenSeedScheduler_replay {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w bits : List Bool) :
    let field := configurationFieldContext ntm c w
    (justesenSeedScheduler ntm c).replay w bits
      (configurationJustesenSeedSchedulerEntry ntm c w) =
      (field, (justesenSeedSchedulerFor ntm c (configurationSeedSearchSetup ntm c w) field).run
        w bits) := by
  intro field
  let empty := configurationSeedSearchSetup ntm c []
  let setup := configurationSeedSearchSetup ntm c w
  let family := justesenSeedSchedulerFor ntm c empty
  let entered := justesenSeedSchedulerFor ntm c setup field
  let e := Equiv.refl JustesenSeedSchedulerState
  change (NondeterministicQueryMachine.retain e family (configurationFieldContext ntm c [])).replay
    w bits (e.symm (field, entered.init)) = (field, entered.run w bits)
  rw [NondeterministicQueryMachine.replay_retain]
  have hentry : (family field).withInit entered.init = entered :=
    SeedSchedulerMachine.machine_withInit empty setup (justesenSeedSchedulerScan ntm c)
      (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply
  exact congrArg (fun M : NondeterministicQueryMachine _ => (field, M.run w bits)) hentry

private theorem justesenSeedSchedulerScan_withInit_of_valid {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (f : SeedSchedulerFrame) (hs : f.request.setup = configurationSeedSearchSetup ntm c w)
    (hv : f.Valid) :
    let I := configurationInstance ntm c w
    let setup := configurationSeedSearchSetup ntm c w
    let n := setup.parameters.search.subdivision.vertexCount
    ∃ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source : Fin n),
      (justesenSeedSchedulerScan ntm c).withInit
        (justesenSourceLoopEntryOfRequest f.request (configurationFieldContext ntm c w)) =
        justesenSourceLoop ntm c
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, setup.targetID⟩
          n := by
  intro I setup n
  rcases f with ⟨⟨saved, rank, source⟩, cursor, answer⟩
  change saved = setup at hs
  subst saved
  have hrank := hv.seed_lt
  change rank < setup.parameters.search.seedLimit at hrank
  rw [configurationSeedScheduler_seedLimit ntm c w,
    (configurationSeedSearchSetup_endpoints ntm c w).1] at hrank
  have hends := configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w
  have hroot := fun j hj => configurationSeedSearchSetup_originalSourceID_lt_vertexCount
    ntm c w (position := j) hj
  have hsource : source < n := hv.source_lt hends.1 hroot
  refine ⟨⟨rank, hrank⟩, ⟨source, hsource⟩, ?_⟩
  rw [show justesenSourceLoopEntryOfRequest ⟨setup, rank, source⟩
      (configurationFieldContext ntm c w) = _ from
    justesenSourceLoopEntryOfRequest_eq ntm c w rank source]
  exact justesenSourceLoop_withInit ntm c _ _ 0 n

/-- Every selector prefix of the fixed retained-field scheduler fits in logarithmically
many bits in the original input length, including replays that reject. -/
theorem configurationJustesenSeedScheduler_length_run_le_log {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w bits : List Bool, (encJustesenSeedSchedulerState
      ((justesenSeedScheduler ntm c).replay w bits
        (configurationJustesenSeedSchedulerEntry ntm c w))).length ≤
          C * (Nat.log2 w.length + 1) := by
  obtain ⟨F, hfield⟩ := length_configurationFieldContext_le_log ntm c
  obtain ⟨A, hsetup⟩ := length_configurationSeedSearchSetup_le_log ntm c
  obtain ⟨B, hscan⟩ := configurationJustesenSourceLoop_length_run_le_log ntm c
  refine ⟨2 * F + 24 * A + B + 22, fun w bits => ?_⟩
  let setup := configurationSeedSearchSetup ntm c w
  let field := configurationFieldContext ntm c w
  let bound := Nat.log2 w.length + 1
  let n := setup.parameters.search.subdivision.vertexCount
  let scan := justesenSeedSchedulerScan ntm c
  let start := fun r => justesenSourceLoopEntryOfRequest r field
  have hends := configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w
  have hroot := fun j hj => configurationSeedSearchSetup_originalSourceID_lt_vertexCount
    ntm c w (position := j) hj
  have hcap (f : SeedSchedulerFrame) (hs : f.request.setup = setup)
      (hv : f.Valid)
      (_ : f.needsScan = true) (choices : List Bool) :
      (encJustesenSourceLoopState (scan.replay w choices (start f.request))).length ≤
        B * bound := by
    obtain ⟨seed, source, hreenter⟩ :=
      justesenSeedSchedulerScan_withInit_of_valid ntm c w f hs hv
    have h := hscan w seed source ⟨setup.targetID, hends.2⟩ n le_rfl choices
    rw [← hreenter] at h
    exact h
  have hmachine := SeedSchedulerMachine.length_run_le setup scan start SourceRoundLoop.reply
    encJustesenSourceLoopState w (B * bound) hends.1 hroot hcap bits
  rw [configurationJustesenSeedScheduler_replay ntm c w bits]
  change (encPair encFieldContext (SeedSchedulerMachine.encState encJustesenSourceLoopState)
    (field, (justesenSeedSchedulerFor ntm c setup field).run w bits)).length ≤ _
  rw [length_encPair]
  have hF : (encFieldContext field).length ≤ F * bound := hfield w
  have hA : (encSeedSearchSetup setup).length ≤ A * bound := hsetup w
  have hM : (SeedSchedulerMachine.encState encJustesenSourceLoopState
      ((justesenSeedSchedulerFor ntm c setup field).run w bits)).length ≤
        24 * (encSeedSearchSetup setup).length + B * bound + 21 := hmachine
  have hconst : 22 ≤ 22 * bound := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change _ ≤ (2 * F + 24 * A + B + 22) * bound
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

/-- Charge the full-fuel scan and one return selector at each designated or indexed frame. -/
noncomputable def configurationJustesenSeedSchedulerClock {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  let size := (configurationSeedSearchSetup ntm c w).parameters.search
  size.seedLimit * ((1 + size.subdivision.originalCount) *
    (configurationJustesenSourceLoopClock ntm c w + 1))

/-- The scheduler's selector clock is polynomial in the original word length. -/
theorem configurationJustesenSeedSchedulerClock_polyBounded {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenSeedSchedulerClock ntm c) :=
  configurationSeedScheduler_clock_polyBounded ntm c
    ((configurationJustesenSourceLoopClock_polyBounded ntm c).add (.const 1))

/-- Every scheduler branch, including rejection and either designated answer, halts within
the common clock at the original-word entry. -/
theorem configurationJustesenSeedScheduler_haltsWithin_clock {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    NondeterministicQueryMachine.HaltsWithin
      ((justesenSeedScheduler ntm c).withInit (configurationJustesenSeedSchedulerEntry ntm c w))
      w (configurationJustesenSeedSchedulerClock ntm c w) := by
  let setup := configurationSeedSearchSetup ntm c w
  let empty := configurationSeedSearchSetup ntm c []
  let field := configurationFieldContext ntm c w
  let scan := justesenSeedSchedulerScan ntm c
  let start := fun r => justesenSourceLoopEntryOfRequest r field
  let clock := configurationJustesenSourceLoopClock ntm c w
  have hends := configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w
  have hscan (f : SeedSchedulerFrame) (hs : f.request.setup = setup) (hv : f.Valid)
      (_ : f.needsScan = true) : (scan.withInit (start f.request)).HaltsWithin w clock := by
    obtain ⟨seed, source, hreenter⟩ :=
      justesenSeedSchedulerScan_withInit_of_valid ntm c w f hs hv
    change NondeterministicQueryMachine.HaltsWithin ((justesenSeedSchedulerScan ntm c).withInit
      (justesenSourceLoopEntryOfRequest f.request (configurationFieldContext ntm c w))) w clock
    rw [hreenter]
    exact configurationJustesenSourceLoop_haltsWithin_clock ntm c w
      seed source ⟨setup.targetID, hends.2⟩ _ le_rfl
  have hscheduler := SeedSchedulerMachine.haltsWithin setup scan start SourceRoundLoop.reply
    w clock hscan
  intro bits hlen
  rw [NondeterministicQueryMachine.run_withInit,
    configurationJustesenSeedScheduler_replay ntm c w bits]
  change (justesenSeedSchedulerFor ntm c empty field).halted
    ((justesenSeedSchedulerFor ntm c setup field).run w bits) = true
  have hhalt := congrArg NondeterministicQueryMachine.halted
    (SeedSchedulerMachine.machine_withInit empty setup scan start SourceRoundLoop.reply)
  change (justesenSeedSchedulerFor ntm c empty field).halted =
    (justesenSeedSchedulerFor ntm c setup field).halted at hhalt
  rw [hhalt]
  exact hscheduler bits hlen

end Cslib.Complexity.STCON
