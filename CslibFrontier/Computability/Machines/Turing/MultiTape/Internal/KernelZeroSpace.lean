/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1138 @b1635b2e
-- The section on the identity (`tidyCopy`) is from crei:crei/tidy-universal @7f7c0696
-- (unsubmitted).

public import Mathlib.Basic.Finite.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Id
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

/-! # The existing zero-workspace rewind and copy machines

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-! ### Machines without work tapes -/

section NoWorkTapes

variable {State : Type*} {tm : MultiTapeTM 0 Symbol State}

/-- If a machine without work tapes has a run path from its start to a halted configuration, then
following it with `Turing.MultiTapeTM.rewindInput` computes the output of that configuration
tidily: the rewind returns the input head from its position `p` in `p - 1 + 2` further steps. -/
public theorem computesTidily_seq_rewindInput_of_runPath {q : tm.RunPath input}
    (hh : q.head = wordsCfg input (some tm.q₀) (fun _ => []) []) (hl : q.last.Halted) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input q.last.output
      (q.time + (q.last.inputPos.val - 1 + 2)) 0 := by
  let r := MultiTapeNTM.RunPath.ofDeterministic (rewindInput Symbol)
    (q.last.withState (some (rewindInput Symbol).q₀)) (q.last.inputPos.val - 1 + 2)
  have hr : r.last = wordsCfg input none (fun _ => []) q.last.output :=
    (runFrom_rewindInput q.last.inputPos q.last.workTapes q.last.workTapePos q.last.output).trans
      (Cfg.ext_zero_tapes rfl rfl rfl)
  obtain ⟨p, hph, hpl, hpt, -⟩ := exists_runPath_seq (p₁ := r) hl rfl
  exact computesTidily_iff.mpr ⟨p, by rw [hph, hh]; rfl, by simp [hpl, hr], hpt,
    by simp [MultiTapeNTM.RunPath.space]⟩

/-- A machine without work tapes that computes `output` in time `t`, followed by
`Turing.MultiTapeTM.rewindInput`, computes `output` tidily in time `2 * t + 2`: in `t` steps the
input head moves at most `t` cells, so the rewind takes at most `t + 2` steps. -/
public theorem ComputesInTimeAndSpace.computesTidily_seq_rewindInput {output : List Symbol}
    {t s : ℕ} (h : ComputesInTimeAndSpace tm input output t s) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input output (2 * t + 2) 0 := by
  obtain ⟨⟨u, hu_halt, hu_out⟩, htime, -⟩ := h
  -- the computation path of `t` steps ends halted
  let q := MultiTapeNTM.ComputationPath.ofDeterministic tm input t
  have hl : q.last.Halted := htime q le_rfl
  -- the machine has halted after both `t` and `u` steps, so the outputs agree
  have hout : q.last.output = output := by
    change (tm.runFrom (tm.initCfg input) t).output = output
    rcases le_total u t with hut | htu
    · rw [runFrom_eq_of_halt _ _ hut hu_halt, hu_out]
    · rw [← runFrom_eq_of_halt _ _ htu hl, hu_out]
  have hpos : q.last.inputPos.val ≤ 1 + t := by
    change ((tm.runFrom (tm.initCfg input) t).inputPos : ℕ) ≤ 1 + t
    simpa [Cfg.init] using inputPos_runFrom_le tm (tm.initCfg input) t
  have h := computesTidily_seq_rewindInput_of_runPath (q := q.toRunPath)
    (q.head_eq.trans (Cfg.init_eq_wordsCfg _ _)) hl
  rw [hout] at h
  exact h.mono (by change t + _ ≤ _; omega) le_rfl

/-- A completed zero-work-tape run followed by the explicit input rewinder is tidy. -/
public theorem computesTidily_seq_explicitRewind_of_runPath {path : tm.RunPath input}
    (hhead : path.head = wordsCfg input (some tm.q₀) (fun _ => []) [])
    (hhalt : path.last.Halted) :
    (tm.seq (MultiTapeMachine.rewindInput Symbol).toTM).ComputesTidilyInTimeAndSpace
      input path.last.output (path.time + (path.last.inputPos.val - 1 + 2)) 0 := by
  let rewind := MultiTapeNTM.RunPath.ofDeterministic
    (MultiTapeMachine.rewindInput Symbol).toTM
    (path.last.withState (some (MultiTapeMachine.rewindInput Symbol).initial))
    (path.last.inputPos.val - 1 + 2)
  have hrewind : rewind.last = wordsCfg input none (fun _ => []) path.last.output :=
    (MultiTapeMachine.runFrom_rewindInput path.last.inputPos path.last.workTapes
      path.last.workTapePos path.last.output).trans (Cfg.ext_zero_tapes rfl rfl rfl)
  obtain ⟨combined, hcombinedHead, hcombinedLast, hcombinedTime, -⟩ :=
    exists_runPath_seq (p₁ := rewind) hhalt rfl
  exact computesTidily_iff.mpr ⟨combined, by rw [hcombinedHead, hhead]; rfl,
    by simp [hcombinedLast, hrewind], hcombinedTime,
    by simp [MultiTapeNTM.RunPath.space]⟩

/-- A zero-work-tape computation followed by the explicit-table input rewinder is tidy with the
same exact clock as the established relation-based wrapper. -/
public theorem ComputesInTimeAndSpace.computesTidily_seq_explicitRewind {output : List Symbol}
    {t s : ℕ} (h : ComputesInTimeAndSpace tm input output t s) :
    (tm.seq (MultiTapeMachine.rewindInput Symbol).toTM).ComputesTidilyInTimeAndSpace
      input output (2 * t + 2) 0 := by
  obtain ⟨⟨steps, hhalt, houtput⟩, htime, -⟩ := h
  let path := MultiTapeNTM.ComputationPath.ofDeterministic tm input t
  have hpathHalt : path.last.Halted := htime path le_rfl
  have hpathOutput : path.last.output = output := by
    change (tm.runFrom (tm.initCfg input) t).output = output
    rcases le_total steps t with hle | hle
    · rw [runFrom_eq_of_halt _ _ hle hhalt, houtput]
    · rw [← runFrom_eq_of_halt _ _ hle hpathHalt, houtput]
  have hposition : path.last.inputPos.val ≤ 1 + t := by
    change ((tm.runFrom (tm.initCfg input) t).inputPos : ℕ) ≤ 1 + t
    simpa [Cfg.init] using inputPos_runFrom_le tm (tm.initCfg input) t
  have htidy := computesTidily_seq_explicitRewind_of_runPath (path := path.toRunPath)
    (path.head_eq.trans (Cfg.init_eq_wordsCfg _ _)) hpathHalt
  rw [hpathOutput] at htidy
  exact htidy.mono (by change t + _ ≤ _; omega) le_rfl

end NoWorkTapes

/-! ### Zero space -/

/-! ### The identity -/

/-- The identity as an explicit transition table: copy the input, then rewind its head. -/
public def MultiTapeMachine.tidyCopy (Symbol : Type) :
    MultiTapeMachine 0 Symbol (Unit ⊕ RewindState) Empty Id :=
  (MultiTapeMachine.copyInput Symbol).seq (MultiTapeMachine.rewindInput Symbol)

/-- The identity as a tidy machine without work tapes: copy the input to the output, then move the
input head back to the start. -/
public noncomputable def tidyCopy (Symbol : Type*) : MultiTapeTM 0 Symbol (Unit ⊕ RewindState) :=
  copyInput.seq (rewindInput Symbol)

/-- `tidyCopy` computes the identity tidily, in time linear in the length of the word. -/
public theorem computesTidily_tidyCopy (w : List Symbol) :
    (tidyCopy Symbol).ComputesTidilyInTimeAndSpace w w (2 * w.length + 4) 0 :=
  (CopyInput.computesInTimeAndSpace w).computesTidily_seq_rewindInput.mono (by omega) le_rfl

/-- The retained explicit identity table has the same exact tidy computation certificate. -/
public theorem MultiTapeMachine.computesTidily_tidyCopy
    {Symbol : Type} (word : List Symbol) :
    (MultiTapeMachine.tidyCopy Symbol).toTM.ComputesTidilyInTimeAndSpace
      word word (2 * word.length + 4) 0 := by
  rw [MultiTapeMachine.tidyCopy, MultiTapeMachine.toTM_seq]
  have h := ComputesInTimeAndSpace.computesTidily_seq_explicitRewind
    (t := word.length + 1) (s := 0) (CopyInput.computesInTimeAndSpace word)
  simpa [MultiTapeTM.copyInput, Nat.mul_add, Nat.add_assoc] using h

end Turing.MultiTapeTM
