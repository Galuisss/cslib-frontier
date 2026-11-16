/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81
-- `transformsTapes_clearWork_only` and `ComputableTidilyInTimeAndSpace.comp_linear` are from
-- crei:crei/tidy-universal @7f7c0696 (unsubmitted).

public import Mathlib.Basic.Finite.Sum
public import Cslib.Foundations.Data.Fin.Tuple
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelFacts
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Sequential
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.InputFromTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.OutputToTape

/-! # The existing composition machine and its run theorem

The explicit-table constructors in `Turing.MultiTapeMachine` are the retained implementation.
Their direct run theorems establish the same exact semantics and resource bounds as the established
deterministic plumbing machines, without recovering a transition function from those opaque
machines. Higher computability-calculus theorems remain in the original facade.
-/

public section

namespace Turing.MultiTapeMachine

variable {k₁ k₂ : ℕ} {S₁ S₂ : Type}

section WorkCursor

variable {Symbol : Type*}

/-- The explicit transition table that moves a one-tape head to the word frontier. -/
def forwardWork (Symbol : Type*) : MultiTapeMachine 1 Symbol Unit Empty Id :=
  ofTr () fun _ _ work ↦
    match work 0 with
    | some _ => ⟨0, fun _ => (none, 1), none, some ()⟩
    | none => ⟨0, fun _ => (none, 0), none, none⟩

namespace ForwardWork

variable {input : List Symbol} {inpos : Fin (input.length + 2)} {out : List Symbol}

private theorem transition (inputSymbol : Option Symbol) (work : Fin 1 → Option Symbol) :
    (forwardWork Symbol).toTM.tr () inputSymbol work =
      match work 0 with
      | some _ => ⟨0, fun _ => (none, 1), none, some ()⟩
      | none => ⟨0, fun _ => (none, 0), none, none⟩ := by
  simp only [forwardWork, toTM, ofTr, MultiTapeTM.tr_ofTr]
  cases work 0 <;> rfl

private theorem runFrom_walk {w : List Symbol} {p : ℕ} (n : ℕ) (hn : p + n ≤ w.length) :
    (forwardWork Symbol).toTM.runFrom
        ⟨some (), inpos, fun _ => Turing.tapeOfList w, fun _ => (p : ℤ), out⟩ n =
      ⟨some (), inpos, fun _ => Turing.tapeOfList w, fun _ => (p : ℤ) + n, out⟩ := by
  induction n with
  | zero => simp [MultiTapeTM.runFrom]
  | succ n ih =>
    have hsym : Turing.tapeOfList w ((p : ℤ) + n) = some (w[p + n]'(by lia)) := by
      rw [← Nat.cast_add, Turing.tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by lia)
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
      ih (by lia), MultiTapeTM.step_of_state rfl]
    simp [transition, Turing.Action.apply, Cfg.workTapeSymbols, hsym, add_assoc]

end ForwardWork

/-- Exact run of the explicit frontier scanner. -/
theorem runFrom_forwardWork {input : List Symbol} (inpos : Fin (input.length + 2))
    (w : List Symbol) (out : List Symbol) {p n : ℕ} (hpn : p + n = w.length) :
    (forwardWork Symbol).toTM.runFrom
        ⟨some (forwardWork Symbol).initial, inpos, fun _ => Turing.tapeOfList w,
          fun _ => (p : ℤ), out⟩ (n + 1) =
      ⟨none, inpos, fun _ => Turing.tapeOfList w, fun _ => (w.length : ℤ), out⟩ := by
  rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
    ForwardWork.runFrom_walk _ hpn.le, show (p : ℤ) + n = w.length by lia,
    MultiTapeTM.step_of_state rfl]
  simp [ForwardWork.transition, Turing.Action.apply, Cfg.workTapeSymbols]

/-- Every prefix of the explicit frontier scan keeps its head between the start and frontier. -/
theorem workTapePos_runFrom_forwardWork {input : List Symbol}
    (inpos : Fin (input.length + 2)) (w : List Symbol) (out : List Symbol)
    {p : ℕ} (hp : p ≤ w.length) (steps : ℕ) :
    ((forwardWork Symbol).toTM.runFrom
      ⟨some (forwardWork Symbol).initial, inpos, fun _ => Turing.tapeOfList w,
        fun _ => (p : ℤ), out⟩ steps).workTapePos 0 ∈ Set.Icc (p : ℤ) w.length := by
  rcases Nat.lt_or_ge steps (w.length - p + 1) with hlt | hge
  · rw [ForwardWork.runFrom_walk steps (by lia)]
    simp only [Set.mem_Icc]
    constructor <;> lia
  · have hrun := runFrom_forwardWork (Symbol := Symbol) inpos w out (Nat.add_sub_cancel' hp)
    rw [(forwardWork Symbol).toTM.runFrom_eq_of_halt _ hge (by rw [hrun]), hrun]
    simp [hp]

/-- The explicit transition table that rewinds one work-tape head, optionally overwriting cells. -/
def rewindWork (Symbol : Type*) (write : Option (Option Symbol) := none) :
    MultiTapeMachine 1 Symbol MultiTapeTM.RewindWorkState Empty Id :=
  ofTr .start fun state _ work =>
    match state, work 0 with
    | .start, _ => ⟨0, fun _ => (none, -1), none, some .scan⟩
    | .scan, some _ => ⟨0, fun _ => (write, -1), none, some .scan⟩
    | .scan, none => ⟨0, fun _ => (none, 1), none, none⟩

namespace RewindWork

variable {input : List Symbol} {write : Option (Option Symbol)}
  {ip : Fin (input.length + 2)} {tape : ℤ → Option Symbol} {out : List Symbol} {p : ℤ}

private theorem transition (state : MultiTapeTM.RewindWorkState)
    (inputSymbol : Option Symbol) (work : Fin 1 → Option Symbol) :
    (rewindWork Symbol write).toTM.tr state inputSymbol work =
      match state, work 0 with
      | .start, _ => ⟨0, fun _ => (none, -1), none, some .scan⟩
      | .scan, some _ => ⟨0, fun _ => (write, -1), none, some .scan⟩
      | .scan, none => ⟨0, fun _ => (none, 1), none, none⟩ := by
  simp only [rewindWork, toTM, ofTr, MultiTapeTM.tr_ofTr]
  cases state <;> cases work 0 <;> rfl

private theorem step_start :
    (rewindWork Symbol write).toTM.step
        ⟨some .start, ip, fun _ => tape, fun _ => p, out⟩ =
      ⟨some .scan, ip, fun _ => tape, fun _ => p - 1, out⟩ := by
  rw [MultiTapeTM.step_of_state rfl, transition]
  simp [Turing.Action.apply, sub_eq_add_neg]

private theorem step_scan_some {symbol : Symbol} (hs : tape p = some symbol) :
    (rewindWork Symbol write).toTM.step
        ⟨some .scan, ip, fun _ => tape, fun _ => p, out⟩ =
      ⟨some .scan, ip, fun _ => write.elim tape (Function.update tape p),
        fun _ => p - 1, out⟩ := by
  rw [MultiTapeTM.step_of_state rfl, transition]
  cases write <;> simp [Turing.Action.apply, Cfg.workTapeSymbols, hs, sub_eq_add_neg]

private theorem step_scan_none (hs : tape p = none) :
    (rewindWork Symbol write).toTM.step
        ⟨some .scan, ip, fun _ => tape, fun _ => p, out⟩ =
      ⟨none, ip, fun _ => tape, fun _ => p + 1, out⟩ := by
  rw [MultiTapeTM.step_of_state rfl, transition]
  simp [Turing.Action.apply, Cfg.workTapeSymbols, hs]

private theorem runFrom_scan {w : List Symbol} (hw : tape = Turing.tapeOfList w)
    {l : ℕ} (hl : l ≤ w.length) (n : ℕ) (hn : n ≤ l) :
    (rewindWork Symbol write).toTM.runFrom
        ⟨some .scan, ip, fun _ => tape, fun _ => (l : ℤ) - 1, out⟩ n =
      ⟨some .scan, ip,
        fun _ z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (tape z) else tape z,
        fun _ => (l : ℤ) - 1 - n, out⟩ := by
  induction n with
  | zero => simp [MultiTapeTM.runFrom, show ∀ z : ℤ, ¬((l : ℤ) ≤ z ∧ z < l) by omega]
  | succ n ih =>
    have hsym : (fun z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (tape z) else tape z)
        ((l : ℤ) - 1 - n) = some (w[l - 1 - n]'(by omega)) := by
      dsimp only
      rw [ite_eq_right (by omega), hw,
        show (l : ℤ) - 1 - n = ((l - 1 - n : ℕ) : ℤ) by omega,
        Turing.tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by omega)
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
      ih (by omega), step_scan_some hsym]
    congr 2
    · cases write with
      | none => simp
      | some cell =>
        funext _ z
        simp only [Option.elim_some, Function.update_apply, Option.getD_some]
        split_ifs <;> first | rfl | omega
    · funext _
      omega

end RewindWork

/-- Exact run of the explicit work-tape rewinder. -/
theorem runFrom_rewindWork {input : List Symbol} (write : Option (Option Symbol))
    (ip : Fin (input.length + 2)) (tape : ℤ → Option Symbol) (out : List Symbol)
    {w : List Symbol} (hw : tape = Turing.tapeOfList w) {p : ℕ} (hp : p ≤ w.length) :
    (rewindWork Symbol write).toTM.runFrom
        ⟨some (rewindWork Symbol write).initial, ip, fun _ => tape, fun _ => (p : ℤ), out⟩
        (p + 2) =
      ⟨none, ip,
        fun _ z => if 0 ≤ z ∧ z < p then write.getD (tape z) else tape z,
        fun _ => 0, out⟩ := by
  rw [show (rewindWork Symbol write).initial = .start from rfl, MultiTapeTM.runFrom,
    Function.iterate_succ_apply, RewindWork.step_start, Function.iterate_succ_apply',
    ← MultiTapeTM.runFrom, RewindWork.runFrom_scan hw hp p le_rfl,
    show (p : ℤ) - 1 - p = -1 by omega,
    RewindWork.step_scan_none (by simp [hw, Turing.tapeOfList]; rfl)]
  simp

/-- Rewinding without writing preserves the tape contents. -/
theorem runFrom_rewindWork_none {input : List Symbol} (ip : Fin (input.length + 2))
    (tape : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol}
    (hw : tape = Turing.tapeOfList w) {p : ℕ} (hp : p ≤ w.length) :
    (rewindWork Symbol).toTM.runFrom
        ⟨some (rewindWork Symbol).initial, ip, fun _ => tape, fun _ => (p : ℤ), out⟩
        (p + 2) = ⟨none, ip, fun _ => tape, fun _ => 0, out⟩ := by
  simpa using runFrom_rewindWork (Symbol := Symbol) none ip tape out hw hp

/-- Rewinding from the frontier while erasing leaves the work tape blank. -/
theorem runFrom_rewindWork_erase {input : List Symbol} (ip : Fin (input.length + 2))
    (tape : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol}
    (hw : tape = Turing.tapeOfList w) :
    (rewindWork Symbol (some none)).toTM.runFrom
        ⟨some (rewindWork Symbol (some none)).initial, ip, fun _ => tape,
          fun _ => (w.length : ℤ), out⟩ (w.length + 2) =
      ⟨none, ip, fun _ _ => none, fun _ => 0, out⟩ := by
  rw [runFrom_rewindWork (Symbol := Symbol) _ ip tape out hw le_rfl]
  congr 2
  funext _ z
  split_ifs with h
  · rfl
  · rw [hw, Turing.tapeOfList_eq_none_iff]
    omega

/-- Every prefix of the explicit rewind stays between the blank before the word and its start. -/
theorem workTapePos_runFrom_rewindWork {input : List Symbol}
    (write : Option (Option Symbol)) (ip : Fin (input.length + 2))
    (tape : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol}
    (hw : tape = Turing.tapeOfList w) {p : ℕ} (hp : p ≤ w.length) (steps : ℕ) :
    ((rewindWork Symbol write).toTM.runFrom
      ⟨some (rewindWork Symbol write).initial, ip, fun _ => tape,
        fun _ => (p : ℤ), out⟩ steps).workTapePos 0 ∈ Set.Icc (-1) (p : ℤ) := by
  rcases steps with _ | steps
  · simp [MultiTapeTM.runFrom]
  rcases Nat.lt_or_ge steps (p + 1) with hlt | hge
  · rw [show (rewindWork Symbol write).initial = .start from rfl, MultiTapeTM.runFrom,
      Function.iterate_succ_apply, RewindWork.step_start, ← MultiTapeTM.runFrom,
      RewindWork.runFrom_scan hw hp steps (by omega)]
    simp only [Set.mem_Icc]
    constructor <;> omega
  · have hrun := runFrom_rewindWork (Symbol := Symbol) write ip tape out hw hp
    rw [(rewindWork Symbol write).toTM.runFrom_eq_of_halt _
      (by omega : p + 2 ≤ steps + 1) (by rw [hrun]), hrun]
    simp

end WorkCursor

variable {Symbol : Type}

/-- The explicit two-step table that writes immediately to the left of a work-tape head. -/
def markWork (Symbol : Type) (write : Option Symbol) :
    MultiTapeMachine 1 Symbol MultiTapeTM.MarkWorkState Empty Id :=
  ofTr .start fun state _ _ =>
    match state with
    | .start => ⟨0, fun _ => (none, -1), none, some .put⟩
    | .put => ⟨0, fun _ => (some write, 1), none, none⟩

private theorem markWork_transition (write : Option Symbol) (state : MultiTapeTM.MarkWorkState)
    (inputSymbol : Option Symbol) (work : Fin 1 → Option Symbol) :
    (markWork Symbol write).toTM.tr state inputSymbol work =
      match state with
      | .start => ⟨0, fun _ => (none, -1), none, some .put⟩
      | .put => ⟨0, fun _ => (some write, 1), none, none⟩ := by
  simp only [markWork, toTM, ofTr, MultiTapeTM.tr_ofTr]
  cases state <;> rfl

/-- The explicit marker writes the cell immediately left of its head in exactly two steps. -/
theorem runFrom_markWork {input : List Symbol} (write : Option Symbol)
    (ip : Fin (input.length + 2)) (tape : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) :
    (markWork Symbol write).toTM.runFrom
        ⟨some (markWork Symbol write).initial, ip, fun _ => tape, fun _ => p, out⟩ 2 =
      ⟨none, ip, fun _ => Function.update tape (p - 1) write, fun _ => p, out⟩ := by
  have hstart : (markWork Symbol write).toTM.step
      ⟨some .start, ip, fun _ => tape, fun _ => p, out⟩ =
      ⟨some .put, ip, fun _ => tape, fun _ => p - 1, out⟩ := by
    rw [MultiTapeTM.step_of_state rfl, markWork_transition]
    simp [Turing.Action.apply, sub_eq_add_neg]
  have hput : (markWork Symbol write).toTM.step
      ⟨some .put, ip, fun _ => tape, fun _ => p - 1, out⟩ =
      ⟨none, ip, fun _ => Function.update tape (p - 1) write, fun _ => p, out⟩ := by
    rw [MultiTapeTM.step_of_state rfl, markWork_transition]
    simp [Turing.Action.apply]
  change (markWork Symbol write).toTM.step
    ((markWork Symbol write).toTM.step
      ⟨some .start, ip, fun _ => tape, fun _ => p, out⟩) = _
  rw [hstart, hput]

/-- The explicit table that scans to the word frontier and erases while rewinding. -/
def clearWork (Symbol : Type) :
    MultiTapeMachine 1 Symbol (Unit ⊕ MultiTapeTM.RewindWorkState) Empty Id :=
  (forwardWork Symbol).seq (rewindWork Symbol (some none))

/-- The explicit clear table erases its work-tape word with the established exact clock and
independent workspace bound. -/
theorem transformsTapes_clearWork (word : List Symbol) :
    MultiTapeTM.TransformsTapes (clearWork Symbol).toTM
      (fun _ tapes => tapes 0 = word)
      (fun _ _ tapes' emitted => tapes' = (fun _ => []) ∧ emitted = [])
      (3 * (word.length + 1)) (word.length + 2) := by
  intro input tapes out htapes
  obtain rfl : tapes = fun _ => word := funext fun i => Fin.fin_one_eq_zero i ▸ htapes
  rw [clearWork, toTM_seq]
  let first := MultiTapeNTM.RunPath.ofDeterministic (forwardWork Symbol).toTM
    (Turing.wordsCfg input (some ()) (fun _ => word) out) (word.length + 1)
  let second := MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol (some none)).toTM
    (⟨some (rewindWork Symbol (some none)).initial, 1, fun _ => Turing.tapeOfList word,
      fun _ => word.length, out⟩ : Cfg 1 Symbol MultiTapeTM.RewindWorkState input)
    (word.length + 2)
  have hfirst : first.last = _ := runFrom_forwardWork (Symbol := Symbol) 1 word out (zero_add _)
  have hsecond : second.last = _ :=
    runFrom_rewindWork_erase (Symbol := Symbol) 1 (Turing.tapeOfList word) out rfl
  obtain ⟨path, hhead, hlast, htime, hvisited⟩ :=
    MultiTapeTM.exists_runPath_seq (p₀ := first) (p₁ := second) (by rw [hfirst])
      (by rw [hfirst]; rfl)
  refine ⟨fun _ => [], [], ⟨rfl, rfl⟩, path, hhead,
    by rw [hlast, hsecond]; simp [Cfg.mapState, Turing.wordsCfg],
    (show path.length ≤ word.length + 1 + (word.length + 2) from htime).trans (by lia), ?_⟩
  rw [MultiTapeNTM.RunPath.space, Fin.sum_univ_one]
  refine (Finset.card_le_card (t := .Icc (-1 : ℤ) word.length)
    ((hvisited 0).trans (Finset.union_subset ?_ ?_))).trans (by simp) <;>
    refine Finset.image_subset_iff.mpr fun steps _ => Finset.mem_Icc.2 ?_
  · exact Set.Icc_subset_Icc_left (by lia)
      (workTapePos_runFrom_forwardWork (Symbol := Symbol) (input := input)
        1 word out (Nat.zero_le word.length) steps)
  · exact workTapePos_runFrom_rewindWork (Symbol := Symbol) (some none) (input := input)
      1 (Turing.tapeOfList word) out rfl le_rfl steps

/-- Buffer output on a fresh work tape and rewind that tape to its first cell. -/
def outputToWord (machine : MultiTapeMachine k₁ Symbol S₁ Empty Id) :
    MultiTapeMachine (k₁ + 1) Symbol (S₁ ⊕ MultiTapeTM.RewindWorkState) Empty Id :=
  machine.outputToTape.seq
    ((rewindWork Symbol).extendTapes (MultiTapeTM.tapeEmb (Fin.last k₁)))

namespace OutputToWord

variable {k : ℕ} {State : Type} {input : List Symbol}

private theorem outCfg_wordsCfg (state : Option State) :
    MultiTapeTM.outCfg (Turing.wordsCfg input state (fun _ : Fin k => []) []) =
      Turing.wordsCfg input state (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext tape <;>
    induction tape using Fin.lastCases <;>
    simp [MultiTapeTM.outCfg, Turing.wordsCfg]

private theorem oneTapeCfg_outCfg_wordsCfg (state : Option State)
    (tapes : Fin k → List Symbol) (out : List Symbol) :
    MultiTapeTM.oneTapeCfg (Fin.last k)
        (MultiTapeTM.outCfg (Turing.wordsCfg input state tapes out)) =
      ⟨state, 1, fun _ => Turing.tapeOfList out, fun _ => (out.length : ℤ), []⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;>
    simp [MultiTapeTM.oneTapeCfg]

private theorem exists_runPath_rewindLast (out : List Symbol) :
    ∃ path : ((rewindWork Symbol).toTM.extendTapes
        (MultiTapeTM.tapeEmb (Fin.last k))).RunPath input,
      path.head = MultiTapeTM.outCfg
        (Turing.wordsCfg input (some (rewindWork Symbol).initial) (fun _ : Fin k => []) out) ∧
      path.last = Turing.wordsCfg input none
        (Function.update (fun _ => []) (Fin.last k) out) [] ∧
      path.time = out.length + 2 ∧ path.space ≤ out.length + k + 3 := by
  let cfg := MultiTapeTM.outCfg
    (Turing.wordsCfg input (some (rewindWork Symbol).initial) (fun _ : Fin k => []) out)
  let run := MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol).toTM
    (MultiTapeTM.oneTapeCfg (Fin.last k) cfg) (out.length + 2)
  refine ⟨run.map (MultiTapeTM.embedHom _ (MultiTapeTM.tapeEmb (Fin.last k))
      cfg.workTapes cfg.workTapePos), MultiTapeTM.embed_oneTapeCfg _ cfg, ?_, rfl, ?_⟩
  · change MultiTapeTM.embed _
      ((rewindWork Symbol).toTM.runFrom (MultiTapeTM.oneTapeCfg _ cfg) (out.length + 2)) _ _ = _
    rw [oneTapeCfg_outCfg_wordsCfg, runFrom_rewindWork_none (Symbol := Symbol)
      _ _ _ rfl le_rfl, MultiTapeTM.embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext tape <;>
      induction tape using Fin.lastCases <;> simp [cfg, Turing.wordsCfg]
  · have hspace : run.space ≤ 1 * (out.length + 2 + 1) :=
      run.space_le_mul_time_add_one
    exact (MultiTapeTM.space_map_embedHom_le ..).trans (by omega)

end OutputToWord

/-- An explicit tidy computation writes its output to a fresh tape and rewinds the write head,
with the established exact clock and workspace formula. -/
theorem computesTidilyInTimeAndSpace_outputToWord
    {machine : MultiTapeMachine k₁ Symbol S₁ Empty Id}
    {input output : List Symbol} {time space : ℕ}
    (h : machine.toTM.ComputesTidilyInTimeAndSpace input output time space) :
    MultiTapeTM.TransformsTapes machine.outputToWord.toTM
      (fun word tapes => word = input ∧ tapes = fun _ => [])
      (fun _ _ tapes' emitted =>
        tapes' = Function.update (fun _ => []) (Fin.last k₁) output ∧ emitted = [])
      (time + output.length + 2) (space + 2 * output.length + k₁ + 4) := by
  obtain ⟨path, hhead, hlast, htime, hspace⟩ := MultiTapeTM.computesTidily_iff.mp h
  rw [outputToWord, toTM_seq, toTM_extendTapes, toTM_outputToTape]
  rw [MultiTapeTM.transformsTapes_iff_nil_output]
  rintro actual _ ⟨hactual, rfl⟩
  subst actual
  let first := path.map (MultiTapeTM.outCfgHom machine.toTM)
  have hfirstLast : first.last = MultiTapeTM.outCfg
      (Turing.wordsCfg input none (fun _ => []) output) := by simp [first, hlast]
  have hfirstSpace : first.space ≤ path.space + (output.length + 1) := by
    simpa [hlast] using MultiTapeTM.space_map_outCfgHom_le machine.toTM path
  obtain ⟨second, hsecondHead, hsecondLast, hsecondTime, hsecondSpace⟩ :=
    OutputToWord.exists_runPath_rewindLast (k := k₁) (input := input) output
  obtain ⟨combined, hcombinedHead, hcombinedLast, hcombinedTime, hcombinedSpace⟩ :=
    MultiTapeTM.exists_runPath_seq_space_le (p₀ := first) (p₁ := second)
      (by rw [hfirstLast]; rfl) (by rw [hsecondHead, hfirstLast]; rfl)
  refine ⟨_, [], ⟨rfl, rfl⟩, combined, ?_, by simp [hcombinedLast, hsecondLast], ?_, by omega⟩
  · simp only [hcombinedHead, first, RelSeries.head_map, MultiTapeTM.outCfgHom_apply,
      hhead, OutputToWord.outCfg_wordsCfg]
    rfl
  · simp only [MultiTapeNTM.RunPath.time] at htime hsecondTime ⊢
    have : first.length = path.length := rfl
    omega

/-- Place the explicit marker on the flag tape used by virtual-input execution. -/
private def markFlag (k : ℕ) (write : Option Symbol) :
    MultiTapeMachine (k + 2) Symbol MultiTapeTM.MarkWorkState Empty Id :=
  (markWork Symbol write).extendTapes
    (MultiTapeTM.tapeEmb (Fin.natAdd k 1))

/-- Run an explicit machine on a work-tape word, setting and then erasing the boundary flag. -/
def inputFromWord (machine : MultiTapeMachine k₂ Symbol S₂ Empty Id) (mark : Symbol) :
    MultiTapeMachine (k₂ + 2) Symbol
      (MultiTapeTM.MarkWorkState ⊕ S₂ ⊕ MultiTapeTM.MarkWorkState) Empty Id :=
  (markFlag k₂ (some mark)).seq
    (machine.inputFromTape.seq (markFlag k₂ none))

namespace InputFromWord

variable {k : ℕ} {State : Type} {input : List Symbol}

private theorem oneTapeCfg_flag (write : Option Symbol) (tapes : Fin k → ℤ → Option Symbol)
    (virtualInput flag : ℤ → Option Symbol) (out : List Symbol)
    (inputPos : Fin (input.length + 2)) :
    MultiTapeTM.oneTapeCfg (Fin.natAdd k 1)
        (⟨some (markWork Symbol write).initial, inputPos,
          Fin.append tapes ![virtualInput, flag], fun _ => 0, out⟩ :
          Cfg (k + 2) Symbol MultiTapeTM.MarkWorkState input) =
      ⟨some (markWork Symbol write).initial, inputPos, fun _ => flag, fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;>
    simp [MultiTapeTM.oneTapeCfg, Fin.append_right]

private theorem exists_runPath_markFlag (write : Option Symbol)
    (tapes : Fin k → ℤ → Option Symbol) (virtualInput flag : ℤ → Option Symbol)
    (out : List Symbol) (inputPos : Fin (input.length + 2)) :
    ∃ path : (markFlag (Symbol := Symbol) k write).toTM.RunPath input,
      path.head = ⟨some (markFlag (Symbol := Symbol) k write).initial, inputPos,
        Fin.append tapes ![virtualInput, flag], fun _ => 0, out⟩ ∧
      path.last = ⟨none, inputPos,
        Fin.append tapes ![virtualInput, Function.update flag (-1) write], fun _ => 0, out⟩ ∧
      path.time = 2 ∧ path.space ≤ k + 4 := by
  let cfg : Cfg (k + 2) Symbol MultiTapeTM.MarkWorkState input :=
    ⟨some (markWork Symbol write).initial, inputPos,
      Fin.append tapes ![virtualInput, flag], fun _ => 0, out⟩
  let run := MultiTapeNTM.RunPath.ofDeterministic (markWork Symbol write).toTM
    (MultiTapeTM.oneTapeCfg (Fin.natAdd k 1) cfg) 2
  rw [markFlag, toTM_extendTapes]
  refine ⟨run.map (MultiTapeTM.embedHom _ (MultiTapeTM.tapeEmb (Fin.natAdd k 1))
      cfg.workTapes cfg.workTapePos), MultiTapeTM.embed_oneTapeCfg _ cfg, ?_, rfl, ?_⟩
  · change MultiTapeTM.embed _
      ((markWork Symbol write).toTM.runFrom (MultiTapeTM.oneTapeCfg _ cfg) 2) _ _ = _
    rw [oneTapeCfg_flag, runFrom_markWork (Symbol := Symbol), MultiTapeTM.embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · simpa [cfg] using MultiTapeTM.update_append_flag tapes virtualInput flag
        (Function.update flag (-1) write)
    · funext tape
      simp [cfg, Function.update_apply]
  · have hspace : run.space ≤ 1 * (2 + 1) := run.space_le_mul_time_add_one
    exact (MultiTapeTM.space_map_embedHom_le ..).trans (by omega)

private theorem wordsCfg_append_words {State' : Type} {outer : List Symbol}
    (state : Option State') (tapes : Fin k → List Symbol) (word out : List Symbol) :
    Turing.wordsCfg outer state (Fin.append tapes ![word, []]) out =
      ⟨state, 1, Fin.append (fun tape => Turing.tapeOfList (tapes tape))
        ![Turing.tapeOfList word, fun _ => none], fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl
    ((Fin.comp_append Turing.tapeOfList tapes ![word, []]).trans
      (congrArg _ (funext fun i => ?_))) rfl rfl
  match i with
  | 0 | 1 => simp

private theorem exists_runPath_setFlag (mark : Symbol) (tapes : Fin k → List Symbol)
    (word out outer : List Symbol) :
    ∃ path : (markFlag (Symbol := Symbol) k (some mark)).toTM.RunPath outer,
      path.head = Turing.wordsCfg outer
        (some (markFlag (Symbol := Symbol) k (some mark)).initial)
        (Fin.append tapes ![word, []]) out ∧
      path.last = MultiTapeTM.inCfg mark
        (Turing.wordsCfg word (none : Option MultiTapeTM.MarkWorkState) tapes out) outer ∧
      path.time = 2 ∧ path.space ≤ k + 4 := by
  rw [wordsCfg_append_words, MultiTapeTM.inCfg_wordsCfg]
  exact exists_runPath_markFlag _ _ _ _ _ _

private theorem exists_runPath_eraseFlag (mark : Symbol) (tapes : Fin k → List Symbol)
    (word out outer : List Symbol) :
    ∃ path : (markFlag (Symbol := Symbol) k none).toTM.RunPath outer,
      path.head = (MultiTapeTM.inCfg mark
        (Turing.wordsCfg word (none : Option State) tapes out) outer).withState
          (some (markFlag (Symbol := Symbol) k none).initial) ∧
      path.last = Turing.wordsCfg outer none (Fin.append tapes ![word, []]) out ∧
      path.time = 2 ∧ path.space ≤ k + 4 := by
  obtain ⟨path, hhead, hlast, htime, hspace⟩ := exists_runPath_markFlag
    (Symbol := Symbol) none (fun tape => Turing.tapeOfList (tapes tape))
    (Turing.tapeOfList word) (Function.update (fun _ => none) (-1) (some mark)) out
    (1 : Fin (outer.length + 2))
  refine ⟨path, by rw [hhead, MultiTapeTM.inCfg_wordsCfg]; rfl, ?_, htime, hspace⟩
  rw [hlast, wordsCfg_append_words, Function.update_idem]
  simp

end InputFromWord

/-- Exact tape transformation of the explicit virtual-input wrapper. -/
theorem transformsTapes_inputFromWord (mark : Symbol)
    {machine : MultiTapeMachine k₂ Symbol S₂ Empty Id} {word emitted : List Symbol}
    {tapes₀ tapes₁ : Fin k₂ → List Symbol} {time space : ℕ}
    (hMachine : ∃ path : machine.toTM.RunPath word,
      path.head = Turing.wordsCfg word (some machine.initial) tapes₀ [] ∧
      path.last = Turing.wordsCfg word none tapes₁ emitted ∧
      path.time ≤ time ∧ path.space ≤ space) :
    MultiTapeTM.TransformsTapes (machine.inputFromWord mark).toTM
      (fun _ tapes => tapes = Fin.append tapes₀ ![word, []])
      (fun _ _ tapes' out => tapes' = Fin.append tapes₁ ![word, []] ∧ out = emitted)
      (time + 4) (space + 2 * word.length + 2 * k₂ + 12) := by
  obtain ⟨machinePath, hMachineHead, hMachineLast, hMachineTime, hMachineSpace⟩ := hMachine
  rw [inputFromWord, toTM_seq, toTM_seq, toTM_inputFromTape]
  rw [MultiTapeTM.transformsTapes_iff_nil_output]
  rintro outer _ rfl
  obtain ⟨setFlag, hSetHead, hSetLast, hSetTime, hSetSpace⟩ :=
    InputFromWord.exists_runPath_setFlag (Symbol := Symbol) mark tapes₀ word [] outer
  let virtualRun := machinePath.map (MultiTapeTM.inCfgHom machine.toTM mark outer)
  have hVirtualLast : virtualRun.last =
      MultiTapeTM.inCfg mark (Turing.wordsCfg word none tapes₁ emitted) outer := by
    simp [virtualRun, hMachineLast]
  have hVirtualSpace : virtualRun.space ≤ machinePath.space + 2 * (word.length + 2) :=
    MultiTapeTM.space_map_inCfgHom_le machine.toTM mark outer machinePath
  obtain ⟨eraseFlag, hEraseHead, hEraseLast, hEraseTime, hEraseSpace⟩ :=
    InputFromWord.exists_runPath_eraseFlag (State := S₂) mark tapes₁ word emitted outer
  obtain ⟨tail, hTailHead, hTailLast, hTailTime, hTailSpace⟩ :=
    MultiTapeTM.exists_runPath_seq_space_le (p₀ := virtualRun) (p₁ := eraseFlag)
      (by rw [hVirtualLast]; rfl) (by rw [hEraseHead, hVirtualLast]; rfl)
  obtain ⟨combined, hCombinedHead, hCombinedLast, hCombinedTime, hCombinedSpace⟩ :=
    MultiTapeTM.exists_runPath_seq_space_le (p₀ := setFlag) (p₁ := tail)
      (by rw [hSetLast]; rfl)
      (by simp [hTailHead, virtualRun, hMachineHead, hSetLast]; rfl)
  refine ⟨_, emitted, ⟨rfl, rfl⟩, combined,
    by rw [hCombinedHead, hSetHead]; rfl,
    by simp [hCombinedLast, hTailLast, hEraseLast], ?_, ?_⟩
  · simp only [MultiTapeNTM.RunPath.time] at hMachineTime hSetTime hEraseTime ⊢
    have : virtualRun.length = machinePath.length := rfl
    omega
  · omega

/-- Run a tidy explicit table on a selected input tape, preserving that tape and emitting the
table's output. -/
theorem transformsTapes_inputFromWord_extendTapes (mark : Symbol)
    {machine : MultiTapeMachine k₂ Symbol S₂ Empty Id}
    {input output : List Symbol} {time space K : ℕ}
    (h : machine.toTM.ComputesTidilyInTimeAndSpace input output time space)
    {embedding : Fin (k₂ + 2) ↪ Fin K} {value : Fin K}
    (hvalue : embedding (Fin.natAdd k₂ 0) = value) :
    MultiTapeTM.TransformsTapes ((machine.inputFromWord mark).extendTapes embedding).toTM
      (fun _ tapes => tapes = Function.update (fun _ => []) value input)
      (fun _ tapes tapes' emitted => tapes' = tapes ∧ emitted = output)
      (time + 4)
      (space + 2 * (input.length + 2) + 2 * k₂ + 8 + (K - (k₂ + 2))) := by
  have hbase : MultiTapeTM.TransformsTapes (machine.inputFromWord mark).toTM
      (fun _ tapes => True ∧
        tapes = Function.update (fun _ => []) (Fin.natAdd k₂ 0) input)
      (fun _ tapes tapes' emitted =>
        tapes' = Function.update tapes (Fin.natAdd k₂ 0) input ∧ emitted = output)
      (time + 4) (space + 2 * (input.length + 2) + 2 * k₂ + 8) := by
    refine (transformsTapes_inputFromWord mark
      (MultiTapeTM.computesTidily_iff.mp h)).imp
      (fun _ tapes htapes => by rw [htapes.2, MultiTapeTM.append_nil_eq_update])
      (fun _ tapes tapes' _ htapes ⟨htapes', hemitted⟩ => ⟨?_, hemitted⟩)
      le_rfl (by omega)
    rw [htapes', htapes.2, MultiTapeTM.append_nil_eq_update, Function.update_idem]
  have hselected := hbase.extendTapes_update embedding
  rw [hvalue] at hselected
  rw [toTM_extendTapes]
  exact hselected.imp
    (P' := fun _ tapes => tapes = Function.update (fun _ => []) value input)
    (Q' := fun _ tapes tapes' emitted => tapes' = tapes ∧ emitted = output)
    (fun _ _ htapes => ⟨trivial, htapes⟩)
    (fun _ _ _ _ htapes ⟨htapes', hemitted⟩ =>
      ⟨by rw [htapes', htapes, Function.update_idem], hemitted⟩) le_rfl le_rfl

/-- Choice-free retained composition of two explicit transition tables. Its control and tape
layout are the established tidy composition layout. -/
def comp (outer : MultiTapeMachine k₂ Symbol S₂ Empty Id)
    (inner : MultiTapeMachine k₁ Symbol S₁ Empty Id) (mark : Symbol) :
    MultiTapeMachine (max k₁ k₂ + 2) Symbol
      ((S₁ ⊕ MultiTapeTM.RewindWorkState) ⊕
        (MultiTapeTM.MarkWorkState ⊕ S₂ ⊕ MultiTapeTM.MarkWorkState) ⊕
          Unit ⊕ MultiTapeTM.RewindWorkState) Empty Id :=
  ((inner.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).seq
    (((outer.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
      ((clearWork Symbol).extendTapes
        (MultiTapeTM.tapeEmb (Fin.natAdd (max k₁ k₂) 0))))

private theorem transformsTapes_clearWork_only {k : ℕ} (tape : Fin k)
    (word : List Symbol) :
    MultiTapeTM.TransformsTapes
      ((clearWork Symbol).extendTapes (MultiTapeTM.tapeEmb tape)).toTM
      (fun _ tapes => tapes = Function.update (fun _ => []) tape word)
      (fun _ _ tapes' emitted => tapes' = (fun _ => []) ∧ emitted = [])
      (3 * (word.length + 1)) (word.length + 1 + k) := by
  rw [toTM_extendTapes]
  exact ((transformsTapes_clearWork (Symbol := Symbol) word).tapeEmb tape).imp
    (fun _ _ htapes => by rw [htapes, Function.update_self])
    (fun _ tapes tapes' _ htapes ⟨value, ⟨hvalue, hemitted⟩, htapes'⟩ =>
      ⟨by rw [htapes', hvalue, htapes, Function.update_idem]; simp, hemitted⟩)
    le_rfl (by have := tape.pos; lia)

/-- Complete semantic and exact-resource certificate for the choice-free composition table. -/
theorem computesTidilyInTimeAndSpace_comp
    {outer : MultiTapeMachine k₂ Symbol S₂ Empty Id}
    {inner : MultiTapeMachine k₁ Symbol S₁ Empty Id}
    {input intermediate output : List Symbol} {time₁ space₁ time₂ space₂ : ℕ}
    (h₁ : inner.toTM.ComputesTidilyInTimeAndSpace
      input intermediate time₁ space₁)
    (h₂ : outer.toTM.ComputesTidilyInTimeAndSpace
      intermediate output time₂ space₂) (mark : Symbol) :
    (outer.comp inner mark).toTM.ComputesTidilyInTimeAndSpace input output
      (time₁ + time₂ + 4 * intermediate.length + 9)
      (space₁ + space₂ + 5 * intermediate.length + (6 * max k₁ k₂ + 20)) := by
  set tapeCount := max k₁ k₂
  set buffer : Fin (tapeCount + 2) := Fin.natAdd tapeCount 0
  have hbuffer : Fin.append (fun _ : Fin tapeCount => ([] : List Symbol)) ![intermediate, []] =
      Function.update (fun _ => []) buffer intermediate := by
    funext tape
    cases tape using Fin.addCases with
    | left source =>
        simp [buffer, Function.update_of_ne (Fin.castAdd_ne_natAdd source 0)]
    | right extra => match extra with | 0 | 1 => simp [buffer]
  have hphase₁Shape (tapes' : Fin (tapeCount + 1 + 1) → List Symbol)
      (hselected : (fun tape => tapes' (Fin.castSuccEmb tape)) =
        Function.update (fun _ => []) (Fin.last tapeCount) intermediate)
      (hextra : ∀ tape ∉ Set.range Fin.castSuccEmb, tapes' tape = []) :
      tapes' = Function.update (fun _ => []) buffer intermediate := by
    funext tape
    induction tape using Fin.lastCases with
    | last =>
        rw [hextra _ fun ⟨source, hsource⟩ => Fin.castSucc_ne_last source hsource]
        simp [buffer, Fin.ext_iff]
    | cast source =>
        rw [show tapes' source.castSucc = _ from congrFun hselected source]
        simp [buffer, Function.update_apply, Fin.ext_iff]
  have h₁Extended :
      (inner.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).toTM
        |>.ComputesTidilyInTimeAndSpace input intermediate time₁
          (space₁ + (max k₁ k₂ - k₁)) := by
    rw [toTM_extendTapes]
    exact h₁.extendTapes _
  have hphase₁Raw :=
    (computesTidilyInTimeAndSpace_outputToWord h₁Extended).extendTapes Fin.castSuccEmb
  have hphase₁Machine : MultiTapeTM.TransformsTapes
      (((inner.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
        Fin.castSuccEmb).toTM)
      (fun word tapes => word = input ∧ tapes = fun _ => [])
      (fun _ _ tapes' emitted =>
        tapes' = Function.update (fun _ => []) buffer intermediate ∧ emitted = [])
      (time₁ + intermediate.length + 2)
      (space₁ + (max k₁ k₂ - k₁) + 2 * intermediate.length +
        max k₁ k₂ + 4 + ((max k₁ k₂ + 2) - (max k₁ k₂ + 1))) := by
    rw [toTM_extendTapes]
    exact hphase₁Raw.imp (P' := fun word tapes => word = input ∧ tapes = fun _ => [])
      (Q' := fun _ _ tapes' emitted =>
        tapes' = Function.update (fun _ => []) buffer intermediate ∧ emitted = [])
      (fun _ _ ⟨hinput, htapes⟩ => ⟨hinput, by simp [htapes]⟩)
      (fun _ _ tapes' _ ⟨_, htapes⟩ ⟨⟨hselected, hemitted⟩, hextra⟩ =>
        ⟨hphase₁Shape tapes' hselected fun tape htape =>
          (hextra tape htape).trans (congrFun htapes tape), hemitted⟩)
      le_rfl le_rfl
  have h₂Extended :
      (outer.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).toTM
        |>.ComputesTidilyInTimeAndSpace intermediate output time₂
          (space₂ + (max k₁ k₂ - k₂)) := by
    rw [toTM_extendTapes]
    exact h₂.extendTapes _
  have hphase₂ := (transformsTapes_inputFromWord mark
      (MultiTapeTM.computesTidily_iff.mp h₂Extended)).imp
    (P' := fun _ tapes => tapes = Function.update (fun _ => []) buffer intermediate)
    (Q' := fun _ _ tapes' emitted =>
      tapes' = Function.update (fun _ => []) buffer intermediate ∧ emitted = output)
    (fun _ _ htapes => htapes.trans hbuffer.symm)
    (fun _ _ _ _ _ ⟨htapes', hemitted⟩ => ⟨htapes'.trans hbuffer, hemitted⟩)
    le_rfl le_rfl
  have hphase₃ := transformsTapes_clearWork_only (Symbol := Symbol) buffer intermediate
  rw [comp, toTM_seq, toTM_seq]
  refine (MultiTapeTM.transformsTapes_seq hphase₁Machine
    (MultiTapeTM.transformsTapes_seq hphase₂ hphase₃
      fun _ _ _ _ _ hpost => hpost.1)
    fun _ _ _ _ _ hpost => hpost.1).imp (fun _ _ h => h) ?_ (by omega) (by omega)
  rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨_, _, _, ⟨-, rfl⟩,
    ⟨htapes, rfl⟩, rfl⟩, rfl⟩
  exact ⟨htapes, by simp⟩

end Turing.MultiTapeMachine

end

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol S₁ S₂ : Type*}

/-- `tm₂` after `tm₁`, both with their work tapes padded to `max k₁ k₂`: run `tm₁` with its output
written to the work tape `Fin.natAdd (max k₁ k₂) 0`, run `tm₂` reading its input from that tape
(using `mark` on the last work tape to flag the left end of the input), then clear that tape. -/
public noncomputable def comp (tm₂ : MultiTapeTM k₂ Symbol S₂) (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (mark : Symbol) : MultiTapeTM (max k₁ k₂ + 2) Symbol
      ((S₁ ⊕ RewindWorkState) ⊕ (MarkWorkState ⊕ S₂ ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState) :=
  ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).seq
    (((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
      ((clearWork Symbol).extendTapes (tapeEmb (Fin.natAdd (max k₁ k₂) 0))))

/-- Clearing the only non-blank work tape leaves all work tapes blank. -/
public theorem transformsTapes_clearWork_only {k : ℕ} (i : Fin k) (w : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb i))
      (fun _ ws => ws = Function.update (fun _ => []) i w)
      (fun _ _ ws' e => ws' = (fun _ => []) ∧ e = []) (3 * (w.length + 1)) (w.length + 1 + k) :=
  (transformsTapes_clearWork_tapeEmb i w).imp (fun _ _ hws => by rw [hws, Function.update_self])
    (fun _ _ _ _ hws ⟨hws', he⟩ => ⟨by simp [hws', hws], he⟩) le_rfl le_rfl

/-- If `tm₁` computes `w` from `x` tidily and `tm₂` computes `y` from `w` tidily, then
`tm₂.comp tm₁ mark` computes `y` from `x` tidily. -/
public theorem ComputesTidilyInTimeAndSpace.comp {tm₁ : MultiTapeTM k₁ Symbol S₁}
    {tm₂ : MultiTapeTM k₂ Symbol S₂} {x w y : List Symbol} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x w t₁ s₁)
    (h₂ : tm₂.ComputesTidilyInTimeAndSpace w y t₂ s₂) (mark : Symbol) :
    (tm₂.comp tm₁ mark).ComputesTidilyInTimeAndSpace x y (t₁ + t₂ + 4 * w.length + 9)
      (s₁ + s₂ + 5 * w.length + (6 * max k₁ k₂ + 20)) := by
  set K := max k₁ k₂
  -- the work tape holding the intermediate word `w`
  set A : Fin (K + 2) := Fin.natAdd K 0
  have hA : Fin.append (fun _ : Fin K => ([] : List Symbol)) ![w, []] =
      Function.update (fun _ => []) A w := by
    funext l
    cases l using Fin.addCases with
    | left j => simp [A, Function.update_of_ne (Fin.castAdd_ne_natAdd j 0)]
    | right i => match i with | 0 | 1 => simp [A]
  -- phase 1: `tm₁` writes `w` to `A`
  have hQ₁ (ws' : Fin (K + 1 + 1) → List Symbol)
      (hv : (fun j => ws' (Fin.castSuccEmb j)) = Function.update (fun _ => []) (Fin.last K) w)
      (hx : ∀ l ∉ Set.range Fin.castSuccEmb, ws' l = []) :
      ws' = Function.update (fun _ => []) A w := by
    funext l
    induction l using Fin.lastCases with
    | last =>
      rw [hx _ fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj]
      simp [A, Fin.ext_iff]
    | cast j =>
      rw [show ws' j.castSucc = _ from congrFun hv j]
      simp [A, Function.update_apply, Fin.ext_iff]
  have hp₁ := ((h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
    Fin.castSuccEmb).imp (P' := fun inp ws => inp = x ∧ ws = fun _ => [])
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) A w ∧ e = [])
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
    (fun _ _ ws' _ ⟨_, hws⟩ ⟨⟨hv, he⟩, hx⟩ => ⟨hQ₁ ws' hv fun l hl => (hx l hl).trans
      (congrFun hws l), he⟩) le_rfl le_rfl
  -- phase 2: `tm₂` reads `w` from `A` and emits `y`
  have hp₂ := (transformsTapes_inputFromWord mark
      (computesTidily_iff.mp (h₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))))).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) A w)
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) A w ∧ e = y)
    (fun _ _ hws => hws.trans hA.symm) (fun _ _ _ _ _ ⟨hws', he⟩ => ⟨hws'.trans hA, he⟩)
    le_rfl le_rfl
  -- phase 3: clear `A`
  have hclear : Function.update (Function.update (fun _ => []) A w) A [] = fun _ => [] := by grind
  have hp₃ := (transformsTapes_clearWork_tapeEmb (Symbol := Symbol) A w).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) A w)
    (Q' := fun _ _ ws' e => ws' = (fun _ => []) ∧ e = [])
    (fun _ _ hws => by rw [hws, Function.update_self])
    (fun _ _ _ _ hws ⟨hws', he⟩ => ⟨by rw [hws', hws, hclear], he⟩) le_rfl le_rfl
  refine (transformsTapes_seq hp₁ (transformsTapes_seq hp₂ hp₃ fun _ _ _ _ _ hQ => hQ.1)
    fun _ _ _ _ _ hQ => hQ.1).imp (fun _ _ h => h) ?_ (by omega) (by omega)
  rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩, rfl⟩
  exact ⟨hws, by simp⟩

end Turing.MultiTapeTM
