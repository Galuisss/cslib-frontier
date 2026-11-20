/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting

/-!
# Counting view of the native query loop

The relation-based query-loop compiler samples a bit to specify one of two
transitions. Both values select the same instruction outside a choice state.
For counting, a deterministic step has one occurrence, and a choice boundary
has one occurrence for each bit.

## Main definitions

* `Turing.NondeterministicQueryMachine.Native.countingMachine`: the occurrence-sensitive
  machine with branching only at choice boundaries.
* `Turing.NondeterministicQueryMachine.Native.replayChoices`: replay occurrences and record
  the genuine binary choices.

## Main results

* `Turing.NondeterministicQueryMachine.Native.toNTM_countingMachine`: forgetting occurrence
  labels recovers the original machine and its space bounds.
* `Turing.NondeterministicQueryMachine.Native.eq_occurrences_of_replayChoices`: a first-halting
  branch is determined by the bit sequence at its choice boundaries.
* `Turing.NondeterministicQueryMachine.Native.countingMachine_haltsWithin`: the original
  time bound applies to counted runs.
* `Turing.NondeterministicQueryMachine.Native.branchCount_le_one_of_choiceTrace`: a verdict
  with a unique bit sequence has at most one counted branch.
-/

public section

namespace Turing.NondeterministicQueryMachine.Native

variable {k : ℕ} {SI SF : Type} {SP : Bool → Type}
  (I : MultiTapeTM k Bool SI) (P : (b : Bool) → MultiTapeTM k Bool (SP b))
  (F : MultiTapeTM k Bool SF) (C : Fin k)

private def choiceBits : State SI SP SF → List Bool
  | .choose => [false, true]
  | _ => [false]

/-- Use one transition occurrence per bit at a choice boundary and one occurrence everywhere
else. This preserves deterministic routines when counting branches. -/
noncomputable def countingMachine : MultiTapeCTM k Bool (State SI SP SF) where
  initial := .init I.q₀
  tr q input work _ :=
    (choiceBits q).map fun b =>
      MultiTapeMachine.Action.emptyOracleEquiv.symm (instruction I P F C q input work b)

/-- The counting presentation is nonblocking, even outside the compiler's state invariants. -/
theorem countingMachine_nonblocking : (countingMachine I P F C).Nonblocking := by
  intro q input work
  cases q <;> simp [countingMachine, choiceBits]

/-- Forgetting the occurrence labels recovers the native compiler's reachability relation. -/
theorem toNTM_countingMachine : (countingMachine I P F C).toNTM = machine I P F C := by
  have h (q : State SI SP SF) (input : Option Bool) (work : Fin k → Option Bool)
      (act : Turing.Action k Bool (State SI SP SF)) :
      (countingMachine I P F C).toNTM.Tr q input work act ↔
        (machine I P F C).Tr q input work act := by
    rw [machine, MultiTapePTM.tr_toNTM_iff]
    simp only [MultiTapeCTM.toNTM, countingMachine, List.mem_map,
      Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    cases q <;> simp [choiceBits, tr_withCoin, instruction]
  change MultiTapeNTM.mk _ _ = MultiTapeNTM.mk _ _
  congr 1
  funext q input work act
  exact propext (h q input work act)

/-- A bound on the native computation paths is also a clock for the counting presentation. -/
theorem countingMachine_haltsWithin {input : List Bool} {fuel : ℕ}
    (h : (machine I P F C).RunsInTime input fuel) :
    (countingMachine I P F C).HaltsWithin fuel
      (Cfg.init (.init I.q₀) input) := by
  apply MultiTapeCTM.haltsWithin_of_paths (countingMachine_nonblocking I P F C)
  rw [toNTM_countingMachine]
  intro p hp hlen
  exact h ⟨p, hp⟩ hlen

private def atChoice {input : List Bool} (cfg : Cfg k Bool (State SI SP SF) input) : Bool :=
  match cfg.state with
  | some .choose => true
  | _ => false

private theorem step_index_lt {input : List Bool}
    {cfg next : Cfg k Bool (State SI SP SF) input} {i : ℕ}
    (h : (countingMachine I P F C).step? cfg i = some next) :
    i < if atChoice cfg then 2 else 1 := by
  obtain ⟨hi, _⟩ := ((countingMachine I P F C).step?_eq_some_iff _ _ _).mp h
  cases hq : cfg.state with
  | none => simp [MultiTapeCTM.actions, hq] at hi
  | some q =>
    cases q <;> simpa [MultiTapeCTM.actions, hq, countingMachine, choiceBits, atChoice] using hi

/-- Replay actual occurrence indices and retain just the bits used at choice boundaries. -/
noncomputable def replayChoices {input : List Bool} :
    Cfg k Bool (State SI SP SF) input → List ℕ →
      Option (List Bool × Cfg k Bool (State SI SP SF) input)
  | cfg, [] => some ([], cfg)
  | cfg, i :: rest => ((countingMachine I P F C).step? cfg i).bind fun next =>
    (replayChoices next rest).map fun (bits, final) =>
      ((if atChoice cfg then (i == 1) :: bits else bits), final)

/-- The final configuration of the bit-recording replay is the ordinary replay result. -/
theorem map_snd_replayChoices {input : List Bool} (cfg : Cfg k Bool (State SI SP SF) input)
    (indices : List ℕ) :
    (replayChoices I P F C cfg indices).map Prod.snd =
      (countingMachine I P F C).runBranch cfg indices := by
  induction indices generalizing cfg with
  | nil => rfl
  | cons i rest ih =>
    rw [replayChoices, MultiTapeCTM.runBranch_cons]
    cases h : (countingMachine I P F C).step? cfg i with
    | none => rfl
    | some next =>
      simp only [Option.bind]
      rw [← ih next]
      cases hnext : replayChoices I P F C next rest with
      | none => rfl
      | some pair => cases pair; rfl

/-- Two first-halting occurrence traces with the same genuine choice bits coincide. -/
theorem eq_occurrences_of_replayChoices {input : List Bool}
    {cfg final₁ final₂ : Cfg k Bool (State SI SP SF) input} {bits : List Bool}
    {indices₁ indices₂ : List ℕ}
    (h₁ : replayChoices I P F C cfg indices₁ = some (bits, final₁))
    (h₂ : replayChoices I P F C cfg indices₂ = some (bits, final₂))
    (hh₁ : final₁.Halted) (hh₂ : final₂.Halted) : indices₁ = indices₂ := by
  induction indices₁ generalizing cfg bits indices₂ with
  | nil =>
    have heq : cfg = final₁ := congrArg Prod.snd (Option.some.inj h₁)
    have h := congrArg (Option.map Prod.snd) h₂
    rw [map_snd_replayChoices, MultiTapeCTM.runBranch_of_halted _ (heq.symm ▸ hh₁)] at h
    by_contra hne
    simp [Ne.symm hne] at h
  | cons i rest ih =>
    cases indices₂ with
    | nil =>
      have heq : cfg = final₂ := congrArg Prod.snd (Option.some.inj h₂)
      have h := congrArg (Option.map Prod.snd) h₁
      rw [map_snd_replayChoices, MultiTapeCTM.runBranch_of_halted _ (heq.symm ▸ hh₂)] at h
      simp at h
    | cons j tail =>
      simp only [replayChoices, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨x, hx, ⟨bs, f₁⟩, hxs, hbits₁⟩ := h₁
      obtain ⟨y, hy, ⟨cs, f₂⟩, hys, hbits₂⟩ := h₂
      have hb₁ := congrArg Prod.fst hbits₁
      have hb₂ := congrArg Prod.fst hbits₂
      have he : (if atChoice cfg then (i == 1) :: bs else bs) =
          (if atChoice cfg then (j == 1) :: cs else cs) := hb₁.trans hb₂.symm
      have hi := step_index_lt I P F C hx
      have hj := step_index_lt I P F C hy
      have hsame : i = j ∧ bs = cs := by
        cases hc : atChoice cfg
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hi hj he
          exact ⟨by omega, he⟩
        · simp only [hc, ↓reduceIte, List.cons.injEq] at hi hj he
          refine ⟨?_, he.2⟩
          by_contra hne
          have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
          rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at he
      obtain ⟨rfl, rfl⟩ := hsame
      obtain rfl : x = y := Option.some.inj (hx.symm.trans hy)
      have hf₁ : f₁ = final₁ := congrArg Prod.snd hbits₁
      have hf₂ : f₂ = final₂ := congrArg Prod.snd hbits₂
      rw [hf₁] at hxs
      rw [hf₂] at hys
      exact congrArg (i :: ·) (ih hxs hys)

/-- If a verdict determines the genuine choice sequence on every terminal replay, it has
at most one counted branch. -/
theorem branchCount_le_one_of_choiceTrace {input : List Bool}
    (cfg : Cfg k Bool (State SI SP SF) input) (fuel : ℕ) (verdict : List Bool → Bool)
    (bits : List Bool)
    (hbits : ∀ indices trace final, replayChoices I P F C cfg indices = some (trace, final) →
      final.Halted → verdict final.output → trace = bits) :
    (countingMachine I P F C).branchCount verdict fuel cfg ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  have htrace {indices : List ℕ}
      (h : indices ∈ ((countingMachine I P F C).branches fuel cfg).filter fun is =>
        ((countingMachine I P F C).runBranch cfg is).any fun final => verdict final.output) :
      ∃ final, replayChoices I P F C cfg indices = some (bits, final) ∧ final.Halted := by
    obtain ⟨hmem, hv⟩ := Finset.mem_filter.mp h
    obtain ⟨_, final, hr, hh⟩ := ((countingMachine I P F C).mem_branches_iff _ _ _).mp hmem
    rw [← map_snd_replayChoices] at hr
    obtain ⟨⟨trace, last⟩, ht, rfl⟩ := Option.map_eq_some_iff.mp hr
    have hv' : verdict last.output := by
      simpa [← map_snd_replayChoices, ht] using hv
    obtain rfl := hbits _ _ _ ht hh hv'
    exact ⟨last, ht, hh⟩
  intro first second hfirst hsecond
  obtain ⟨_, hf, hhf⟩ := htrace hfirst
  obtain ⟨_, hs, hhs⟩ := htrace hsecond
  exact eq_occurrences_of_replayChoices I P F C hf hs hhf hhs

end Turing.NondeterministicQueryMachine.Native
