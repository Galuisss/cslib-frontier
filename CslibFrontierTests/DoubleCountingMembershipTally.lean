/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.MembershipTally

/-! Checks for the membership tally's passing negative answer and rejecting terminal check. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingMembershipTally

open Turing Turing.DoubleCounting.MembershipTally

private def unusedWalk : NondeterministicQueryMachine Unit where
  init := ()
  query := fun _ => 0
  next := fun _ => ()
  halted := fun _ => true
  accept := fun _ => true

private def run (count : ℕ) :=
  (machine ⟨1, 0, 0, 0, ⟨count, 0⟩⟩ unusedWalk (fun _ => ()) (fun _ => some 0)).run []

-- Skipping the only vertex is a successful negative answer when the expected tally is empty.
example : run 0 [false, false] = .inr (.inr (some false)) := rfl

example :
    let ctx : Context := ⟨1, 0, 0, 0, ⟨0, 0⟩⟩
    let M := machine ctx unusedWalk (fun _ => ()) (fun _ => some 0)
    M.FirstHalting [] [false, false] M.init :=
  (firstHalting_finish ⟨1, 0, 0, 0, ⟨0, 0⟩⟩ unusedWalk (fun _ => ()) (fun _ => some 0)
    [] [false] Cslib.DoubleCounting.Scan.Result.zero false rfl rfl).1

-- The same choices reject when the expected count is one.
example : run 1 [false, false] = .inr (.inr none) := rfl

-- A selected walk returns through one deterministic boundary step.
example : run 1 [true, false, false] = .inr (.inr (some true)) := rfl

-- Decode the selected zero-step walk and check the same result in the typed scanner.
example : ∃ branch : Cslib.DoubleCounting.Scan.Branch 1,
    Cslib.DoubleCounting.Scan.run (fun _ _ => false) 0 0 0 ⟨1, 0⟩ branch = some true := by
  suffices ∃ branch : Cslib.DoubleCounting.Scan.Branch 1,
      [true, false, false] = selectors (fun _ => []) branch ∧
        Cslib.DoubleCounting.Scan.run (fun _ _ => false) 0 0 0 ⟨1, 0⟩ branch = some true by
    obtain ⟨branch, _, h⟩ := this
    exact ⟨branch, h⟩
  refine exists_scan_of_firstHalting unusedWalk (fun _ => ()) (fun _ => some 0)
    [] (fun _ _ => false) 0 0 0 ⟨1, 0⟩ (fun _ => []) ?_ [true, false, false] true ?_ ?_
  · intro v _ bits remaining _ hfirst hfuel
    change some 0 = some remaining at hfuel
    cases hfuel
    have hv : v = 0 := Fin.eq_zero v
    subst v
    have hbits : bits = [] := by
      cases bits with
      | nil => rfl
      | cons b bs =>
        have ht := ((unusedWalk.firstHalting_cons_iff [] b bs ()).mp hfirst).1
        cases ht
    exact ⟨[], hbits, Cslib.DoubleCounting.Scan.walkM_replay_eq_some.mpr
      ⟨List.isChainFromTo_singleton, rfl⟩⟩
  · exact (firstHalting_finish ⟨1, 0, 0, 0, ⟨1, 0⟩⟩ unusedWalk (fun _ => ())
      (fun _ => some 0) [] [true, false] ⟨⟨1, 0⟩, true⟩ true rfl rfl).1
  · rfl

private def edge : QueryMachine Unit where
  init := ()
  query := fun _ => 0
  next := fun _ => ()
  halted := fun _ => true
  emit := fun _ => []
  finish := fun _ => []

-- A checked zero-step walk is selected, but the queried vertex is skipped.
example :
    let branch : Cslib.DoubleCounting.Scan.Branch 2 := fun v =>
      if v = 0 then some [] else none
    let bits := selectors (Turing.DoubleCounting.BoundedWalk.selectors 0) branch
    let M := withBoundedWalk edge (fun (_ _ : Fin 2) => ()) (fun _ => false)
      0 0 ⟨2, 0, 1, 0, ⟨1, 0⟩⟩
    M.FirstHalting [] bits M.init ∧ M.run [] bits = .inr (.inr (some false)) := by
  let branch : Cslib.DoubleCounting.Scan.Branch 2 := fun v =>
    if v = 0 then some [] else none
  let bits := selectors (Turing.DoubleCounting.BoundedWalk.selectors 0) branch
  let adjacent : Fin 2 → Fin 2 → Bool := fun _ _ => false
  have hrun : Cslib.DoubleCounting.Scan.run adjacent 0 1 0 ⟨1, 0⟩ branch = some false := by
    rw [Cslib.DoubleCounting.Scan.run_eq_finish,
      Cslib.DoubleCounting.Scan.tallyPrefix_succ adjacent 0 1 0 branch (n := 1) (by decide),
      Cslib.DoubleCounting.Scan.tallyPrefix_succ adjacent 0 1 0 branch (n := 0) (by decide),
      Cslib.DoubleCounting.Scan.tallyPrefix_zero]
    simp [branch, Cslib.DoubleCounting.Scan.walkM, Cslib.DoubleCounting.Scan.readNext,
      bind, StateT.bind, pure, StateT.pure, Cslib.DoubleCounting.Scan.Result.finish,
      Cslib.DoubleCounting.Scan.Result.recordWalk, Cslib.DoubleCounting.Scan.Result.zero,
      Cslib.DoubleCounting.Tally.matches_iff]
  apply (withBoundedWalk_firstHalting_iff edge (fun _ _ => ()) (fun _ => false) 0 0 []
    adjacent 0 1 0 ⟨1, 0⟩ bits false (fun _ _ => rfl) (fun _ _ => rfl)).mpr
  refine ⟨branch, ⟨rfl, hrun⟩, ?_⟩
  intro other hother
  -- The serializer has a fixed-width, prefix-free payload at each selected candidate.
  exact selectors_injective _ (Turing.DoubleCounting.BoundedWalk.eq_of_selectors_prefix 0)
    hother.1.symm

end CslibFrontierTests.DoubleCountingMembershipTally
