/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.AsyncByzantine.Impossibility

/-! Asynchronous Byzantine reliable broadcast (`Basic` and `Impossibility`, checked as a `module`
client with ordinary imports): direct broadcast positive checks (`t = 0` and `n ≤ 2`), equivocation
counterexample on `Fin 3`, message-conservation identity `Protocol.card_msgs_add_traceSent` on
`directProtocol`, dot-notation usability for `Reachable.*` and `SolvesReliableBroadcast.*`, and
`3 ≤ n ≤ 3t` impossibility including the singleton domain `V = Unit`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.AsyncByzantine

open Cslib Cslib.Distributed.AsyncByzantine

/-! ### Direct broadcast: valid for `t = 0` and `n ≤ 2`, broken on `Fin 3` for `t = 1` -/

example : (directProtocol (Fin 4) Bool 0).SolvesReliableBroadcast 0 :=
  solvesReliableBroadcast_direct_of_zero 0

example (t : ℕ) : (directProtocol (Fin 2) Bool 0).SolvesReliableBroadcast t :=
  solvesReliableBroadcast_direct_of_card_le_two 0 (by simp) t

/-- On `Fin 3`, a single faulty dealer `0` can equivocate directly (`true` to `1`, `false` to `2`),
violating consistency in two `byzRecv` steps. -/
theorem direct_fin3_equivocation_reachable :
    let π := directProtocol (Fin 3) Bool 0
    let s₀ := π.start {0} none
    let s₁ := π.recvByz 0 1 true s₀
    let s₂ := π.recvByz 0 2 false s₁
    π.Reachable {0} none s₂ ∧ s₂.ProcDecided 1 true ∧ s₂.ProcDecided 2 false := by
  intro π s₀ s₁ s₂
  have h01 : (π.lts {0}).Tr s₀ (.byzRecv 0 1 true) s₁ := ⟨by decide, by decide, rfl⟩
  have h12 : (π.lts {0}).Tr s₁ (.byzRecv 0 2 false) s₂ := ⟨by decide, by decide, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨[.byzRecv 0 1 true, .byzRecv 0 2 false],
      LTS.MTr.stepL h01 (LTS.MTr.stepL h12 LTS.MTr.refl)⟩
  · simp [s₂, s₁, s₀, π, State.ProcDecided, Protocol.recvByz, Protocol.recvCore,
      Protocol.updateProc, Protocol.start, directProtocol]
  · simp [s₂, s₁, s₀, π, State.ProcDecided, Protocol.recvByz, Protocol.recvCore,
      Protocol.updateProc, Protocol.start, directProtocol]

example : ¬ (directProtocol (Fin 3) Bool 0).SolvesReliableBroadcast 1 := by
  intro h
  obtain ⟨hr, h1, h2⟩ := direct_fin3_equivocation_reachable
  have heq := h.consistency {0} (by decide) none _ hr 1 (by decide) 2 (by decide) true false h1 h2
  cases heq

-- `card_msgs_add_traceSent` conservation on a concrete fault-free `directProtocol` trace on
-- `Fin 3`: 3 initial messages are emitted, 2 are delivered, leaving 1 in flight (`3 + 0 = 1 + 2`).
example :
    let π := directProtocol (Fin 3) Bool 0
    let xl : List (Action (Fin 3) Bool) :=
      [.deliver ⟨0, 0, true⟩, .deliver ⟨0, 1, true⟩]
    let s₀ := π.start ∅ (some true)
    let s₁ := π.recvHonest ⟨0, 0, true⟩ s₀
    let s₂ := π.recvHonest ⟨0, 1, true⟩ s₁
    s₀.msgs.card + π.traceSent s₀ xl = s₂.msgs.card + xl.countP Action.isDeliver ∧
    π.sentInTrace ∅ (some true) xl = 3 ∧
    s₂.msgs.card = 1 ∧
    s₂.ProcDecided 0 true ∧ s₂.ProcDecided 1 true ∧ (s₂.proc 2).out = none := by
  intro π xl s₀ s₁ s₂
  have h01 : (π.lts ∅).Tr s₀ (.deliver ⟨0, 0, true⟩) s₁ := by
    refine ⟨?_, by decide, rfl⟩; decide
  have h12 : (π.lts ∅).Tr s₁ (.deliver ⟨0, 1, true⟩) s₂ := by
    refine ⟨?_, by decide, rfl⟩; decide
  have hcons := π.card_msgs_add_traceSent (LTS.MTr.stepL h01 (LTS.MTr.stepL h12 LTS.MTr.refl))
  exact ⟨hcons, by decide, by decide, by decide, by decide, by decide⟩

-- Dot-notation usability outside `namespace Protocol` (`Reachable.*`, `SolvesReliableBroadcast.*`).
example {P S M V : Type*} {dealer : P} [Fintype P] [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V dealer} {F : Finset P} {input : Option V} {s : State P S M V}
    (hr : π.Reachable F input s) {e : Envelope P M} (he : e ∈ s.msgs) :
    e.src ∉ F ∧ π.Reachable F input s :=
  ⟨hr.msgs_src_notMem he, hr.trans (LTS.CanReach.refl (π.lts F) s)⟩

example {P S M V : Type*} {dealer : P} [Fintype P] [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V dealer} {t : ℕ} (hsol : π.SolvesReliableBroadcast t)
    {F : Finset P} (hF : F.card ≤ t) {input : Option V} {s : State P S M V}
    (hr : π.Reachable F input s) {i j : P} (hi : i ∉ F) (hj : j ∉ F) {v₁ v₂ : V}
    (h₁ : s.ProcDecided i v₁) (h₂ : s.ProcDecided j v₂) : v₁ = v₂ := by
  obtain ⟨ss, xs, k, ha, hsk, _⟩ := hr.exists_admissibleRun
  exact hsol.consistency_admissible hF ha hi hj (hsk.symm ▸ h₁) (hsk.symm ▸ h₂)

/-! ### Impossibility at `3 ≤ n ≤ 3t` (including singleton `Unit`) -/

example {S M : Type*} [DecidableEq M] (π : Protocol (Fin 3) S M Unit 0) :
    ¬ π.SolvesReliableBroadcast 1 :=
  π.not_solvesReliableBroadcast_three

example {S M : Type*} [DecidableEq M] (π : Protocol (Fin 3) S M Bool 0) :
    ¬ π.SolvesReliableBroadcast 1 :=
  π.not_solvesReliableBroadcast_three

example {S M : Type*} [DecidableEq M] (π : Protocol (Fin 6) S M ℕ 0) :
    ¬ π.SolvesReliableBroadcast 2 :=
  π.not_solvesReliableBroadcast (by simp) (by simp)

end CslibFrontierTests.Distributed.AsyncByzantine
