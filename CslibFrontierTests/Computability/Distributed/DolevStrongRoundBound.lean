/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.Byzantine.DolevStrong
import CslibFrontier.Computability.Distributed.Byzantine.RoundBound

/-! Fischer–Lynch `t + 1` round lower bound and Dolev–Strong authenticated synchronous broadcast
(checked as an ordinary `module` client):

* Single-round naive authenticated broadcast (`directAuth`) solving `t = 0` in `1` round and
  failing against one equivocating dealer on `Fin 3`.
* `dolevStrong` on `Fin 3, t = 2` (tolerating `2` traitors out of `3` generals, where
  unauthenticated Byzantine agreement is impossible even for `t = 1`), checked by `decide` against
  coalition delayed-injection and equivocation attacks, plus multi-loyal agreement on `Fin 3`
  (`F = {0}`) and `Fin 4` (`F = {0, 1}`, over `V = ℕ`), two-value flood capping in
  `dolevStrongRound`, and exact/bounded message accounting.
* `Protocol.not_solvesByzantineAgreement_of_rounds_le` refuting `R = 0` (`t = 0`, `Fin 2`), `R = 1`
  (`t = 1`, `Fin 4`), and `R = 2` (`t = 2`, `Fin 7`), and instantiating the two-dimensional
  characterization `exists_solvesByzantineAgreement_iff_full` across all four parameter regimes. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.DolevStrongRoundBound

open Cslib.Distributed.Byzantine

/-! ### 1-round authenticated broadcast: solves `t = 0`, fails on `Fin 3` for `t = 1` -/

/-- Direct single-hop authenticated broadcast: `dealer` sends `⟨input, [dealer]⟩` in round `1`, and
every other process adopts the first chain signed by `dealer` received from `dealer`. -/
def directAuth (P V : Type*) [DecidableEq P] (dealer : P) (v₀ : V) :
    AuthProtocol P V V dealer where
  initDealer v := v
  initOther _ := v₀
  send r j s _ := if r = 0 ∧ j = dealer then [⟨s, [dealer]⟩] else []
  update r i s m :=
    if r = 0 ∧ i ≠ dealer then
      match (m dealer).find? (fun c => decide (dealer ∈ c.signers)) with
      | some c => c.value
      | none => s
    else s
  output _ s := s

theorem directAuth_solves_zero (n : ℕ) (dealer : Fin (n + 1)) (v₀ : Bool) :
    (directAuth (Fin (n + 1)) Bool dealer v₀).SolvesAuthenticatedBroadcast 0 1 where
  wellSigned F adv input r j dst c hc k hk hkne := by
    simp only [directAuth] at hc
    split_ifs at hc with h
    · obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_singleton] at hc
      subst hc
      simp only [List.mem_singleton] at hk
      exact absurd hk hkne
    · simp at hc
  agreement F hF adv input _ i _ j _ := by
    obtain rfl := Finset.card_eq_zero.1 (Nat.le_zero.1 hF)
    have hval : ∀ q : Fin (n + 1),
        (directAuth (Fin (n + 1)) Bool dealer v₀).decision ∅ adv input 1 q = input := by
      intro q
      by_cases hqd : q = dealer <;> simp [AuthProtocol.decision, AuthProtocol.state, directAuth,
        hqd]
    rw [hval i, hval j]
  validity F hF _ adv input _ i _ := by
    obtain rfl := Finset.card_eq_zero.1 (Nat.le_zero.1 hF)
    by_cases hid : i = dealer <;> simp [AuthProtocol.decision, AuthProtocol.state, directAuth, hid]

/-- Equivocating dealer `0` on `Fin 3` sends `⟨true, [0]⟩` to `1` and `⟨false, [0]⟩` to `2`. -/
def equivocatingDealer : ℕ → Fin 3 → Fin 3 → List (SignedChain (Fin 3) Bool) :=
  fun r j i => if r = 0 ∧ j = 0 then [⟨decide (i = 1), [0]⟩] else []

theorem unforgeable_equivocatingDealer (input : Bool) :
    (directAuth (Fin 3) Bool 0 false).Unforgeable {0} input equivocatingDealer := by
  intro r j hj i c hc k hk hkF
  simp only [equivocatingDealer] at hc
  split_ifs at hc with h
  · simp only [List.mem_singleton] at hc
    subst hc
    simp only [List.mem_singleton] at hk
    subst hk
    exact absurd (Finset.mem_singleton_self 0) hkF
  · simp at hc

-- `directAuth` violates agreement on `Fin 3` against a single equivocating dealer (`t = 1`).
example : ¬ (directAuth (Fin 3) Bool 0 false).SolvesAuthenticatedBroadcast 1 1 := by
  intro h
  have h12 := h.agreement {0} (by decide) equivocatingDealer true
    (unforgeable_equivocatingDealer true) 1 (by decide) 2 (by decide)
  revert h12
  decide

/-! ### Dolev–Strong on `Fin 3, t = 2` (2 traitors out of 3 generals!) -/

-- Whereas unauthenticated Byzantine agreement on `Fin 3` is impossible even against `t = 1` fault,
-- `dolevStrong` solves authenticated broadcast on `Fin 3` against `t = 2` faults in `3` rounds.
example : (dolevStrong (Fin 3) Bool 0 false 2).SolvesAuthenticatedBroadcast 2 3 :=
  dolevStrong_solvesAuthenticatedBroadcast 0 false 2 le_rfl

example {S M : Type} (π : Protocol (Fin 3) S M) (R : ℕ) : ¬ π.SolvesByzantineAgreement 1 R :=
  Protocol.not_solvesByzantineAgreement_three π R

/-- Coalition attack 1 on `Fin 3, t = 2` (`F = {0, 1}`, loyal `2`): faulty dealer `0` stays silent
in round 1, then `0` and accomplice `1` conspire to inject a 2-signer chain `⟨true, [1, 0]⟩` in
round 2 (`r = 1`), and attempt to inject a conflicting 2-signer chain `⟨false, [1, 0]⟩` in round 3
(`r = 2`, rejected because `length = 2 < 3`). -/
def coalitionDelayed : ℕ → Fin 3 → Fin 3 → List (SignedChain (Fin 3) Bool)
  | 1, 1, 2 => [⟨true, [1, 0]⟩]
  | 2, 0, 2 => [⟨false, [1, 0]⟩]
  | _, _, _ => []

theorem unforgeable_coalitionDelayed (input : Bool) :
    (dolevStrong (Fin 3) Bool 0 false 2).Unforgeable {0, 1} input coalitionDelayed := by
  intro r j _ i c hc k hk hkF
  match r, j, i with
  | 1, 1, 2 =>
    simp only [coalitionDelayed, List.mem_singleton] at hc
    subst hc
    exact False.elim (by revert k hk hkF; decide)
  | 2, 0, 2 =>
    simp only [coalitionDelayed, List.mem_singleton] at hc
    subst hc
    exact False.elim (by revert k hk hkF; decide)
  | 0, _, _ | _ + 3, _, _ => simp [coalitionDelayed] at hc
  | 1, 0, _ | 1, 2, _ | 1, 1, 0 | 1, 1, 1 => simp [coalitionDelayed] at hc
  | 2, 1, _ | 2, 2, _ | 2, 0, 0 | 2, 0, 1 => simp [coalitionDelayed] at hc

-- Loyal general `2` accepts `true` in round 2, rejects the under-signed `false` chain in round 3,
-- and decides `true`!
example :
    let π := dolevStrong (Fin 3) Bool 0 false 2
    (π.state {0, 1} coalitionDelayed false 1 2).extracted = [] ∧
    (π.state {0, 1} coalitionDelayed false 2 2).extracted = [true] ∧
    (π.state {0, 1} coalitionDelayed false 3 2).extracted = [true] ∧
    π.decision {0, 1} coalitionDelayed false 3 2 = true := by
  decide

/-- Coalition attack 2 on `Fin 3, t = 2` (`F = {0, 1}`, loyal `2`): faulty dealer `0` sends
`⟨true, [0]⟩` to `2` in round 1, then `0` and accomplice `1` conspire to send `⟨false, [1, 0]⟩` to
`2` in round 2; loyal `2` extracts both conflicting values and falls back to `v₀ = false`. -/
def coalitionSplit : ℕ → Fin 3 → Fin 3 → List (SignedChain (Fin 3) Bool)
  | 0, 0, 2 => [⟨true, [0]⟩]
  | 1, 1, 2 => [⟨false, [1, 0]⟩]
  | _, _, _ => []

example :
    let π := dolevStrong (Fin 3) Bool 0 false 2
    (π.state {0, 1} coalitionSplit true 3 2).extracted = [false, true] ∧
    π.decision {0, 1} coalitionSplit true 3 2 = false := by
  decide

-- On `Fin 3, t = 2` with `F = {0}` (equivocating dealer `0`, TWO loyal generals `1` and `2`),
-- `1` and `2` temporarily disagree after round 1 (`[true]` vs `[false]`), cross-relay in round 2,
-- and reach unanimous agreement on the fallback `false` at round 3, sending exactly
-- `12 = 2 * (3 - 1) * 3` chains total (matching `dolevStrong_correctMessagesSent_le` tightly!).
example :
    let π := dolevStrong (Fin 3) Bool 0 false 2
    (π.state {0} equivocatingDealer true 1 1).extracted = [true] ∧
    (π.state {0} equivocatingDealer true 1 2).extracted = [false] ∧
    π.decision {0} equivocatingDealer true 3 1 = false ∧
    π.decision {0} equivocatingDealer true 3 2 = false ∧
    π.correctMessagesSent {0} equivocatingDealer true 3 = 12 := by
  decide

/-! ### `Fin 4, t = 2` over infinite `V = ℕ`: 2 traitors `{0, 1}` vs 2 loyal generals `{2, 3}` -/

/-- Traitors `0` (dealer) and `1` stay silent in round 1, send `⟨42, [1, 0]⟩` only to `2` in round
2 (`r = 1`), and send under-signed `⟨99, [1, 0]⟩` to `3` in round 3 (`r = 2`). Round `t = 2` is not
yet in agreement (`2` has `[42]`, `3` has `[]`), and round `t + 1 = 3` brings both `2` and `3` to
decide `42`! -/
def lateRelayAttack : ℕ → Fin 4 → Fin 4 → List (SignedChain (Fin 4) ℕ)
  | 1, 1, 2 => [⟨42, [1, 0]⟩]
  | 2, 1, 3 => [⟨99, [1, 0]⟩]
  | _, _, _ => []

example :
    let π := dolevStrong (Fin 4) ℕ 0 0 2
    (π.state {0, 1} lateRelayAttack 7 2 2).extracted = [42] ∧
    (π.state {0, 1} lateRelayAttack 7 2 3).extracted = [] ∧
    π.decision {0, 1} lateRelayAttack 7 3 2 = 42 ∧
    π.decision {0, 1} lateRelayAttack 7 3 3 = 42 ∧
    π.correctMessagesSent {0, 1} lateRelayAttack 7 3 = 4 := by
  decide

-- Flood capping: when a faulty dealer sends 3 distinct valid values in round 1, `dolevStrongRound`
-- caps `extracted` and `toRelay` at length `2`, and the network message bound holds.
example :
    let m : Fin 3 → List (SignedChain (Fin 3) (Fin 4)) :=
      fun j => if j = 0 then [⟨1, [0]⟩, ⟨2, [0]⟩, ⟨3, [0]⟩] else []
    let s' := dolevStrongRound (0 : Fin 3) 2 1 0 ⟨[], []⟩ m
    s'.extracted = [2, 1] ∧ s'.toRelay.length = 2 := by
  decide

example (F : Finset (Fin 5)) (adv : ℕ → Fin 5 → Fin 5 → List (SignedChain (Fin 5) ℕ))
    (input : ℕ) (R : ℕ) :
    (dolevStrong (Fin 5) ℕ 0 0 4).correctMessagesSent F adv input R ≤ 50 := by
  have h := dolevStrong_correctMessagesSent_le (P := Fin 5) 0 0 4 F adv input R
  simp only [Fintype.card_fin] at h
  omega

/-! ### Fischer–Lynch `t + 1` round lower bound and two-parameter `iff` -/

-- `R = 0` (`t = 0`, `Fin 2`): zero rounds never suffice on two processes, even without faults.
example {S M : Type} (π : Protocol (Fin 2) S M) : ¬ π.SolvesByzantineAgreement 0 0 :=
  π.not_solvesByzantineAgreement_of_rounds_le (by simp) le_rfl

-- `R = 1` (`t = 1`, `Fin 4`): one round never suffices against one fault, even with `4 > 3 · 1`.
example {S M : Type} (π : Protocol (Fin 4) S M) : ¬ π.SolvesByzantineAgreement 1 1 :=
  π.not_solvesByzantineAgreement_of_rounds_le (by simp) le_rfl

-- `R = 2` (`t = 2`, `Fin 7`): two rounds never suffice against two faults, even with `7 > 3 · 2`.
example {S M : Type} (π : Protocol (Fin 7) S M) : ¬ π.SolvesByzantineAgreement 2 2 :=
  π.not_solvesByzantineAgreement_of_rounds_le (by simp) le_rfl

-- Complete two-parameter `(t, R)` characterization across all four regimes:
-- 1. Degenerate `n ≤ 1`: solvable in `0` rounds against any `t`.
example : ∃ (S M : Type) (π : Protocol (Fin 1) S M), π.SolvesByzantineAgreement 5 0 :=
  (exists_solvesByzantineAgreement_iff_full (Fin 1) 5 0).2 (Or.inl (by simp))

-- 2. Interior `3t < n ∧ t + 1 ≤ R` (`Fin 7, t = 2, R = 3`): solvable!
example : ∃ (S M : Type) (π : Protocol (Fin 7) S M), π.SolvesByzantineAgreement 2 3 :=
  (exists_solvesByzantineAgreement_iff_full (Fin 7) 2 3).2 (Or.inr ⟨by simp, by omega⟩)

-- 3. Too few processes `2 ≤ n ≤ 3t` (`Fin 6, t = 2, R = 10`): unsolvable!
example : ¬ ∃ (S M : Type) (π : Protocol (Fin 6) S M), π.SolvesByzantineAgreement 2 10 := by
  rw [exists_solvesByzantineAgreement_iff_full]
  simp

-- 4. Too few rounds `R ≤ t` (`Fin 7, t = 2, R = 2`): unsolvable!
example : ¬ ∃ (S M : Type) (π : Protocol (Fin 7) S M), π.SolvesByzantineAgreement 2 2 := by
  rw [exists_solvesByzantineAgreement_iff_full]
  simp

end CslibFrontierTests.Distributed.DolevStrongRoundBound
