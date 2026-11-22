/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Byzantine.Basic
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Computability.Distributed.Byzantine.RecursiveOralMessages
import Mathlib.Data.Fintype.EquivFin

/-!
# The `t + 1` round lower bound for Byzantine agreement

No deterministic synchronous protocol on `n ≥ 2` processes solves Byzantine agreement against `t`
faults in `R ≤ t` rounds ([Fischer and Lynch][FischerLynch1982]). Combined with the `3t + 1` node
bound (`CslibFrontier.Computability.Distributed.Byzantine.NodeBound`) and the `(t + 1)`-round oral
messages protocol (`CslibFrontier.Computability.Distributed.Byzantine.RecursiveOralMessages`), this
determines the exact two-parameter solvability region: a protocol on `P` solves Byzantine agreement
against `t` faults in `R` rounds if and only if `Fintype.card P ≤ 1` or
`3 * t < Fintype.card P ∧ t + 1 ≤ R` (`exists_solvesByzantineAgreement_iff_full`).

## Proof outline

By monotonicity in the fault threshold (`Protocol.SolvesByzantineAgreement.mono`) and the `n ≤ 3t`
node bound (`Protocol.not_solvesByzantineAgreement`), it suffices to refute
`π.SolvesByzantineAgreement R R` when `R + 2 ≤ Fintype.card P`.

Even crash-like (silent-omission) schedules suffice. Fix a default message `m₀ : M`. A partial
schedule `(C, alive)` up to round `k` designates at most `k` faulty processes `C` and specifies
which messages faulty processes drop (replacing them by `m₀`) in rounds `< k`; its canonical
extension `extAlive k C alive` silences `C` in all rounds `≥ k` while keeping processes outside `C`
honest. Backward induction on the remaining rounds `d = R - k` proves simultaneously:

1. **Silencing (`P_silence`):** silencing one additional process `p` from round `k` onward does not
   change the round-`R` decision of the remaining correct processes. First silence `p` from round
   `k + 1` onward (`d` remaining rounds), then silence `p`'s round-`(k + 1)` messages one recipient
   `q*` at a time; each single-recipient change alters the state after round `k + 1` only at `q*`,
   which is masked in the remaining `d` rounds by the induction hypothesis with fault set
   `insert p C` of size at most `k + 1`.
2. **Single-process masking (`P_agree`):** two `C`-honest prefixes of length `k` whose states at
   round `k` agree outside `insert p C` reach the same round-`R` decision, obtained by silencing
   `p` from round `k` onward in both runs. Since `(insert p C).card ≤ R + 1 < Fintype.card P`, at
   least one process outside `insert p C` remains correct in both runs.

At `k = 0` (`C = ∅`, `d = R`), flipping the input vector from all-`false` to all-`true` one process
at a time preserves the round-`R` decision of fault-free runs, contradicting validity.

## Main results

* `Cslib.Distributed.Byzantine.Protocol.not_solvesByzantineAgreement_of_rounds_le`: no protocol on
  `n ≥ 2` processes solves Byzantine agreement against `t` faults in `R ≤ t` rounds.
* `Cslib.Distributed.Byzantine.exists_solvesByzantineAgreement_iff_full`: complete characterization
  of `(t, R)`-solvability of synchronous Byzantine agreement on finite process sets.

## References

* [M. J. Fischer, N. A. Lynch, *A lower bound for the time to assure interactive
  consistency*][FischerLynch1982]
* [L. Lamport, R. Shostak, M. Pease, *The Byzantine generals problem*][LamportShostakPease1982]
* [M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*][FischerLynchMerritt1985]
-/

public section

namespace Cslib.Distributed.Byzantine

namespace Protocol

section CrashPeeling

variable {P S M : Type*} [DecidableEq P] (π : Protocol P S M)

/-- Run of `π` under a binary delivery mask `alive`: when `alive r j i` is `false`, `j` sends the
fixed silent fallback message `m₀` to `i` in round `r + 1`. -/
private def crashState (m₀ : M) (alive : ℕ → P → P → Bool) (x : P → Bool) : ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (crashState m₀ alive x r i)
      (fun j => if alive r j i then π.send r j (crashState m₀ alive x r j) i else m₀)

/-- Adversary message table realizing `crashState` for any fault set containing all processes that
ever drop a message. -/
private def crashAdv (m₀ : M) (alive : ℕ → P → P → Bool) (x : P → Bool)
    (r : ℕ) (j i : P) : M :=
  if alive r j i then π.send r j (π.crashState m₀ alive x r j) i else m₀

private theorem state_crashAdv_eq (m₀ : M) (F : Finset P) (alive : ℕ → P → P → Bool)
    (x : P → Bool) {R : ℕ} (hF : ∀ r < R, ∀ j ∉ F, ∀ i, alive r j i = true) :
    ∀ r ≤ R, π.state F (π.crashAdv m₀ alive x) x r = π.crashState m₀ alive x r
  | 0, _ => rfl
  | r + 1, hr => by
    have ih := state_crashAdv_eq m₀ F alive x hF r (by omega)
    funext i
    simp only [state, crashState, ih]
    congr 1
    funext j
    by_cases hj : j ∈ F
    · simp only [hj, ↓reduceIte, crashAdv]
    · simp only [hj, ↓reduceIte, hF r (by omega) j hj i]

private theorem crashDecision_agree {R : ℕ} (h : π.SolvesByzantineAgreement R R) (m₀ : M)
    {C : Finset P} (hC : C.card ≤ R) {alive : ℕ → P → P → Bool}
    (halive : ∀ r < R, ∀ j ∉ C, ∀ i, alive r j i = true) (x : P → Bool)
    {i j : P} (hi : i ∉ C) (hj : j ∉ C) :
    π.output i (π.crashState m₀ alive x R i) = π.output j (π.crashState m₀ alive x R j) := by
  have heq := π.state_crashAdv_eq m₀ C alive x halive R le_rfl
  simpa only [decision, heq] using h.agreement C hC (π.crashAdv m₀ alive x) x i hi j hj

omit [DecidableEq P] in
private theorem crashState_congr_lt (m₀ : M) {alive₁ alive₂ : ℕ → P → P → Bool} (x : P → Bool)
    {k : ℕ} (h : ∀ r < k, alive₁ r = alive₂ r) :
    ∀ r ≤ k, π.crashState m₀ alive₁ x r = π.crashState m₀ alive₂ x r
  | 0, _ => rfl
  | r + 1, hr => by
    have ih := crashState_congr_lt m₀ x h r (by omega)
    simp only [crashState, ih, h r (by omega)]

/-- Canonical continuation from round `k`: keep `alive` before round `k`, and for rounds `≥ k` let
processes outside `C` send honestly while processes in `C` send `m₀`. -/
private def extAlive (k : ℕ) (C : Finset P) (alive : ℕ → P → P → Bool)
    (r : ℕ) (j i : P) : Bool :=
  if r < k then alive r j i else decide (j ∉ C)

/-- Intermediate schedule silencing `p` in round `k + 1` (step `k`) to the recipients in `U` and to
everyone in later rounds, while processes in `C` stay silent from step `k` onward. -/
private def silenceAt (k : ℕ) (C : Finset P) (p : P) (U : Finset P) (alive : ℕ → P → P → Bool)
    (r : ℕ) (j i : P) : Bool :=
  if r < k then alive r j i
  else if r = k then decide (j ∉ C ∧ ¬(j = p ∧ i ∈ U))
  else decide (j ∉ insert p C)

private theorem extAlive_honest {k : ℕ} {C : Finset P} {alive : ℕ → P → P → Bool}
    (h : ∀ r < k, ∀ j ∉ C, ∀ i, alive r j i = true) :
    ∀ r, ∀ j ∉ C, ∀ i, extAlive k C alive r j i = true := by
  intro r j hj i
  unfold extAlive
  split_ifs with hr
  · exact h r hr j hj i
  · exact decide_eq_true hj

private theorem extAlive_succ_extAlive (k : ℕ) (C : Finset P) (alive : ℕ → P → P → Bool) :
    extAlive (k + 1) C (extAlive k C alive) = extAlive k C alive := by
  funext r j i
  unfold extAlive
  split_ifs with h₁ h₂ <;> first | rfl | omega

private theorem silenceAt_empty (k : ℕ) (C : Finset P) (p : P) (alive : ℕ → P → P → Bool) :
    silenceAt k C p ∅ alive = extAlive (k + 1) (insert p C) (extAlive k C alive) := by
  funext r j i
  unfold silenceAt extAlive
  by_cases hlt : r < k
  · have hlt' : r < k + 1 := by omega
    simp only [hlt, hlt', ↓reduceIte]
  · by_cases heq : r = k
    · subst heq
      simp
    · have hlt' : ¬(r < k + 1) := by omega
      simp only [hlt, heq, hlt', ↓reduceIte]

private theorem silenceAt_univ [Fintype P] (k : ℕ) (C : Finset P) (p : P)
    (alive : ℕ → P → P → Bool) :
    silenceAt k C p Finset.univ alive = extAlive k (insert p C) alive := by
  funext r j i
  unfold silenceAt extAlive
  split_ifs with h₁ h₂
  · rfl
  · simp [Finset.mem_insert, not_or, and_comm]
  · rfl

private theorem extAlive_succ_silenceAt (k : ℕ) (C : Finset P) (p : P) (U : Finset P)
    (alive : ℕ → P → P → Bool) :
    extAlive (k + 1) (insert p C) (silenceAt k C p U alive) = silenceAt k C p U alive := by
  funext r j i
  unfold extAlive silenceAt
  split_ifs <;> first | rfl | omega

private theorem silenceAt_honest {k : ℕ} {C : Finset P} {p : P} {U : Finset P}
    {alive : ℕ → P → P → Bool} (h : ∀ r < k, ∀ j ∉ C, ∀ i, alive r j i = true) :
    ∀ r < k + 1, ∀ j ∉ insert p C, ∀ i, silenceAt k C p U alive r j i = true := by
  intro r hr j hj i
  simp only [Finset.mem_insert, not_or] at hj
  obtain ⟨hjp, hjC⟩ := hj
  unfold silenceAt
  split_ifs with h₁ h₂
  · exact h r h₁ j hjC i
  · exact decide_eq_true ⟨hjC, fun h' => hjp h'.1⟩
  · omega

private theorem crashState_silenceAt_insert_eq_of_ne (m₀ : M) (k : ℕ) (C : Finset P)
    (p qstar : P) (U : Finset P) (alive : ℕ → P → P → Bool) (x : P → Bool)
    {q : P} (hq : q ≠ qstar) :
    π.crashState m₀ (silenceAt k C p (insert qstar U) alive) x (k + 1) q =
      π.crashState m₀ (silenceAt k C p U alive) x (k + 1) q := by
  have hk : π.crashState m₀ (silenceAt k C p (insert qstar U) alive) x k =
      π.crashState m₀ (silenceAt k C p U alive) x k :=
    π.crashState_congr_lt m₀ x (fun r hr => by
      funext j i
      unfold silenceAt
      simp only [hr, ↓reduceIte]) k le_rfl
  simp only [crashState, hk]
  congr 1
  funext j
  have hmem : silenceAt k C p (insert qstar U) alive k j q = silenceAt k C p U alive k j q := by
    unfold silenceAt
    simp only [lt_irrefl, ↓reduceIte, Finset.mem_insert, hq, false_or]
  rw [hmem]

private theorem crashState_extAlive_eq (m₀ : M) (k : ℕ) (C : Finset P)
    (alive : ℕ → P → P → Bool) (x : P → Bool) :
    π.crashState m₀ (extAlive k C alive) x k = π.crashState m₀ alive x k :=
  π.crashState_congr_lt m₀ x (fun r hr => by
    funext j i
    unfold extAlive
    simp only [hr, ↓reduceIte]) k le_rfl

private theorem crashState_extAlive_eq_of_agree (m₀ : M) {k : ℕ} {C : Finset P}
    {alive₁ alive₂ : ℕ → P → P → Bool} {x₁ x₂ : P → Bool}
    (hagree : ∀ q ∉ C, π.crashState m₀ alive₁ x₁ k q = π.crashState m₀ alive₂ x₂ k q) :
    ∀ (d : ℕ), ∀ q ∉ C,
      π.crashState m₀ (extAlive k C alive₁) x₁ (k + d) q =
        π.crashState m₀ (extAlive k C alive₂) x₂ (k + d) q
  | 0, q, hq => by
    rw [Nat.add_zero, π.crashState_extAlive_eq, π.crashState_extAlive_eq, hagree q hq]
  | d + 1, q, hq => by
    rw [← Nat.add_assoc, crashState, crashState]
    congr 1
    · exact crashState_extAlive_eq_of_agree m₀ hagree d q hq
    · funext j
      have hext₁ : extAlive k C alive₁ (k + d) j q = decide (j ∉ C) := by
        unfold extAlive
        simp only [show ¬(k + d < k) by omega, ↓reduceIte]
      have hext₂ : extAlive k C alive₂ (k + d) j q = decide (j ∉ C) := by
        unfold extAlive
        simp only [show ¬(k + d < k) by omega, ↓reduceIte]
      rw [hext₁, hext₂]
      by_cases hj : j ∈ C
      · simp only [hj, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      · simp only [hj, not_false_eq_true, decide_true, ↓reduceIte,
          crashState_extAlive_eq_of_agree m₀ hagree d j hj]

/-- Core round-peeling theorem: on at least `R + 2` processes, no protocol solves Byzantine
agreement against `R` faults in `R` rounds. -/
private theorem not_solvesByzantineAgreement_self [Fintype P] {R : ℕ}
    (hn : R + 2 ≤ Fintype.card P) : ¬ π.SolvesByzantineAgreement R R := by
  intro h
  obtain ⟨p₀, -, -⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := (∅ : Finset P))
    (t := Finset.univ) (by rw [Finset.card_empty, Finset.card_univ]; omega)
  let m₀ : M := π.send 0 p₀ (π.init p₀ false) p₀
  -- Backward induction on `d` (`k + d = R`), simultaneously proving single-process silencing
  -- (`P_silence`) and single-process state masking (`P_agree`).
  have peel : ∀ d : ℕ,
      (∀ (k : ℕ), k + d = R → ∀ (C : Finset P), C.card ≤ k → ∀ (p : P)
        (alive : ℕ → P → P → Bool) (x : P → Bool),
        (∀ r < k, ∀ j ∉ C, ∀ i, alive r j i = true) →
        ∀ i₁ ∉ C, ∀ i₂ ∉ insert p C,
          π.output i₁ (π.crashState m₀ (extAlive k C alive) x R i₁) =
            π.output i₂ (π.crashState m₀ (extAlive k (insert p C) alive) x R i₂)) ∧
      (∀ (k : ℕ), k + d = R → ∀ (C : Finset P), C.card ≤ k → ∀ (p : P)
        (alive₁ alive₂ : ℕ → P → P → Bool) (x₁ x₂ : P → Bool),
        (∀ r < k, ∀ j ∉ C, ∀ i, alive₁ r j i = true) →
        (∀ r < k, ∀ j ∉ C, ∀ i, alive₂ r j i = true) →
        (∀ q ∉ insert p C, π.crashState m₀ alive₁ x₁ k q = π.crashState m₀ alive₂ x₂ k q) →
        ∀ i₁ ∉ C, ∀ i₂ ∉ C,
          π.output i₁ (π.crashState m₀ (extAlive k C alive₁) x₁ R i₁) =
            π.output i₂ (π.crashState m₀ (extAlive k C alive₂) x₂ R i₂)) := by
    intro d
    induction d with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro k hk C hC p alive x halive i₁ hi₁ i₂ hi₂
        rw [Nat.add_zero] at hk
        subst hk
        rw [π.crashState_extAlive_eq m₀ k (insert p C) alive x,
          ← π.crashState_extAlive_eq m₀ k C alive x]
        exact π.crashDecision_agree h m₀ hC
          (fun r _ j hj i => extAlive_honest halive r j hj i) x hi₁
          (fun hmem => hi₂ (Finset.mem_insert_of_mem hmem))
      · intro k hk C hC p alive₁ alive₂ x₁ x₂ halive₁ halive₂ hagree i₁ hi₁ i₂ hi₂
        rw [Nat.add_zero] at hk
        subst hk
        have hcard : (insert p C).card < (Finset.univ : Finset P).card := by
          rw [Finset.card_univ]
          have := Finset.card_insert_le p C
          omega
        obtain ⟨q₀, -, hq₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        have hq₀C : q₀ ∉ C := fun hmem => hq₀ (Finset.mem_insert_of_mem hmem)
        have h₁ := π.crashDecision_agree h m₀ hC
          (fun r _ j hj i => extAlive_honest halive₁ r j hj i) x₁ hi₁ hq₀C
        have h₂ := π.crashDecision_agree h m₀ hC
          (fun r _ j hj i => extAlive_honest halive₂ r j hj i) x₂ hq₀C hi₂
        have hmid : π.crashState m₀ (extAlive k C alive₁) x₁ k q₀ =
            π.crashState m₀ (extAlive k C alive₂) x₂ k q₀ := by
          rw [π.crashState_extAlive_eq, π.crashState_extAlive_eq, hagree q₀ hq₀]
        rw [h₁, hmid, h₂]
    | succ d ih =>
      obtain ⟨ih_sil, ih_agr⟩ := ih
      have hsil : ∀ (k : ℕ), k + (d + 1) = R → ∀ (C : Finset P), C.card ≤ k → ∀ (p : P)
          (alive : ℕ → P → P → Bool) (x : P → Bool),
          (∀ r < k, ∀ j ∉ C, ∀ i, alive r j i = true) →
          ∀ i₁ ∉ C, ∀ i₂ ∉ insert p C,
            π.output i₁ (π.crashState m₀ (extAlive k C alive) x R i₁) =
              π.output i₂ (π.crashState m₀ (extAlive k (insert p C) alive) x R i₂) := by
        intro k hk C hC p alive x halive i₁ hi₁ i₂ hi₂
        have hk' : (k + 1) + d = R := by omega
        -- Step 1: silence `p` from round `k + 1` onward (`silenceAt k C p ∅ alive`).
        have hstep1 := ih_sil (k + 1) hk' C (by omega) p (extAlive k C alive) x
          (fun r _ j hj i => extAlive_honest halive r j hj i) i₁ hi₁ i₂ hi₂
        rw [extAlive_succ_extAlive, ← silenceAt_empty] at hstep1
        -- Step 2: silence `p` in round `k` one recipient at a time across `U : Finset P`.
        have hC' : (insert p C).card ≤ k + 1 :=
          (Finset.card_insert_le p C).trans (by omega)
        have hstep2 : ∀ U : Finset P,
            π.output i₂ (π.crashState m₀ (silenceAt k C p ∅ alive) x R i₂) =
              π.output i₂ (π.crashState m₀ (silenceAt k C p U alive) x R i₂) := by
          intro U
          induction U using Finset.induction with
          | empty => rfl
          | insert qstar U hqU ihU =>
            refine ihU.trans ?_
            have hstep := ih_agr (k + 1) hk' (insert p C) hC' qstar
              (silenceAt k C p U alive) (silenceAt k C p (insert qstar U) alive) x x
              (silenceAt_honest halive) (silenceAt_honest halive)
              (fun q hq => (π.crashState_silenceAt_insert_eq_of_ne m₀ k C p qstar U alive x
                (fun heq => hq (by simp [heq]))).symm)
              i₂ hi₂ i₂ hi₂
            simpa only [extAlive_succ_silenceAt] using hstep
        have huniv := hstep2 Finset.univ
        rw [silenceAt_univ] at huniv
        exact hstep1.trans huniv
      refine ⟨hsil, ?_⟩
      intro k hk C hC p alive₁ alive₂ x₁ x₂ halive₁ halive₂ hagree i₁ hi₁ i₂ hi₂
      have hcard : (insert p C).card < (Finset.univ : Finset P).card := by
        rw [Finset.card_univ]
        have := Finset.card_insert_le p C
        omega
      obtain ⟨q₀, -, hq₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      have h₁ := hsil k hk C hC p alive₁ x₁ halive₁ i₁ hi₁ q₀ hq₀
      have h₂ := hsil k hk C hC p alive₂ x₂ halive₂ i₂ hi₂ q₀ hq₀
      have hmid := π.crashState_extAlive_eq_of_agree m₀ hagree (d + 1) q₀ hq₀
      rw [hk] at hmid
      exact h₁.trans ((congrArg (π.output q₀) hmid).trans h₂.symm)
  -- Apply `P_agree` at `k = 0, C = ∅, d = R`, flipping inputs from `false` to `true` one process
  -- at a time.
  let aliveTrue : ℕ → P → P → Bool := fun _ _ _ => true
  have hall_eq : ∀ U : Finset P,
      π.output p₀ (π.crashState m₀ aliveTrue (fun _ => false) R p₀) =
        π.output p₀ (π.crashState m₀ aliveTrue (fun i => decide (i ∈ U)) R p₀) := by
    intro U
    induction U using Finset.induction with
    | empty =>
      simp only [Finset.notMem_empty, decide_false]
    | insert p U hpU ihU =>
      refine ihU.trans ?_
      have hstep := (peel R).2 0 (Nat.zero_add R) ∅ (by simp) p aliveTrue aliveTrue
        (fun i => decide (i ∈ U)) (fun i => decide (i ∈ insert p U))
        (fun _ hr => absurd hr (Nat.not_lt_zero _))
        (fun _ hr => absurd hr (Nat.not_lt_zero _))
        (fun q hq => by
          have hqp : q ≠ p := fun heq => hq (by simp [heq])
          simp only [crashState, Finset.mem_insert, hqp, false_or])
        p₀ (Finset.notMem_empty p₀) p₀ (Finset.notMem_empty p₀)
      have hext : extAlive 0 ∅ aliveTrue = aliveTrue := by
        funext r j i
        simp [extAlive, aliveTrue]
      simpa only [hext] using hstep
  have hfalse_true :
      π.output p₀ (π.crashState m₀ aliveTrue (fun _ => false) R p₀) =
        π.output p₀ (π.crashState m₀ aliveTrue (fun _ => true) R p₀) := by
    simpa only [Finset.mem_univ, decide_true] using hall_eq Finset.univ
  have hstate_eq : ∀ x, π.crashState m₀ aliveTrue x R p₀ =
      π.state ∅ (π.crashAdv m₀ aliveTrue x) x R p₀ := fun x =>
    congrFun (π.state_crashAdv_eq m₀ ∅ aliveTrue x (fun _ _ _ _ _ => rfl) R le_rfl).symm p₀
  have hval_false : π.output p₀ (π.crashState m₀ aliveTrue (fun _ => false) R p₀) = false := by
    rw [hstate_eq]
    exact h.validity ∅ (Nat.zero_le R) _ (fun _ => false) false (fun _ _ => rfl)
      p₀ (Finset.notMem_empty p₀)
  have hval_true : π.output p₀ (π.crashState m₀ aliveTrue (fun _ => true) R p₀) = true := by
    rw [hstate_eq]
    exact h.validity ∅ (Nat.zero_le R) _ (fun _ => true) true (fun _ _ => rfl)
      p₀ (Finset.notMem_empty p₀)
  rw [hval_false, hval_true] at hfalse_true
  exact Bool.false_ne_true hfalse_true

/-- **The `t + 1` round lower bound** ([Fischer and Lynch][FischerLynch1982]): no deterministic
synchronous protocol on `n ≥ 2` processes solves Byzantine agreement against `t` faults in
`R ≤ t` rounds. -/
theorem not_solvesByzantineAgreement_of_rounds_le [Fintype P] {t R : ℕ}
    (h2 : 2 ≤ Fintype.card P) (hR : R ≤ t) :
    ¬ π.SolvesByzantineAgreement t R := by
  intro h
  by_cases hcard : R + 2 ≤ Fintype.card P
  · exact π.not_solvesByzantineAgreement_self hcard (h.mono hR)
  · exact π.not_solvesByzantineAgreement h2 (by omega) h

end CrashPeeling

/-- Reindex a protocol along equivalences of the process, state and message types. -/
private def reindex {P Q S S' M M' : Type*} (eP : P ≃ Q) (eS : S' ≃ S) (eM : M' ≃ M)
    (π : Protocol Q S M) : Protocol P S' M' where
  init i b := eS.symm (π.init (eP i) b)
  send r i s j := eM.symm (π.send r (eP i) (eS s) (eP j))
  update r i s m := eS.symm (π.update r (eP i) (eS s) (fun j => eM (m (eP.symm j))))
  output i s := π.output (eP i) (eS s)

private theorem reindex_state {P Q S S' M M' : Type*} [DecidableEq P] [DecidableEq Q]
    (eP : P ≃ Q) (eS : S' ≃ S) (eM : M' ≃ M) (π : Protocol Q S M)
    (F : Finset P) (adv : ℕ → P → P → M') (x : P → Bool) :
    ∀ (r : ℕ) (i : P),
      (reindex eP eS eM π).state F adv x r i =
        eS.symm (π.state (F.map eP.toEmbedding)
          (fun r j i => eM (adv r (eP.symm j) (eP.symm i))) (fun j => x (eP.symm j)) r (eP i))
  | 0, i => by simp only [state, reindex, Equiv.symm_apply_apply]
  | r + 1, i => by
    have ih := reindex_state eP eS eM π F adv x r
    rw [state]
    simp only [ih, state]
    change eS.symm (π.update r (eP i) _ _) = _
    congr 1
    rw [Equiv.apply_symm_apply]
    congr 1
    funext j
    by_cases hj : eP.symm j ∈ F
    · have hj' : j ∈ F.map eP.toEmbedding := by
        simpa only [Finset.mem_map_equiv] using hj
      simp only [hj, hj', ↓reduceIte, Equiv.symm_apply_apply]
    · have hj' : j ∉ F.map eP.toEmbedding := by
        simpa only [Finset.mem_map_equiv] using hj
      simp only [hj, hj', ↓reduceIte, reindex, Equiv.apply_symm_apply]

private theorem reindex_decision {P Q S S' M M' : Type*} [DecidableEq P] [DecidableEq Q]
    (eP : P ≃ Q) (eS : S' ≃ S) (eM : M' ≃ M) (π : Protocol Q S M)
    (F : Finset P) (adv : ℕ → P → P → M') (x : P → Bool) (R : ℕ) (i : P) :
    (reindex eP eS eM π).decision F adv x R i =
      π.decision (F.map eP.toEmbedding)
        (fun r j i => eM (adv r (eP.symm j) (eP.symm i))) (fun j => x (eP.symm j)) R (eP i) := by
  rw [decision, reindex_state]
  simp only [reindex, decision, Equiv.apply_symm_apply]

private theorem solvesByzantineAgreement_reindex {P Q S S' M M' : Type*}
    [DecidableEq P] [DecidableEq Q] (eP : P ≃ Q) (eS : S' ≃ S) (eM : M' ≃ M)
    {π : Protocol Q S M} {t R : ℕ} (h : π.SolvesByzantineAgreement t R) :
    (reindex eP eS eM π).SolvesByzantineAgreement t R where
  agreement F hF adv x i hi j hj := by
    have hF' : (F.map eP.toEmbedding).card ≤ t := by simpa only [Finset.card_map] using hF
    have hi' : eP i ∉ F.map eP.toEmbedding := by
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hi
    have hj' : eP j ∉ F.map eP.toEmbedding := by
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hj
    rw [reindex_decision, reindex_decision]
    exact h.agreement _ hF' _ _ (eP i) hi' (eP j) hj'
  validity F hF adv x v hv i hi := by
    have hF' : (F.map eP.toEmbedding).card ≤ t := by simpa only [Finset.card_map] using hF
    have hi' : eP i ∉ F.map eP.toEmbedding := by
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hi
    rw [reindex_decision]
    refine h.validity _ hF' _ _ v (fun j hj => ?_) (eP i) hi'
    exact hv (eP.symm j) (by simpa only [Finset.mem_map_equiv] using hj)

end Protocol

/-- **Complete two-parameter characterization of synchronous Byzantine agreement.**
For a finite process type `P`, fault bound `t`, and fixed decision round `R`, some deterministic
synchronous protocol solves Byzantine agreement on `P` against `t` faults in `R` rounds if and only
if `Fintype.card P ≤ 1` or both `3 * t < Fintype.card P` and `t + 1 ≤ R`:

* `Fintype.card P ≤ 1`: solved in `0` rounds by `Protocol.ownInput`
  (`Protocol.solvesByzantineAgreement_ownInput`).
* `3 * t < Fintype.card P` and `t + 1 ≤ R`: solved by recursive oral messages `om`
  (`solvesByzantineAgreement_om`, [Lamport, Shostak and Pease][LamportShostakPease1982]).
* `2 ≤ Fintype.card P ≤ 3 * t`: excluded by the node bound `Protocol.not_solvesByzantineAgreement`
  ([Fischer, Lynch and Merritt][FischerLynchMerritt1985]).
* `2 ≤ Fintype.card P` and `R ≤ t`: excluded by the round bound
  `Protocol.not_solvesByzantineAgreement_of_rounds_le` ([Fischer and Lynch][FischerLynch1982]). -/
theorem exists_solvesByzantineAgreement_iff_full.{u, v, w} (P : Type u) [Fintype P] [DecidableEq P]
    (t R : ℕ) :
    (∃ (S : Type v) (M : Type w) (π : Protocol P S M), π.SolvesByzantineAgreement t R) ↔
      Fintype.card P ≤ 1 ∨ (3 * t < Fintype.card P ∧ t + 1 ≤ R) := by
  constructor
  · rintro ⟨S, M, π, h⟩
    by_cases h1 : Fintype.card P ≤ 1
    · exact Or.inl h1
    · refine Or.inr ⟨?_, ?_⟩
      · by_contra h3
        exact π.not_solvesByzantineAgreement (by omega) (by omega) h
      · by_contra hR
        exact π.not_solvesByzantineAgreement_of_rounds_le (by omega) (by omega) h
  · rintro (h1 | ⟨h3, hR⟩)
    · have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.1 h1
      exact ⟨ULift.{v} Bool, ULift.{w} Unit,
        Protocol.reindex (Equiv.refl P) Equiv.ulift Equiv.ulift (Protocol.ownInput P),
        Protocol.solvesByzantineAgreement_reindex (Equiv.refl P) Equiv.ulift Equiv.ulift
          (Protocol.solvesByzantineAgreement_ownInput t R)⟩
    · let eP := Fintype.equivFin P
      have hcard : 3 * t < Fintype.card (Fin (Fintype.card P)) := by
        simpa only [Fintype.card_fin] using h3
      exact ⟨ULift.{v} (List (Fin (Fintype.card P)) → Bool),
        ULift.{w} (List (Fin (Fintype.card P)) → Bool),
        Protocol.reindex eP Equiv.ulift Equiv.ulift (om (Fin (Fintype.card P)) t),
        Protocol.solvesByzantineAgreement_reindex eP Equiv.ulift Equiv.ulift
          (solvesByzantineAgreement_om hcard hR)⟩

end Cslib.Distributed.Byzantine
