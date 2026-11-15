/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Salted.Word

/-!
# Passive security of the salted joint-oracle Fujisaki--Okamoto transform

This file builds the single-user, single-challenge classical-ROM security experiment needed for
the HQC v5.1 salted transform. The challenge uses one fused joint-oracle reply `(key, coins)` at
the public input `(prefix, message, salt)`. `programChallenge` answers exactly that input with the
challenge reply and forwards every other joint, rejection and decapsulation query unchanged.
Keeping this distinguished reply outside `CacheState` is important: the challenge ciphertext is
punctured from decapsulation, so its own PKE decryption behavior must not create an extra
correctness opportunity.

The first proved hop in this module is the challenge-aware form of the salted `CORR` theorem.
It preserves the split security budgets `(qG, qJ, qD)` and loses exactly `(qG + qD) * δ`; direct
queries to the challenge input are answered locally and cost zero in the forwarded program.

The remaining passive challenge-randomization and implicit-rejection-seed hops follow
[GlabushHoevelmannsStebila2025], Theorems 11 and 13. Their source maps and the final composed
bound are added beside the corresponding games below rather than treating the already-proved
correctness hop as the complete security theorem.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.ChallengeData`: hidden message, public salt,
  fused joint reply and independent random challenge key.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.programChallenge`: deterministic challenge
  programming with all other queries forwarded.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.postGuessRealGame` and
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.postGuessSimGame`: the real and keyless
  games after the implicit-rejection seed-guessing hop.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.postGuessRealSuccessGame` and
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.postGuessSimSuccessGame`: the corresponding
  hidden-bit success experiments.

## Main results

* `QueryBounds.programChallenge`, `SecurityQueryBounds.programChallenge` and
  `ROQueryBounds.programChallenge`: challenge programming preserves every forwarded query budget.
* `Scheme.advantage_postGuessRealSuccessGame_simSuccessGame_le`: the challenge-aware `CORR` loss is
  `(qG + qD) * δ`.

## References

* [L. Glabush, K. Hövelmanns, D. Stebila, *Tight Multi-challenge Security Reductions for Key
  Encapsulation Mechanisms*][GlabushHoevelmannsStebila2025], Theorems 11 and 13.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto.Salted

open Probability
open scoped ENNReal NNReal

variable {PK SK M R CT JointPrefix Salt RejectPrefix Sigma K : Type}

/-- Hidden data used to make one salted KEM challenge. `reply` is the single fused random-oracle
answer whose named fields are the real challenge key and PKE encryption coins; `randomKey` is the
independent key used in the random challenge world. -/
structure ChallengeData (M Salt K R : Type) where
  /-- Uniform challenge message. -/
  message : M
  /-- Uniform public challenge salt. -/
  salt : Salt
  /-- Fused `(key, coins)` reply programmed at the challenge input. -/
  reply : JointReply K R
  /-- Independent random-world challenge key. -/
  randomKey : K

namespace Scheme

/-- Sample one hidden single-challenge record. The key and coin projections of the fused reply are
independent with exactly the laws bundled by the salted scheme. -/
noncomputable def sampleChallengeData [Fintype M] [Nonempty M] [Fintype Salt] [Nonempty Salt]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K) :
    ProbComp (ChallengeData M Salt K R) := do
  let message ← ProbComp.uniform M
  let salt ← ProbComp.uniform Salt
  let key ← S.sampleKey
  let coins ← S.pke.sampleCoins
  let randomKey ← S.sampleKey
  return ⟨message, salt, ⟨key, coins⟩, randomKey⟩

end Scheme

namespace ChallengeData

/-- The fused oracle input programmed for a sampled challenge. -/
def input (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (data : ChallengeData M Salt K R) : JointInput JointPrefix M Salt :=
  S.jointInput pk data.message data.salt

/-- The salted ciphertext determined by a sampled challenge record. -/
def ciphertext (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (data : ChallengeData M Salt K R) : Ciphertext CT Salt :=
  ⟨S.pke.encDet pk data.message data.reply.coins, data.salt⟩

/-- Public KEM challenge selected by the hidden real-or-random bit. -/
def challenge (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (pk : PK) (data : ChallengeData M Salt K R) (random : Bool) :
    KEM.Challenge PK (Ciphertext CT Salt) K :=
  ⟨pk, data.ciphertext S pk, if random then data.randomKey else data.reply.key⟩

end ChallengeData

/-- Substitute the distinguished fused challenge reply for its exact joint input and forward every
other query on the same typed oracle interface. The challenge call itself is removed from the
forwarded program, so it cannot be counted as a correctness opportunity. -/
def programChallenge [DecidableEq (JointInput JointPrefix M Salt)]
    (input : JointInput JointPrefix M Salt) (reply : JointReply K R) :
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) →
      OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
        (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) (Response K R q)
  | .joint queried =>
      if queried = input then pure reply else OracleComp.query (Query.joint queried)
  | .rejection queried => OracleComp.query (Query.rejection queried)
  | .decaps ciphertext => OracleComp.query (Query.decaps ciphertext)

private theorem isCostBounded_programChallenge
    [DecidableEq (JointInput JointPrefix M Salt)]
    (cost : Query JointPrefix M Salt RejectPrefix Sigma CT → ℕ)
    (input : JointInput JointPrefix M Salt) (reply : JointReply K R)
    (q : Query JointPrefix M Salt RejectPrefix Sigma CT) :
    OracleComp.IsCostBounded cost (programChallenge input reply q) (cost q) := by
  cases q with
  | joint queried =>
      simp only [programChallenge]
      split
      · exact OracleComp.IsCostBounded.pure _ _
      · exact OracleComp.IsCostBounded.query _
  | rejection queried => exact OracleComp.IsCostBounded.query _
  | decaps ciphertext => exact OracleComp.IsCostBounded.query _

namespace QueryBounds

/-- Programming the challenge reply preserves the joint-`G` and decapsulation bounds used by
`CORR`; the distinguished joint call is answered locally. -/
theorem programChallenge [DecidableEq (JointInput JointPrefix M Salt)]
    {α : Type}
    {program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) α}
    {qG qD : ℕ} (h : QueryBounds program qG qD)
    (input : JointInput JointPrefix M Salt) (reply : JointReply K R) :
    QueryBounds (OracleComp.interpret (programChallenge input reply) program) qG qD :=
  ⟨OracleComp.IsCostBounded.interpret
      (isCostBounded_programChallenge Query.jointCost input reply) h.1,
    OracleComp.IsCostBounded.interpret
      (isCostBounded_programChallenge Query.decapsCost input reply) h.2⟩

end QueryBounds

namespace SecurityQueryBounds

/-- Challenge programming preserves the full split `(qG, qJ, qD)` security bounds. -/
theorem programChallenge [DecidableEq (JointInput JointPrefix M Salt)]
    {α : Type}
    {program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) α}
    {qG qJ qD : ℕ} (h : SecurityQueryBounds program qG qJ qD)
    (input : JointInput JointPrefix M Salt) (reply : JointReply K R) :
    SecurityQueryBounds (OracleComp.interpret (programChallenge input reply) program) qG qJ qD :=
  ⟨OracleComp.IsCostBounded.interpret
      (isCostBounded_programChallenge Query.jointCost input reply) h.1,
    OracleComp.IsCostBounded.interpret
      (isCostBounded_programChallenge Query.rejectionCost input reply) h.2.1,
    OracleComp.IsCostBounded.interpret
      (isCostBounded_programChallenge Query.decapsCost input reply) h.2.2⟩

end SecurityQueryBounds

namespace ROQueryBounds

/-- Challenge programming preserves the explicit total tagged-random-oracle and decapsulation
budgets. -/
theorem programChallenge [DecidableEq (JointInput JointPrefix M Salt)]
    {α : Type}
    {program : OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) α}
    {qRO qD : ℕ} (h : ROQueryBounds program qRO qD)
    (input : JointInput JointPrefix M Salt) (reply : JointReply K R) :
    ROQueryBounds (OracleComp.interpret (programChallenge input reply) program) qRO qD :=
  ⟨OracleComp.IsCostBounded.interpret
      (isCostBounded_programChallenge Query.roCost input reply) h.1,
    OracleComp.IsCostBounded.interpret
      (isCostBounded_programChallenge Query.decapsCost input reply) h.2⟩

end ROQueryBounds

namespace Scheme

/-- Fix the adversary's private coins and public challenge, then substitute the challenge's fused
reply at its exact joint-oracle input. -/
def programmedRun [DecidableEq (JointInput JointPrefix M Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    (coins : A.Coins) (pk : PK) (data : ChallengeData M Salt K R) (random : Bool) :
    OracleComp (Response (JointPrefix := JointPrefix) (M := M) (Salt := Salt)
      (RejectPrefix := RejectPrefix) (Sigma := Sigma) (CT := CT) K R) Bool :=
  OracleComp.interpret (programChallenge (data.input S pk) data.reply)
    (A.run coins (data.challenge S pk random))

/-- Fixed-key real post-seed-guessing game, including adversary coins and hidden challenge data. -/
noncomputable def postGuessRealAt [Fintype M] [Nonempty M]
    [Fintype Salt] [Nonempty Salt]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    (pk : PK) (sk : SK) (random : Bool) : PMF Bool :=
  (ProbComp.eval A.coins).bind fun coins =>
    (ProbComp.eval S.sampleChallengeData).bind fun data =>
      ((OracleComp.interpret (S.realHandler pk sk (data.ciphertext S pk))
        (programmedRun S A coins pk data random)).run {}).map Prod.fst

/-- Fixed-public-key keyless post-seed-guessing game with the same challenge law. -/
noncomputable def postGuessSimAt [Fintype M] [Nonempty M]
    [Fintype Salt] [Nonempty Salt]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    (pk : PK) (random : Bool) : PMF Bool :=
  (ProbComp.eval A.coins).bind fun coins =>
    (ProbComp.eval S.sampleChallengeData).bind fun data =>
      ((OracleComp.interpret (S.simHandler pk (data.ciphertext S pk))
        (programmedRun S A coins pk data random)).run {}).map Prod.fst

/-- Real decrypt/re-encrypt IND-CCA game after the implicit-rejection seed has been replaced by an
independent decapsulation table. The challenge's fused reply is programmed locally. -/
noncomputable def postGuessRealGame [Fintype M] [Nonempty M]
    [Fintype Salt] [Nonempty Salt]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    (random : Bool) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys => S.postGuessRealAt A keys.1 keys.2 random

/-- Keyless simulated IND-CCA game with the same programmed challenge law. -/
noncomputable def postGuessSimGame [Fintype M] [Nonempty M]
    [Fintype Salt] [Nonempty Salt]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    (random : Bool) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys => S.postGuessSimAt A keys.1 random

/-- Hidden-bit success experiment for real decrypt/re-encrypt decapsulation after the
implicit-rejection seed-guessing hop. -/
noncomputable def postGuessRealSuccessGame [Fintype M] [Nonempty M]
    [Fintype Salt] [Nonempty Salt]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (PMF.uniformOfFintype Bool).bind fun random =>
      (S.postGuessRealAt A keys.1 keys.2 random).map fun guess => guess == random

/-- Hidden-bit success experiment for keyless patched-cache decapsulation after the
implicit-rejection seed-guessing hop. -/
noncomputable def postGuessSimSuccessGame [Fintype M] [Nonempty M]
    [Fintype Salt] [Nonempty Salt]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (PMF.uniformOfFintype Bool).bind fun random =>
      (S.postGuessSimAt A keys.1 random).map fun guess => guess == random

private theorem closeTo_postGuessRealAt_simAt
    [Finite JointPrefix] [Fintype M] [Nonempty M] [Fintype Salt] [Nonempty Salt]
    [Finite RejectPrefix]
    [Finite Sigma] [Finite CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    (pk : PK) (sk : SK) (random : Bool) {qG qJ qD : ℕ}
    (hbounds : A.SecurityQueryBounded qG qJ qD) :
    CloseTo (postGuessRealAt S A pk sk random) (postGuessSimAt S A pk random)
      (((qG + qD : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk)) := by
  refine (CloseTo.bind_right_tsum (ProbComp.eval A.coins)
    (err := fun _ => (((qG + qD : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk))) fun coins _ => ?_).mono ?_
  · refine (CloseTo.bind_right_tsum (ProbComp.eval S.sampleChallengeData)
      (err := fun _ => (((qG + qD : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk))) fun data _ => ?_).mono ?_
    · apply S.closeTo_run_realHandler_simHandler
      exact ((hbounds coins (data.challenge S pk random)).programChallenge
        (data.input S pk) data.reply).toQueryBounds
    · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Challenge-aware salted-FO `CORR` hop.** After the implicit-rejection seed-guessing hop,
replacing decrypt/re-encrypt decapsulation by the keyless patched-cache simulator changes the
hidden-bit success experiment by at most `(qG + qD) * δ`. Averaging the fixed-bit bounds preserves
this coefficient directly in the source normalization `|Pr[success] - 1/2|`. The distinguished
challenge joint query is programmed outside the correctness cache, so there is no extra `+1`. -/
theorem advantage_postGuessRealSuccessGame_simSuccessGame_le
    [Finite JointPrefix] [Fintype M] [Nonempty M] [Fintype Salt] [Nonempty Salt]
    [Finite RejectPrefix]
    [Finite Sigma] [Finite CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (A : RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R)
    {qG qJ qD : ℕ} (hbounds : A.SecurityQueryBounded qG qJ qD)
    {δ : ℝ} (hδ : S.pke.DeltaCorrect δ) :
    (Game.advantage (S.postGuessRealSuccessGame A) (S.postGuessSimSuccessGame A) : ℝ) ≤
      ((qG + qD : ℕ) : ℝ) * δ := by
  simpa only [postGuessRealSuccessGame, postGuessSimSuccessGame] using
    S.pke.advantage_bind_keyGen_le
      (fun pk sk => (PMF.uniformOfFintype Bool).bind fun random =>
        (postGuessRealAt S A pk sk random).map fun guess => guess == random)
      (fun pk _ => (PMF.uniformOfFintype Bool).bind fun random =>
        (postGuessSimAt S A pk random).map fun guess => guess == random)
      (qG + qD) (fun pk sk => CloseTo.bind_right (PMF.uniformOfFintype Bool) fun random _ =>
        (closeTo_postGuessRealAt_simAt S A pk sk random hbounds).map fun guess => guess == random)
      hδ

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
