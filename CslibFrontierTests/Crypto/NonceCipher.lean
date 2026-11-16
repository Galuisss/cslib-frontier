/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.NonceBased

/-!
# Tests for deterministic nonce-based encryption and AEAD

Clients of `CslibFrontier.Crypto.Computational.Encryption.NonceBased` under `module`
encapsulation:

1. Concrete `Correct` checks for a cleartext cipher, a one-time boolean XOR cipher, and a
   unit-message cipher.
2. `cpaExperiment` on one valid query: advantage `0` for one-time boolean XOR under a uniform
   boolean key, and advantage `1` for a cleartext cipher.
3. `ciExperiment` on one valid query: winning with a fresh triple (`succProbability = 1`).
4. Inadmissible challenge pairs and repeated nonces force `cpaExperiment` to output `false` for
   both challenge bits (`advantage = 0`) even on a cleartext cipher.
5. Repeated nonces force `ciExperiment` to output `false` (`succProbability = 0`) even with a
   fresh valid forgery candidate.
6. Distinct nonces preserve full distinguishing and forging behavior in both experiments.
7. Replayed `(c, d, n)` triples lose in `ciExperiment`, whereas reusing the same ciphertext `c`
   and nonce `n` with different associated data `d' ≠ d` wins when decryption accepts.
8. One-query word adversaries routed through `OracleCodec.adapt` distinguish a cleartext
   nonce-based cipher with advantage `1` and win `ciExperiment` with probability `1`.
9. Nonvacuity of `NonceCipher.INDCPA`, `NonceCipher.CiphertextIntegrity`, and `NonceCipher.AEAD`,
   specialization `D := Unit` (Attack Game 5.3), and level-`n` experiment unfolding.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.NonceCipher

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### Schemes and correctness -/

private def cleartextCipher (D N : Type) : NonceCipher Unit (List Bool) D (List Bool) N where
  encrypt _ m _ _ := m
  decrypt _ c _ _ := some c

example (D N : Type) : (cleartextCipher D N).Correct := fun _ _ _ _ => rfl

private def cleartextBoolCipher : NonceCipher Unit Bool Unit Bool Bool where
  encrypt _ m _ _ := m
  decrypt _ c _ _ := some c

example : cleartextBoolCipher.Correct := fun _ _ _ _ => rfl

private def boolOtpCipher : NonceCipher Bool Bool Unit Bool ℕ where
  encrypt k m _ _ := xor k m
  decrypt k c _ _ := some (xor k c)

example : boolOtpCipher.Correct := by
  intro k m _ _
  cases k <;> cases m <;> rfl

private def unitMsgCipher : NonceCipher Unit Unit Unit Unit Unit where
  encrypt _ _ _ _ := ()
  decrypt _ _ _ _ := some ()

example : unitMsgCipher.Correct := fun _ _ _ _ => rfl

private def constUnitCipher (D : ℕ → Type) (n : ℕ) :
    NonceCipher Unit (List Bool) (D n) Unit ℕ where
  encrypt _ _ _ _ := ()
  decrypt _ _ _ _ := none

private def sameLen : List Bool → List Bool → Bool
  | m₀, m₁ => m₀.length == m₁.length

/-! ### One-query `cpaExperiment`: boolean OTP (`0`) and cleartext (`1`) -/

private def boolOtpOneQuery :
    ProbOracleComp (fun _ : MessagePair Bool × Unit × ℕ => Bool) Bool :=
  ProbOracleComp.query (⟨false, true⟩, (), 0)

example :
    Experiment.advantage
      (boolOtpCipher.cpaExperiment (ProbComp.uniform Bool) (fun _ _ => true)
        boolOtpOneQuery false)
      (boolOtpCipher.cpaExperiment (ProbComp.uniform Bool) (fun _ _ => true)
        boolOtpOneQuery true) = 0 := by
  have hfalse :
      ProbComp.eval (boolOtpCipher.cpaExperiment (ProbComp.uniform Bool)
        (fun _ _ => true) boolOtpOneQuery false) = PMF.uniformOfFintype Bool := by
    simp only [NonceCipher.cpaExperiment, boolOtpOneQuery, boolOtpCipher, ProbOracleComp.runLog,
      ProbOracleComp.runState_query, StateT.run]
    ext b
    cases b <;> simp [ProbComp.eval_uniform]
  have htrue :
      ProbComp.eval (boolOtpCipher.cpaExperiment (ProbComp.uniform Bool)
        (fun _ _ => true) boolOtpOneQuery true) = PMF.uniformOfFintype Bool := by
    simp only [NonceCipher.cpaExperiment, boolOtpOneQuery, boolOtpCipher, ProbOracleComp.runLog,
      ProbOracleComp.runState_query, StateT.run]
    ext b
    cases b <;> simp [ProbComp.eval_uniform]
  simp [Experiment.advantage, hfalse, htrue]

private def cleartextOneQuery :
    ProbOracleComp (fun _ : MessagePair (List Bool) × Unit × ℕ => List Bool) Bool := do
  let c ← ProbOracleComp.query (⟨[false], [true]⟩, (), 0)
  return c == [true]

example :
    ProbComp.eval ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen
      cleartextOneQuery false) = PMF.pure false := by
  simp only [NonceCipher.cpaExperiment, ProbOracleComp.runLog, cleartextOneQuery, bind_pure_comp,
    map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    Functor.map_map, pure_bind, ProbComp.eval_map]
  dsimp only [StateT.run]
  simp [cleartextCipher, sameLen]

example :
    ProbComp.eval ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen
      cleartextOneQuery true) = PMF.pure true := by
  simp only [NonceCipher.cpaExperiment, ProbOracleComp.runLog, cleartextOneQuery, bind_pure_comp,
    map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    Functor.map_map, pure_bind, ProbComp.eval_map]
  dsimp only [StateT.run]
  simp [cleartextCipher, sameLen]

example :
    Experiment.advantage
      ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen cleartextOneQuery false)
      ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen cleartextOneQuery true) = 1 := by
  simp only [NonceCipher.cpaExperiment, ProbOracleComp.runLog, cleartextOneQuery, bind_pure_comp,
    map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    Functor.map_map, pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.advantage, Game.succProbability, cleartextCipher, sameLen]

/-! ### Inadmissible challenge pair and repeated nonce in `cpaExperiment` -/

private def inadmissiblePairAdv :
    ProbOracleComp (fun _ : MessagePair (List Bool) × Unit × ℕ => List Bool) Bool := do
  let c ← ProbOracleComp.query (⟨[false], [true, false]⟩, (), 0)
  return c == [true, false]

example (b : Bool) :
    ProbComp.eval ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen
      inadmissiblePairAdv b) = PMF.pure false := by
  cases b <;>
    (simp only [NonceCipher.cpaExperiment, ProbOracleComp.runLog, inadmissiblePairAdv,
      bind_pure_comp, map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query,
      StateT.run_map, Functor.map_map, pure_bind, ProbComp.eval_map];
     dsimp only [StateT.run];
     simp [cleartextCipher, sameLen])

example :
    Experiment.advantage
      ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen inadmissiblePairAdv false)
      ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen inadmissiblePairAdv true) = 0 := by
  simp only [NonceCipher.cpaExperiment, ProbOracleComp.runLog, inadmissiblePairAdv, bind_pure_comp,
    map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    Functor.map_map, pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.advantage, cleartextCipher, sameLen]

private def repeatedNonceCPAAdv :
    ProbOracleComp (fun _ : MessagePair (List Bool) × Unit × ℕ => List Bool) Bool := do
  let c ← ProbOracleComp.query (⟨[false], [true]⟩, (), 0)
  let _ ← ProbOracleComp.query (⟨[true], [false]⟩, (), 0)
  return c == [true]

example (b : Bool) :
    ProbComp.eval ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen
      repeatedNonceCPAAdv b) = PMF.pure false := by
  cases b <;>
    (simp only [NonceCipher.cpaExperiment, ProbOracleComp.runLog, repeatedNonceCPAAdv,
      bind_pure_comp, map_pure, ProbOracleComp.runState_bind, ProbOracleComp.runState_query,
      ProbOracleComp.runState_map, StateT.run_bind, StateT.run_map, map_bind, Functor.map_map,
      pure_bind, ProbComp.eval_bind, ProbComp.eval_map];
     dsimp only [StateT.run];
     simp [cleartextCipher, sameLen])

example :
    Experiment.advantage
      ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen repeatedNonceCPAAdv false)
      ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen repeatedNonceCPAAdv true) = 0 := by
  simp only [NonceCipher.cpaExperiment, ProbOracleComp.runLog, repeatedNonceCPAAdv, bind_pure_comp,
    map_pure, ProbOracleComp.runState_bind, ProbOracleComp.runState_query,
    ProbOracleComp.runState_map, StateT.run_bind, StateT.run_map, map_bind, Functor.map_map,
    pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.advantage, cleartextCipher, sameLen]

private def distinctNoncesCPAAdv :
    ProbOracleComp (fun _ : MessagePair (List Bool) × Unit × ℕ => List Bool) Bool := do
  let _ ← ProbOracleComp.query (⟨[false], [true]⟩, (), 0)
  let c ← ProbOracleComp.query (⟨[true], [false]⟩, (), 1)
  return c == [false]

example :
    Experiment.advantage
      ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen distinctNoncesCPAAdv false)
      ((cleartextCipher Unit ℕ).cpaExperiment (pure ()) sameLen distinctNoncesCPAAdv true) = 1 := by
  simp only [NonceCipher.cpaExperiment, ProbOracleComp.runLog, distinctNoncesCPAAdv, bind_pure_comp,
    map_pure, ProbOracleComp.runState_bind, ProbOracleComp.runState_query,
    ProbOracleComp.runState_map, StateT.run_bind, StateT.run_map, map_bind, Functor.map_map,
    pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.advantage, Game.succProbability, cleartextCipher, sameLen]

/-! ### `ciExperiment`: valid query, repeated nonce, distinct nonces, replay, and AD swap -/

private def ciFreshOneQuery :
    ProbOracleComp (fun _ : List Bool × Bool × ℕ => List Bool) (List Bool × Bool × ℕ) := do
  let _ ← ProbOracleComp.query ([false], false, 0)
  return ([true], false, 0)

example :
    Experiment.succProbability
      ((cleartextCipher Bool ℕ).ciExperiment (pure ()) ciFreshOneQuery) = 1 := by
  simp only [NonceCipher.ciExperiment, ProbOracleComp.runLog, ciFreshOneQuery, bind_pure_comp,
    map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.succProbability, Game.succProbability, cleartextCipher]

private def ciRepeatedNonceAdv :
    ProbOracleComp (fun _ : List Bool × Bool × ℕ => List Bool) (List Bool × Bool × ℕ) := do
  let _ ← ProbOracleComp.query ([false], false, 0)
  let _ ← ProbOracleComp.query ([true], true, 0)
  return ([false, true], false, 0)

example :
    Experiment.succProbability
      ((cleartextCipher Bool ℕ).ciExperiment (pure ()) ciRepeatedNonceAdv) = 0 := by
  simp only [NonceCipher.ciExperiment, ProbOracleComp.runLog, ciRepeatedNonceAdv, bind_pure_comp,
    map_pure, ProbOracleComp.runState_bind, ProbOracleComp.runState_query,
    ProbOracleComp.runState_map, StateT.run_bind, StateT.run_map, pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.succProbability, Game.succProbability, cleartextCipher]

private def ciDistinctNoncesAdv :
    ProbOracleComp (fun _ : List Bool × Bool × ℕ => List Bool) (List Bool × Bool × ℕ) := do
  let _ ← ProbOracleComp.query ([false], false, 0)
  let _ ← ProbOracleComp.query ([false], false, 1)
  return ([true], false, 0)

example :
    Experiment.succProbability
      ((cleartextCipher Bool ℕ).ciExperiment (pure ()) ciDistinctNoncesAdv) = 1 := by
  simp only [NonceCipher.ciExperiment, ProbOracleComp.runLog, ciDistinctNoncesAdv, bind_pure_comp,
    map_pure, ProbOracleComp.runState_bind, ProbOracleComp.runState_query,
    ProbOracleComp.runState_map, StateT.run_bind, StateT.run_map, pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.succProbability, Game.succProbability, cleartextCipher]

private def ciReplayAdv :
    ProbOracleComp (fun _ : List Bool × Bool × ℕ => List Bool) (List Bool × Bool × ℕ) := do
  let c ← ProbOracleComp.query ([false], false, 0)
  return (c, false, 0)

example :
    Experiment.succProbability
      ((cleartextCipher Bool ℕ).ciExperiment (pure ()) ciReplayAdv) = 0 := by
  simp only [NonceCipher.ciExperiment, ProbOracleComp.runLog, ciReplayAdv, bind_pure_comp,
    map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map,
    pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.succProbability, Game.succProbability, cleartextCipher]

private def ciSameCiphertextDiffADAdv :
    ProbOracleComp (fun _ : List Bool × Bool × ℕ => List Bool) (List Bool × Bool × ℕ) := do
  let c ← ProbOracleComp.query ([false], false, 0)
  return (c, true, 0)

example :
    Experiment.succProbability
      ((cleartextCipher Bool ℕ).ciExperiment (pure ()) ciSameCiphertextDiffADAdv) = 1 := by
  simp only [NonceCipher.ciExperiment, ProbOracleComp.runLog, ciSameCiphertextDiffADAdv,
    bind_pure_comp, map_pure, ProbOracleComp.runState_map, ProbOracleComp.runState_query,
    StateT.run_map, pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.succProbability, Game.succProbability, cleartextCipher]

/-! ### Word-level cleartext break and forgery through `OracleCodec.adapt` -/

private def cleartextBoolCodec :
    OracleCodec Unit (MessagePair Bool × Unit × Bool) (fun _ => Bool) where
  encodeQuery q := ((), [q.1.msg₀, q.1.msg₁, q.2.2])
  decodeQuery
    | ((), [m₀, m₁, nonce]) => some (⟨m₀, m₁⟩, (), nonce)
    | _ => none
  decodeQuery_eq_some_iff := by
    intro ⟨⟨⟩, req⟩ ⟨⟨m₀, m₁⟩, ⟨⟩, nonce⟩
    rcases req with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | rest⟩⟩⟩
    · simp
    · simp
    · simp
    · exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩
    · simp
  encodeReply _ := encBool

private def wordCleartextBreaker : ℕ → List Bool → WordOracleComp Unit Bool := fun _ _ => do
  let r ← ProbOracleComp.query ((), [false, true, false])
  return r == [true]

example (n : ℕ) :
    Experiment.advantage
      (cleartextBoolCipher.cpaExperiment (pure ()) (fun _ _ => true)
        (cleartextBoolCodec.adapt (wordCleartextBreaker n [])) false)
      (cleartextBoolCipher.cpaExperiment (pure ()) (fun _ _ => true)
        (cleartextBoolCodec.adapt (wordCleartextBreaker n [])) true) = 1 := by
  simp [Experiment.advantage, Game.succProbability, NonceCipher.cpaExperiment,
    wordCleartextBreaker, cleartextBoolCodec, OracleCodec.wordOracle, cleartextBoolCipher,
    ProbOracleComp.runLog, StateT.run, encBool_apply]

private def cleartextBoolCICodec :
    OracleCodec Unit (Bool × Unit × Bool) (fun _ => Bool) where
  encodeQuery q := ((), [q.1, q.2.2])
  decodeQuery
    | ((), [m, nonce]) => some (m, (), nonce)
    | _ => none
  decodeQuery_eq_some_iff := by
    intro ⟨⟨⟩, req⟩ ⟨m, ⟨⟩, nonce⟩
    rcases req with _ | ⟨a, _ | ⟨b, _ | rest⟩⟩
    · simp
    · simp
    · exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩
    · simp
  encodeReply _ := encBool

private def wordCleartextForger : ℕ → List Bool → WordOracleComp Unit (List Bool) :=
  fun _ _ => do
    let _ ← ProbOracleComp.query ((), [false, false])
    return [true]

private def boolCandidate (_n : ℕ) : List Bool → Bool × Unit × Bool
  | c :: _ => (c, (), false)
  | [] => (false, (), false)

example (n : ℕ) :
    Experiment.succProbability
      (cleartextBoolCipher.ciExperiment (pure ())
        (boolCandidate n <$> cleartextBoolCICodec.adapt (wordCleartextForger n []))) = 1 := by
  simp only [NonceCipher.ciExperiment, ProbOracleComp.runLog, wordCleartextForger,
    cleartextBoolCICodec, bind_pure_comp, OracleCodec.adapt_map, OracleCodec.adapt_query,
    OracleCodec.wordOracle, Functor.map_map, map_pure, ProbOracleComp.runState_map,
    ProbOracleComp.runState_query, StateT.run_map, pure_bind]
  dsimp only [StateT.run]
  simp [Experiment.succProbability, Game.succProbability, boolCandidate, cleartextBoolCipher]

/-! ### Nonvacuity, `D := Unit` specialization, and level-`n` unfolding -/

private theorem constUnitCipher_indcpa (D : ℕ → Type)
    (valid : ∀ _n, List Bool → List Bool → Bool)
    (codec : ∀ n, OracleCodec Unit (MessagePair (List Bool) × D n × ℕ) fun _ => Unit) :
    NonceCipher.INDCPA (constUnitCipher D) (fun _ => pure ()) valid codec := by
  intro W _
  simp [NonceCipher.cpaExperiment, constUnitCipher]

private theorem constUnitCipher_ci (D : ℕ → Type) [∀ n, DecidableEq (D n)]
    (codec : ∀ n, OracleCodec Unit (List Bool × D n × ℕ) fun _ => Unit)
    (candidate : ∀ n, List Bool → Unit × D n × ℕ) :
    NonceCipher.CiphertextIntegrity (constUnitCipher D) (fun _ => pure ()) codec candidate := by
  intro W _
  have hzero : (fun n => Game.advantage
      (ProbComp.eval ((constUnitCipher D n).ciExperiment (pure ())
        (candidate n <$> (codec n).adapt (W n []))))
      (PMF.pure false)) = fun _ => 0 := by
    funext n
    have hfail : ProbComp.eval ((constUnitCipher D n).ciExperiment (pure ())
        (candidate n <$> (codec n).adapt (W n []))) = PMF.pure false := by
      simp only [NonceCipher.ciExperiment, constUnitCipher, ProbComp.eval_bind,
        ProbComp.eval_pure, PMF.pure_bind, Option.isSome_none, Bool.false_and]
      exact PMF.map_const _ false
    simp [hfail]
  rw [hzero]
  exact negligible_zero

private theorem constUnitCipher_aead (D : ℕ → Type) [∀ n, DecidableEq (D n)]
    (valid : ∀ _n, List Bool → List Bool → Bool)
    (cpaCodec : ∀ n, OracleCodec Unit (MessagePair (List Bool) × D n × ℕ) fun _ => Unit)
    (ciCodec : ∀ n, OracleCodec Unit (List Bool × D n × ℕ) fun _ => Unit)
    (candidate : ∀ n, List Bool → Unit × D n × ℕ) :
    NonceCipher.AEAD (constUnitCipher D) (fun _ => pure ()) valid cpaCodec ciCodec candidate :=
  ⟨constUnitCipher_indcpa D valid cpaCodec, constUnitCipher_ci D ciCodec candidate⟩

-- Specialization `D := fun _ => Unit` recovers Attack Game 5.3 without associated data.
example (cpaCodec : ∀ _n, OracleCodec Unit (MessagePair (List Bool) × Unit × ℕ) fun _ => Unit)
    (ciCodec : ∀ _n, OracleCodec Unit (List Bool × Unit × ℕ) fun _ => Unit)
    (candidate : ∀ _n, List Bool → Unit × Unit × ℕ) :
    NonceCipher.AEAD (constUnitCipher (fun _ => Unit)) (fun _ => pure ())
      (fun _ => sameLen) cpaCodec ciCodec candidate :=
  constUnitCipher_aead (fun _ => Unit) (fun _ => sameLen) cpaCodec ciCodec candidate

-- A `Correct` cipher can satisfy `INDCPA` without rejecting decryptions.
example (valid : ∀ _n : ℕ, Unit → Unit → Bool)
    (codec : ∀ _n : ℕ, OracleCodec Unit (MessagePair Unit × Unit × Unit) fun _ => Unit) :
    unitMsgCipher.Correct ∧
      NonceCipher.INDCPA (fun _ => unitMsgCipher) (fun _ => pure ()) valid codec := by
  refine ⟨fun _ _ _ _ => rfl, fun W _ => ?_⟩
  simp [NonceCipher.cpaExperiment, unitMsgCipher]

-- Unfolding `INDCPA`, `CiphertextIntegrity`, and `AEAD` to level-`n` experiments across `module`.
example {K M D C N : ℕ → Type} [∀ n, DecidableEq (C n)] [∀ n, DecidableEq (D n)]
    [∀ n, DecidableEq (N n)] (E : ∀ n, NonceCipher (K n) (M n) (D n) (C n) (N n))
    (sampleKey : ∀ n, ProbComp (K n)) (valid : ∀ n, M n → M n → Bool)
    (cpaCodec : ∀ n, OracleCodec Unit (MessagePair (M n) × D n × N n) fun _ => C n)
    (ciCodec : ∀ n, OracleCodec Unit (M n × D n × N n) fun _ => C n)
    (candidate : ∀ n, List Bool → C n × D n × N n)
    (h : NonceCipher.AEAD E sampleKey valid cpaCodec ciCodec candidate) :
    (∀ W : ℕ → List Bool → WordOracleComp Unit Bool, IsOraclePPT encBool W →
      Negligible (fun n => Experiment.advantage
        ((E n).cpaExperiment (sampleKey n) (valid n) ((cpaCodec n).adapt (W n [])) false)
        ((E n).cpaExperiment (sampleKey n) (valid n) ((cpaCodec n).adapt (W n [])) true))) ∧
    (∀ W : ℕ → List Bool → WordOracleComp Unit (List Bool), IsOraclePPT encBits W →
      Negligible (fun n => Experiment.succProbability
        ((E n).ciExperiment (sampleKey n) (candidate n <$> (ciCodec n).adapt (W n []))))) := by
  refine ⟨fun W hW => h.cpa W hW, fun W hW => ?_⟩
  simpa [Experiment.succProbability, Game.advantage_pure_false] using h.ci W hW

end CslibFrontierTests.Crypto.NonceCipher
