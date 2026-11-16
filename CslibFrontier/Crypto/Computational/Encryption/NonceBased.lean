/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState

/-!
# Deterministic nonce-based encryption and AEAD

Deterministic nonce-based ciphers ([BonehShoup2023], Sections 5.5 and 9.5) take a key, plaintext,
associated data, and nonce, returning a ciphertext without fresh randomness. Decryption takes the
key, ciphertext, associated data, and nonce, returning `none` when a ciphertext is rejected.
Setting `D := Unit` specializes the interface to a deterministic nonce-based cipher without
associated data ([BonehShoup2023], Section 5.5).

Security is phrased as generic typed experiments lifted to uniform word-channel oracle-PPT
adversaries (`IsOraclePPT`) via `OracleCodec.adapt`:

* `NonceCipher.cpaExperiment` and `NonceCipher.INDCPA` capture adaptive chosen-plaintext security
  ([BonehShoup2023], Attack Game 5.3 and Definition 5.3, printed pp. 201–202; Definition 9.7,
  printed pp. 377–378). The adversary supplies challenge pairs `(m₀, m₁)` together with associated
  data and a nonce; a run that submits an inadmissible pair or repeats a queried nonce outputs
  `false` for both challenge bits, so its trace contributes zero distinguishing advantage.
* `NonceCipher.ciExperiment` and `NonceCipher.CiphertextIntegrity` capture ciphertext integrity
  with associated data ([BonehShoup2023], Attack Game 9.3 and Definition 9.8, printed p. 378).
  A run wins when queried nonces are distinct, the candidate `(c, d, n)` decrypts to `some m`, and
  `(c, d, n)` did not appear among the encryption oracle's `(ciphertext, associatedData, nonce)`
  responses. (On p. 378 of [BonehShoup2023], Attack Game 9.3 omits `N` from the rejection set and
  decryption line, whereas the surrounding text on p. 378 explicitly states the triple condition.)
* `NonceCipher.AEAD` packages `INDCPA` and `CiphertextIntegrity` for authenticated encryption with
  associated data ([BonehShoup2023], Definition 9.9, printed p. 379).

This module defines the interface and security notions over arbitrary types and key samplers;
uniform polynomial-time certificates for specific cipher algorithms belong with their concrete
constructions.

## Main definitions

* `Cslib.Crypto.NonceCipher`: deterministic nonce-based cipher with associated data.
* `Cslib.Crypto.NonceCipher.Correct`: decryption completeness under matching keys, associated data,
  and nonces.
* `Cslib.Crypto.NonceCipher.cpaExperiment`, `Cslib.Crypto.NonceCipher.INDCPA`: left-or-right CPA
  experiment and security for nonce-respecting adversaries.
* `Cslib.Crypto.NonceCipher.ciExperiment`, `Cslib.Crypto.NonceCipher.CiphertextIntegrity`:
  ciphertext integrity experiment and security with associated data.
* `Cslib.Crypto.NonceCipher.AEAD`: combined IND-CPA security and ciphertext integrity.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.5 (Attack Game 5.3 and Definition 5.3, printed pp. 201–202) and Section 9.5
  (Attack Game 9.3 and Definitions 9.7–9.9, printed pp. 377–379).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- A deterministic nonce-based symmetric cipher with associated data ([BonehShoup2023],
Section 9.5, printed p. 377). Specialize `D := Unit` for a deterministic nonce-based cipher
without associated data ([BonehShoup2023], Section 5.5, printed p. 201). -/
structure NonceCipher (K M D C N : Type) where
  /-- Deterministic encryption mapping a key, plaintext, associated data, and nonce to a
  ciphertext. -/
  encrypt : K → M → D → N → C
  /-- Deterministic decryption mapping a key, ciphertext, associated data, and nonce to `some m`,
  or `none` on rejection. -/
  decrypt : K → C → D → N → Option M

namespace NonceCipher

/-- Decryption completeness ([BonehShoup2023], Sections 5.5 and 9.5, printed pp. 201 and 377):
decrypting `E.encrypt k m d n` under the same key, associated data, and nonce yields `some m`. -/
def Correct {K M D C N : Type} (E : NonceCipher K M D C N) : Prop :=
  ∀ k m d n, E.decrypt k (E.encrypt k m d n) d n = some m

/-- The nonce-based chosen-plaintext experiment ([BonehShoup2023], Section 5.5, Attack Game 5.3,
printed pp. 201–202, and Section 9.5, printed pp. 377–378). Under a key drawn from `sampleKey`,
each query `(pair, d, n) : MessagePair M × D × N` returns `E.encrypt k (pair.select b) d n`.
If any queried message pair fails `valid` or two queries reuse a nonce, the experiment outputs
`false` for both challenge bits `b`. -/
def cpaExperiment {K M D C N : Type} [DecidableEq N] (E : NonceCipher K M D C N)
    (sampleKey : ProbComp K) (valid : M → M → Bool)
    (A : ProbOracleComp (fun _ : MessagePair M × D × N => C) Bool) (b : Bool) : Experiment := do
  let k ← sampleKey
  let (guess, trace) ← A.runLog fun (pair, d, n) => pure (E.encrypt k (pair.select b) d n)
  return guess && trace.all (fun ((pair, _, _), _) => valid pair.msg₀ pair.msg₁) &&
    decide (trace.map fun ((_, _, n), _) => n).Nodup

/-- The nonce-based ciphertext-integrity experiment ([BonehShoup2023], Section 9.5, Attack
Game 9.3, printed p. 378). Under a key drawn from `sampleKey`, each query
`(m, d', n') : M × D × N` returns `E.encrypt k m d' n'`. The adversary outputs a candidate
`(c, d, n)` and wins if `E.decrypt k c d n` is `some _`, `(c, d, n)` was not returned for
`(d, n)` by an encryption query, and all encryption queries used distinct nonces. -/
def ciExperiment {K M D C N : Type} [DecidableEq C] [DecidableEq D] [DecidableEq N]
    (E : NonceCipher K M D C N) (sampleKey : ProbComp K)
    (A : ProbOracleComp (fun _ : M × D × N => C) (C × D × N)) : Experiment := do
  let k ← sampleKey
  let ((c, d, n), trace) ← A.runLog fun (m, d', n') => pure (E.encrypt k m d' n')
  return (E.decrypt k c d n).isSome &&
    decide ((c, d, n) ∉ trace.map fun ((_, d', n'), c') => (c', d', n')) &&
    decide (trace.map fun ((_, _, n'), _) => n').Nodup

/-- Chosen-plaintext security for a family of nonce-based ciphers ([BonehShoup2023], Section 5.5,
Definition 5.3, printed p. 202; Section 9.5, Definition 9.7, printed p. 378): every uniform
oracle-PPT distinguisher adapted via `codec` has negligible advantage between challenge bits
`false` and `true`. -/
def INDCPA {K M D C N : ℕ → Type} [∀ n, DecidableEq (N n)]
    (E : ∀ n, NonceCipher (K n) (M n) (D n) (C n) (N n)) (sampleKey : ∀ n, ProbComp (K n))
    (valid : ∀ n, M n → M n → Bool)
    (codec : ∀ n, OracleCodec Unit (MessagePair (M n) × D n × N n) fun _ => C n) : Prop :=
  Game.Indistinguishable
    (fun W n => ProbComp.eval
      ((E n).cpaExperiment (sampleKey n) (valid n) ((codec n).adapt (W n [])) false))
    (fun W n => ProbComp.eval
      ((E n).cpaExperiment (sampleKey n) (valid n) ((codec n).adapt (W n [])) true))
    (fun W : ℕ → List Bool → WordOracleComp Unit Bool => IsOraclePPT encBool W)

/-- Ciphertext integrity for a family of nonce-based ciphers ([BonehShoup2023], Section 9.5,
Definition 9.8, printed p. 378): every uniform oracle-PPT forger adapted via `codec` and decoded
by `candidate` has negligible probability of producing a valid fresh `(c, d, n)` triple in
`ciExperiment`. -/
def CiphertextIntegrity {K M D C N : ℕ → Type}
    [∀ n, DecidableEq (C n)] [∀ n, DecidableEq (D n)] [∀ n, DecidableEq (N n)]
    (E : ∀ n, NonceCipher (K n) (M n) (D n) (C n) (N n)) (sampleKey : ∀ n, ProbComp (K n))
    (codec : ∀ n, OracleCodec Unit (M n × D n × N n) fun _ => C n)
    (candidate : ∀ n, List Bool → C n × D n × N n) : Prop :=
  Game.Indistinguishable
    (fun W n => ProbComp.eval
      ((E n).ciExperiment (sampleKey n) (candidate n <$> (codec n).adapt (W n []))))
    (fun _ _ => PMF.pure false)
    (fun W : ℕ → List Bool → WordOracleComp Unit (List Bool) => IsOraclePPT encBits W)

/-- Authenticated encryption with associated data ([BonehShoup2023], Section 9.5, Definition 9.9,
printed p. 379): a nonce-based cipher is AEAD-secure when it satisfies both `INDCPA` and
`CiphertextIntegrity`. -/
structure AEAD {K M D C N : ℕ → Type}
    [∀ n, DecidableEq (C n)] [∀ n, DecidableEq (D n)] [∀ n, DecidableEq (N n)]
    (E : ∀ n, NonceCipher (K n) (M n) (D n) (C n) (N n)) (sampleKey : ∀ n, ProbComp (K n))
    (valid : ∀ n, M n → M n → Bool)
    (cpaCodec : ∀ n, OracleCodec Unit (MessagePair (M n) × D n × N n) fun _ => C n)
    (ciCodec : ∀ n, OracleCodec Unit (M n × D n × N n) fun _ => C n)
    (candidate : ∀ n, List Bool → C n × D n × N n) : Prop where
  /-- Left-or-right chosen-plaintext security against nonce-respecting adversaries. -/
  cpa : INDCPA E sampleKey valid cpaCodec
  /-- Integrity against ciphertext-tag-associated-data forgeries. -/
  ci : CiphertextIntegrity E sampleKey ciCodec candidate

end NonceCipher

end Cslib.Crypto
