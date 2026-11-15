/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Salted.Correctness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Computability.Probabilistic.RandomOracle.Programming
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Composition

/-!
# Word view of the concrete salted FO correctness handlers

This module carries the typed post-secret-seed-guessing salted Fujisaki--Okamoto `CORR` handler
over word-oracle requests. The three channels remain distinct: `joint` carries the public
prefix, message and salt and returns the framed `(key, coins)` reply; `rejection` carries the
public rejection prefix, secret seed and full salted ciphertext; and `decaps` carries the full
salted ciphertext. Malformed word requests decode to no typed query and receive `[]` without a
typed oracle call.

`WordQueryBounds` keeps the joint-`G` and decapsulation coordinates used by `CORR`, where rejection
costs zero because it cannot create a decryption-failure witness. `WordROQueryBounds` uses one
combined tagged-random-oracle budget for `G` and `J`, while `WordSecurityQueryBounds` keeps the
complete source split `(qG, qJ, qD)`. Adapting through `wordQueryCodec` preserves both conventions
exactly, and the joint plus rejection bounds give a combined random-oracle budget `qG + qJ`.

`programmedWordHandler` routes each source operation through the shared programmable-random-oracle
component without changing the adversary program. Its whole-run theorem therefore derives strict
PPT from the adversary's `IsOraclePPT` certificate while retaining the independent source query
coordinates. The theorem does not manufacture a finite machine description from that existential
certificate; the concrete HQC reduction must separately supply a retained native program and
charge its installed description.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.WordOperation`: the joint, rejection and
  decapsulation word channels.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.encJointInput`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.encJointReply`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.encCiphertext` and
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.encRejectionInput`: framed word layouts of the
  source-shaped queries and joint reply.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.wordQueryCodec`: the typed view of the three word
  channels.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.WordSecurityQueryBounds`: separate joint-`G`,
  rejection-`J` and decapsulation budgets at the word boundary.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.WordROQueryBounds`: one combined tagged
  random-oracle budget plus a separate decapsulation budget.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.WordRandomizedAdversary`: a challenge-aware
  randomized word adversary derived into the finite typed interface.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.simWordHandler`: the word view of the
  concrete keyless handler.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.programmedWordHandler`: source-operation adapter
  for the shared programmable-oracle handler.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.programmedWordResources`: the checked maximum of
  the shared programming charge over the three source operations.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.WordQueryBounds.adapt`: transport the separate
  word-level budgets to the typed correctness interface.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.WordSecurityQueryBounds.adapt`: transport the
  complete `(qG, qJ, qD)` split to the typed security interface.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.WordROQueryBounds.adapt`: transport the combined
  tagged-random-oracle convention to the typed security interface.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.simWordHandler_decaps_challenge`: the
  word handler rejects the punctured challenge without changing its cache.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.run_simWordHandler`: exact joint
  result/cache law of deterministic word and finite typed keyless executions.
* `Scheme.advantage_randomizedRealWordHandler_simWordHandler_le`:
  the finite-carrier randomized word-level `CORR` bound.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.isPPTOn_run_programmedWordHandler`: strict-PPT
  execution derived from a source adversary certificate and the three-operation resource maximum.

## References

* [Glabush--Hövelmanns--Stebila, Theorem 11 and Figure 11][GlabushHoevelmannsStebila2025].
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto.Salted

open Probability
open Turing.MultiTapeTM

variable {PK SK JointPrefix M Salt RejectPrefix Sigma CT K R : Type}

/-- Word-oracle operations of the salted implicit-rejection CCA experiment. -/
inductive WordOperation where
  /-- Query the fused key-and-encryption-coin oracle. -/
  | joint
  /-- Query the independent implicit-rejection oracle. -/
  | rejection
  /-- Query challenge-punctured decapsulation. -/
  | decaps
  deriving DecidableEq

instance : FinEnum WordOperation :=
  FinEnum.ofList [.joint, .rejection, .decaps] (by intro op; cases op <;> simp)

/-- Unary-rank encoding of the three salted-FO word operations, in the order joint, rejection,
decapsulation. -/
abbrev encWordOperation : WordOperation ↪ List Bool := encFinEnum WordOperation

/-- Encoding of a joint-oracle input: framed public prefix, framed message, then salt. -/
enc_structure encJointInput (encJointPrefix : JointPrefix ↪ List Bool)
    (encM : M ↪ List Bool) (encSalt : Salt ↪ List Bool) :
    JointInput JointPrefix M Salt where
  keyPrefix : encJointPrefix, message : encM, salt : encSalt

/-- Encoding of one joint reply: framed session key, then encryption coins. -/
@[expose] def encJointReply (encK : K ↪ List Bool) (encR : R ↪ List Bool) :
    JointReply K R ↪ List Bool :=
  ⟨fun reply => encPair encK encR (reply.key, reply.coins), fun _ _ h => by
    have fields := (encPair encK encR).injective h
    exact congrArg (fun pair : K × R => (⟨pair.1, pair.2⟩ : JointReply K R)) fields⟩

/-- Encoding of a salted ciphertext: framed PKE ciphertext, then salt. -/
@[expose] def encCiphertext (encCT : CT ↪ List Bool) (encSalt : Salt ↪ List Bool) :
    Ciphertext CT Salt ↪ List Bool :=
  ⟨fun ciphertext => encPair encCT encSalt (ciphertext.pke, ciphertext.salt), fun _ _ h => by
    have fields := (encPair encCT encSalt).injective h
    exact congrArg (fun pair : CT × Salt => (⟨pair.1, pair.2⟩ : Ciphertext CT Salt)) fields⟩

/-- Encoding of an implicit-rejection input: framed public prefix, framed secret seed, then the
salted ciphertext encoding. -/
enc_structure encRejectionInput (encRejectPrefix : RejectPrefix ↪ List Bool)
    (encSigma : Sigma ↪ List Bool) (encCT : CT ↪ List Bool) (encSalt : Salt ↪ List Bool) :
    RejectionInput RejectPrefix Sigma CT Salt where
  keyPrefix : encRejectPrefix, secret : encSigma, ciphertext : (encCiphertext encCT encSalt)

/-- Total decoder for a framed joint-oracle input. -/
def jointInputDecoder {encJointPrefix : JointPrefix ↪ List Bool} {encM : M ↪ List Bool}
    {encSalt : Salt ↪ List Bool} (jointPrefix : Decoder encJointPrefix)
    (message : Decoder encM) (salt : Decoder encSalt) :
    Decoder (encJointInput encJointPrefix encM encSalt) :=
  (jointPrefix.pair (message.pair salt)).map
    (fun ⟨keyPrefix, message, salt⟩ => ⟨keyPrefix, message, salt⟩)
    (fun input => (input.keyPrefix, input.message, input.salt))
    (by rintro ⟨_, _, _⟩; rfl) (by rintro ⟨_, _, _⟩; rfl)

/-- Total decoder for a framed salted ciphertext. -/
def ciphertextDecoder {encCT : CT ↪ List Bool} {encSalt : Salt ↪ List Bool}
    (ciphertext : Decoder encCT) (salt : Decoder encSalt) :
    Decoder (encCiphertext encCT encSalt) :=
  (ciphertext.pair salt).map (fun fields => ⟨fields.1, fields.2⟩)
    (fun ciphertext => (ciphertext.pke, ciphertext.salt)) (by rintro ⟨_, _⟩; rfl)
    (by rintro ⟨_, _⟩; rfl)

/-- Total decoder for a framed implicit-rejection input. -/
def rejectionInputDecoder {encRejectPrefix : RejectPrefix ↪ List Bool}
    {encSigma : Sigma ↪ List Bool} {encCT : CT ↪ List Bool} {encSalt : Salt ↪ List Bool}
    (rejectPrefix : Decoder encRejectPrefix) (sigma : Decoder encSigma)
    (ciphertext : Decoder (encCiphertext encCT encSalt)) :
    Decoder (encRejectionInput encRejectPrefix encSigma encCT encSalt) :=
  (rejectPrefix.pair (sigma.pair ciphertext)).map
    (fun ⟨keyPrefix, secret, ciphertext⟩ => ⟨keyPrefix, secret, ciphertext⟩)
    (fun input => (input.keyPrefix, input.secret, input.ciphertext))
    (by rintro ⟨_, _, _⟩; rfl) (by rintro ⟨_, _, _⟩; rfl)

/-- The request carrying a typed salted-FO query on the three word channels. -/
@[expose] def wordRequest (encJointPrefix : JointPrefix ↪ List Bool) (encM : M ↪ List Bool)
    (encSalt : Salt ↪ List Bool) (encRejectPrefix : RejectPrefix ↪ List Bool)
    (encSigma : Sigma ↪ List Bool) (encCT : CT ↪ List Bool) :
    Query JointPrefix M Salt RejectPrefix Sigma CT →
      WordOperation × List Bool
  | .joint input => (.joint, encJointInput encJointPrefix encM encSalt input)
  | .rejection input =>
    (.rejection, encRejectionInput encRejectPrefix encSigma encCT encSalt input)
  | .decaps ciphertext => (.decaps, encCiphertext encCT encSalt ciphertext)

/-- Canonical typed view of the three salted-FO word channels. Replies preserve the source field
order: joint replies encode the key before the coins, rejection replies are keys, and
decapsulation replies are optional keys. -/
@[expose] def wordQueryCodec {encJointPrefix : JointPrefix ↪ List Bool}
    {encM : M ↪ List Bool} {encSalt : Salt ↪ List Bool}
    {encRejectPrefix : RejectPrefix ↪ List Bool} {encSigma : Sigma ↪ List Bool}
    {encCT : CT ↪ List Bool} (joint : Decoder (encJointInput encJointPrefix encM encSalt))
    (rejection : Decoder (encRejectionInput encRejectPrefix encSigma encCT encSalt))
    (ciphertext : Decoder (encCiphertext encCT encSalt)) (encK : K ↪ List Bool)
    (encR : R ↪ List Bool) : OracleCodec WordOperation
      (Query JointPrefix M Salt RejectPrefix Sigma CT) (Response K R) where
  encodeQuery := wordRequest encJointPrefix encM encSalt encRejectPrefix encSigma encCT
  decodeQuery
    | (.joint, word) => (joint.decodeCanonical word).map Query.joint
    | (.rejection, word) => (rejection.decodeCanonical word).map Query.rejection
    | (.decaps, word) => (ciphertext.decodeCanonical word).map Query.decaps
  decodeQuery_eq_some_iff request q := by
    rcases request with ⟨operation, word⟩
    cases operation <;> cases q <;>
      simp [wordRequest, Decoder.decodeCanonical_eq_some_iff]
  encodeReply
    | .joint _ => encJointReply encK encR
    | .rejection _ => encK
    | .decaps _ => encOption encK

/-- Cost of a word request in the joint-oracle coordinate. One framed `(key, coins)` response
still costs one request. -/
@[expose, simp] def wordJointCost : WordOperation × List Bool → ℕ
  | (.joint, _) => 1
  | (.rejection, _) => 0
  | (.decaps, _) => 0

/-- Cost of a word request in the combined random-oracle coordinate. Both the joint `G` channel
and the separate rejection `J` channel cost one. -/
@[expose, simp] def wordROCost : WordOperation × List Bool → ℕ
  | (.joint, _) => 1
  | (.rejection, _) => 1
  | (.decaps, _) => 0

/-- Cost of a word request in the separate implicit-rejection `J` coordinate. -/
@[expose, simp] def wordRejectionCost : WordOperation × List Bool → ℕ
  | (.joint, _) => 0
  | (.rejection, _) => 1
  | (.decaps, _) => 0

/-- Cost of a word request in the decapsulation coordinate. -/
@[expose, simp] def wordDecapsCost : WordOperation × List Bool → ℕ
  | (.joint, _) => 0
  | (.rejection, _) => 0
  | (.decaps, _) => 1

/-- Independent joint-oracle and decapsulation budgets for a deterministic word-level salted-FO
program. Randomized adversaries apply these bounds after fixing their private random tape. -/
@[expose] def WordQueryBounds {α : Type}
    (program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α)
    (qG qD : ℕ) : Prop :=
  OracleComp.IsCostBounded wordJointCost program qG ∧
    OracleComp.IsCostBounded wordDecapsCost program qD

/-- Security-level word bounds with separate joint-`G`, rejection-`J` and decapsulation
coordinates. -/
@[expose] def WordSecurityQueryBounds {α : Type}
    (program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α)
    (qG qJ qD : ℕ) : Prop :=
  OracleComp.IsCostBounded wordJointCost program qG ∧
    OracleComp.IsCostBounded wordRejectionCost program qJ ∧
    OracleComp.IsCostBounded wordDecapsCost program qD

/-- One combined budget for the tagged word-level `G` and `J` channels, with a separate
decapsulation budget. -/
@[expose] def WordROQueryBounds {α : Type}
    (program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α)
    (qRO qD : ℕ) : Prop :=
  OracleComp.IsCostBounded wordROCost program qRO ∧
    OracleComp.IsCostBounded wordDecapsCost program qD

namespace WordSecurityQueryBounds

/-- The combined random-oracle budget implies the joint-only budget consumed by `CORR`. -/
theorem toWordQueryBounds {α : Type}
    {program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α} {qG qJ qD : ℕ}
    (h : WordSecurityQueryBounds program qG qJ qD) : WordQueryBounds program qG qD :=
  ⟨h.1, h.2.2⟩

/-- The separate word `G` and `J` bounds give a combined budget `qG + qJ`. -/
theorem roCostBounded {α : Type}
    {program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α} {qG qJ qD : ℕ}
    (h : WordSecurityQueryBounds program qG qJ qD) :
    OracleComp.IsCostBounded wordROCost program (qG + qJ) := by
  convert h.1.add h.2.1 using 1
  funext request
  rcases request with ⟨operation, word⟩
  cases operation <;> rfl

/-- Adapting a word program preserves the combined `G`/`J` and decapsulation budgets. -/
theorem adapt {α : Type}
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (hjoint : ∀ q, wordJointCost (codec.encodeQuery q) = Query.jointCost q)
    (hrejection : ∀ q, wordRejectionCost (codec.encodeQuery q) = Query.rejectionCost q)
    (hdecaps : ∀ q, wordDecapsCost (codec.encodeQuery q) = Query.decapsCost q)
    {program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α} {qG qJ qD : ℕ}
    (h : WordSecurityQueryBounds program qG qJ qD) :
    SecurityQueryBounds (codec.adaptOracle program) qG qJ qD := by
  refine ⟨codec.isCostBounded_adaptOracle (wordCost := wordJointCost) ?_ h.1,
    codec.isCostBounded_adaptOracle (wordCost := wordRejectionCost) ?_ h.2.1,
    codec.isCostBounded_adaptOracle (wordCost := wordDecapsCost) ?_ h.2.2⟩
  · intro query
    rw [hjoint query]
  · intro query
    rw [hrejection query]
  · intro query
    rw [hdecaps query]

end WordSecurityQueryBounds

namespace WordROQueryBounds

/-- A combined word `qRO` budget implies separate `qRO` upper bounds for `G` and `J`. -/
theorem toWordSecurityQueryBounds {α : Type}
    {program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α} {qRO qD : ℕ}
    (h : WordROQueryBounds program qRO qD) :
    WordSecurityQueryBounds program qRO qRO qD :=
  ⟨h.1.of_le fun request => by rcases request with ⟨operation, word⟩; cases operation <;> simp,
    h.1.of_le fun request => by rcases request with ⟨operation, word⟩; cases operation <;> simp,
    h.2⟩

/-- A combined word random-oracle budget implies the joint-only budget consumed by `CORR`. -/
theorem toWordQueryBounds {α : Type}
    {program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α} {qRO qD : ℕ}
    (h : WordROQueryBounds program qRO qD) : WordQueryBounds program qRO qD :=
  h.toWordSecurityQueryBounds.toWordQueryBounds

/-- Adapting a word program preserves the combined tagged-random-oracle and decapsulation
budgets. -/
theorem adapt {α : Type}
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (hro : ∀ q, wordROCost (codec.encodeQuery q) = Query.roCost q)
    (hdecaps : ∀ q, wordDecapsCost (codec.encodeQuery q) = Query.decapsCost q)
    {program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α} {qRO qD : ℕ}
    (h : WordROQueryBounds program qRO qD) :
    ROQueryBounds (codec.adaptOracle program) qRO qD := by
  refine ⟨codec.isCostBounded_adaptOracle (wordCost := wordROCost) ?_ h.1,
    codec.isCostBounded_adaptOracle (wordCost := wordDecapsCost) ?_ h.2⟩
  · intro q
    rw [hro q]
  · intro q
    rw [hdecaps q]

end WordROQueryBounds

namespace WordQueryBounds

/-- Adapting a word program to the typed salted-FO interface preserves the independent joint and
decapsulation budgets. -/
theorem adapt {α : Type}
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (hjoint : ∀ q, wordJointCost (codec.encodeQuery q) = Query.jointCost q)
    (hdecaps : ∀ q, wordDecapsCost (codec.encodeQuery q) = Query.decapsCost q)
    {program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α} {qG qD : ℕ}
    (h : WordQueryBounds program qG qD) :
    QueryBounds (codec.adaptOracle program) qG qD := by
  refine ⟨codec.isCostBounded_adaptOracle (wordCost := wordJointCost) ?_ h.1,
    codec.isCostBounded_adaptOracle (wordCost := wordDecapsCost) ?_ h.2⟩
  · intro q
    rw [hjoint q]
  · intro q
    rw [hdecaps q]

end WordQueryBounds

/-- A randomized challenge-aware adversary whose deterministic programs use the three word
channels. Its private coins are sampled before the public KEM challenge, as in
`RandomizedAdversary`. -/
structure WordRandomizedAdversary (PK CT Salt K : Type) where
  /-- Type of the adversary's private random tape. -/
  Coins : Type
  /-- Distribution of private random tapes. -/
  coins : ProbComp Coins
  /-- Deterministic word-oracle program after fixing the tape and public challenge. -/
  run : Coins → KEM.Challenge PK (Ciphertext CT Salt) K →
    OracleComp (fun _ : WordOperation × List Bool => List Bool) Bool

namespace WordRandomizedAdversary

/-- Per-random-tape and per-challenge word-level joint-oracle and decapsulation bounds. -/
@[expose] def QueryBounded (A : WordRandomizedAdversary PK CT Salt K)
    (qG qD : ℕ) : Prop :=
  ∀ coins challenge, WordQueryBounds (A.run coins challenge) qG qD

/-- Per-random-tape and per-challenge word security bounds, counting both `G` and `J`. -/
@[expose] def SecurityQueryBounded (A : WordRandomizedAdversary PK CT Salt K)
    (qG qJ qD : ℕ) : Prop :=
  ∀ coins challenge, WordSecurityQueryBounds (A.run coins challenge) qG qJ qD

/-- Per-random-tape and per-challenge combined tagged-random-oracle and decapsulation bounds. -/
@[expose] def ROQueryBounded (A : WordRandomizedAdversary PK CT Salt K)
    (qRO qD : ℕ) : Prop :=
  ∀ coins challenge, WordROQueryBounds (A.run coins challenge) qRO qD

/-- Interpret a word adversary over the finite typed salted-FO query interface. This is an
explicit witness derived from the adversary and codec, not an additional security premise. -/
def toTyped (A : WordRandomizedAdversary PK CT Salt K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R)) :
    RandomizedAdversary PK JointPrefix M Salt RejectPrefix Sigma CT K R where
  Coins := A.Coins
  coins := A.coins
  run coins challenge := codec.adaptOracle (A.run coins challenge)

/-- Word query bounds transport to the derived finite typed adversary. -/
theorem queryBounded_toTyped (A : WordRandomizedAdversary PK CT Salt K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (hjoint : ∀ q, wordJointCost (codec.encodeQuery q) = Query.jointCost q)
    (hdecaps : ∀ q, wordDecapsCost (codec.encodeQuery q) = Query.decapsCost q)
    {qG qD : ℕ} (h : A.QueryBounded qG qD) :
    (A.toTyped codec).QueryBounded qG qD := by
  intro coins challenge
  exact WordQueryBounds.adapt codec hjoint hdecaps (h coins challenge)

/-- Combined word security bounds transport to the derived finite typed adversary. -/
theorem securityQueryBounded_toTyped (A : WordRandomizedAdversary PK CT Salt K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (hjoint : ∀ q, wordJointCost (codec.encodeQuery q) = Query.jointCost q)
    (hrejection : ∀ q, wordRejectionCost (codec.encodeQuery q) = Query.rejectionCost q)
    (hdecaps : ∀ q, wordDecapsCost (codec.encodeQuery q) = Query.decapsCost q)
    {qG qJ qD : ℕ} (h : A.SecurityQueryBounded qG qJ qD) :
    (A.toTyped codec).SecurityQueryBounded qG qJ qD := by
  intro coins challenge
  exact WordSecurityQueryBounds.adapt codec hjoint hrejection hdecaps (h coins challenge)

/-- Combined word random-oracle bounds transport to the derived finite typed adversary. -/
theorem roQueryBounded_toTyped (A : WordRandomizedAdversary PK CT Salt K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (hro : ∀ q, wordROCost (codec.encodeQuery q) = Query.roCost q)
    (hdecaps : ∀ q, wordDecapsCost (codec.encodeQuery q) = Query.decapsCost q)
    {qRO qD : ℕ} (h : A.ROQueryBounded qRO qD) :
    (A.toTyped codec).ROQueryBounded qRO qD := by
  intro coins challenge
  exact WordROQueryBounds.adapt codec hro hdecaps (h coins challenge)

end WordRandomizedAdversary

namespace Scheme

/-- The word view of the concrete decrypt/re-encrypt salted-FO handler. -/
@[expose] noncomputable def realWordHandler
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt) :
    WordOperation × List Bool →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (List Bool) :=
  codec.wordOracle (S.realHandler pk sk challenge)

/-- The word view of the concrete keyless salted-FO handler. Requests carrying no typed query are
answered with `[]` and do not change the cache. This definition carries no efficiency claim. -/
@[expose] noncomputable def simWordHandler
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (pk : PK) (challenge : Ciphertext CT Salt) :
    WordOperation × List Bool →
      StateT (CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) PMF (List Bool) :=
  codec.wordOracle (S.simHandler pk challenge)

/-- The punctured word handler rejects its challenge ciphertext without changing the state. -/
@[simp] theorem simWordHandler_decaps_challenge
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (pk : PK) (challenge : Ciphertext CT Salt)
    (st : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    S.simWordHandler codec pk challenge (codec.encodeQuery (.decaps challenge)) st =
      PMF.pure (codec.encodeReply (.decaps challenge) none, st) := by
  rw [simWordHandler, codec.wordOracle_encodeQuery]
  change ((codec.encodeReply (.decaps challenge) <$>
      S.simHandler pk challenge (.decaps challenge)).run st) = _
  rw [StateT.run_map]
  change (fun p => (codec.encodeReply (.decaps challenge) p.1, p.2)) <$>
      S.simHandler pk challenge (.decaps challenge) st = _
  rw [S.simHandler_decaps_challenge pk challenge st]
  rw [PMF.monad_map_eq_map, PMF.pure_map]

/-- Running a deterministic word program against `realWordHandler` has exactly the joint
result/cache law of its typed adaptation against `realHandler`. -/
theorem run_realWordHandler
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    {α : Type} (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (pk : PK) (sk : SK) (challenge : Ciphertext CT Salt)
    (program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α)
    (initial : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    (OracleComp.interpret (S.realHandler pk sk challenge)
        (codec.adaptOracle program)).run initial =
      (OracleComp.interpret (S.realWordHandler codec pk sk challenge) program).run initial := by
  rw [codec.interpret_adaptOracle]
  rfl

/-- Running a deterministic word program against `simWordHandler` has exactly the joint
result/cache law of its typed adaptation against `simHandler`. -/
theorem run_simWordHandler
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    {α : Type}
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (pk : PK) (challenge : Ciphertext CT Salt)
    (program : OracleComp (fun _ : WordOperation × List Bool => List Bool) α)
    (initial : CacheState JointPrefix M Salt RejectPrefix Sigma CT K R) :
    (OracleComp.interpret (S.simHandler pk challenge)
        (codec.adaptOracle program)).run initial =
      (OracleComp.interpret (S.simWordHandler codec pk challenge) program).run initial := by
  rw [codec.interpret_adaptOracle]
  rfl

/-- Run a challenge-aware word adversary against the post-secret-seed-guessing real handler. -/
noncomputable def randomizedRealWordHandlerGame
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : WordRandomizedAdversary PK CT Salt K) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup keys.1)).bind fun challenge =>
        ((OracleComp.interpret (S.realWordHandler codec keys.1 keys.2 challenge.1)
          (A.run coins ⟨keys.1, challenge.1, challenge.2⟩)).run {}).map Prod.fst

/-- Run the same challenge-aware word adversary against the keyless handler. -/
noncomputable def randomizedSimWordHandlerGame
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : WordRandomizedAdversary PK CT Salt K) : PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
    (ProbComp.eval A.coins).bind fun coins =>
      (ProbComp.eval (challengeSetup keys.1)).bind fun challenge =>
        ((OracleComp.interpret (S.simWordHandler codec keys.1 challenge.1)
          (A.run coins ⟨keys.1, challenge.1, challenge.2⟩)).run {}).map Prod.fst

/-- The word real-handler game is exactly the finite typed real-handler game of the adversary
derived by `WordRandomizedAdversary.toTyped`. -/
theorem randomizedRealWordHandlerGame_eq
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : WordRandomizedAdversary PK CT Salt K) :
    S.randomizedRealWordHandlerGame codec challengeSetup A =
      S.randomizedRealHandlerGame challengeSetup (A.toTyped codec) := by
  unfold randomizedRealWordHandlerGame Scheme.randomizedRealHandlerGame
    WordRandomizedAdversary.toTyped
  simp_rw [S.run_realWordHandler]

/-- The word simulated-handler game is exactly the finite typed simulated-handler game of the
adversary derived by `WordRandomizedAdversary.toTyped`. -/
theorem randomizedSimWordHandlerGame_eq
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : WordRandomizedAdversary PK CT Salt K) :
    S.randomizedSimWordHandlerGame codec challengeSetup A =
      S.randomizedSimHandlerGame challengeSetup (A.toTyped codec) := by
  unfold randomizedSimWordHandlerGame Scheme.randomizedSimHandlerGame
    WordRandomizedAdversary.toTyped
  simp_rw [S.run_simWordHandler]

/-- **Finite-carrier word-level salted-FO `CORR` hop.** A randomized word adversary with separate
`qG` and `qD` bounds inherits the concrete typed bound. The finite instances belong to the
source carriers; the unbounded request words are only an executable boundary. -/
theorem advantage_randomizedRealWordHandler_simWordHandler_le
    [Finite JointPrefix] [Fintype M] [Nonempty M] [Finite Salt] [Finite RejectPrefix]
    [Finite Sigma] [Finite CT] [Finite K] [Finite R]
    [DecidableEq (JointInput JointPrefix M Salt)]
    [DecidableEq (RejectionInput RejectPrefix Sigma CT Salt)]
    [DecidableEq (Ciphertext CT Salt)]
    (S : Scheme PK SK M R CT JointPrefix Salt RejectPrefix Sigma K)
    (codec : OracleCodec WordOperation (Query JointPrefix M Salt RejectPrefix Sigma CT)
      (Response K R))
    (challengeSetup : PK → ProbComp (Ciphertext CT Salt × K))
    (A : WordRandomizedAdversary PK CT Salt K)
    (hjoint : ∀ q, wordJointCost (codec.encodeQuery q) = Query.jointCost q)
    (hdecaps : ∀ q, wordDecapsCost (codec.encodeQuery q) = Query.decapsCost q)
    {qG qD : ℕ} (hbounds : A.QueryBounded qG qD)
    {δ : ℝ} (hδ : S.pke.DeltaCorrect δ) :
    (Game.advantage
      (S.randomizedRealWordHandlerGame codec challengeSetup A)
      (S.randomizedSimWordHandlerGame codec challengeSetup A) : ℝ) ≤
      ((qG + qD : ℕ) : ℝ) * δ := by
  rw [S.randomizedRealWordHandlerGame_eq, S.randomizedSimWordHandlerGame_eq]
  exact S.advantage_randomizedRealHandler_simHandler_le challengeSetup (A.toTyped codec)
    (A.queryBounded_toTyped codec hjoint hdecaps hbounds) hδ

end Scheme

/-! ### Source-operation adapter for the shared programmable word oracle -/

/-- Framed source request carried by the shared `.program` channel. The operation tag remains in
the payload, so joint, rejection and decapsulation are still distinguishable to the inactive and
finishing callbacks. -/
@[expose] def programmingPayload (request : WordOperation × List Bool) : List Bool :=
  encPair encWordOperation encBits request

/-- Route one source-shaped salted request through the shared lazy programmable-oracle handler.
The source program itself is unchanged; only its handler receives the framed operation and word
on the shared `.program` channel. -/
@[expose] def programmedWordHandler {Caller Log : Type}
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (caller : Caller) (request : WordOperation × List Bool) :
    StateT (RandomOracle.ProgrammingState Log) ProbComp (List Bool) :=
  RandomOracle.lazyProgramWordHandler dist active inactive samplePre point finish caller
    (.program, programmingPayload request)

/-- The source-operation adapter is strict PPT when the six callbacks of the shared programming
component are. This is a direct preprocessing instance of
`RandomOracle.isPPTOn_lazyProgramWordHandler`. -/
theorem isPPTOn_programmedWordHandler {Caller Log : Type}
    (input : Caller ↪ List Bool) (encLog : Log ↪ List Bool)
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (hdist : Probability.IsPPTOn input encBits dist)
    (hactive : ComputableInPolyTime (fun p : Caller × List Bool => active p.1 p.2)
      (encPair input encBits) encBool)
    (hinactive : Probability.IsPPTOn (encPair (encPair input encBits) encLog)
      (encPair encBits encLog) (fun p => inactive p.1.1 p.1.2 p.2))
    (hsamplePre : Probability.IsPPTOn (encPair input encBits) encBits
      (fun p => samplePre p.1 p.2))
    (hpoint : ComputableInPolyTime
      (fun p : (Caller × List Bool) × List Bool => point p.1.1 p.1.2 p.2)
      (encPair (encPair input encBits) encBits) encBits)
    (hfinish : ComputableInPolyTime
      (fun p : ((((Caller × List Bool) × List Bool) × List Bool) × Log) =>
        finish p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair input encBits) encBits) encBits) encLog)
      (encPair encBits encLog)) :
    Probability.IsPPTOn
      (Probability.encHandlerCall input encWordOperation
        (RandomOracle.encProgrammingState Log encLog))
      (encPair encBits (RandomOracle.encProgrammingState Log encLog))
      (fun p => programmedWordHandler dist active inactive samplePre point finish
        p.1 p.2.1 p.2.2) := by
  have hprepare : ComputableInPolyTime
      (fun p : Caller × (WordOperation × List Bool) × RandomOracle.ProgrammingState Log =>
        (p.1, (RandomOracle.ProgrammingOp.program, programmingPayload p.2.1), p.2.2))
      (Probability.encHandlerCall input encWordOperation
        (RandomOracle.encProgrammingState Log encLog))
      (Probability.encHandlerCall input RandomOracle.encProgrammingOp
        (RandomOracle.encProgrammingState Log encLog)) := by
    unfold programmingPayload
    fun_prop
  have hshared := RandomOracle.isPPTOn_lazyProgramWordHandler input encLog dist active inactive
    samplePre point finish hdist hactive hinactive hsamplePre hpoint hfinish
  exact (hshared.preprocess hprepare).congr fun _ => rfl

/-- Operation-independent resource allowance for the three salted-FO word channels. It is the
maximum of the shared programming charge for the joint, rejection and decapsulation tags, all on
the same request word. -/
@[expose] def programmedWordResources {Caller : Type}
    (digestBound : Caller → ℕ) (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (caller : Caller) (request : List Bool) : ℕ :=
  max
    (RandomOracle.programmingResources digestBound pointBound replyBound logGrowth caller
      (programmingPayload (.joint, request)))
    (max
      (RandomOracle.programmingResources digestBound pointBound replyBound logGrowth caller
        (programmingPayload (.rejection, request)))
      (RandomOracle.programmingResources digestBound pointBound replyBound logGrowth caller
        (programmingPayload (.decaps, request))))

/-- Every tagged salted-FO programming call is bounded by `programmedWordResources`. -/
theorem programmingResources_le_programmedWordResources {Caller : Type}
    (digestBound : Caller → ℕ) (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (caller : Caller) (operation : WordOperation) (request : List Bool) :
    RandomOracle.programmingResources digestBound pointBound replyBound logGrowth caller
        (programmingPayload (operation, request)) ≤
      programmedWordResources digestBound pointBound replyBound logGrowth caller request := by
  cases operation
  · exact Nat.le_max_left _ _
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  · exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

/-- The three-operation maximum is polynomial-time computable from certificates for the four
source bound functions. -/
theorem computableInPolyTime_programmedWordResources {Caller : Type}
    (input : Caller ↪ List Bool) (digestBound : Caller → ℕ)
    (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (hdigestBound : ComputableInPolyTime digestBound input encUnary)
    (hpointBound : ComputableInPolyTime (fun p : Caller × List Bool => pointBound p.1 p.2)
      (encPair input encBits) encUnary)
    (hreplyBound : ComputableInPolyTime (fun p : Caller × List Bool => replyBound p.1 p.2)
      (encPair input encBits) encUnary)
    (hlogGrowth : ComputableInPolyTime (fun p : Caller × List Bool => logGrowth p.1 p.2)
      (encPair input encBits) encUnary) :
    ComputableInPolyTime (fun p : Caller × List Bool =>
      programmedWordResources digestBound pointBound replyBound logGrowth p.1 p.2)
      (encPair input encBits) encUnary := by
  have hshared := RandomOracle.computableInPolyTime_programmingResources input digestBound
    pointBound replyBound logGrowth hdigestBound hpointBound hreplyBound hlogGrowth
  unfold programmedWordResources programmingPayload
  fun_prop

/-- **Adversary-derived strict-PPT salted programming run.** A source `WordOperation` adversary
is executed unchanged against `programmedWordHandler`; hence any independent `qRO` and `qD`
bounds proved about that program remain available. The execution certificate is derived from the
adversary's `IsOraclePPT` proof and the shared #5293(A) handler certificate.

The operation-independent allowance is the checked maximum of the joint, rejection and
decapsulation charges on the same request word. This theorem intentionally makes no
static-description claim: a concrete HQC theorem must additionally retain and charge named native
adversary, reducer and handler artifacts. -/
theorem isPPTOn_run_programmedWordHandler {Caller Log β : Type}
    (input : Caller ↪ List Bool) (output : β ↪ List Bool) (encLog : Log ↪ List Bool)
    (program : ℕ → List Bool → WordOracleComp WordOperation β)
    (dist : Caller → ProbComp (List Bool)) (active : Caller → List Bool → Bool)
    (inactive : Caller → List Bool → Log → ProbComp (List Bool × Log))
    (samplePre : Caller → List Bool → ProbComp (List Bool))
    (point : Caller → List Bool → List Bool → List Bool)
    (finish : Caller → List Bool → List Bool → List Bool → Log → List Bool × Log)
    (prepare : Caller → ℕ × List Bool)
    (initial : Caller → RandomOracle.ProgrammingState Log)
    (digestBound : Caller → ℕ) (pointBound replyBound logGrowth : Caller → List Bool → ℕ)
    (logInvariant : Caller → Log → Prop)
    (hprogram : Probability.IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (hdistPPT : Probability.IsPPTOn input encBits dist)
    (hactivePPT : ComputableInPolyTime (fun p : Caller × List Bool => active p.1 p.2)
      (encPair input encBits) encBool)
    (hinactivePPT : Probability.IsPPTOn (encPair (encPair input encBits) encLog)
      (encPair encBits encLog) (fun p => inactive p.1.1 p.1.2 p.2))
    (hsamplePrePPT : Probability.IsPPTOn (encPair input encBits) encBits
      (fun p => samplePre p.1 p.2))
    (hpointPPT : ComputableInPolyTime
      (fun p : (Caller × List Bool) × List Bool => point p.1.1 p.1.2 p.2)
      (encPair (encPair input encBits) encBits) encBits)
    (hfinishPPT : ComputableInPolyTime
      (fun p : ((((Caller × List Bool) × List Bool) × List Bool) × Log) =>
        finish p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair input encBits) encBits) encBits) encLog)
      (encPair encBits encLog))
    (hinitial : ComputableInPolyTime initial input
      (RandomOracle.encProgrammingState Log encLog))
    (hdigestBoundPPT : ComputableInPolyTime digestBound input encUnary)
    (hpointBoundPPT : ComputableInPolyTime (fun p : Caller × List Bool => pointBound p.1 p.2)
      (encPair input encBits) encUnary)
    (hreplyBoundPPT : ComputableInPolyTime (fun p : Caller × List Bool => replyBound p.1 p.2)
      (encPair input encBits) encUnary)
    (hlogGrowthPPT : ComputableInPolyTime (fun p : Caller × List Bool => logGrowth p.1 p.2)
      (encPair input encBits) encUnary)
    (hdist : ∀ caller digest, digest ∈ (ProbComp.eval (dist caller)).support →
      digest.length ≤ digestBound caller)
    (hpoint : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      (point caller request coins).length ≤ pointBound caller request)
    (hinactive : ∀ caller request log, logInvariant caller log →
      ∀ result ∈ (ProbComp.eval (inactive caller request log)).support,
        logInvariant caller result.2 ∧ result.1.length ≤ replyBound caller request ∧
          (encLog result.2).length ≤ (encLog log).length + logGrowth caller request)
    (hfinish : ∀ caller request coins,
      coins ∈ (ProbComp.eval (samplePre caller request)).support →
      ∀ digest, digest.length ≤ digestBound caller → ∀ log, logInvariant caller log →
        logInvariant caller (finish caller request coins digest log).2 ∧
          (finish caller request coins digest log).1.length ≤ replyBound caller request ∧
          (encLog (finish caller request coins digest log).2).length ≤
            (encLog log).length + logGrowth caller request)
    (hinitCache : ∀ caller entry, entry ∈ (initial caller).cache →
      entry.2.length ≤ digestBound caller)
    (hinitLog : ∀ caller, logInvariant caller (initial caller).log) :
    Probability.IsPPTOn input
      (encPair output (RandomOracle.encProgrammingState Log encLog))
      (fun caller => ((program (prepare caller).1 (prepare caller).2).runState
        (programmedWordHandler dist active inactive samplePre point finish caller)).run
          (initial caller)) := by
  apply hprogram.isPPTOn_runState hprepare
    (isPPTOn_programmedWordHandler input encLog dist active inactive samplePre point finish
      hdistPPT hactivePPT hinactivePPT hsamplePrePPT hpointPPT hfinishPPT)
    hinitial (RandomOracle.ProgrammingInvariant digestBound logInvariant)
    (fun caller => RandomOracle.ProgrammingInvariant.intro digestBound logInvariant caller
      (initial caller) (hinitCache caller) (hinitLog caller))
    (computableInPolyTime_programmedWordResources input digestBound pointBound replyBound logGrowth
      hdigestBoundPPT hpointBoundPPT hreplyBoundPPT hlogGrowthPPT)
  intro caller request state hstate result hresult
  have hstep := RandomOracle.lazyProgramWordHandler_support encLog dist active inactive samplePre
    point finish digestBound pointBound replyBound logGrowth logInvariant hdist hpoint hinactive
    hfinish caller (.program, programmingPayload request) state hstate result hresult
  refine ⟨hstep.1, hstep.2.1.trans ?_, hstep.2.2.trans ?_⟩
  · exact programmingResources_le_programmedWordResources digestBound pointBound replyBound
      logGrowth caller request.1 request.2
  · exact Nat.add_le_add_left
      (programmingResources_le_programmedWordResources digestBound pointBound replyBound logGrowth
        caller request.1 request.2) _

end Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
