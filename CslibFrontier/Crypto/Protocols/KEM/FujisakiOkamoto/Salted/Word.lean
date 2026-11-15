/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Salted.Correctness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec

/-!
# Word view of the concrete salted FO correctness handlers

This module carries the typed post-secret-seed-guessing salted Fujisaki--Okamoto `CORR` handler
over native word-oracle requests. The three channels remain distinct: `joint` carries the public
prefix, message and salt and returns the framed `(key, coins)` reply; `rejection` carries the
public rejection prefix, secret seed and full salted ciphertext; and `decaps` carries the full
salted ciphertext. Malformed word requests decode to no typed query and receive `[]` without a
typed oracle call.

`WordQueryBounds` keeps the source's independent `qRO` and `qD` coordinates. Adapting a word
program through `wordQueryCodec` preserves both bounds exactly: one joint request costs one even
though its reply contains two framed fields, rejection costs zero in both coordinates, and one
decapsulation request costs one only in the `qD` coordinate.

This is an encoding and semantic bridge, not an efficiency theorem. The programmable random-oracle
realization and its strict-PPT certificate live in
`CslibFrontier.Computability.Probabilistic.RandomOracle.Programming`; the HQC family reduction
must instantiate that shared component and separately account for installed program descriptions.

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
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.WordQueryBounds`: independent word-level joint
  and decapsulation query budgets.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.simWordHandler`: the word view of the
  concrete keyless handler.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.WordQueryBounds.adapt`: transport the separate
  word-level budgets to the typed correctness interface.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.simWordHandler_decaps_challenge`: the
  word handler rejects the punctured challenge without changing its cache.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Salted.Scheme.runWith_simWordHandler`: exact joint
  result/cache law of the word and typed keyless executions.

## References

* [Glabush--Hövelmanns--Stebila, Theorem 11 and Figure 11][GlabushHoevelmannsStebila2025].
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto.Salted

open Probability
open Turing.MultiTapeTM

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
enc_structure encJointInput : JointInput (List Bool) (List Bool) (List Bool) where
  keyPrefix : encBits, message : encBits, salt : encBits

/-- Encoding of one joint reply: framed session key, then encryption coins. -/
enc_structure encJointReply : JointReply (List Bool) (List Bool) where
  key : encBits, coins : encBits

/-- Encoding of a salted ciphertext: framed PKE ciphertext, then salt. -/
enc_structure encCiphertext : Ciphertext (List Bool) (List Bool) where
  pke : encBits, salt : encBits

/-- Encoding of an implicit-rejection input: framed public prefix, framed secret seed, then the
salted ciphertext encoding. -/
enc_structure encRejectionInput :
    RejectionInput (List Bool) (List Bool) (List Bool) (List Bool) where
  keyPrefix : encBits, secret : encBits, ciphertext : encCiphertext

/-- The request carrying a typed salted-FO query on the three word channels. -/
@[expose] def wordRequest :
    Query (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) →
      WordOperation × List Bool
  | .joint input => (.joint, encJointInput input)
  | .rejection input => (.rejection, encRejectionInput input)
  | .decaps ciphertext => (.decaps, encCiphertext ciphertext)

/-- Distinct typed salted-FO queries have distinct word requests. -/
theorem wordRequest_injective : Function.Injective wordRequest := by
  intro q q' h
  cases q <;> cases q' <;> simp only [wordRequest, Prod.mk.injEq, true_and,
    reduceCtorEq, false_and] at h ⊢
  · exact congrArg Query.joint (encJointInput.injective h)
  · exact congrArg Query.rejection (encRejectionInput.injective h)
  · exact congrArg Query.decaps (encCiphertext.injective h)

/-- Canonical typed view of the three salted-FO word channels. Replies preserve the source field
order: joint replies encode the key before the coins, rejection replies are keys, and
decapsulation replies are optional keys. -/
@[expose] noncomputable def wordQueryCodec : OracleCodec WordOperation
    (Query (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) (List Bool))
    (Response (List Bool) (List Bool)) where
  encodeQuery := wordRequest
  decodeQuery := Function.partialInv wordRequest
  decodeQuery_eq_some_iff _ _ := wordRequest_injective.isPartialInv _ _
  encodeReply
    | .joint _ => encJointReply
    | .rejection _ => encBits
    | .decaps _ => encOption encBits

/-- Cost of a word request in the joint-oracle coordinate. One framed `(key, coins)` response
still costs one request. -/
@[expose, simp] def wordJointCost : WordOperation × List Bool → ℕ
  | (.joint, _) => 1
  | (.rejection, _) => 0
  | (.decaps, _) => 0

/-- Cost of a word request in the decapsulation coordinate. -/
@[expose, simp] def wordDecapsCost : WordOperation × List Bool → ℕ
  | (.joint, _) => 0
  | (.rejection, _) => 0
  | (.decaps, _) => 1

/-- Independent joint-oracle and decapsulation budgets for a word-level salted-FO program.
Private fair-coin samples cost zero in both coordinates. -/
@[expose] def WordQueryBounds {α : Type} (program : WordOracleComp WordOperation α)
    (qRO qD : ℕ) : Prop :=
  OracleComp.IsCostBounded (Sum.elim (fun _ => 0) wordJointCost) program qRO ∧
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) wordDecapsCost) program qD

namespace WordQueryBounds

/-- Adapting a word program to the typed salted-FO interface preserves the independent joint and
decapsulation budgets. -/
theorem adapt {α : Type} {program : WordOracleComp WordOperation α} {qRO qD : ℕ}
    (h : WordQueryBounds program qRO qD) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) Query.jointCost)
        (wordQueryCodec.adapt program) qRO ∧
      OracleComp.IsCostBounded (Sum.elim (fun _ => 0) Query.decapsCost)
        (wordQueryCodec.adapt program) qD := by
  refine ⟨wordQueryCodec.isCostBounded_adapt (wordCost := wordJointCost) ?_ h.1,
    wordQueryCodec.isCostBounded_adapt (wordCost := wordDecapsCost) ?_ h.2⟩
  · intro q
    cases q <;> rfl
  · intro q
    cases q <;> rfl

end WordQueryBounds

namespace Scheme

/-- The word view of the concrete keyless salted-FO handler. Requests carrying no typed query are
answered with `[]` and do not change the cache. This definition carries no efficiency claim. -/
@[expose] noncomputable def simWordHandler
    [DecidableEq (JointInput (List Bool) (List Bool) (List Bool))]
    [DecidableEq (RejectionInput (List Bool) (List Bool) (List Bool) (List Bool))]
    [DecidableEq (Ciphertext (List Bool) (List Bool))]
    (S : Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)
      (List Bool) (List Bool) (List Bool) (List Bool) (List Bool))
    (pk : List Bool) (challenge : Ciphertext (List Bool) (List Bool)) :
    WordOperation × List Bool →
      StateT (CacheState (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)
        (List Bool) (List Bool) (List Bool)) PMF (List Bool) :=
  wordQueryCodec.wordOracle (S.simHandler pk challenge)

/-- The punctured word handler rejects its challenge ciphertext without changing the state. -/
@[simp] theorem simWordHandler_decaps_challenge
    [DecidableEq (JointInput (List Bool) (List Bool) (List Bool))]
    [DecidableEq (RejectionInput (List Bool) (List Bool) (List Bool) (List Bool))]
    [DecidableEq (Ciphertext (List Bool) (List Bool))]
    (S : Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)
      (List Bool) (List Bool) (List Bool) (List Bool) (List Bool))
    (pk : List Bool) (challenge : Ciphertext (List Bool) (List Bool))
    (st : CacheState (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)
      (List Bool) (List Bool) (List Bool)) :
    S.simWordHandler pk challenge (wordQueryCodec.encodeQuery (.decaps challenge)) st =
      PMF.pure (encOption encBits (none : Option (List Bool)), st) := by
  rw [simWordHandler, wordQueryCodec.wordOracle_encodeQuery]
  change ((wordQueryCodec.encodeReply (.decaps challenge) <$>
      S.simHandler pk challenge (.decaps challenge)).run st) = _
  rw [StateT.run_map]
  change (fun p => (wordQueryCodec.encodeReply (.decaps challenge) p.1, p.2)) <$>
      S.simHandler pk challenge (.decaps challenge) st = _
  rw [S.simHandler_decaps_challenge pk challenge st]
  rw [PMF.monad_map_eq_map, PMF.pure_map]
  rfl

/-- Running a word program against `simWordHandler` has exactly the joint result/cache law of its
typed adaptation against `simHandler`. -/
theorem runWith_simWordHandler
    [DecidableEq (JointInput (List Bool) (List Bool) (List Bool))]
    [DecidableEq (RejectionInput (List Bool) (List Bool) (List Bool) (List Bool))]
    [DecidableEq (Ciphertext (List Bool) (List Bool))]
    {α : Type}
    (S : Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)
      (List Bool) (List Bool) (List Bool) (List Bool) (List Bool))
    (pk : List Bool) (challenge : Ciphertext (List Bool) (List Bool))
    (program : WordOracleComp WordOperation α)
    (initial : CacheState (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)
      (List Bool) (List Bool) (List Bool)) :
    ProbOracleComp.runWith (S.simHandler pk challenge) (wordQueryCodec.adapt program) initial =
      ProbOracleComp.runWith (S.simWordHandler pk challenge) program initial :=
  wordQueryCodec.runWith_adapt _ _ _

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
