/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Salted.Word

/-!
# Tests for the word view of the salted FO correctness handler

These clients check the field order of the framed encodings, keep the direct joint-oracle and
decapsulation budgets separate, and exercise challenge puncturing through the word handler.
-/

public section

namespace CslibFrontierTests.SaltedFOWord

open Cslib
open Cslib.Crypto
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
open Cslib.Probability
open Turing.MultiTapeTM

abbrev Word := List Bool

def jointInput : JointInput Bool Bool Bool := ⟨true, false, true⟩

def ciphertext : Ciphertext Bool Bool := ⟨true, false⟩

def challenge : Ciphertext Bool Bool := ⟨false, true⟩

def rejectionInput : RejectionInput Bool Bool Bool Bool :=
  ⟨false, true, ciphertext⟩

def boolJointInputDecoder : Decoder (encJointInput encBool encBool encBool) :=
  jointInputDecoder Decoder.bool Decoder.bool Decoder.bool

def boolCiphertextDecoder : Decoder (encCiphertext encBool encBool) :=
  ciphertextDecoder Decoder.bool Decoder.bool

def boolRejectionInputDecoder :
    Decoder (encRejectionInput encBool encBool encBool encBool) :=
  rejectionInputDecoder Decoder.bool Decoder.bool boolCiphertextDecoder

/-- Finite typed salted-FO queries carried by the unbounded word boundary. -/
def boolCodec : OracleCodec WordOperation (Query Bool Bool Bool Bool Bool Bool)
    (Response Bool Bool) :=
  wordQueryCodec boolJointInputDecoder boolRejectionInputDecoder boolCiphertextDecoder
    encBool encBool

example (key coins : Bool) :
    encJointReply encBool encBool (⟨key, coins⟩ : JointReply Bool Bool) =
      frame [key] ++ [coins] := by
  rfl

example :
    encJointInput encBool encBool encBool jointInput =
      frame [true] ++ frame [false] ++ [true] := by
  rfl

example :
    boolCodec.decodeQuery (boolCodec.encodeQuery (Query.joint jointInput)) =
      some (Query.joint jointInput) :=
  boolCodec.decodeQuery_encodeQuery _

/-- A noncanonical Boolean payload is not forwarded as a typed query. -/
example : boolCodec.decodeQuery (.joint, []) = none := by
  decide

example :
    (boolCodec.encodeQuery (Query.rejection rejectionInput)).1 = .rejection ∧
      (boolCodec.encodeQuery (Query.decaps ciphertext)).1 = .decaps := by
  decide

/-- One deterministic call on every source-shaped channel. Rejection costs zero in the `CORR`
coordinate and one in its separate security coordinate. -/
def oneEach : OracleComp (fun _ : WordOperation × Word => Word) Bool := do
  let jointReply ← OracleComp.query
    (.joint, encJointInput encBool encBool encBool jointInput)
  let rejectionReply ← OracleComp.query
    (.rejection, encRejectionInput encBool encBool encBool encBool rejectionInput)
  let decapsReply ← OracleComp.query
    (.decaps, encCiphertext encBool encBool ciphertext)
  return jointReply == rejectionReply ++ decapsReply

theorem oneEach_bounds : WordQueryBounds oneEach 1 1 := by
  constructor
  · simpa [oneEach, wordJointCost] using
      (OracleComp.IsCostBounded.query
        (spec := fun _ : WordOperation × Word => Word)
        (cost := wordJointCost)
        (.joint, encJointInput encBool encBool encBool jointInput)).bind
        fun (jointReply : Word) =>
          (OracleComp.IsCostBounded.query
            (spec := fun _ : WordOperation × Word => Word)
            (cost := wordJointCost)
            (.rejection, encRejectionInput encBool encBool encBool encBool rejectionInput)).bind
            fun (rejectionReply : Word) =>
              (OracleComp.IsCostBounded.query
                (spec := fun _ : WordOperation × Word => Word)
                (cost := wordJointCost)
                (.decaps, encCiphertext encBool encBool ciphertext)).bind
                fun (decapsReply : Word) =>
                  OracleComp.IsCostBounded.pure
                    (jointReply == rejectionReply ++ decapsReply) 0
  · simpa [oneEach, wordDecapsCost] using
      (OracleComp.IsCostBounded.query
        (spec := fun _ : WordOperation × Word => Word)
        (cost := wordDecapsCost)
        (.joint, encJointInput encBool encBool encBool jointInput)).bind
        fun (jointReply : Word) =>
          (OracleComp.IsCostBounded.query
            (spec := fun _ : WordOperation × Word => Word)
            (cost := wordDecapsCost)
            (.rejection, encRejectionInput encBool encBool encBool encBool rejectionInput)).bind
            fun (rejectionReply : Word) =>
              (OracleComp.IsCostBounded.query
                (spec := fun _ : WordOperation × Word => Word)
                (cost := wordDecapsCost)
                (.decaps, encCiphertext encBool encBool ciphertext)).bind
                fun (decapsReply : Word) =>
                  OracleComp.IsCostBounded.pure
                    (jointReply == rejectionReply ++ decapsReply) 0

theorem oneEach_securityBounds : WordSecurityQueryBounds oneEach 1 1 1 := by
  refine ⟨oneEach_bounds.1, ?_, oneEach_bounds.2⟩
  simpa [oneEach, wordRejectionCost] using
      (OracleComp.IsCostBounded.query
        (spec := fun _ : WordOperation × Word => Word)
        (cost := wordRejectionCost)
        (.joint, encJointInput encBool encBool encBool jointInput)).bind
        fun (jointReply : Word) =>
          (OracleComp.IsCostBounded.query
            (spec := fun _ : WordOperation × Word => Word)
            (cost := wordRejectionCost)
            (.rejection, encRejectionInput encBool encBool encBool encBool rejectionInput)).bind
            fun (rejectionReply : Word) =>
              (OracleComp.IsCostBounded.query
                (spec := fun _ : WordOperation × Word => Word)
                (cost := wordRejectionCost)
                (.decaps, encCiphertext encBool encBool ciphertext)).bind
                fun (decapsReply : Word) =>
                  OracleComp.IsCostBounded.pure
                    (jointReply == rejectionReply ++ decapsReply) 0

theorem oneEach_roBounds : WordROQueryBounds oneEach 2 1 :=
  ⟨oneEach_securityBounds.roCostBounded, oneEach_bounds.2⟩

theorem boolCodec_jointCost (q : Query Bool Bool Bool Bool Bool Bool) :
    wordJointCost (boolCodec.encodeQuery q) = Query.jointCost q := by
  cases q <;> rfl

theorem boolCodec_roCost (q : Query Bool Bool Bool Bool Bool Bool) :
    wordROCost (boolCodec.encodeQuery q) = Query.roCost q := by
  cases q <;> rfl

theorem boolCodec_rejectionCost (q : Query Bool Bool Bool Bool Bool Bool) :
    wordRejectionCost (boolCodec.encodeQuery q) = Query.rejectionCost q := by
  cases q <;> rfl

theorem boolCodec_decapsCost (q : Query Bool Bool Bool Bool Bool Bool) :
    wordDecapsCost (boolCodec.encodeQuery q) = Query.decapsCost q := by
  cases q <;> rfl

example : QueryBounds (boolCodec.adaptOracle oneEach) 1 1 :=
  WordQueryBounds.adapt boolCodec boolCodec_jointCost boolCodec_decapsCost oneEach_bounds

example : SecurityQueryBounds (boolCodec.adaptOracle oneEach) 1 1 1 :=
  WordSecurityQueryBounds.adapt boolCodec boolCodec_jointCost boolCodec_rejectionCost
    boolCodec_decapsCost oneEach_securityBounds

example : ROQueryBounds (boolCodec.adaptOracle oneEach) 2 1 :=
  WordROQueryBounds.adapt boolCodec boolCodec_roCost boolCodec_decapsCost oneEach_roBounds

example : SecurityQueryBounds (boolCodec.adaptOracle oneEach) 2 2 1 :=
  (WordROQueryBounds.adapt boolCodec boolCodec_roCost boolCodec_decapsCost
    oneEach_roBounds).toSecurityQueryBounds

example : OracleComp.IsCostBounded wordROCost oneEach 2 :=
  oneEach_securityBounds.roCostBounded

/-- Perfect deterministic Boolean PKE used to exercise the finite typed handler. -/
noncomputable def boolPKE : ExplicitCoinPKE Bool Bool Bool Bool Bool where
  keyGen := pure (false, false)
  sampleCoins := pure false
  encDet _ message _ := message
  dec _ ciphertext := some ciphertext

/-- Finite Boolean salted scheme with visibly different domain prefixes. -/
noncomputable def boolScheme :
    Scheme Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool where
  pke := boolPKE
  sampleKey := pure false
  jointPrefix _ := false
  rejectionPrefix _ := true
  rejectionSecret sk := sk

abbrev BoolState := CacheState Bool Bool Bool Bool Bool Bool Bool Bool

example :
    boolScheme.simWordHandler boolCodec false challenge
        (boolCodec.encodeQuery (Query.decaps challenge)) ({} : BoolState) =
      pure (encOption encBool (none : Option Bool), ({} : BoolState)) := by
  exact boolScheme.simWordHandler_decaps_challenge boolCodec false challenge {}

example :
    (OracleComp.interpret (boolScheme.simHandler false challenge)
        (boolCodec.adaptOracle oneEach)).run ({} : BoolState) =
      (OracleComp.interpret (boolScheme.simWordHandler boolCodec false challenge)
        oneEach).run ({} : BoolState) :=
  boolScheme.run_simWordHandler boolCodec false challenge oneEach {}

noncomputable def boolChallengeSetup (_ : Bool) :
    ProbComp (Ciphertext Bool Bool × Bool) := do
  let salt ← ProbComp.uniform Bool
  return (⟨false, salt⟩, true)

def challengeProgram (challenge : KEM.Challenge Bool (Ciphertext Bool Bool) Bool) :
    OracleComp (fun _ : WordOperation × Word => Word) Bool := do
  let reply ← OracleComp.query (.joint,
    encJointInput encBool encBool encBool ⟨challenge.pk, false, challenge.ct.salt⟩)
  return reply == encJointReply encBool encBool ⟨challenge.key, false⟩

noncomputable def boolRandomizedAdversary :
    WordRandomizedAdversary Bool Bool Bool Bool where
  Coins := Bool
  coins := ProbComp.uniform Bool
  run _ challenge := challengeProgram challenge

theorem boolRandomizedAdversary_bounded : boolRandomizedAdversary.QueryBounded 1 0 := by
  intro _ challenge
  change WordQueryBounds (challengeProgram challenge) 1 0
  constructor <;>
    exact (OracleComp.IsCostBounded.query
      (spec := fun _ : WordOperation × Word => Word)
      (WordOperation.joint, encJointInput encBool encBool encBool
        ⟨challenge.pk, false, challenge.ct.salt⟩)).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

theorem boolPKE_deltaCorrect_zero : boolPKE.DeltaCorrect 0 := by
  apply ExplicitCoinPKE.deltaCorrect_zero_of_perfect
  intro _ _ _ _ _ _
  rfl

/-- End-to-end finite-carrier client of the randomized word-level `CORR` theorem. -/
example :
    (Game.advantage
      (boolScheme.randomizedRealWordHandlerGame boolCodec boolChallengeSetup
        boolRandomizedAdversary)
      (boolScheme.randomizedSimWordHandlerGame boolCodec boolChallengeSetup
        boolRandomizedAdversary) : ℝ) ≤
      ((1 + 0 : ℕ) : ℝ) * 0 := by
  exact boolScheme.advantage_randomizedRealWordHandler_simWordHandler_le boolCodec
    boolChallengeSetup boolRandomizedAdversary boolCodec_jointCost boolCodec_decapsCost
    boolRandomizedAdversary_bounded boolPKE_deltaCorrect_zero

end CslibFrontierTests.SaltedFOWord
