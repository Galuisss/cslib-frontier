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
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.FujisakiOkamoto.Salted
open Cslib.Probability
open Turing.MultiTapeTM

abbrev Word := List Bool

def jointInput : JointInput Word Word Word := ⟨[true], [false, true], [false]⟩

def ciphertext : Ciphertext Word Word := ⟨[true, false], [true]⟩

def challenge : Ciphertext Word Word := ⟨[false], [false, true]⟩

def rejectionInput : RejectionInput Word Word Word Word :=
  ⟨[true, true], [false, false], ciphertext⟩

example (key coins : Word) :
    encJointReply (⟨key, coins⟩ : JointReply Word Word) = frame key ++ coins := by
  rfl

example :
    encJointInput jointInput = frame [true] ++ frame [false, true] ++ [false] := by
  rfl

example :
    wordQueryCodec.decodeQuery (wordQueryCodec.encodeQuery (Query.joint jointInput)) =
      some (Query.joint jointInput) :=
  wordQueryCodec.decodeQuery_encodeQuery _

example :
    (wordQueryCodec.encodeQuery (Query.rejection rejectionInput)).1 = .rejection ∧
      (wordQueryCodec.encodeQuery (Query.decaps ciphertext)).1 = .decaps := by
  simp [wordQueryCodec, wordRequest]

/-- One call on every source-shaped channel. The rejection call costs zero in both loss
coordinates. -/
def oneEach : WordOracleComp WordOperation Bool := do
  let jointReply ← ProbOracleComp.query (.joint, encJointInput jointInput)
  let rejectionReply ← ProbOracleComp.query (.rejection, encRejectionInput rejectionInput)
  let decapsReply ← ProbOracleComp.query (.decaps, encCiphertext ciphertext)
  return jointReply == rejectionReply ++ decapsReply

theorem oneEach_bounds : WordQueryBounds oneEach 1 1 := by
  constructor
  · simpa [oneEach, wordJointCost] using
      (ProbOracleComp.isCostBounded_query
        (spec := fun _ : WordOperation × Word => Word) wordJointCost
        (.joint, encJointInput jointInput)).bind fun (jointReply : Word) =>
        (ProbOracleComp.isCostBounded_query
          (spec := fun _ : WordOperation × Word => Word) wordJointCost
          (.rejection, encRejectionInput rejectionInput)).bind fun (rejectionReply : Word) =>
          (ProbOracleComp.isCostBounded_query
            (spec := fun _ : WordOperation × Word => Word) wordJointCost
            (.decaps, encCiphertext ciphertext)).bind fun (decapsReply : Word) =>
            OracleComp.IsCostBounded.pure (jointReply == rejectionReply ++ decapsReply) 0
  · simpa [oneEach, wordDecapsCost] using
      (ProbOracleComp.isCostBounded_query
        (spec := fun _ : WordOperation × Word => Word) wordDecapsCost
        (.joint, encJointInput jointInput)).bind fun (jointReply : Word) =>
        (ProbOracleComp.isCostBounded_query
          (spec := fun _ : WordOperation × Word => Word) wordDecapsCost
          (.rejection, encRejectionInput rejectionInput)).bind fun (rejectionReply : Word) =>
          (ProbOracleComp.isCostBounded_query
            (spec := fun _ : WordOperation × Word => Word) wordDecapsCost
            (.decaps, encCiphertext ciphertext)).bind fun (decapsReply : Word) =>
            OracleComp.IsCostBounded.pure (jointReply == rejectionReply ++ decapsReply) 0

example :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) Query.jointCost)
        (wordQueryCodec.adapt oneEach) 1 ∧
      OracleComp.IsCostBounded (Sum.elim (fun _ => 0) Query.decapsCost)
        (wordQueryCodec.adapt oneEach) 1 :=
  WordQueryBounds.adapt oneEach_bounds

/-- Deterministic word PKE used only to exercise challenge puncturing. -/
noncomputable def wordPKE : ExplicitCoinPKE Word Word Word Word Word where
  keyGen := pure ([], [])
  sampleCoins := pure []
  encDet _ message _ := message
  dec _ ciphertext := some ciphertext

/-- Word-valued salted scheme with visibly different domain prefixes. -/
noncomputable def wordScheme :
    Scheme Word Word Word Word Word Word Word Word Word Word where
  pke := wordPKE
  sampleKey := pure []
  jointPrefix _ := [false]
  rejectionPrefix _ := [true]
  rejectionSecret sk := sk

abbrev WordState := CacheState Word Word Word Word Word Word Word Word

example :
    wordScheme.simWordHandler [] challenge
        (wordQueryCodec.encodeQuery (Query.decaps challenge)) ({} : WordState) =
      pure (encOption encBits (none : Option Word), ({} : WordState)) := by
  exact wordScheme.simWordHandler_decaps_challenge [] challenge {}

example :
    ProbOracleComp.runWith (wordScheme.simHandler [] challenge)
        (wordQueryCodec.adapt oneEach) ({} : WordState) =
      ProbOracleComp.runWith (wordScheme.simWordHandler [] challenge)
        oneEach ({} : WordState) :=
  wordScheme.runWith_simWordHandler [] challenge oneEach {}

end CslibFrontierTests.SaltedFOWord
