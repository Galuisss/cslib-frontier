/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of local-only files)

public import CslibFrontier.Crypto.Protocols.KEM.HQC

/-!
# Tests for the ideal expanded-value HQC-KEM instance

These ordinary-module clients check the source-sensitive semantic boundaries: finite HQC
carriers, salt binding, the `(K, θ)` reply order, the independent rejection input, and challenge
ciphertext exclusion.
-/

namespace CslibFrontierTests.Crypto.HQCKEM

open Cslib.Crypto Cslib.Crypto.HQC Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.FujisakiOkamoto

public section

noncomputable section

/-- One-bit toy HQC parameters used only to exercise the typed KEM boundary. -/
def toyParams : PKEParams where
  n := 1
  k := 1
  ell := 0
  omega := 0
  omegaR := 0
  omegaE := 0
  delta := 0
  ell_le_n := by omega
  omega_le_n := by omega
  omegaR_le_n := by omega
  omegaE_le_n := by omega

def zeroRingWord : RingWord toyParams := fun _ => false

def toyPublicKey : PKEPublicKey toyParams := ⟨zeroRingWord, zeroRingWord⟩

def toySecretKey : PKESecretKey toyParams := zeroRingWord

def toyCoins : PKECoins toyParams := ⟨zeroRingWord, zeroRingWord, zeroRingWord⟩

def toyEncode : PKEMessage toyParams → Codeword toyParams := fun message => message

def toyDecode : Codeword toyParams → PKEMessage toyParams := fun codeword => codeword

def toyHash (_ : PKEPublicKey toyParams) : PublicKeyHash := fun _ => false

def falseSalt : KEMSalt := fun _ => false

def trueSalt : KEMSalt := fun _ => true

def toySigma : PKEMessage toyParams := fun _ => false

def toyDecapsKey : DecapsKey toyParams := ⟨toyPublicKey, toySecretKey, toySigma⟩

/-- The joint reply key reads the salt's first bit; its encryption coins are separate. -/
def toyJoint (input : Salted.JointInput PublicKeyHash (PKEMessage toyParams) KEMSalt) :
    Salted.JointReply KEMKey (PKECoins toyParams) :=
  ⟨fun _ => input.salt 0, toyCoins⟩

/-- The rejection key reads `σ`, independently of the joint reply. -/
def toyRejection (input : Salted.RejectionInput PublicKeyHash (PKEMessage toyParams)
    (PKECiphertext toyParams) KEMSalt) : KEMKey :=
  fun _ => input.secret ⟨0, by simp [toyParams]⟩

abbrev ToyState := Salted.CacheState PublicKeyHash (PKEMessage toyParams) KEMSalt PublicKeyHash
  (PKEMessage toyParams) (PKECiphertext toyParams) KEMKey (PKECoins toyParams)

example : Fintype (PKEPublicKey toyParams) := inferInstance

example : Fintype (PKECoins toyParams) := inferInstance

example : Fintype (PKECiphertext toyParams) := inferInstance

example : Fintype (KEMCiphertext toyParams) := inferInstance

-- The sampled public salt is carried unchanged by the KEM ciphertext.
example :
    (encapsDet toyParams toyEncode toyHash toyJoint toyPublicKey (fun _ => false) trueSalt).1.salt =
      trueSalt :=
  rfl

-- The salt is also part of the single joint-oracle input.
example :
    (encapsDet toyParams toyEncode toyHash toyJoint toyPublicKey
      (fun _ => false) falseSalt).2 ≠
    (encapsDet toyParams toyEncode toyHash toyJoint toyPublicKey
      (fun _ => false) trueSalt).2 := by
  intro h
  have hfirst := congrFun h 0
  simp [encapsDet, toyJoint, falseSalt, trueSalt] at hfirst

-- The PKE encryption receives the `coins` field while the KEM returns the `key` field.
example (message : PKEMessage toyParams) (salt : KEMSalt) :
    (encapsDet toyParams toyEncode toyHash toyJoint toyPublicKey message salt).1.pke =
      pkeEncrypt toyParams toyEncode toyPublicKey message
        (toyJoint ⟨toyHash toyPublicKey, message, salt⟩).coins ∧
    (encapsDet toyParams toyEncode toyHash toyJoint toyPublicKey message salt).2 =
      (toyJoint ⟨toyHash toyPublicKey, message, salt⟩).key :=
  ⟨rfl, rfl⟩

-- Both salted-scheme prefixes are `H(pk)`, while only the rejection domain receives `σ`.
example :
    (toSaltedScheme toyParams toyEncode toyDecode toyHash).jointPrefix toyPublicKey =
      toyHash toyPublicKey ∧
    (toSaltedScheme toyParams toyEncode toyDecode toyHash).rejectionPrefix toyPublicKey =
      toyHash toyPublicKey ∧
    (toSaltedScheme toyParams toyEncode toyDecode toyHash).rejectionSecret toyDecapsKey =
      toySigma :=
  ⟨rfl, rfl, rfl⟩

-- The common dispatcher rejects the full challenge ciphertext before decapsulation runs.
example (challenge : KEMCiphertext toyParams) :
    (toSaltedScheme toyParams toyEncode toyDecode toyHash).simHandler toyPublicKey challenge
        (.decaps challenge) ({} : ToyState) =
      PMF.pure (none, ({} : ToyState)) :=
  (toSaltedScheme toyParams toyEncode toyDecode toyHash).simHandler_decaps_challenge
    toyPublicKey challenge {}

-- A failed re-encryption exposes exactly the separate source-shaped rejection input.
example (ciphertext : KEMCiphertext toyParams)
    (hbad : pkeEncrypt toyParams toyEncode toyDecapsKey.pk
      (pkeDecrypt toyParams toyDecode toyDecapsKey.sk ciphertext.pke)
      (toyJoint ⟨toyHash toyDecapsKey.pk,
        pkeDecrypt toyParams toyDecode toyDecapsKey.sk ciphertext.pke,
        ciphertext.salt⟩).coins ≠ ciphertext.pke) :
    kemDecaps toyParams toyEncode toyDecode toyHash toyJoint toyRejection toyDecapsKey ciphertext =
      toyRejection ⟨toyHash toyDecapsKey.pk, toyDecapsKey.sigma, ciphertext⟩ :=
  kemDecaps_of_reencrypt_ne toyParams toyEncode toyDecode toyHash toyJoint toyRejection
    toyDecapsKey ciphertext hbad

end

end

end CslibFrontierTests.Crypto.HQCKEM
