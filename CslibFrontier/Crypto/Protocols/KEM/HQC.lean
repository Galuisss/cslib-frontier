/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.PKE
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Salted.Correctness

/-!
# The ideal expanded-value HQC key-encapsulation mechanism

This file instantiates the salted implicit-rejection transform used by HQC-KEM v5.1 over the
ideal algebraic HQC-PKE core. It follows [HQC2026], Section 3.7, Algorithms `HQC-KEM.Keygen`,
`HQC-KEM.Encaps` and `HQC-KEM.Decaps`, printed pp. 41--43:

* encapsulation samples a message and 128-bit salt, obtains `(K, θ)` from the single joint oracle
  `G(H(ekKEM), m, salt)`, and returns the PKE ciphertext together with the salt;
* decapsulation decrypts, repeats the same joint query, and accepts its key exactly when
  re-encryption with `θ` reproduces the PKE ciphertext;
* rejection returns `J(H(ekPKE), σ, cKEM)` from a separate oracle domain.

The reply fields are named `key` and `coins`, so the source order `(K, θ)` cannot be swapped
silently. `encapsDet` exposes the deterministic core used after sampling the message and salt,
and `toSaltedScheme` is the exact finite typed instance consumed by the joint-oracle correctness
games.

As in `Cslib.Crypto.HQC.toExplicitCoinPKE`, this is an ideal expanded-value model. Its
decapsulation key stores the expanded PKE keys and the rejection secret `σ`; it does not claim
equivalence with the compressed `seedKEM`, XOF expansion, byte encodings or the production
fixed-weight sampler. The ideal PKE decoder is total, so the source's separate `m' = ⊥` rejection
test is vacuous here; a failed re-encryption still takes the `J` branch.

## Main definitions

* `Cslib.Crypto.HQC.DecapsKey`: expanded PKE public/secret keys and rejection secret `σ`.
* `Cslib.Crypto.HQC.encapsDet`, `Cslib.Crypto.HQC.kemEncaps`,
  `Cslib.Crypto.HQC.kemDecaps`: the ideal HQC-KEM algorithms.
* `Cslib.Crypto.HQC.toKEM`: the algorithms as a typed KEM.
* `Cslib.Crypto.HQC.toSaltedScheme`: the same data as the finite salted joint-oracle scheme.

## Main results

* `Cslib.Crypto.HQC.kemDecaps_encapsDet`: honest decapsulation returns the joint-oracle key
  whenever the underlying PKE decryption succeeds.
* `Cslib.Crypto.HQC.kemDecaps_of_reencrypt_ne`: failed re-encryption returns the separate
  implicit-rejection key.

## References

* [HQC specification, version 5.1][HQC2026], Section 3.7, pp. 41--43.
-/

public section

namespace Cslib.Crypto.HQC

open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.FujisakiOkamoto

/-- The 256-bit digest `H(ekKEM)` used as the public prefix of the `G` and `J` domains. -/
abbrev PublicKeyHash := BitString 256

/-- The 128-bit public salt carried by every HQC-KEM ciphertext. -/
abbrev KEMSalt := BitString 128

/-- The 256-bit shared key returned by HQC-KEM. -/
abbrev KEMKey := BitString 256

noncomputable instance (P : PKEParams) : Fintype (PKEPublicKey P) :=
  Fintype.ofFinite (PKEPublicKey P)

noncomputable instance (P : PKEParams) : Fintype (PKECoins P) :=
  Fintype.ofFinite (PKECoins P)

noncomputable instance (P : PKEParams) : Fintype (PKECiphertext P) :=
  Fintype.ofFinite (PKECiphertext P)

/-- An HQC-KEM ciphertext is an HQC-PKE ciphertext paired with its public salt. -/
abbrev KEMCiphertext (P : PKEParams) := Salted.Ciphertext (PKECiphertext P) KEMSalt

/-- Expanded ideal HQC-KEM decapsulation key. The v5.1 byte-level algorithm regenerates these
fields from `seedKEM`; this semantic layer stores the regenerated values directly. -/
structure DecapsKey (P : PKEParams) where
  /-- PKE public key retained for the re-encryption check and public-prefix hash. -/
  pk : PKEPublicKey P
  /-- PKE secret key used for decryption. -/
  sk : PKESecretKey P
  /-- Secret implicit-rejection input `σ`. -/
  sigma : PKEMessage P
  deriving DecidableEq

instance (P : PKEParams) : Finite (DecapsKey P) :=
  Finite.of_injective (fun key => (key.pk, key.sk, key.sigma)) fun _ _ h => by
    exact congrArg (fun ⟨pk, sk, sigma⟩ => (⟨pk, sk, sigma⟩ : DecapsKey P)) h

noncomputable instance (P : PKEParams) : Fintype (DecapsKey P) :=
  Fintype.ofFinite (DecapsKey P)

/-- Ideal expanded HQC-KEM key generation. The PKE key pair has its ideal fixed-weight law and
the rejection secret `σ` is uniform and independent. -/
noncomputable def kemKeyGen (P : PKEParams) :
    ProbComp (PKEPublicKey P × DecapsKey P) := do
  let (pk, sk) ← pkeKeyGen P
  let sigma ← ProbComp.uniform (PKEMessage P)
  return (pk, ⟨pk, sk, sigma⟩)

/-- Deterministic core of HQC-KEM encapsulation after sampling `m` and `salt`. The single joint
reply is consumed in source order: `reply.key = K` and `reply.coins = θ`. -/
@[expose] def encapsDet (P : PKEParams) (encode : PKEMessage P → Codeword P)
    (H : PKEPublicKey P → PublicKeyHash)
    (G : Salted.JointInput PublicKeyHash (PKEMessage P) KEMSalt →
      Salted.JointReply KEMKey (PKECoins P))
    (pk : PKEPublicKey P) (message : PKEMessage P) (salt : KEMSalt) :
    KEMCiphertext P × KEMKey :=
  let reply := G ⟨H pk, message, salt⟩
  (⟨pkeEncrypt P encode pk message reply.coins, salt⟩, reply.key)

/-- HQC-KEM encapsulation with independent uniform message and salt. -/
noncomputable def kemEncaps (P : PKEParams) (encode : PKEMessage P → Codeword P)
    (H : PKEPublicKey P → PublicKeyHash)
    (G : Salted.JointInput PublicKeyHash (PKEMessage P) KEMSalt →
      Salted.JointReply KEMKey (PKECoins P))
    (pk : PKEPublicKey P) : ProbComp (KEMCiphertext P × KEMKey) := do
  let message ← ProbComp.uniform (PKEMessage P)
  let salt ← ProbComp.uniform KEMSalt
  return encapsDet P encode H G pk message salt

/-- HQC-KEM decapsulation with implicit rejection. The public salt is included in both the
repeated `G` input and the `J` input, and rejection hashes the complete salted ciphertext. -/
@[expose] def kemDecaps (P : PKEParams) (encode : PKEMessage P → Codeword P)
    (decode : Codeword P → PKEMessage P) (H : PKEPublicKey P → PublicKeyHash)
    (G : Salted.JointInput PublicKeyHash (PKEMessage P) KEMSalt →
      Salted.JointReply KEMKey (PKECoins P))
    (J : Salted.RejectionInput PublicKeyHash (PKEMessage P)
      (PKECiphertext P) KEMSalt → KEMKey)
    (dk : DecapsKey P) (ciphertext : KEMCiphertext P) : KEMKey :=
  let message := pkeDecrypt P decode dk.sk ciphertext.pke
  let reply := G ⟨H dk.pk, message, ciphertext.salt⟩
  if pkeEncrypt P encode dk.pk message reply.coins = ciphertext.pke then reply.key
  else J ⟨H dk.pk, dk.sigma, ciphertext⟩

/-- The ideal expanded HQC algorithms as a typed KEM. Decapsulation uses implicit rejection and
therefore always returns `some key`. -/
noncomputable def toKEM (P : PKEParams) (encode : PKEMessage P → Codeword P)
    (decode : Codeword P → PKEMessage P) (H : PKEPublicKey P → PublicKeyHash)
    (G : Salted.JointInput PublicKeyHash (PKEMessage P) KEMSalt →
      Salted.JointReply KEMKey (PKECoins P))
    (J : Salted.RejectionInput PublicKeyHash (PKEMessage P)
      (PKECiphertext P) KEMSalt → KEMKey) :
    KEM (PKEPublicKey P) (DecapsKey P) (KEMCiphertext P) KEMKey where
  keyGen := kemKeyGen P
  encaps := kemEncaps P encode H G
  decaps dk ciphertext := some (kemDecaps P encode decode H G J dk ciphertext)

/-- The HQC PKE lifted to the expanded KEM decapsulation key. This is the PKE component of the
salted joint-oracle correctness instance; encryption ignores the extra stored fields and
decryption reads only `dk.sk`. -/
@[expose] noncomputable def toKEMExplicitCoinPKE (P : PKEParams)
    (encode : PKEMessage P → Codeword P) (decode : Codeword P → PKEMessage P) :
    ExplicitCoinPKE (PKEPublicKey P) (DecapsKey P) (PKEMessage P) (PKECoins P)
      (PKECiphertext P) where
  keyGen := kemKeyGen P
  sampleCoins := pkeSampleCoins P
  encDet := pkeEncrypt P encode
  dec dk ciphertext := some (pkeDecrypt P decode dk.sk ciphertext)

/-- Exact finite typed HQC instance of the salted joint-oracle scheme. Both public prefixes are
`H(pk)`, the joint reply is `(K, θ)`, and `rejectionSecret` exposes only `σ`. -/
@[expose] noncomputable def toSaltedScheme (P : PKEParams)
    (encode : PKEMessage P → Codeword P) (decode : Codeword P → PKEMessage P)
    (H : PKEPublicKey P → PublicKeyHash) :
    Salted.Scheme (PKEPublicKey P) (DecapsKey P) (PKEMessage P) (PKECoins P)
      (PKECiphertext P) PublicKeyHash KEMSalt PublicKeyHash (PKEMessage P) KEMKey where
  pke := toKEMExplicitCoinPKE P encode decode
  sampleKey := ProbComp.uniform KEMKey
  jointPrefix := H
  rejectionPrefix := H
  rejectionSecret := DecapsKey.sigma

/-- Honest decapsulation returns the `key` field, not the encryption-coins field, of the single
joint reply. -/
theorem kemDecaps_encapsDet (P : PKEParams) (encode : PKEMessage P → Codeword P)
    (decode : Codeword P → PKEMessage P) (H : PKEPublicKey P → PublicKeyHash)
    (G : Salted.JointInput PublicKeyHash (PKEMessage P) KEMSalt →
      Salted.JointReply KEMKey (PKECoins P))
    (J : Salted.RejectionInput PublicKeyHash (PKEMessage P)
      (PKECiphertext P) KEMSalt → KEMKey)
    (pk : PKEPublicKey P) (sk : PKESecretKey P) (sigma : PKEMessage P)
    (message : PKEMessage P) (salt : KEMSalt)
    (hdec : pkeDecrypt P decode sk
      (pkeEncrypt P encode pk message (G ⟨H pk, message, salt⟩).coins) = message) :
    kemDecaps P encode decode H G J ⟨pk, sk, sigma⟩
        (encapsDet P encode H G pk message salt).1 =
      (encapsDet P encode H G pk message salt).2 := by
  simp [kemDecaps, encapsDet, hdec]

/-- A failed PKE re-encryption check takes the separate `J(H(pk), σ, cKEM)` branch. -/
theorem kemDecaps_of_reencrypt_ne (P : PKEParams) (encode : PKEMessage P → Codeword P)
    (decode : Codeword P → PKEMessage P) (H : PKEPublicKey P → PublicKeyHash)
    (G : Salted.JointInput PublicKeyHash (PKEMessage P) KEMSalt →
      Salted.JointReply KEMKey (PKECoins P))
    (J : Salted.RejectionInput PublicKeyHash (PKEMessage P)
      (PKECiphertext P) KEMSalt → KEMKey)
    (dk : DecapsKey P) (ciphertext : KEMCiphertext P)
    (hbad : pkeEncrypt P encode dk.pk (pkeDecrypt P decode dk.sk ciphertext.pke)
      (G ⟨H dk.pk, pkeDecrypt P decode dk.sk ciphertext.pke, ciphertext.salt⟩).coins ≠
        ciphertext.pke) :
    kemDecaps P encode decode H G J dk ciphertext =
      J ⟨H dk.pk, dk.sigma, ciphertext⟩ := by
  simp [kemDecaps, hbad]

end Cslib.Crypto.HQC
