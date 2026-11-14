/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Encoding
public import CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE

/-!
# ML-KEM ciphertext byte encoding

FIPS 203 Algorithm 14 encodes the `k` polynomials of a compressed K-PKE ciphertext's vector part
at width `d_u`, encodes its scalar part at width `d_v`, and concatenates those bytes in that order.
Algorithm 15 parses the same two consecutive regions. The resulting lengths are 768, 1088 and
1568 bytes for ML-KEM-512, ML-KEM-768 and ML-KEM-1024, respectively (Section 8, Table 3).

This module connects that exact byte layout to the existing coefficient-form `Ciphertext` type for
the three standardized parameter records. Exact-length byte types make the Algorithm 15 length
boundary explicit. This does not serialize keys, identify NTT and coefficient representations,
implement the external ML-KEM interface's input checks, or prove correctness, security, execution
cost, constant-time behavior or FIPS validation.

## Main definitions

* `Cslib.Crypto.MLKEM.ciphertextByteLength`, `Cslib.Crypto.MLKEM.CiphertextBytes`: the typed wire
  boundary for a parameter record.
* `Cslib.Crypto.MLKEM.encodeCiphertext`, `Cslib.Crypto.MLKEM.decodeCiphertext`: the ciphertext
  codec for a parameter record satisfying `Params.IsStandard`.
* `Cslib.Crypto.MLKEM.encodeCiphertext512`, `Cslib.Crypto.MLKEM.decodeCiphertext512`: thin
  ML-KEM-512 aliases, with analogous aliases for ML-KEM-768 and ML-KEM-1024.

## Main results

* `Cslib.Crypto.MLKEM.decodeCiphertext_encodeCiphertext`: semantic ciphertexts round-trip for
  every standard parameter record.
* `Cslib.Crypto.MLKEM.encodeCiphertext_decodeCiphertext`: every exact-length standard ciphertext
  byte string round-trips.
* `Cslib.Crypto.MLKEM.ciphertextByteLength_mlkem512`: the standard byte lengths, with analogous
  results for ML-KEM-768 and ML-KEM-1024.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Section 5,
  Algorithms 14–15 and Section 8, Table 3][NISTFIPS203].
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

/-- The bytes in the `k` width-`d_u` vector encodings followed by the width-`d_v` scalar
encoding for a standard parameter record. This is algebraically `32 * (d_u * k + d_v)`, the
length in FIPS 203 Algorithm 14; the three codecs below deliberately do not apply it to the
library's nonstandard degrees. -/
def ciphertextByteLength (P : Params) : ℕ :=
  P.k * (32 * P.du) + 32 * P.dv

/-- The byte length agrees with the factored expression in FIPS 203 Algorithm 14. -/
theorem ciphertextByteLength_eq_fips (P : Params) :
    ciphertextByteLength P = 32 * (P.du * P.k + P.dv) := by
  simp only [ciphertextByteLength, Nat.mul_add]
  ac_rfl

/-- The exact serialized ciphertext boundary selected by `ciphertextByteLength`. This module
constructs values of this type only for the three standard parameter records. -/
abbrev CiphertextBytes (P : Params) := FixedBytes (ciphertextByteLength P)

/-- The serialized ciphertext boundary measured in bits. This is the I/O width to charge when the
codec is later realized as a machine program; it is not a running-time or program-size bound. -/
def ciphertextBitLength (P : Params) : ℕ :=
  8 * ciphertextByteLength P

/-- ML-KEM-512 ciphertexts occupy 768 bytes. -/
@[simp] theorem ciphertextByteLength_mlkem512 : ciphertextByteLength mlkem512 = 768 := by
  decide

/-- ML-KEM-768 ciphertexts occupy 1088 bytes. -/
@[simp] theorem ciphertextByteLength_mlkem768 : ciphertextByteLength mlkem768 = 1088 := by
  decide

/-- ML-KEM-1024 ciphertexts occupy 1568 bytes. -/
@[simp] theorem ciphertextByteLength_mlkem1024 : ciphertextByteLength mlkem1024 = 1568 := by
  decide

/-- ML-KEM-512 ciphertexts occupy 6144 bits. -/
@[simp] theorem ciphertextBitLength_mlkem512 : ciphertextBitLength mlkem512 = 6144 := by
  decide

/-- ML-KEM-768 ciphertexts occupy 8704 bits. -/
@[simp] theorem ciphertextBitLength_mlkem768 : ciphertextBitLength mlkem768 = 8704 := by
  decide

/-- ML-KEM-1024 ciphertexts occupy 12544 bits. -/
@[simp] theorem ciphertextBitLength_mlkem1024 : ciphertextBitLength mlkem1024 = 12544 := by
  decide

private def leftBytes {m n : ℕ} (B : FixedBytes (m + n)) : FixedBytes m := fun i =>
  B (Fin.castAdd n i)

private def rightBytes {m n : ℕ} (B : FixedBytes (m + n)) : FixedBytes n := fun i =>
  B (Fin.natAdd m i)

@[simp] private theorem leftBytes_append {m n : ℕ} (X : FixedBytes m) (Y : FixedBytes n) :
    leftBytes (FixedBytes.append X Y) = X := by
  funext i
  simp [leftBytes]

@[simp] private theorem rightBytes_append {m n : ℕ} (X : FixedBytes m) (Y : FixedBytes n) :
    rightBytes (FixedBytes.append X Y) = Y := by
  funext i
  simp [rightBytes]

@[simp] private theorem append_leftBytes_rightBytes {m n : ℕ} (B : FixedBytes (m + n)) :
    FixedBytes.append (leftBytes B) (rightBytes B) = B := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [leftBytes]
  · simp [rightBytes]

private abbrev CiphertextParts (k : ℕ) (du dv : CodecWidth) :=
  (Fin k → Coefficients du) × Coefficients dv

private def encodeCiphertextParts (k : ℕ) (du dv : CodecWidth)
    (ct : CiphertextParts k du dv) : FixedBytes (k * (32 * du.val) + 32 * dv.val) :=
  FixedBytes.append (byteEncodeVector du k ct.1) (byteEncode dv ct.2)

private def decodeCiphertextParts (k : ℕ) (du dv : CodecWidth)
    (B : FixedBytes (k * (32 * du.val) + 32 * dv.val)) : CiphertextParts k du dv :=
  (byteDecodeVector du k
      (leftBytes (m := k * (32 * du.val)) (n := 32 * dv.val) B),
    byteDecode dv (rightBytes (m := k * (32 * du.val)) (n := 32 * dv.val) B))

@[simp] private theorem decodeCiphertextParts_encodeCiphertextParts (k : ℕ)
    (du dv : CodecWidth) (ct : CiphertextParts k du dv) :
    decodeCiphertextParts k du dv (encodeCiphertextParts k du dv ct) = ct := by
  simp [decodeCiphertextParts, encodeCiphertextParts]

private theorem encodeCiphertextParts_decodeCiphertextParts (k : ℕ)
    (du dv : CodecWidth) (hdu : du.val ≤ 11) (hdv : dv.val ≤ 11)
    (B : FixedBytes (k * (32 * du.val) + 32 * dv.val)) :
    encodeCiphertextParts k du dv (decodeCiphertextParts k du dv B) = B := by
  simp only [encodeCiphertextParts, decodeCiphertextParts]
  rw [byteEncodeVector_byteDecodeVector du hdu,
    byteEncode_byteDecode dv hdv, append_leftBytes_rightBytes]

/-! ### Standard parameter records -/

/-- Serialize a ciphertext in the order of FIPS 203 Algorithm 14. The standardness proof fixes
the rank and the two codec widths to one of the three approved parameter records. -/
def encodeCiphertext {P : Params} (h : P.IsStandard) (ct : Ciphertext P) : CiphertextBytes P := by
  rcases h with rfl | rfl | rfl
  · exact encodeCiphertextParts 2 width10 width4 ct
  · exact encodeCiphertextParts 3 width10 width4 ct
  · exact encodeCiphertextParts 4 width11 width5 ct

/-- Parse an exact-length ciphertext as in FIPS 203 Algorithm 15. The standardness proof fixes the
rank and the two codec widths to one of the three approved parameter records. -/
def decodeCiphertext {P : Params} (h : P.IsStandard) (B : CiphertextBytes P) : Ciphertext P := by
  rcases h with rfl | rfl | rfl
  · exact decodeCiphertextParts 2 width10 width4 B
  · exact decodeCiphertextParts 3 width10 width4 B
  · exact decodeCiphertextParts 4 width11 width5 B

/-- A ciphertext for any standard parameter record survives serialization and parsing. -/
@[simp] theorem decodeCiphertext_encodeCiphertext {P : Params} (h : P.IsStandard)
    (ct : Ciphertext P) : decodeCiphertext h (encodeCiphertext h ct) = ct := by
  rcases h with rfl | rfl | rfl
  · simpa [decodeCiphertext, encodeCiphertext] using
      decodeCiphertextParts_encodeCiphertextParts 2 width10 width4 ct
  · simpa [decodeCiphertext, encodeCiphertext] using
      decodeCiphertextParts_encodeCiphertextParts 3 width10 width4 ct
  · simpa [decodeCiphertext, encodeCiphertext] using
      decodeCiphertextParts_encodeCiphertextParts 4 width11 width5 ct

/-- Every exact-length ciphertext byte string for a standard parameter record survives parsing
and serialization. -/
@[simp] theorem encodeCiphertext_decodeCiphertext {P : Params} (h : P.IsStandard)
    (B : CiphertextBytes P) : encodeCiphertext h (decodeCiphertext h B) = B := by
  rcases h with rfl | rfl | rfl
  · simpa [decodeCiphertext, encodeCiphertext] using
      encodeCiphertextParts_decodeCiphertextParts 2 width10 width4 (by decide) (by decide) B
  · simpa [decodeCiphertext, encodeCiphertext] using
      encodeCiphertextParts_decodeCiphertextParts 3 width10 width4 (by decide) (by decide) B
  · simpa [decodeCiphertext, encodeCiphertext] using
      encodeCiphertextParts_decodeCiphertextParts 4 width11 width5 (by decide) (by decide) B

private theorem mlkem512_isStandard : mlkem512.IsStandard := Or.inl rfl

private theorem mlkem768_isStandard : mlkem768.IsStandard := Or.inr (Or.inl rfl)

private theorem mlkem1024_isStandard : mlkem1024.IsStandard := Or.inr (Or.inr rfl)

/-! ### Thin aliases for the three standard records -/

/-- Serialize an ML-KEM-512 ciphertext in the order of FIPS 203 Algorithm 14. -/
def encodeCiphertext512 (ct : Ciphertext mlkem512) : CiphertextBytes mlkem512 :=
  encodeCiphertext mlkem512_isStandard ct

/-- Parse an exact-length ML-KEM-512 ciphertext as in FIPS 203 Algorithm 15. -/
def decodeCiphertext512 (B : CiphertextBytes mlkem512) : Ciphertext mlkem512 :=
  decodeCiphertext mlkem512_isStandard B

/-- An ML-KEM-512 ciphertext survives serialization and parsing. -/
@[simp] theorem decodeCiphertext512_encodeCiphertext512 (ct : Ciphertext mlkem512) :
    decodeCiphertext512 (encodeCiphertext512 ct) = ct := by
  simpa only [decodeCiphertext512, encodeCiphertext512] using
    decodeCiphertext_encodeCiphertext mlkem512_isStandard ct

/-- Every exact-length ML-KEM-512 ciphertext byte string survives parsing and serialization. -/
@[simp] theorem encodeCiphertext512_decodeCiphertext512 (B : CiphertextBytes mlkem512) :
    encodeCiphertext512 (decodeCiphertext512 B) = B := by
  simpa only [decodeCiphertext512, encodeCiphertext512] using
    encodeCiphertext_decodeCiphertext mlkem512_isStandard B

/-- Serialize an ML-KEM-768 ciphertext in the order of FIPS 203 Algorithm 14. -/
def encodeCiphertext768 (ct : Ciphertext mlkem768) : CiphertextBytes mlkem768 :=
  encodeCiphertext mlkem768_isStandard ct

/-- Parse an exact-length ML-KEM-768 ciphertext as in FIPS 203 Algorithm 15. -/
def decodeCiphertext768 (B : CiphertextBytes mlkem768) : Ciphertext mlkem768 :=
  decodeCiphertext mlkem768_isStandard B

/-- An ML-KEM-768 ciphertext survives serialization and parsing. -/
@[simp] theorem decodeCiphertext768_encodeCiphertext768 (ct : Ciphertext mlkem768) :
    decodeCiphertext768 (encodeCiphertext768 ct) = ct := by
  simpa only [decodeCiphertext768, encodeCiphertext768] using
    decodeCiphertext_encodeCiphertext mlkem768_isStandard ct

/-- Every exact-length ML-KEM-768 ciphertext byte string survives parsing and serialization. -/
@[simp] theorem encodeCiphertext768_decodeCiphertext768 (B : CiphertextBytes mlkem768) :
    encodeCiphertext768 (decodeCiphertext768 B) = B := by
  simpa only [decodeCiphertext768, encodeCiphertext768] using
    encodeCiphertext_decodeCiphertext mlkem768_isStandard B

/-- Serialize an ML-KEM-1024 ciphertext in the order of FIPS 203 Algorithm 14. -/
def encodeCiphertext1024 (ct : Ciphertext mlkem1024) : CiphertextBytes mlkem1024 :=
  encodeCiphertext mlkem1024_isStandard ct

/-- Parse an exact-length ML-KEM-1024 ciphertext as in FIPS 203 Algorithm 15. -/
def decodeCiphertext1024 (B : CiphertextBytes mlkem1024) : Ciphertext mlkem1024 :=
  decodeCiphertext mlkem1024_isStandard B

/-- An ML-KEM-1024 ciphertext survives serialization and parsing. -/
@[simp] theorem decodeCiphertext1024_encodeCiphertext1024 (ct : Ciphertext mlkem1024) :
    decodeCiphertext1024 (encodeCiphertext1024 ct) = ct := by
  simpa only [decodeCiphertext1024, encodeCiphertext1024] using
    decodeCiphertext_encodeCiphertext mlkem1024_isStandard ct

/-- Every exact-length ML-KEM-1024 ciphertext byte string survives parsing and serialization. -/
@[simp] theorem encodeCiphertext1024_decodeCiphertext1024 (B : CiphertextBytes mlkem1024) :
    encodeCiphertext1024 (decodeCiphertext1024 B) = B := by
  simpa only [decodeCiphertext1024, encodeCiphertext1024] using
    encodeCiphertext_decodeCiphertext mlkem1024_isStandard B

end Cslib.Crypto.MLKEM
