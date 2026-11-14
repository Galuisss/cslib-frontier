/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SIS.MLKEM.CiphertextEncoding
meta import CslibFrontier.Crypto.Computational.SIS.MLKEM.CiphertextEncoding

/-!
# Tests for ML-KEM ciphertext byte encoding

These ordinary-import clients pin the FIPS 203 Algorithm 14 order: all vector polynomials are
serialized first in increasing position order, followed by the scalar polynomial. They also pin
the three standard ciphertext lengths. They do not claim key serialization, external-interface
validation, correctness, security or FIPS validation.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MLKEMCiphertextEncoding

open Cslib.Crypto Cslib.Crypto.MLKEM

set_option linter.hashCommand false

private def orderingCiphertext : Ciphertext mlkem512 :=
  (fun j i =>
      if j.val = 0 ∧ i.val = 0 then 1
      else if j.val = 0 ∧ i.val = 255 then 513
      else if j.val = 1 ∧ i.val = 0 then 2
      else 0,
    fun i => if i.val = 0 then 3 else 0)

-- Coefficient 255 of the first polynomial is 513: its low and high bits occupy the last two
-- bytes of that polynomial. The next nonzero byte begins the second polynomial at byte 320.
#guard (encodeCiphertext512 orderingCiphertext 0).val == 1
#guard (encodeCiphertext512 orderingCiphertext 318).val == 0x40
#guard (encodeCiphertext512 orderingCiphertext 319).val == 0x80
#guard (encodeCiphertext512 orderingCiphertext 320).val == 2
#guard (encodeCiphertext512 orderingCiphertext 639).val == 0
-- The scalar polynomial follows both 320-byte vector polynomials.
#guard (encodeCiphertext512 orderingCiphertext 640).val == 3

#guard decide (decodeCiphertext512 (encodeCiphertext512 orderingCiphertext) = orderingCiphertext)

example : decodeCiphertext512 (encodeCiphertext512 orderingCiphertext) = orderingCiphertext :=
  decodeCiphertext512_encodeCiphertext512 orderingCiphertext

example : ciphertextByteLength mlkem512 = 768 ∧
    ciphertextByteLength mlkem768 = 1088 ∧ ciphertextByteLength mlkem1024 = 1568 := by
  decide

example : ciphertextBitLength mlkem512 = 6144 ∧
    ciphertextBitLength mlkem768 = 8704 ∧ ciphertextBitLength mlkem1024 = 12544 := by
  decide

end CslibFrontierTests.Crypto.MLKEMCiphertextEncoding
