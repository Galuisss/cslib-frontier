/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
meta import CslibFrontier.Crypto.Computational.MLDSA.FIPS204

/-!
# ML-DSA byte verification

Exercise Algorithm 29's signed shuffle and rejection stream, Algorithm 27's digest boundary,
and Algorithm 21's rejection of noncanonical hint encodings.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204

-- Independent SHAKE256(0^256) expansion followed by the FIPS 204 Algorithm 29 shuffle.
private def zeroDigestSupport (value : ZMod 8380417) : Option (List ℕ) := do
  let c ← sampleInBall .mlDSA44 (List.replicate 32 0)
  return ((List.finRange 256).filter fun i => c i == value).map Fin.val

#guard zeroDigestSupport 1 ==
  some [5, 17, 23, 29, 30, 34, 51, 54, 59, 67, 88, 113, 127, 141, 147, 231, 233, 236, 248]
#guard zeroDigestSupport (-1) == some
  [18, 25, 38, 48, 70, 79, 86, 87, 98, 100, 114, 116, 129, 173, 195, 213, 219, 242, 244, 253]

private def signature (digest : List Byte) (hint : List Byte) : List Byte :=
  digest ++ List.replicate 2304 0 ++ hint

private def digest44 : List Byte := (List.finRange 32).map (fun i => Fin.ofNat 256 i.val)

#guard (sigDecode .mlDSA44 (signature digest44 (List.replicate 84 0))).map (·.digest) ==
  some digest44
#guard (sigDecode .mlDSA44 (signature digest44 (List.replicate 83 0))).isNone
-- Index 7 is used twice in the first row. A nonzero unused byte is also invalid.
#guard (sigDecode .mlDSA44 (signature digest44
  ([7, 7] ++ List.replicate 78 0 ++ [2, 2, 2, 2]))).isNone
#guard (sigDecode .mlDSA44 (signature digest44 (1 :: List.replicate 83 0))).isNone

#guard verify .mlDSA44 [] [] [] [] == some false
#guard verify .mlDSA44 [] [] (List.replicate 256 0) [] == none
