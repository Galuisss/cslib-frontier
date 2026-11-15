/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.PKE
public import CslibFrontier.Crypto.Primitives.HQC.SupportDensity

/-!
# Published HQC parameter sets

This file records the three HQC version 5.1 parameter rows used by the ideal algebraic PKE model.
The ring length, message length, sparse weights and concatenated-code length are from
[HQC2026], Tables 7 and 8, pp. 32 and 44. The truncation length is
`ℓ = n - n₁n₂'`, as specified in Table 2, p. 9.

The source does not assign a numerical value to the decoder threshold `Δ` appearing in the PKE
correctness discussion. Each parameter set therefore takes that value explicitly. These
definitions do not assert a numerical decoding-failure rate or identify the rounded density
figures printed in Table 17 with exact values.

## Main definitions

* `Cslib.Crypto.HQC.hqc1PKEParams`, `Cslib.Crypto.HQC.hqc3PKEParams`,
  `Cslib.Crypto.HQC.hqc5PKEParams`: the three published algebraic PKE parameter rows, with an
  explicit decoder threshold.
* `Cslib.Crypto.HQC.pkeCoinsUpperDensity32`: the exact production-to-ideal upper factor for the
  three encryption-coin support draws.

## Main results

* `Cslib.Crypto.HQC.pkeCoinsUpperDensity32_eq_cube`: equal encryption and error weights reduce
  the exact three-draw factor to a cube.

## References

* [HQC specification, version 5.1][HQC2026], Tables 2, 7, 8 and 17, pp. 9, 32, 44 and 65.
-/

public section

namespace Cslib.Crypto.HQC

open scoped ENNReal

/-- The HQC-1 row of [HQC2026], Table 8, p. 44, with `ℓ = 17669 - 17664 = 5` from
Tables 2 and 7. The decoder threshold remains an explicit input because the source gives no
numerical value for `Δ`. -/
@[expose] def hqc1PKEParams (decoderRadius : ℕ) : PKEParams where
  n := 17669
  k := 128
  ell := 5
  omega := 67
  omegaR := 76
  omegaE := 76
  delta := decoderRadius
  ell_le_n := by decide
  omega_le_n := by decide
  omegaR_le_n := by decide
  omegaE_le_n := by decide

/-- The HQC-3 row of [HQC2026], Table 8, p. 44, with `ℓ = 35851 - 35840 = 11` from
Tables 2 and 7. The decoder threshold remains an explicit input because the source gives no
numerical value for `Δ`. -/
@[expose] def hqc3PKEParams (decoderRadius : ℕ) : PKEParams where
  n := 35851
  k := 192
  ell := 11
  omega := 101
  omegaR := 114
  omegaE := 114
  delta := decoderRadius
  ell_le_n := by decide
  omega_le_n := by decide
  omegaR_le_n := by decide
  omegaE_le_n := by decide

/-- The HQC-5 row of [HQC2026], Table 8, p. 44, with `ℓ = 57637 - 57600 = 37` from
Tables 2 and 7. The decoder threshold remains an explicit input because the source gives no
numerical value for `Δ`. -/
@[expose] def hqc5PKEParams (decoderRadius : ℕ) : PKEParams where
  n := 57637
  k := 256
  ell := 37
  omega := 132
  omegaR := 150
  omegaE := 150
  delta := decoderRadius
  ell_le_n := by decide
  omega_le_n := by decide
  omegaR_le_n := by decide
  omegaE_le_n := by decide

/-- The exact upper density factor for the production encryption-coin draws `(r₂, e, r₁)` when
each shrinking-interval candidate is drawn from 32 fair bits. This is an exact product, not a
rounded Table-17 decimal and not a multiplier for a difference or game advantage. -/
noncomputable def pkeCoinsUpperDensity32 (P : PKEParams) : ℝ≥0∞ :=
  supportUpperDensity 32 P.n 0 P.omegaR ^ 2 *
    supportUpperDensity 32 P.n 0 P.omegaE

/-- When the encryption-vector and encryption-error weights agree, the exact three-draw upper
density is the cube of their common one-draw factor. -/
theorem pkeCoinsUpperDensity32_eq_cube (P : PKEParams) (h : P.omegaE = P.omegaR) :
    pkeCoinsUpperDensity32 P = supportUpperDensity 32 P.n 0 P.omegaR ^ 3 := by
  unfold pkeCoinsUpperDensity32
  rw [h]
  exact (pow_succ _ 2).symm

end Cslib.Crypto.HQC
