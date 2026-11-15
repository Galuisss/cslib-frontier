/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of frontier HQC parameter declarations)

public import CslibFrontier.Crypto.Primitives.HQC.Parameters

/-! Checked source fields and exact production-density specializations for HQC-1, HQC-3 and
HQC-5. -/

public section

namespace CslibFrontierTests.HQCParameters

open Cslib.Crypto.HQC

example (decoderRadius : ℕ) :
    (hqc1PKEParams decoderRadius).n = 17669 ∧
      (hqc1PKEParams decoderRadius).k = 128 ∧
      (hqc1PKEParams decoderRadius).ell = 5 ∧
      (hqc1PKEParams decoderRadius).codeLen = 17664 ∧
      (hqc1PKEParams decoderRadius).omega = 67 ∧
      (hqc1PKEParams decoderRadius).omegaR = 76 ∧
      (hqc1PKEParams decoderRadius).omegaE = 76 ∧
      (hqc1PKEParams decoderRadius).delta = decoderRadius := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example (decoderRadius : ℕ) :
    (hqc3PKEParams decoderRadius).n = 35851 ∧
      (hqc3PKEParams decoderRadius).k = 192 ∧
      (hqc3PKEParams decoderRadius).ell = 11 ∧
      (hqc3PKEParams decoderRadius).codeLen = 35840 ∧
      (hqc3PKEParams decoderRadius).omega = 101 ∧
      (hqc3PKEParams decoderRadius).omegaR = 114 ∧
      (hqc3PKEParams decoderRadius).omegaE = 114 ∧
      (hqc3PKEParams decoderRadius).delta = decoderRadius := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example (decoderRadius : ℕ) :
    (hqc5PKEParams decoderRadius).n = 57637 ∧
      (hqc5PKEParams decoderRadius).k = 256 ∧
      (hqc5PKEParams decoderRadius).ell = 37 ∧
      (hqc5PKEParams decoderRadius).codeLen = 57600 ∧
      (hqc5PKEParams decoderRadius).omega = 132 ∧
      (hqc5PKEParams decoderRadius).omegaR = 150 ∧
      (hqc5PKEParams decoderRadius).omegaE = 150 ∧
      (hqc5PKEParams decoderRadius).delta = decoderRadius := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- These are the exact message-space exponents used in the Equation-(15) denominators.
example (decoderRadius1 decoderRadius3 decoderRadius5 : ℕ) :
    (2 : ℕ) ^ (hqc1PKEParams decoderRadius1).k = 2 ^ 128 ∧
      (2 : ℕ) ^ (hqc3PKEParams decoderRadius3).k = 2 ^ 192 ∧
      (2 : ℕ) ^ (hqc5PKEParams decoderRadius5).k = 2 ^ 256 := by
  exact ⟨rfl, rfl, rfl⟩

example (decoderRadius : ℕ) :
    pkeCoinsUpperDensity32 (hqc1PKEParams decoderRadius) =
      supportUpperDensity 32 17669 0 76 ^ 3 :=
  pkeCoinsUpperDensity32_eq_cube _ rfl

example (decoderRadius : ℕ) :
    pkeCoinsUpperDensity32 (hqc3PKEParams decoderRadius) =
      supportUpperDensity 32 35851 0 114 ^ 3 :=
  pkeCoinsUpperDensity32_eq_cube _ rfl

example (decoderRadius : ℕ) :
    pkeCoinsUpperDensity32 (hqc5PKEParams decoderRadius) =
      supportUpperDensity 32 57637 0 150 ^ 3 :=
  pkeCoinsUpperDensity32_eq_cube _ rfl

end CslibFrontierTests.HQCParameters
