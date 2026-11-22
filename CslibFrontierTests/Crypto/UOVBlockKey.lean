/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.UOV.BlockKey
public import Mathlib.Algebra.Field.ZMod

/-!
# Characteristic-two and Round-3 field clients of UOV block keys and signing linearization

These ordinary-import clients exercise `Cslib.Crypto.UOV.BlockKeySeed` and `FieldChoice`:

1. A concrete characteristic-two `(v = 2, m = 2)` instance over `ZMod 2` with nonzero `O`,
   non-symmetric upper-triangular `P₀⁽¹⁾`, nonzero mixed block `P₁⁽²⁾`, and solved nontrivial
   target `t = ![1, 1]`. Regression guards verify that dropping the `Pᵢ⁽¹⁾ᵀ O` transpose term,
   dropping the mixed block `Pᵢ⁽²⁾`, or omitting the `O x` oil-embedding term from `s` each breaks
   the linear system or produces a vector rejected by `seed.publicMap`.
2. Instantiations over Round-3 `FieldChoice` (`UOV.F16` with `q = 16` and `UOV.F256` with
   `q = 256`, alongside proofs that `ZMod 16` and `ZMod 256` are not domains), verifying
   characteristic two, field cardinalities `16` and `256`, oil-subspace vanishing, and signing
   correctness via `BlockKeySeed.publicMap_signatureVector_eq_iff` without unfolding matrix bodies.
-/

public section

namespace CslibFrontierTests.Crypto.UOVBlockKey

open Cslib Cslib.Crypto Cslib.Crypto.UOV Matrix

/-- Concrete `(v = 2, m = 2)` characteristic-two seed with non-symmetric `P₀⁽¹⁾`, nonzero `O`, and
nonzero mixed block `P₁⁽²⁾`. -/
def charTwoSeed : BlockKeySeed (ZMod 2) 2 2 where
  oilMatrix := !![1, 0; 0, 1]
  vinegarBlock
    | 0 => !![1, 1; 0, 0]
    | 1 => 0
  mixedBlock
    | 0 => 0
    | 1 => !![1, 0; 0, 1]

private def sampleVinegar : Fin 2 → ZMod 2 := ![0, 1]
private def sampleTarget : Fin 2 → ZMod 2 := ![1, 1]
private def sampleOilSolution : Fin 2 → ZMod 2 := ![1, 1]

/-- Both public matrices of `charTwoSeed` are upper triangular on `Fin 4`. -/
theorem charTwoSeed_upper (i : Fin 2) :
    (charTwoSeed.publicMatrix i).IsUpperTriangular := by
  apply charTwoSeed.isUpperTriangular_publicMatrix
  intro a b hab
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [charTwoSeed] at hab ⊢

-- Solved linear system `L x = t - y` over `ZMod 2`.
private theorem charTwoSeed_solves_linear_system :
    charTwoSeed.signingSystemMatrix sampleVinegar *ᵥ sampleOilSolution =
      sampleTarget - vinegarEval charTwoSeed.vinegarBlock sampleVinegar := by
  decide

-- Signing correctness follows directly from `publicMap_signatureVector_eq_iff` without unfolding
-- matrix helpers.
example :
    charTwoSeed.publicMap
      (signatureVector charTwoSeed.oilMatrix sampleVinegar sampleOilSolution) =
        sampleTarget :=
  (charTwoSeed.publicMap_signatureVector_eq_iff
    sampleVinegar sampleOilSolution sampleTarget).mpr charTwoSeed_solves_linear_system

-- Regression 1: dropping the `Pᵢ⁽¹⁾ᵀ O` transpose contribution breaks the signing linear system.
example :
    let wrongS : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i =>
      charTwoSeed.vinegarBlock i * charTwoSeed.oilMatrix + charTwoSeed.mixedBlock i
    signingMatrix wrongS sampleVinegar *ᵥ sampleOilSolution ≠
      sampleTarget - vinegarEval charTwoSeed.vinegarBlock sampleVinegar := by
  decide

-- Regression 2: dropping the mixed block `Pᵢ⁽²⁾` breaks the signing linear system.
example :
    let wrongS : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i =>
      (charTwoSeed.vinegarBlock i + (charTwoSeed.vinegarBlock i).transpose) *
        charTwoSeed.oilMatrix
    signingMatrix wrongS sampleVinegar *ᵥ sampleOilSolution ≠
      sampleTarget - vinegarEval charTwoSeed.vinegarBlock sampleVinegar := by
  decide

-- Regression 3: omitting the `O x` oil-embedding contribution from `s` (`[u; x]` instead of
-- `[u + O x; x]`) fails public-key verification at `sampleTarget`.
example :
    charTwoSeed.publicMap (Fin.append sampleVinegar sampleOilSolution) ≠ sampleTarget := by
  decide

/-! ## Round-3 `FieldChoice` (`GF(16)` and `GF(256)`) clients -/

-- `FieldChoice.gf16` and `FieldChoice.gf256` have orders `16` and `256` and are fields, whereas
-- `ZMod 16` and `ZMod 256` have nontrivial zero divisors (`4 * 4 = 0`, `16 * 16 = 0`).
example :
    Fintype.card FieldChoice.gf16.Carrier = 16 ∧
      Fintype.card FieldChoice.gf256.Carrier = 256 ∧
      ¬ IsDomain (ZMod 16) ∧ ¬ IsDomain (ZMod 256) := by
  refine ⟨FieldChoice.card_carrier .gf16, FieldChoice.card_carrier .gf256, ?_, ?_⟩
  · intro h
    have hz : (4 : ZMod 16) * 4 = 0 := by decide
    rcases mul_eq_zero.mp hz with h4 | h4 <;> revert h4 <;> decide
  · intro h
    have hz : (16 : ZMod 256) * 16 = 0 := by decide
    rcases mul_eq_zero.mp hz with h16 | h16 <;> revert h16 <;> decide

/-- Over either Round-3 field choice (`q ∈ {16, 256}`) and any dimensions `(v, m)`, every
`BlockKeySeed` embeds its `m` oil coordinates injectively, vanishes on its embedded oil space, and
certifies any solution of its `m × m` signing linear system without unfolding matrix definitions. -/
theorem fieldChoice_signing_correct (c : FieldChoice) {v m : ℕ}
    (seed : BlockKeySeed c.Carrier v m)
    (u : Fin v → c.Carrier) (x t : Fin m → c.Carrier)
    (hx : seed.signingSystemMatrix u *ᵥ x = t - vinegarEval seed.vinegarBlock u) :
    Function.Injective (oilEmbed seed.oilMatrix) ∧
      seed.publicMap (oilEmbed seed.oilMatrix x) = 0 ∧
      seed.publicMap (signatureVector seed.oilMatrix u x) = t :=
  ⟨oilEmbed_injective seed.oilMatrix,
    seed.publicMap_vanishesOn _ (oilEmbed_mem_blockOilSubspace seed.oilMatrix x),
    (seed.publicMap_signatureVector_eq_iff u x t).mpr hx⟩

/-- Uniqueness check on `charTwoSeed`: any upper-triangular `2 × 2` lower-right block making the
assembled `4 × 4` block matrix vanish on `blockOilSubspace charTwoSeed.oilMatrix` must equal
`oilBlock`. -/
example (i : Fin 2) (P3 : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (hP3 : P3.IsUpperTriangular)
    (hvan : MultivariateQuadraticMap.VanishesOn
      (blockMatrix (charTwoSeed.vinegarBlock i) (charTwoSeed.mixedBlock i) P3).toQuadraticForm'
      (blockOilSubspace charTwoSeed.oilMatrix)) :
    P3 = oilBlock charTwoSeed.oilMatrix (charTwoSeed.vinegarBlock i) (charTwoSeed.mixedBlock i) :=
  (eq_oilBlock_iff _ _ _).mp ⟨hP3, hvan⟩

/-- Concrete non-symmetric characteristic-two check over `UOV.F16` (`GF(16)`): `1 + 1 = 0`, while
solving `L x = t - y` over `F16` yields a valid preimage of `t`. -/
noncomputable example :
    let α : F16 := AdjoinRoot.root (leastIrreducible 4)
    let seed : BlockKeySeed F16 2 1 :=
      { oilMatrix := !![1; α]
        vinegarBlock := fun _ => !![1, α; 0, 1]
        mixedBlock := fun _ => !![α; 1] }
    let u : Fin 2 → F16 := ![0, 1]
    let x : Fin 1 → F16 := ![1]
    let t : Fin 1 → F16 := vinegarEval seed.vinegarBlock u + seed.signingSystemMatrix u *ᵥ x
    (1 : F16) + 1 = 0 ∧ seed.publicMap (signatureVector seed.oilMatrix u x) = t :=
  ⟨CharTwo.add_self_eq_zero 1,
    (BlockKeySeed.publicMap_signatureVector_eq_iff _ _ _ _).mpr (by simp)⟩

end CslibFrontierTests.Crypto.UOVBlockKey
