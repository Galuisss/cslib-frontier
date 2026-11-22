/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UOV.Field
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.UpperTriangularQuadratic
public import CslibFrontier.Foundations.LinearAlgebra.MultivariateQuadratic
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Round-3 UOV block public keys and signing linearization

In Version 3.0 of the UOV specification ([UOV2026], §3.1, pp. 11–13, and §3.2.3 / Figure 2,
pp. 14–17), the secret oil subspace is the column space of the `(v + m) × m` block matrix
`[O; Iₘ]` for `O ∈ R^{v × m}`, and each of the `m` homogeneous public polynomials is represented
by an upper-triangular `(v + m) × (v + m)` block matrix

```text
Pᵢ = [[Pᵢ⁽¹⁾, Pᵢ⁽²⁾],
      [0,     Pᵢ⁽³⁾]]
```

with `Pᵢ⁽³⁾ = Upper(-Oᵀ Pᵢ⁽¹⁾ O - Oᵀ Pᵢ⁽²⁾)`. Because `Upper(M) - M` induces an alternating
bilinear form in every characteristic (`Matrix.isAlt_toLinearMap₂'_upperQuadratic_sub`), the
restricted matrix `[Oᵀ Iₘ] Pᵢ [O; Iₘ] = Oᵀ Pᵢ⁽¹⁾ O + Oᵀ Pᵢ⁽²⁾ + Pᵢ⁽³⁾` induces an alternating
bilinear form and therefore vanishes identically on the embedded oil subspace, including in
characteristic two.

To invert the resulting public map `P : R^{v + m} → R^m` at target `t` given a vinegar vector
`u ∈ R^v`, UOV forms the candidate preimage `s = [u; 0] + [O; Iₘ] x`, the vinegar evaluation
`yᵢ = uᵀ Pᵢ⁽¹⁾ u`, the precomputed secret-key matrices `Sᵢ = (Pᵢ⁽¹⁾ + Pᵢ⁽¹⁾ᵀ) O + Pᵢ⁽²⁾`, and the
`m × m` linear system matrix `L` whose `i`-th row is `uᵀ Sᵢ`. Reusing
`MultivariateQuadraticMap.map_add_of_mem` and `MultivariateQuadraticMap.polar_ofMatrices_apply`
yields the exact characteristic-independent linearization law

```text
P(s)ᵢ = uᵀ Pᵢ⁽¹⁾ u + (uᵀ Sᵢ) x,
```

so `P(s) = t` if and only if `L x = t - y`.

The algebraic construction is parameterized over any commutative ring `R` and dimensions `(v, m)`.
`FieldChoice` links the Round-3 field orders `q ∈ {16, 256}` ([UOV2026], §3.2.1, p. 14, and §3.3,
p. 19) to the genuine characteristic-two extension fields `UOV.F16 = F₂[X]/(X⁴ + X + 1)` and
`UOV.F256 = F₂[X]/(X⁸ + X⁴ + X³ + X + 1)` rather than the non-domain residue rings `ZMod 16` or
`ZMod 256`. Seed expansion (`SHAKE256` / `AES128-CTR`), byte serialization, the 256-attempt
counter loop, retry failure bounds, and ROM/QROM security reductions remain open under #4987.

## Main definitions

* `Cslib.Crypto.UOV.BlockKeySeed`: the secret oil matrix `O` together with the upper-left and
  mixed blocks `P⁽¹⁾` and `P⁽²⁾`.
* `Cslib.Crypto.UOV.vinegarEmbed`, `Cslib.Crypto.UOV.oilEmbed`,
  `Cslib.Crypto.UOV.oilEmbedLinear`, `Cslib.Crypto.UOV.blockOilSubspace`,
  `Cslib.Crypto.UOV.signatureVector`: `[u; 0]`, `[O; Iₘ] x`, the `[O; Iₘ]` column-space
  submodule, and `s = [u; 0] + [O; Iₘ] x`.
* `Cslib.Crypto.UOV.oilBlock`, `Cslib.Crypto.UOV.blockMatrix`,
  `Cslib.Crypto.UOV.BlockKeySeed.publicMatrix`, `Cslib.Crypto.UOV.BlockKeySeed.publicMap`:
  `Pᵢ⁽³⁾ = Upper(-Oᵀ Pᵢ⁽¹⁾ O - Oᵀ Pᵢ⁽²⁾)`, the reindexed `(v + m) × (v + m)` block matrix `Pᵢ`,
  and the induced `MultivariateQuadraticMap`.
* `Cslib.Crypto.UOV.linearizationMatrix`, `Cslib.Crypto.UOV.vinegarEval`,
  `Cslib.Crypto.UOV.signingMatrix`, `Cslib.Crypto.UOV.BlockKeySeed.signingSystemMatrix`:
  `Sᵢ = (Pᵢ⁽¹⁾ + Pᵢ⁽¹⁾ᵀ) O + Pᵢ⁽²⁾`, `yᵢ = uᵀ Pᵢ⁽¹⁾ u`, and the row matrix `L`.
* `Cslib.Crypto.UOV.FieldChoice`: Round-3 field selector (`gf16` / `gf256`) mapping `q ∈ {16, 256}`
  to `UOV.F16` and `UOV.F256`.

## Main results

* `Cslib.Crypto.UOV.oilEmbed_injective`: the oil-space parameterization `x ↦ [O x; x]` is
  injective over every commutative ring.
* `Cslib.Crypto.UOV.isUpperTriangular_blockMatrix`,
  `Cslib.Crypto.UOV.BlockKeySeed.isUpperTriangular_publicMatrix`: `Pᵢ` is upper triangular whenever
  `Pᵢ⁽¹⁾` is.
* `Cslib.Crypto.UOV.isAlt_oilRestriction`: `[Oᵀ Iₘ] Pᵢ [O; Iₘ]` induces an alternating bilinear
  form in every characteristic.
* `Cslib.Crypto.UOV.eq_oilBlock_iff`: `oilBlock O P1 P2` is the unique upper-triangular `m × m`
  block making `(blockMatrix P1 P2 P3).toQuadraticForm'` vanish on `blockOilSubspace O`.
* `Cslib.Crypto.UOV.BlockKeySeed.publicMap_vanishesOn`: the constructed public map vanishes on
  `blockOilSubspace O`.
* `Cslib.Crypto.UOV.BlockKeySeed.publicMap_signatureVector_apply`,
  `Cslib.Crypto.UOV.BlockKeySeed.publicMap_signatureVector`: exact coordinate and vector signing
  linearization identities `P([u; 0] + [O; Iₘ] x) = y + L x`.
* `Cslib.Crypto.UOV.BlockKeySeed.publicMap_signatureVector_eq_iff`: `P(s) = t ↔ L x = t - y`.
* `Cslib.Crypto.UOV.FieldChoice.card_carrier`: `Fintype.card c.Carrier = c.order` (`16` or `256`).

## References

* [W. Beullens et al., *UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting
  Documentation*, v3.0, §3.1, pp. 11–13; §3.2.1–3.2.3 / Figure 2, pp. 13–17; §3.3, p. 19][UOV2026]
-/

public section

namespace Cslib.Crypto.UOV

open Matrix

private theorem append_comp_finSumFinEquiv {α : Type*} {v m : ℕ}
    (a : Fin v → α) (b : Fin m → α) :
    Fin.append a b ∘ finSumFinEquiv = Sum.elim a b := by
  ext s
  cases s with
  | inl i => simp [Fin.append_left]
  | inr j => simp [Fin.append_right]

section BlockConstruction

variable {R : Type*} [CommRing R] {v m : ℕ}

/-- The expanded algebraic inputs from which Round-3 UOV constructs its public key and signing
matrices ([UOV2026], Figure 2, p. 16): the secret oil matrix `O ∈ R^{v × m}` together with the
vinegar-vinegar blocks `P1 i ∈ R^{v × v}` and vinegar-oil blocks `P2 i ∈ R^{v × m}`. -/
structure BlockKeySeed (R : Type*) (v m : ℕ) where
  /-- Secret oil-space generator `O ∈ R^{v × m}` defining the oil embedding `x ↦ [O x; x]`. -/
  oilMatrix : Matrix (Fin v) (Fin m) R
  /-- Upper-left vinegar quadratic blocks `Pᵢ⁽¹⁾ ∈ R^{v × v}`. -/
  vinegarBlock : Fin m → Matrix (Fin v) (Fin v) R
  /-- Upper-right mixed vinegar-oil blocks `Pᵢ⁽²⁾ ∈ R^{v × m}`. -/
  mixedBlock : Fin m → Matrix (Fin v) (Fin m) R

/-- Embed a vinegar vector `u ∈ R^v` as `[u; 0] ∈ R^{v + m}`. -/
@[expose] def vinegarEmbed (u : Fin v → R) : Fin (v + m) → R :=
  Fin.append u 0

/-- Embed an oil coordinate vector `x ∈ R^m` as `[O x; x] ∈ R^{v + m}` ([UOV2026], §3.1, p. 12). -/
@[expose] def oilEmbed (O : Matrix (Fin v) (Fin m) R) (x : Fin m → R) : Fin (v + m) → R :=
  Fin.append (O *ᵥ x) x

/-- The oil-space parameterization `x ↦ [O x; x]` is injective because its last `m` coordinates
recover `x` directly ([UOV2026], §3.1, p. 12). -/
theorem oilEmbed_injective (O : Matrix (Fin v) (Fin m) R) :
    Function.Injective (oilEmbed O) := by
  intro x y h
  ext j
  simpa [oilEmbed, Fin.append_right] using congrFun h (finSumFinEquiv (Sum.inr j))

/-- Linear map `x ↦ [O x; x]` parametrizing the Round-3 UOV oil subspace. -/
def oilEmbedLinear (O : Matrix (Fin v) (Fin m) R) :
    (Fin m → R) →ₗ[R] (Fin (v + m) → R) where
  toFun := oilEmbed O
  map_add' x y := by
    ext k
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
    · simp [oilEmbed, Fin.append_left, mulVec_add]
    · simp [oilEmbed, Fin.append_right]
  map_smul' c x := by
    ext k
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
    · simp [oilEmbed, Fin.append_left, mulVec_smul]
    · simp [oilEmbed, Fin.append_right]

@[simp]
theorem oilEmbedLinear_apply (O : Matrix (Fin v) (Fin m) R) (x : Fin m → R) :
    oilEmbedLinear O x = oilEmbed O x := by
  rfl

/-- The hidden oil subspace spanned by the columns of `[O; Iₘ]`. -/
def blockOilSubspace (O : Matrix (Fin v) (Fin m) R) :
    Submodule R (Fin (v + m) → R) :=
  LinearMap.range (oilEmbedLinear O)

@[simp]
theorem mem_blockOilSubspace {O : Matrix (Fin v) (Fin m) R} {z : Fin (v + m) → R} :
    z ∈ blockOilSubspace O ↔ ∃ x, oilEmbed O x = z := by
  simp [blockOilSubspace]

/-- Every vector `oilEmbed O x` lies in `blockOilSubspace O`. -/
theorem oilEmbed_mem_blockOilSubspace (O : Matrix (Fin v) (Fin m) R) (x : Fin m → R) :
    oilEmbed O x ∈ blockOilSubspace O :=
  ⟨x, rfl⟩

/-- Candidate UOV signature vector `s = [u; 0] + [O; Iₘ] x = [u + O x; x]`
([UOV2026], §3.1, p. 12). -/
@[expose] def signatureVector (O : Matrix (Fin v) (Fin m) R)
    (u : Fin v → R) (x : Fin m → R) : Fin (v + m) → R :=
  vinegarEmbed u + oilEmbed O x

/-- `signatureVector O u x` equals `Fin.append (u + O *ᵥ x) x`. -/
theorem signatureVector_eq_append (O : Matrix (Fin v) (Fin m) R)
    (u : Fin v → R) (x : Fin m → R) :
    signatureVector O u x = Fin.append (u + O *ᵥ x) x := by
  ext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · simp [signatureVector, vinegarEmbed, oilEmbed, Fin.append_left]
  · simp [signatureVector, vinegarEmbed, oilEmbed, Fin.append_right]

/-- The lower-right oil block `Pᵢ⁽³⁾ = Upper(-Oᵀ Pᵢ⁽¹⁾ O - Oᵀ Pᵢ⁽²⁾)` ([UOV2026], §3.1, p. 12,
and Figure 2, line 5, p. 16). -/
@[expose] def oilBlock (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R) :
    Matrix (Fin m) (Fin m) R :=
  (-O.transpose * P1 * O - O.transpose * P2).upperQuadratic

/-- In characteristic two, signs drop from `oilBlock`:
`Pᵢ⁽³⁾ = Upper(Oᵀ Pᵢ⁽¹⁾ O + Oᵀ Pᵢ⁽²⁾)`. -/
theorem oilBlock_eq_of_charTwo [CharP R 2] (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R) :
    oilBlock O P1 P2 = (O.transpose * P1 * O + O.transpose * P2).upperQuadratic := by
  rw [oilBlock]
  congr 1
  ext i j
  simp [Matrix.neg_mul, CharTwo.sub_eq_add, CharTwo.neg_eq]

/-- Assemble the `(v + m) × (v + m)` public polynomial matrix `[[P1, P2], [0, P3]]` indexed on
`Fin (v + m)` via `finSumFinEquiv` ([UOV2026], §3.1, p. 12). -/
@[expose] def blockMatrix (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R)
    (P3 : Matrix (Fin m) (Fin m) R) : Matrix (Fin (v + m)) (Fin (v + m)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P1 P2 0 P3)

/-- When `P1` and `P3` are upper triangular, the assembled `(v + m) × (v + m)` block matrix is
upper triangular under the standard order on `Fin (v + m)`. -/
theorem isUpperTriangular_blockMatrix {P1 : Matrix (Fin v) (Fin v) R}
    (P2 : Matrix (Fin v) (Fin m) R) {P3 : Matrix (Fin m) (Fin m) R}
    (hP1 : P1.IsUpperTriangular) (hP3 : P3.IsUpperTriangular) :
    (blockMatrix P1 P2 P3).IsUpperTriangular := by
  intro a b hab
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective a <;>
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective b
  · have hij : j < i := by
      simp only [id_eq, finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd] at hab
      exact hab
    simpa [blockMatrix] using hP1 hij
  · exfalso
    simp only [id_eq, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def,
      Fin.val_castAdd, Fin.val_natAdd] at hab
    omega
  · simp [blockMatrix]
  · have hij : j < i := by
      simp only [id_eq, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd] at hab
      omega
    simpa [blockMatrix] using hP3 hij

/-- The restricted oil-space matrix `Oᵀ P1 O + Oᵀ P2 + oilBlock O P1 P2` (`[Oᵀ Iₘ] Pᵢ [O; Iₘ]`)
induces an alternating bilinear form in every characteristic ([UOV2026], §3.1, p. 12). -/
theorem isAlt_oilRestriction (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R) :
    (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R)
      (O.transpose * P1 * O + O.transpose * P2 + oilBlock O P1 P2)).IsAlt := by
  let M : Matrix (Fin m) (Fin m) R := -O.transpose * P1 * O - O.transpose * P2
  have hsub : O.transpose * P1 * O + O.transpose * P2 + oilBlock O P1 P2 =
      M.upperQuadratic - M := by
    ext i j
    simp only [oilBlock, M, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_mul, Matrix.neg_apply]
    ring
  rw [hsub]
  exact Matrix.isAlt_toLinearMap₂'_upperQuadratic_sub M

private theorem append_dotProduct_blockMatrix_mulVec (P1 : Matrix (Fin v) (Fin v) R)
    (P2 : Matrix (Fin v) (Fin m) R) (P3 : Matrix (Fin m) (Fin m) R)
    (a c : Fin v → R) (b d : Fin m → R) :
    Fin.append a b ⬝ᵥ (blockMatrix P1 P2 P3 *ᵥ Fin.append c d) =
      a ⬝ᵥ (P1 *ᵥ c) + a ⬝ᵥ (P2 *ᵥ d) + b ⬝ᵥ (P3 *ᵥ d) := by
  have hsum : Fin.append a b ⬝ᵥ (blockMatrix P1 P2 P3 *ᵥ Fin.append c d) =
      Sum.elim a b ⬝ᵥ (Matrix.fromBlocks P1 P2 0 P3 *ᵥ Sum.elim c d) := by
    simp only [blockMatrix, dotProduct, mulVec]
    rw [← finSumFinEquiv.sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h1 : Fin.append a b (finSumFinEquiv s) = Sum.elim a b s :=
      congrFun (append_comp_finSumFinEquiv a b) s
    rw [h1]
    congr 1
    rw [← finSumFinEquiv.sum_comp]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h2 : Fin.append c d (finSumFinEquiv t) = Sum.elim c d t :=
      congrFun (append_comp_finSumFinEquiv c d) t
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, h2]
  rw [hsum, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, dotProduct_add]

private theorem toQuadraticForm'_blockMatrix_oilEmbed (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R)
    (P3 : Matrix (Fin m) (Fin m) R) (x : Fin m → R) :
    (blockMatrix P1 P2 P3).toQuadraticForm' (oilEmbed O x) =
      P3.toQuadraticForm' x - (-O.transpose * P1 * O - O.transpose * P2).toQuadraticForm' x := by
  rw [Matrix.toQuadraticForm'_apply, Matrix.toQuadraticForm'_apply, Matrix.toQuadraticForm'_apply,
    oilEmbed, append_dotProduct_blockMatrix_mulVec]
  have h1 : (O *ᵥ x) ⬝ᵥ (P1 *ᵥ (O *ᵥ x)) = x ⬝ᵥ ((O.transpose * P1 * O) *ᵥ x) := by
    symm
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  have h2 : (O *ᵥ x) ⬝ᵥ (P2 *ᵥ x) = x ⬝ᵥ ((O.transpose * P2) *ᵥ x) := by
    symm
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [h1, h2]
  simp only [Matrix.sub_mulVec, Matrix.neg_mul, Matrix.neg_mulVec, dotProduct_sub, dotProduct_neg]
  ring

/-- **Uniqueness of the oil block `Pᵢ⁽³⁾`** ([UOV2026], §3.1, p. 12): an `m × m` matrix `P3` is
upper triangular and makes `(blockMatrix P1 P2 P3).toQuadraticForm'` vanish on
`blockOilSubspace O` if and only if `P3 = oilBlock O P1 P2`. -/
theorem eq_oilBlock_iff (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R)
    {P3 : Matrix (Fin m) (Fin m) R} :
    (P3.IsUpperTriangular ∧
      MultivariateQuadraticMap.VanishesOn
        (blockMatrix P1 P2 P3).toQuadraticForm' (blockOilSubspace O)) ↔
      P3 = oilBlock O P1 P2 := by
  have hvan : MultivariateQuadraticMap.VanishesOn
      (blockMatrix P1 P2 P3).toQuadraticForm' (blockOilSubspace O) ↔
        P3.toQuadraticForm' = (-O.transpose * P1 * O - O.transpose * P2).toQuadraticForm' := by
    constructor
    · intro h
      ext x
      have hx : (blockMatrix P1 P2 P3).toQuadraticForm' (oilEmbed O x) = 0 :=
        h (oilEmbed O x) (oilEmbed_mem_blockOilSubspace O x)
      rw [toQuadraticForm'_blockMatrix_oilEmbed] at hx
      exact sub_eq_zero.mp hx
    · intro h z hz
      obtain ⟨x, rfl⟩ := mem_blockOilSubspace.mp hz
      rw [toQuadraticForm'_blockMatrix_oilEmbed, h, sub_self]
  rw [hvan, oilBlock, Matrix.eq_upperQuadratic_iff_toQuadraticForm'_eq]

/-- `i`-th public polynomial matrix `Pᵢ` constructed from `seed`. -/
@[expose] def BlockKeySeed.publicMatrix (seed : BlockKeySeed R v m) (i : Fin m) :
    Matrix (Fin (v + m)) (Fin (v + m)) R :=
  blockMatrix (seed.vinegarBlock i) (seed.mixedBlock i)
    (oilBlock seed.oilMatrix (seed.vinegarBlock i) (seed.mixedBlock i))

/-- Every `seed.publicMatrix i` is upper triangular when `seed.vinegarBlock i` is. -/
theorem BlockKeySeed.isUpperTriangular_publicMatrix (seed : BlockKeySeed R v m)
    {i : Fin m} (hP1 : (seed.vinegarBlock i).IsUpperTriangular) :
    (seed.publicMatrix i).IsUpperTriangular :=
  isUpperTriangular_blockMatrix _ hP1 (Matrix.isUpperTriangular_upperQuadratic _)

/-- The Round-3 UOV public quadratic map `P : R^{v + m} → R^m` assembled from
`seed.publicMatrix`. -/
@[expose] def BlockKeySeed.publicMap (seed : BlockKeySeed R v m) :
    MultivariateQuadraticMap R (Fin (v + m)) (Fin m) :=
  MultivariateQuadraticMap.ofMatrices seed.publicMatrix

/-- The constructed public quadratic map vanishes on the entire embedded oil subspace `[O; Iₘ]`. -/
theorem BlockKeySeed.publicMap_vanishesOn (seed : BlockKeySeed R v m) :
    MultivariateQuadraticMap.VanishesOn seed.publicMap (blockOilSubspace seed.oilMatrix) := by
  intro z hz
  obtain ⟨x, rfl⟩ := mem_blockOilSubspace.mp hz
  ext i
  change (seed.publicMatrix i).toQuadraticForm' (oilEmbed seed.oilMatrix x) = 0
  rw [BlockKeySeed.publicMatrix, toQuadraticForm'_blockMatrix_oilEmbed, oilBlock,
    Matrix.toQuadraticForm'_upperQuadratic, sub_self]

/-! ## Signing linearization -/

/-- Precomputed secret-key matrix `Sᵢ = (Pᵢ⁽¹⁾ + Pᵢ⁽¹⁾ᵀ) O + Pᵢ⁽²⁾ ∈ R^{v × m}`
([UOV2026], §3.1, p. 13, and `UOV.ExpandSK`, Figure 2, line 4, p. 16). -/
@[expose] def linearizationMatrix (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R) :
    Matrix (Fin v) (Fin m) R :=
  (P1 + P1.transpose) * O + P2

/-- Vinegar evaluation vector `y ∈ R^m` with `yᵢ = uᵀ Pᵢ⁽¹⁾ u` ([UOV2026], §3.1, p. 13). -/
@[expose] def vinegarEval (P1 : Fin m → Matrix (Fin v) (Fin v) R)
    (u : Fin v → R) : Fin m → R :=
  fun i => u ⬝ᵥ (P1 i *ᵥ u)

/-- `seed.publicMap` evaluated at `vinegarEmbed u = [u; 0]` equals
`vinegarEval seed.vinegarBlock u`. -/
@[simp]
theorem BlockKeySeed.publicMap_vinegarEmbed (seed : BlockKeySeed R v m) (u : Fin v → R) :
    seed.publicMap (vinegarEmbed u) = vinegarEval seed.vinegarBlock u := by
  ext i
  rw [BlockKeySeed.publicMap, MultivariateQuadraticMap.ofMatrices_apply,
    BlockKeySeed.publicMatrix, vinegarEmbed, append_dotProduct_blockMatrix_mulVec]
  simp [vinegarEval]

/-- The `m × m` signing linear-system matrix `L` whose `i`-th row is `uᵀ Sᵢ`
([UOV2026], §3.1, p. 13). -/
@[expose] def signingMatrix (S : Fin m → Matrix (Fin v) (Fin m) R)
    (u : Fin v → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => (u ᵥ* S i) j

@[simp]
theorem signingMatrix_mulVec_apply (S : Fin m → Matrix (Fin v) (Fin m) R)
    (u : Fin v → R) (x : Fin m → R) (i : Fin m) :
    (signingMatrix S u *ᵥ x) i = (u ᵥ* S i) ⬝ᵥ x :=
  rfl

/-- `seed`'s signing matrix `L` at vinegar vector `u`. -/
@[expose] def BlockKeySeed.signingSystemMatrix (seed : BlockKeySeed R v m)
    (u : Fin v → R) : Matrix (Fin m) (Fin m) R :=
  signingMatrix
    (fun i => linearizationMatrix seed.oilMatrix (seed.vinegarBlock i) (seed.mixedBlock i)) u

/-- Polar evaluation between `[u; 0]` and `[O x; x]` equals `(uᵀ Sᵢ) x`, retaining the transpose
contribution `Pᵢ⁽¹⁾ᵀ O` in every characteristic. -/
theorem BlockKeySeed.polar_vinegarEmbed_oilEmbed_apply (seed : BlockKeySeed R v m)
    (u : Fin v → R) (x : Fin m → R) (i : Fin m) :
    QuadraticMap.polar seed.publicMap (vinegarEmbed u) (oilEmbed seed.oilMatrix x) i =
      (u ᵥ* linearizationMatrix seed.oilMatrix (seed.vinegarBlock i) (seed.mixedBlock i)) ⬝ᵥ x := by
  rw [BlockKeySeed.publicMap, MultivariateQuadraticMap.polar_ofMatrices_apply,
    BlockKeySeed.publicMatrix, vinegarEmbed, oilEmbed,
    append_dotProduct_blockMatrix_mulVec, append_dotProduct_blockMatrix_mulVec]
  simp only [mulVec_zero, dotProduct_zero, zero_dotProduct, add_zero]
  have htrans : (seed.oilMatrix *ᵥ x) ⬝ᵥ (seed.vinegarBlock i *ᵥ u) =
      u ⬝ᵥ ((seed.vinegarBlock i).transpose *ᵥ (seed.oilMatrix *ᵥ x)) := by
    rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [htrans, ← dotProduct_mulVec]
  simp only [linearizationMatrix, Matrix.add_mul, add_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_add]
  ring

/-- **UOV coordinate signing linearization** ([UOV2026], §3.1, pp. 12–13):
`pᵢ([u; 0] + [O; Iₘ] x) = uᵀ Pᵢ⁽¹⁾ u + (uᵀ Sᵢ) x` in every characteristic. -/
theorem BlockKeySeed.publicMap_signatureVector_apply (seed : BlockKeySeed R v m)
    (u : Fin v → R) (x : Fin m → R) (i : Fin m) :
    seed.publicMap (signatureVector seed.oilMatrix u x) i =
      u ⬝ᵥ (seed.vinegarBlock i *ᵥ u) +
        (u ᵥ* linearizationMatrix seed.oilMatrix
          (seed.vinegarBlock i) (seed.mixedBlock i)) ⬝ᵥ x := by
  have hlin := MultivariateQuadraticMap.map_add_of_mem seed.publicMap_vanishesOn
    (vinegarEmbed u) (oilEmbed_mem_blockOilSubspace seed.oilMatrix x)
  have hi := congrFun hlin i
  simpa only [signatureVector, Pi.add_apply, BlockKeySeed.publicMap_vinegarEmbed, vinegarEval,
    QuadraticMap.polarBilin_apply_apply, BlockKeySeed.polar_vinegarEmbed_oilEmbed_apply] using hi

/-- **UOV vector signing linearization** ([UOV2026], §3.1, p. 13):
`P([u; 0] + [O; Iₘ] x) = y + L x`. -/
theorem BlockKeySeed.publicMap_signatureVector (seed : BlockKeySeed R v m)
    (u : Fin v → R) (x : Fin m → R) :
    seed.publicMap (signatureVector seed.oilMatrix u x) =
      vinegarEval seed.vinegarBlock u + seed.signingSystemMatrix u *ᵥ x := by
  ext i
  exact seed.publicMap_signatureVector_apply u x i

/-- **UOV signing linear-system equivalence** ([UOV2026], §3.1, p. 13, and `UOV.Sign` /
`UOV.Verify`, Figure 2, pp. 16–17): `P([u; 0] + [O; Iₘ] x) = t` if and only if `L x = t - y`. -/
theorem BlockKeySeed.publicMap_signatureVector_eq_iff (seed : BlockKeySeed R v m)
    (u : Fin v → R) (x t : Fin m → R) :
    seed.publicMap (signatureVector seed.oilMatrix u x) = t ↔
      seed.signingSystemMatrix u *ᵥ x = t - vinegarEval seed.vinegarBlock u := by
  rw [seed.publicMap_signatureVector, add_comm, eq_sub_iff_add_eq]

end BlockConstruction

/-! ## Round-3 binary extension field choices (`q ∈ {16, 256}`) -/

/-- The two finite-field choices `q ∈ {16, 256}` permitted by Round-3 UOV ([UOV2026], §3.2.1,
p. 14, and §3.3, p. 19), mapping to the binary extension fields `UOV.F16 = F₂[X]/(X⁴ + X + 1)`
and `UOV.F256 = F₂[X]/(X⁸ + X⁴ + X³ + X + 1)` rather than `ZMod 16` or `ZMod 256`. -/
inductive FieldChoice : Type
  /-- `GF(16) = F₂[X]/(X⁴ + X + 1)` (`UOV.F16`, `q = 16`). -/
  | gf16
  /-- `GF(256) = F₂[X]/(X⁸ + X⁴ + X³ + X + 1)` (`UOV.F256`, `q = 256`). -/
  | gf256
  deriving DecidableEq, Repr

namespace FieldChoice

/-- Finite-field carrier (`UOV.F16` or `UOV.F256`) of a Round-3 `FieldChoice`. -/
@[expose] def Carrier : FieldChoice → Type
  | .gf16 => F16
  | .gf256 => F256

/-- Field order `q ∈ {16, 256}` of a Round-3 `FieldChoice`. -/
@[expose] def order : FieldChoice → ℕ
  | .gf16 => 16
  | .gf256 => 256

noncomputable instance instField : (c : FieldChoice) → Field c.Carrier
  | .gf16 => inferInstanceAs (Field F16)
  | .gf256 => inferInstanceAs (Field F256)

noncomputable instance instFintype : (c : FieldChoice) → Fintype c.Carrier
  | .gf16 => inferInstanceAs (Fintype F16)
  | .gf256 => inferInstanceAs (Fintype F256)

noncomputable instance instDecidableEq : (c : FieldChoice) → DecidableEq c.Carrier
  | .gf16 => inferInstanceAs (DecidableEq F16)
  | .gf256 => inferInstanceAs (DecidableEq F256)

instance instCharTwo : (c : FieldChoice) → CharP c.Carrier 2
  | .gf16 => inferInstanceAs (CharP F16 2)
  | .gf256 => inferInstanceAs (CharP F256 2)

/-- Every Round-3 `FieldChoice` carrier is a genuine finite field of cardinality `c.order`
(`16` or `256`). -/
@[simp]
theorem card_carrier : (c : FieldChoice) → Fintype.card c.Carrier = c.order
  | .gf16 => BinaryField.card (w := 4) (by decide)
  | .gf256 => BinaryField.card (w := 8) (by decide)

end FieldChoice

end Cslib.Crypto.UOV
