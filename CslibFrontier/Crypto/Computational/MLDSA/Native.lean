/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.PolyTime.Int.ExactDiv
public import CslibFrontier.Crypto.Computational.LWE.Module.Native
public import CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native ML-DSA verification and residue-list operations

Shared for assessment under the ML-DSA M1-M5 plan in #5293 (comments 6946126101, 6948621431).
Contributed by @karnseth's team (agent-assisted).

`Cslib.Crypto.MLDSA.Basic`, `Cslib.Crypto.MLDSA.KeyOnly` and
`Cslib.Crypto.MLDSA.CompressedKeyOnly` define ML-DSA rounding, hint recovery, verification and
low-part extraction over `Fin n → ZMod q`. This module gives total implementations on
natural-residue and signed-binary-integer lists, proves exact agreement with the typed operations,
and supplies plain `ComputableInPolyTime` certificates for parameter schedules encoded by
`encParams`.

## Main definitions

* `Cslib.Crypto.MLDSA.encParams`: parameter encoding with `n`, `k`, `ℓ` in unary and `q`, `η`,
  `γ₁`, `γ₂`, `τ`, `β` in binary.
* `Cslib.Crypto.MLDSA.centeredMod`, `Cslib.Crypto.MLDSA.power2RoundResidue`,
  `Cslib.Crypto.MLDSA.decomposeResidue`, `Cslib.Crypto.MLDSA.highBitsResidue`,
  `Cslib.Crypto.MLDSA.lowBitsResidue`, `Cslib.Crypto.MLDSA.useHintResidue`,
  `Cslib.Crypto.MLDSA.hintResidualResidue`: scalar rounding and hint operations on residues.
* `Cslib.Crypto.MLDSA.verifierCommitmentResidues`,
  `Cslib.Crypto.MLDSA.compressedVerifierCommitmentResidues`,
  `Cslib.Crypto.MLDSA.responseShortResidues`, `Cslib.Crypto.MLDSA.inBallResidues`,
  `Cslib.Crypto.MLDSA.verifyFromHashResidues`: vector commitments and verification checks.
* `Cslib.Crypto.MLDSA.forgeryLowPartResidues`,
  `Cslib.Crypto.MLDSA.compressedForgeryLowPartResidues`,
  `Cslib.Crypto.MLDSA.verifierHighBitsWord`, `Cslib.Crypto.MLDSA.verifyWithHashWord`,
  `Cslib.Crypto.MLDSA.compressedVerifierHighBitsWord`,
  `Cslib.Crypto.MLDSA.compressedVerifyWithHashWord`: residue-level low-part extraction and
  word-level verification helpers.

## Main results

* `Cslib.Crypto.MLDSA.power2RoundResidue_val`, `Cslib.Crypto.MLDSA.decomposeResidue_val`,
  `Cslib.Crypto.MLDSA.useHintResidue_val`, `Cslib.Crypto.MLDSA.hintResidualResidue_val`: scalar
  agreement with `power2Round`, `decompose`, `useHint` and `hintResidual`.
* `Cslib.Crypto.MLDSA.verifierCommitmentResidues_eq`,
  `Cslib.Crypto.MLDSA.compressedVerifierCommitmentResidues_eq`,
  `Cslib.Crypto.MLDSA.responseShortResidues_eq`, `Cslib.Crypto.MLDSA.inBallResidues_eq`:
  agreement of commitments and norm/challenge checks.
* `Cslib.Crypto.MLDSA.forgeryLowPartResidues_eq`,
  `Cslib.Crypto.MLDSA.compressedForgeryLowPartResidues_eq`,
  `Cslib.Crypto.MLDSA.verifierHighBitsWord_encode`,
  `Cslib.Crypto.MLDSA.compressedVerifierHighBitsWord_encode`: agreement of low-part extraction
  and word-level verification helpers.
* `Turing.MultiTapeTM.ComputableInPolyTime` certificates for the operations above.

## References

* [S. Bai et al., *CRYSTALS-Dilithium: Algorithm Specifications and Supporting
  Documentation*, Version 3.1][BaiEtAl2021Dilithium]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
* [National Institute of Standards and Technology, *Module-Lattice-Based Digital Signature
  Standard*][NISTFIPS204]
-/

@[expose] public section

namespace Cslib.Crypto.MLDSA

open Turing.MultiTapeTM

/-! ### Parameter encoding and scalar residue operations -/

/-- Encoding of ML-DSA parameters: ring degree `n` and module dimensions `k`, `ℓ` in unary, and
modulus `q`, secret bound `η`, masking range `γ₁`, rounding range `γ₂`, challenge weight `τ` and
rejection margin `β` in binary. -/
enc_structure encParams : Params where
  n : encUnary, q : encNat, k : encUnary, ℓ : encUnary,
  η : encNat, γ₁ : encNat, γ₂ : encNat, τ : encNat, β : encNat

/-- Centered modular representative of a natural `x` modulo `m`, matching
`((x : ZMod m).valMinAbs)` for every `m` (including `m = 0`, where `ZMod 0 = ℤ`). -/
def centeredMod (m x : ℕ) : ℤ :=
  if m = 0 then (x : ℤ)
  else
    let r := x % m
    if r ≤ m / 2 then (r : ℤ) else (r : ℤ) - (m : ℤ)

/-- `centeredMod` computes `ZMod.valMinAbs` for every modulus `m`. -/
theorem centeredMod_eq_valMinAbs (m x : ℕ) :
    centeredMod m x = ((x : ZMod m).valMinAbs) := by
  by_cases hm : m = 0
  · subst hm
    rfl
  · have : NeZero m := ⟨hm⟩
    simp only [centeredMod, hm, ↓reduceIte, ZMod.valMinAbs_def_pos, ZMod.val_natCast]

/-- On the canonical representative of `r : ZMod q`, `centeredMod q` is `r.valMinAbs`. -/
theorem centeredMod_val {q : ℕ} [NeZero q] (r : ZMod q) :
    centeredMod q r.val = r.valMinAbs := by
  rw [centeredMod_eq_valMinAbs, ZMod.natCast_zmod_val]

/-- Scalar `Power2Round` on a canonical residue `x = r.val` with shift `d`. -/
def power2RoundResidue (d x : ℕ) : ℤ × ℤ :=
  let r₀ := centeredMod (2 ^ d) x
  (((x : ℤ) - r₀) / (2 ^ d : ℕ), r₀)

/-- `power2RoundResidue` computes `power2Round`. -/
theorem power2RoundResidue_val (q d : ℕ) (r : ZMod q) :
    power2RoundResidue d r.val = power2Round q d r := by
  simp only [power2RoundResidue, power2Round, centeredMod_eq_valMinAbs, Int.cast_natCast]

/-- Scalar `Decompose` on a canonical residue `x = r.val` with modulus `q` and range `2 γ₂`. -/
def decomposeResidue (q γ₂ x : ℕ) : ℤ × ℤ :=
  let r₀ := centeredMod (2 * γ₂) x
  if (x : ℤ) - r₀ = (q : ℤ) - 1 then (0, r₀ - 1)
  else (((x : ℤ) - r₀) / (2 * γ₂ : ℕ), r₀)

/-- Scalar `HighBits` on a canonical residue. -/
def highBitsResidue (q γ₂ x : ℕ) : ℤ := (decomposeResidue q γ₂ x).1

/-- Scalar `LowBits` on a canonical residue. -/
def lowBitsResidue (q γ₂ x : ℕ) : ℤ := (decomposeResidue q γ₂ x).2

/-- `decomposeResidue` computes `decompose`. -/
theorem decomposeResidue_val (q γ₂ : ℕ) (r : ZMod q) :
    decomposeResidue q γ₂ r.val = decompose q γ₂ r := by
  simp only [decomposeResidue, decompose, centeredMod_eq_valMinAbs, Int.cast_natCast]

/-- `highBitsResidue` computes `highBits`. -/
theorem highBitsResidue_val (q γ₂ : ℕ) (r : ZMod q) :
    highBitsResidue q γ₂ r.val = highBits q γ₂ r := by
  rw [highBitsResidue, highBits, decomposeResidue_val]

/-- `lowBitsResidue` computes `lowBits`. -/
theorem lowBitsResidue_val (q γ₂ : ℕ) (r : ZMod q) :
    lowBitsResidue q γ₂ r.val = lowBits q γ₂ r := by
  rw [lowBitsResidue, lowBits, decomposeResidue_val]

/-- Scalar `UseHint` on a hint bit `h` and canonical residue `x = r.val`. -/
def useHintResidue (q γ₂ : ℕ) (h : Bool) (x : ℕ) : ℤ :=
  let m : ℕ := (q - 1) / (2 * γ₂)
  if h then
    if 0 < lowBitsResidue q γ₂ x then (highBitsResidue q γ₂ x + 1) % (m : ℤ)
    else (highBitsResidue q γ₂ x - 1) % (m : ℤ)
  else highBitsResidue q γ₂ x

/-- `useHintResidue` computes `useHint`. -/
theorem useHintResidue_val (q γ₂ : ℕ) (h : Bool) (r : ZMod q) :
    useHintResidue q γ₂ h r.val = useHint q γ₂ h r := by
  cases h <;> simp [useHintResidue, useHint, highBitsResidue_val, lowBitsResidue_val]

/-- Canonical residue of `hintResidual q γ₂ h r` from `x = r.val`. -/
def hintResidualResidue (q γ₂ : ℕ) (h : Bool) (x : ℕ) : ℕ :=
  ((useHintResidue q γ₂ h x * (2 * γ₂ : ℕ) - (x : ℤ)) % (q : ℤ)).toNat

/-- `hintResidualResidue` computes the canonical residue of `hintResidual` when `q ≠ 0`. -/
theorem hintResidualResidue_val {q : ℕ} [NeZero q] (γ₂ : ℕ) (h : Bool) (r : ZMod q) :
    hintResidualResidue q γ₂ h r.val = (hintResidual q γ₂ h r).val := by
  simp only [hintResidualResidue, useHintResidue_val, ← ZMod.val_intCast, Int.toNat_natCast]
  congr 1
  simp [hintResidual]

/-! ### Vector commitments, verification and candidate extraction -/

/-- Residue rows of a `k × ℓ` module matrix: row `i` is `polyVecResidues (A i)`. -/
def matrixResidues {k ℓ n q : ℕ} (A : Matrix (Fin k) (Fin ℓ) (Fin n → ZMod q)) :
    List (List (List ℕ)) :=
  List.ofFn fun i => polyVecResidues (A i)

/-- Framed list encoding of the residue rows of a module matrix, each row in
`encPolyVecResidues`. -/
abbrev encMatrixResidues : List (List (List ℕ)) ↪ List Bool :=
  encList encPolyVecResidues

/-- An integer polynomial vector `Fin k → Fin n → ℤ` as `k` lists of `n` integers. -/
def intPolyVecList {k n : ℕ} (w : Fin k → Fin n → ℤ) : List (List ℤ) :=
  List.ofFn fun i => List.ofFn fun j => w i j

/-- Framed list encoding of integer polynomial vectors, with entries in `encIntBin`. -/
abbrev encIntPolyVec : List (List ℤ) ↪ List Bool :=
  encList (encList encIntBin)

/-- A Boolean hint grid `Fin k → Fin n → Bool` as `k` bit lists of length `n`. -/
def boolGridList {k n : ℕ} (h : Fin k → Fin n → Bool) : List (List Bool) :=
  List.ofFn fun i => List.ofFn fun j => h i j

/-- Framed list encoding of Boolean hint grids, with each polynomial's hints as raw bits. -/
abbrev encBoolGrid : List (List Bool) ↪ List Bool :=
  encList encBits

/-- Decode `(matrixResidues pk.A, polyVecResidues pk.t)` from `ModuleLWE.encodeSample`. -/
def decodePublicKeyResidues (P : Params) (sample : List Bool) :
    List (List (List ℕ)) × List (List ℕ) :=
  let s := ModuleLWE.sampleDecoder.decode sample
  (ModuleLWE.entryResidues P.k P.ℓ P.n ((Decoder.list (Decoder.list Decoder.nat)).decode s.1),
    ModuleLWE.chunkResidues P.k P.n s.2)

/-- `decodePublicKeyResidues` recovers the matrix and target residue lists of a public key. -/
theorem decodePublicKeyResidues_encodeSample (P : Params) (pk : PublicKey P) :
    decodePublicKeyResidues P (ModuleLWE.encodeSample (pk.A, pk.t)) =
      (matrixResidues pk.A, polyVecResidues pk.t) := by
  simp only [decodePublicKeyResidues, ModuleLWE.encodeSample, ModuleLWE.sampleDecoder.decode_enc,
    ModuleLWE.entryResidues_encodeMatrix, ModuleLWE.chunkResidues_flattenPolyVec, matrixResidues]

/-- Native `moduleSISMap A z` on residue lists, returning `k` residue lists of length `n`. -/
def moduleSISMapResidues (k n q : ℕ) (A : List (List (List ℕ))) (z : List (List ℕ)) :
    List (List ℕ) :=
  (List.range k).map fun i => negacyclicInnerResidues n q (A.getD i []) z

/-- Multiply each polynomial in a vector of residue lists on the left by `c`. -/
def scaleVecResidues (n q : ℕ) (c : List ℕ) (v : List (List ℕ)) : List (List ℕ) :=
  v.map (negacyclicMulResidues n q c)

/-- Coefficientwise addition modulo `q` of two vectors of residue lists. -/
def addVecResidues (q : ℕ) (u v : List (List ℕ)) : List (List ℕ) :=
  (u.zip v).map fun p => addResidues q p.1 p.2

/-- Coefficientwise subtraction modulo `q` of two vectors of residue lists. -/
def subVecResidues (q : ℕ) (u v : List (List ℕ)) : List (List ℕ) :=
  (u.zip v).map fun p => subResidues q p.1 p.2

/-- Native verifier commitment `A z - c t` on residue lists. -/
def verifierCommitmentResidues (P : Params) (A : List (List (List ℕ)))
    (t z : List (List ℕ)) (c : List ℕ) : List (List ℕ) :=
  subVecResidues P.q (moduleSISMapResidues P.k P.n P.q A z) (scaleVecResidues P.n P.q c t)

/-- Native `publicKeyHighTerm` (`t₁ · 2^d mod q`) on residue lists. -/
def publicKeyHighTermResidues (q d : ℕ) (t : List (List ℕ)) : List (List ℕ) :=
  t.map fun p => p.map fun x => (((power2RoundResidue d x).1 * (2 ^ d : ℕ)) % (q : ℤ)).toNat

/-- Native `publicKeyLowPart` (`t₀ mod q`) on residue lists. -/
def publicKeyLowPartResidues (q d : ℕ) (t : List (List ℕ)) : List (List ℕ) :=
  t.map fun p => p.map fun x => ((power2RoundResidue d x).2 % (q : ℤ)).toNat

/-- Native compressed verifier commitment `A z - c (t₁ 2^d)` on residue lists. -/
def compressedVerifierCommitmentResidues (P : Params) (d : ℕ) (A : List (List (List ℕ)))
    (t z : List (List ℕ)) (c : List ℕ) : List (List ℕ) :=
  subVecResidues P.q (moduleSISMapResidues P.k P.n P.q A z)
    (scaleVecResidues P.n P.q c (publicKeyHighTermResidues P.q d t))

/-- Coefficientwise `HighBits` on residue lists. -/
def highBitsVecResidues (q γ₂ : ℕ) (w : List (List ℕ)) : List (List ℤ) :=
  w.map fun p => p.map (highBitsResidue q γ₂)

/-- Coefficientwise `UseHint` on hint bit rows and residue lists. -/
def useHintGridResidues (q γ₂ : ℕ) (h : List (List Bool)) (r : List (List ℕ)) : List (List ℤ) :=
  (h.zip r).map fun row => (row.1.zip row.2).map fun x => useHintResidue q γ₂ x.1 x.2

/-- Native `ResponseShort P z` check on `P.ℓ` polynomials of degree `P.n`. -/
def responseShortResidues (P : Params) (z : List (List ℕ)) : Bool :=
  (List.range P.ℓ).all fun i =>
    (List.range P.n).all fun j =>
      decide (((centeredMod P.q ((z.getD i []).getD j 0)).natAbs : ℤ) < (P.γ₁ : ℤ) - P.β)

/-- Native `InBall τ c` check on `n` challenge residues modulo `q`. -/
def inBallResidues (n q τ : ℕ) (c : List ℕ) : Bool :=
  ((List.range n).all fun i => decide ((centeredMod q (c.getD i 0)).natAbs ≤ 1)) &&
    (((List.range n).countP fun i => c.getD i 0 % q != 0) == τ)

/-- Final verification check given `(z, c)` and the challenge residues `cHash` returned by `H`. -/
def verifyFromHashResidues (P : Params) (z : List (List ℕ)) (c cHash : List ℕ) : Bool :=
  responseShortResidues P z && inBallResidues P.n P.q P.τ c && (cHash == c)

/-- Native `forgeryLowPart` (`-LowBits(A z - c t) mod q`) on residue lists. -/
def forgeryLowPartResidues (P : Params) (A : List (List (List ℕ))) (t z : List (List ℕ))
    (c : List ℕ) : List (List ℕ) :=
  (verifierCommitmentResidues P A t z c).map fun row =>
    row.map fun x => ((-lowBitsResidue P.q P.γ₂ x) % (P.q : ℤ)).toNat

/-- Native `compressedForgeryLowPart` (`hintResidual + c t₀ mod q`) on residue lists. -/
def compressedForgeryLowPartResidues (P : Params) (d : ℕ) (A : List (List (List ℕ)))
    (t z : List (List ℕ)) (h : List (List Bool)) (c : List ℕ) : List (List ℕ) :=
  let r := compressedVerifierCommitmentResidues P d A t z c
  let res := (h.zip r).map fun row =>
    (row.1.zip row.2).map fun x => hintResidualResidue P.q P.γ₂ x.1 x.2
  addVecResidues P.q res (scaleVecResidues P.n P.q c (publicKeyLowPartResidues P.q d t))

/-! ### Forgery and candidate word encodings and decoders -/

/-- Word layout of an uncompressed forgery `(M, (z, c))`: framed message bits `M`, framed
polynomial-vector residues of `z` (`encPolyVecResidues`), then challenge residues `c`
(`encList encNat`). -/
abbrev encForgeryWords : List Bool × List (List ℕ) × List ℕ ↪ List Bool :=
  encPair encBits (encPair encPolyVecResidues (encList encNat))

/-- Encode an uncompressed forgery `(M, (z, c))` as a bit word. -/
def encodeForgery {P : Params} (f : List Bool × Signature P) : List Bool :=
  encForgeryWords (f.1, polyVecResidues f.2.z, polyResidues f.2.c)

/-- Total decoder for `encForgeryWords`. -/
def forgeryDecoder : Decoder encForgeryWords :=
  Decoder.pair Decoder.bits
    (Decoder.pair (Decoder.list (Decoder.list Decoder.nat)) (Decoder.list Decoder.nat))

/-- Word layout of a compressed forgery `(M, (z, h, c))`: framed message bits `M`, framed
polynomial-vector residues of `z` (`encPolyVecResidues`), framed hint bit rows `h`
(`encBoolGrid`), then challenge residues `c` (`encList encNat`). -/
abbrev encCompressedForgeryWords :
    List Bool × List (List ℕ) × List (List Bool) × List ℕ ↪ List Bool :=
  encPair encBits (encPair encPolyVecResidues (encPair encBoolGrid (encList encNat)))

/-- Encode a compressed forgery `(M, (z, h, c))` as a bit word. -/
def encodeCompressedForgery {P : Params} (f : List Bool × CompressedSignature P) : List Bool :=
  encCompressedForgeryWords (f.1, polyVecResidues f.2.z, boolGridList f.2.h, polyResidues f.2.c)

/-- Total decoder for `encCompressedForgeryWords`. -/
def compressedForgeryDecoder : Decoder encCompressedForgeryWords :=
  Decoder.pair Decoder.bits (Decoder.pair (Decoder.list (Decoder.list Decoder.nat))
    (Decoder.pair (Decoder.list Decoder.bits) (Decoder.list Decoder.nat)))

/-- Extract `(HighBits(A z - c t), M)` from encoded public-key sample and forgery words. -/
def verifierHighBitsWord (P : Params) (sample forgery : List Bool) :
    List (List ℤ) × List Bool :=
  let pk := decodePublicKeyResidues P sample
  let fg := forgeryDecoder.decode forgery
  let zc := fg.2
  (highBitsVecResidues P.q P.γ₂ (verifierCommitmentResidues P pk.1 pk.2 zc.1 zc.2), fg.1)

/-- Check an encoded uncompressed forgery against already-evaluated hash challenge residues. -/
def verifyWithHashWord (P : Params) (forgery : List Bool) (cHash : List ℕ) : Bool :=
  let zc := (forgeryDecoder.decode forgery).2
  verifyFromHashResidues P zc.1 zc.2 cHash

/-- Extract `(UseHint(h, A z - c t₁ 2^d), M)` from encoded public-key sample and compressed
forgery words. -/
def compressedVerifierHighBitsWord (P : Params) (d : ℕ) (sample forgery : List Bool) :
    List (List ℤ) × List Bool :=
  let pk := decodePublicKeyResidues P sample
  let fg := compressedForgeryDecoder.decode forgery
  let zhc := fg.2
  let hc := zhc.2
  (useHintGridResidues P.q P.γ₂ hc.1
    (compressedVerifierCommitmentResidues P d pk.1 pk.2 zhc.1 hc.2), fg.1)

/-- Check an encoded compressed forgery against already-evaluated hash challenge residues. -/
def compressedVerifyWithHashWord (P : Params) (forgery : List Bool) (cHash : List ℕ) : Bool :=
  let zhc := (compressedForgeryDecoder.decode forgery).2
  let hc := zhc.2
  verifyFromHashResidues P zhc.1 hc.2 cHash

/-! ### Agreement theorems -/

section Agreement

theorem moduleSISMapResidues_eq {k ℓ n q : ℕ} [NeZero q]
    (A : Matrix (Fin k) (Fin ℓ) (Fin n → ZMod q)) (z : Fin ℓ → Fin n → ZMod q) :
    moduleSISMapResidues k n q (matrixResidues A) (polyVecResidues z) =
      polyVecResidues (moduleSISMap A z) := by
  apply List.ext_getElem (by simp [moduleSISMapResidues, polyVecResidues])
  intro i h₁ h₂
  have hi : i < k := by simpa [moduleSISMapResidues] using h₁
  simp only [moduleSISMapResidues, List.getElem_map, List.getElem_range]
  rw [show (matrixResidues A).getD i [] = polyVecResidues (A ⟨i, hi⟩) by
      simp [matrixResidues, hi],
    negacyclicInnerResidues_polyVecResidues]
  simp [polyVecResidues, moduleSISMap, innerPoly]

theorem scaleVecResidues_eq {m n q : ℕ} [NeZero q]
    (c : Fin n → ZMod q) (v : Fin m → Fin n → ZMod q) :
    scaleVecResidues n q (polyResidues c) (polyVecResidues v) =
      polyVecResidues (fun i => negacyclicMul c (v i)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  apply List.ext_getElem (by simp [scaleVecResidues, polyVecResidues])
  intro i h₁ h₂
  simp only [scaleVecResidues, polyVecResidues, List.getElem_map, List.getElem_ofFn, polyResidues]
  exact negacyclicMulResidues_ofFn hq c _

theorem addVecResidues_eq {m n q : ℕ} [NeZero q]
    (u v : Fin m → Fin n → ZMod q) :
    addVecResidues q (polyVecResidues u) (polyVecResidues v) = polyVecResidues (u + v) := by
  apply List.ext_getElem (by simp [addVecResidues, polyVecResidues])
  intro i h₁ h₂
  simp [addVecResidues, polyVecResidues, addResidues_polyResidues]

theorem subVecResidues_eq {m n q : ℕ} [NeZero q]
    (u v : Fin m → Fin n → ZMod q) :
    subVecResidues q (polyVecResidues u) (polyVecResidues v) = polyVecResidues (u - v) := by
  apply List.ext_getElem (by simp [subVecResidues, polyVecResidues])
  intro i h₁ h₂
  simp [subVecResidues, polyVecResidues, subResidues_polyResidues]

/-- Native verifier commitment computes `verifierCommitment`. -/
theorem verifierCommitmentResidues_eq (P : Params) [NeZero P.q] (pk : PublicKey P)
    (z : Fin P.ℓ → Fin P.n → ZMod P.q) (c : Fin P.n → ZMod P.q) :
    verifierCommitmentResidues P (matrixResidues pk.A) (polyVecResidues pk.t)
        (polyVecResidues z) (polyResidues c) =
      polyVecResidues (verifierCommitment P pk z c) := by
  rw [verifierCommitmentResidues, moduleSISMapResidues_eq, scaleVecResidues_eq, subVecResidues_eq]
  rfl

theorem publicKeyHighTermResidues_eq (P : Params) [NeZero P.q] (d : ℕ) (pk : PublicKey P) :
    publicKeyHighTermResidues P.q d (polyVecResidues pk.t) =
      polyVecResidues (publicKeyHighTerm P d pk) := by
  apply List.ext_getElem (by simp [publicKeyHighTermResidues, polyVecResidues])
  intro i h₁ h₂
  apply List.ext_getElem (by simp [publicKeyHighTermResidues, polyVecResidues, polyResidues])
  intro j h₃ h₄
  simp only [publicKeyHighTermResidues, polyVecResidues, polyResidues, List.getElem_map,
    List.getElem_ofFn, power2RoundResidue_val, publicKeyHighTerm, power2RoundVec,
    ← ZMod.val_intCast, Int.toNat_natCast]

theorem publicKeyLowPartResidues_eq (P : Params) [NeZero P.q] (d : ℕ) (pk : PublicKey P) :
    publicKeyLowPartResidues P.q d (polyVecResidues pk.t) =
      polyVecResidues (publicKeyLowPart P d pk) := by
  apply List.ext_getElem (by simp [publicKeyLowPartResidues, polyVecResidues])
  intro i h₁ h₂
  apply List.ext_getElem (by simp [publicKeyLowPartResidues, polyVecResidues, polyResidues])
  intro j h₃ h₄
  simp only [publicKeyLowPartResidues, polyVecResidues, polyResidues, List.getElem_map,
    List.getElem_ofFn, power2RoundResidue_val, publicKeyLowPart, power2RoundVec,
    ← ZMod.val_intCast, Int.toNat_natCast]

/-- Native compressed verifier commitment computes `compressedVerifierCommitment`. -/
theorem compressedVerifierCommitmentResidues_eq (P : Params) [NeZero P.q] (d : ℕ)
    (pk : PublicKey P) (z : Fin P.ℓ → Fin P.n → ZMod P.q) (c : Fin P.n → ZMod P.q) :
    compressedVerifierCommitmentResidues P d (matrixResidues pk.A) (polyVecResidues pk.t)
        (polyVecResidues z) (polyResidues c) =
      polyVecResidues (compressedVerifierCommitment P d pk z c) := by
  rw [compressedVerifierCommitmentResidues, moduleSISMapResidues_eq,
    publicKeyHighTermResidues_eq, scaleVecResidues_eq, subVecResidues_eq]
  rfl

theorem highBitsVecResidues_eq (P : Params) (w : Fin P.k → Fin P.n → ZMod P.q) :
    highBitsVecResidues P.q P.γ₂ (polyVecResidues w) = intPolyVecList (highBitsVec P w) := by
  apply List.ext_getElem (by simp [highBitsVecResidues, polyVecResidues, intPolyVecList])
  intro i h₁ h₂
  apply List.ext_getElem
    (by simp [highBitsVecResidues, polyVecResidues, polyResidues, intPolyVecList])
  intro j h₃ h₄
  simp [highBitsVecResidues, polyVecResidues, polyResidues, intPolyVecList, highBitsResidue_val,
    highBitsVec]

theorem useHintGridResidues_eq (P : Params) (h : Fin P.k → Fin P.n → Bool)
    (r : Fin P.k → Fin P.n → ZMod P.q) :
    useHintGridResidues P.q P.γ₂ (boolGridList h) (polyVecResidues r) =
      intPolyVecList (fun i => useHintVec P.q P.γ₂ (h i) (r i)) := by
  apply List.ext_getElem
    (by simp [useHintGridResidues, boolGridList, polyVecResidues, intPolyVecList])
  intro i h₁ h₂
  apply List.ext_getElem
    (by simp [useHintGridResidues, boolGridList, polyVecResidues, polyResidues, intPolyVecList])
  intro j h₃ h₄
  simp [useHintGridResidues, boolGridList, polyVecResidues, polyResidues, intPolyVecList,
    useHintResidue_val, useHintVec]

/-- `responseShortResidues` decides `ResponseShort P z`. -/
theorem responseShortResidues_eq (P : Params) [NeZero P.q]
    (z : Fin P.ℓ → Fin P.n → ZMod P.q) :
    responseShortResidues P (polyVecResidues z) = decide (ResponseShort P z) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [responseShortResidues, ResponseShort, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  constructor
  · intro h i j
    have hij := h i.val i.isLt j.val j.isLt
    simp only [polyVecResidues, polyResidues, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      i.isLt, j.isLt, ↓reduceDIte, Option.getD_some, Fin.eta, centeredMod_val,
      Int.natCast_natAbs] at hij
    exact hij
  · intro h i hi j hj
    have hij := h ⟨i, hi⟩ ⟨j, hj⟩
    simpa only [polyVecResidues, polyResidues, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      hi, hj, ↓reduceDIte, Option.getD_some, centeredMod_val, Int.natCast_natAbs] using hij

private theorem countP_range_eq_sum (p : ℕ → Bool) :
    ∀ n : ℕ, (List.range n).countP p = ∑ i : Fin n, if p i.val then 1 else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.countP_append, countP_range_eq_sum p n, Fin.sum_univ_castSucc]
    simp

/-- `inBallResidues` decides `InBall τ c`. -/
theorem inBallResidues_eq {n q : ℕ} [NeZero q] (τ : ℕ) (c : Fin n → ZMod q) :
    inBallResidues n q τ (polyResidues c) = decide (InBall τ c) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [inBallResidues, InBall, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq]
  apply and_congr
  · constructor
    · intro h i
      have hi := h i.val i.isLt
      simp only [polyResidues, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt,
        ↓reduceDIte, Option.getD_some, Fin.eta, centeredMod_val] at hi
      rw [← Int.natCast_natAbs]
      exact_mod_cast hi
    · intro h i hi
      have hi' := h ⟨i, hi⟩
      rw [← Int.natCast_natAbs] at hi'
      have hnat : (c ⟨i, hi⟩).valMinAbs.natAbs ≤ 1 := by exact_mod_cast hi'
      simpa only [polyResidues, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
        Option.getD_some, centeredMod_val] using hnat
  · rw [countP_range_eq_sum, Finset.card_filter]
    have hsum : (∑ i : Fin n, if ((polyResidues c).getD i.val 0 % q != 0) = true then 1 else 0) =
        ∑ i : Fin n, if c i ≠ 0 then 1 else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [polyResidues, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt,
        ↓reduceDIte, Option.getD_some, Fin.eta, Nat.mod_eq_of_lt (ZMod.val_lt (c i)),
        bne_iff_ne, ne_eq, ZMod.val_eq_zero]
    rw [hsum]

/-- `forgeryLowPartResidues` computes `forgeryLowPart`. -/
theorem forgeryLowPartResidues_eq (P : Params) [NeZero P.q] (pk : PublicKey P)
    (σ : Signature P) :
    forgeryLowPartResidues P (matrixResidues pk.A) (polyVecResidues pk.t)
        (polyVecResidues σ.z) (polyResidues σ.c) =
      polyVecResidues (forgeryLowPart P pk σ) := by
  rw [forgeryLowPartResidues, verifierCommitmentResidues_eq]
  apply List.ext_getElem (by simp [polyVecResidues])
  intro i h₁ h₂
  apply List.ext_getElem (by simp [polyVecResidues, polyResidues])
  intro j h₃ h₄
  simp only [polyVecResidues, polyResidues, List.getElem_map, List.getElem_ofFn,
    lowBitsResidue_val, forgeryLowPart, ← ZMod.val_intCast, Int.toNat_natCast, Int.cast_neg]

/-- `compressedForgeryLowPartResidues` computes `compressedForgeryLowPart`. -/
theorem compressedForgeryLowPartResidues_eq (P : Params) [NeZero P.q] (d : ℕ)
    (pk : PublicKey P) (σ : CompressedSignature P) :
    compressedForgeryLowPartResidues P d (matrixResidues pk.A) (polyVecResidues pk.t)
        (polyVecResidues σ.z) (boolGridList σ.h) (polyResidues σ.c) =
      polyVecResidues (compressedForgeryLowPart P d pk σ) := by
  rw [compressedForgeryLowPartResidues, compressedVerifierCommitmentResidues_eq,
    publicKeyLowPartResidues_eq, scaleVecResidues_eq]
  set r := compressedVerifierCommitment P d pk σ.z σ.c
  have hres : ((boolGridList σ.h).zip (polyVecResidues r)).map
      (fun row => (row.1.zip row.2).map fun x => hintResidualResidue P.q P.γ₂ x.1 x.2) =
      polyVecResidues (fun i j => hintResidual P.q P.γ₂ (σ.h i j) (r i j)) := by
    apply List.ext_getElem (by simp [boolGridList, polyVecResidues])
    intro i h₁ h₂
    apply List.ext_getElem (by simp [boolGridList, polyVecResidues, polyResidues])
    intro j h₃ h₄
    simp [boolGridList, polyVecResidues, polyResidues, hintResidualResidue_val]
  rw [hres, addVecResidues_eq]
  congr 1
  funext i j
  have hmap := congrFun (congrFun (selfTargetMap_compressedForgeryLowPart d pk σ) i) j
  have hcmpr := congrFun (congrFun
    (compressedVerifierCommitment_eq_verifierCommitment_add_lowPart d pk σ.z σ.c) i) j
  simp only [selfTargetMap, Pi.add_apply] at hmap
  rw [useHint_mul_eq_add_hintResidual] at hmap
  simp only [Pi.add_apply] at hcmpr ⊢
  apply add_right_cancel (b := verifierCommitment P pk σ.z σ.c i j)
  rw [hmap]
  dsimp only [r]
  rw [hcmpr]
  ring

private theorem polyResidues_beq {n q : ℕ} [NeZero q] (a b : Fin n → ZMod q) :
    (polyResidues a == polyResidues b) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  simp only [polyResidues, List.ofFn_inj] at h
  exact funext fun i => ZMod.val_injective q (congrFun h i)

theorem verifierHighBitsWord_encode (P : Params) [NeZero P.q] (pk : PublicKey P)
    (msg : List Bool) (σ : Signature P) :
    verifierHighBitsWord P (ModuleLWE.encodeSample (pk.A, pk.t)) (encodeForgery (msg, σ)) =
      (intPolyVecList (highBitsVec P (verifierCommitment P pk σ.z σ.c)), msg) := by
  simp only [verifierHighBitsWord, decodePublicKeyResidues_encodeSample, encodeForgery,
    forgeryDecoder.decode_enc, verifierCommitmentResidues_eq, highBitsVecResidues_eq]

theorem verifyWithHashWord_encode (P : Params) [NeZero P.q] (msg : List Bool)
    (σ : Signature P) (cHash : Fin P.n → ZMod P.q) :
    verifyWithHashWord P (encodeForgery (msg, σ)) (polyResidues cHash) =
      (decide (ResponseShort P σ.z) && decide (InBall P.τ σ.c) && decide (cHash = σ.c)) := by
  simp only [verifyWithHashWord, encodeForgery, forgeryDecoder.decode_enc, verifyFromHashResidues,
    responseShortResidues_eq, inBallResidues_eq, polyResidues_beq]

theorem compressedVerifierHighBitsWord_encode (P : Params) [NeZero P.q] (d : ℕ)
    (pk : PublicKey P) (msg : List Bool) (σ : CompressedSignature P) :
    compressedVerifierHighBitsWord P d (ModuleLWE.encodeSample (pk.A, pk.t))
        (encodeCompressedForgery (msg, σ)) =
      (intPolyVecList (fun i => useHintVec P.q P.γ₂ (σ.h i)
        (compressedVerifierCommitment P d pk σ.z σ.c i)), msg) := by
  simp only [compressedVerifierHighBitsWord, decodePublicKeyResidues_encodeSample,
    encodeCompressedForgery, compressedForgeryDecoder.decode_enc,
    compressedVerifierCommitmentResidues_eq, useHintGridResidues_eq]

theorem compressedVerifyWithHashWord_encode (P : Params) [NeZero P.q] (msg : List Bool)
    (σ : CompressedSignature P) (cHash : Fin P.n → ZMod P.q) :
    compressedVerifyWithHashWord P (encodeCompressedForgery (msg, σ)) (polyResidues cHash) =
      (decide (ResponseShort P σ.z) && decide (InBall P.τ σ.c) && decide (cHash = σ.c)) := by
  simp only [compressedVerifyWithHashWord, encodeCompressedForgery,
    compressedForgeryDecoder.decode_enc, verifyFromHashResidues, responseShortResidues_eq,
    inBallResidues_eq, polyResidues_beq]

end Agreement

/-! ### Polynomial-time certificates -/

section PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Centered modular reduction of a binary natural modulo a binary modulus. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.centeredMod {m x : α → ℕ}
    (hm : ComputableInPolyTime m input encNat) (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => centeredMod (m a) (x a)) input encIntBin := by
  unfold Cslib.Crypto.MLDSA.centeredMod
  have hr := ComputableInPolyTime.binary_mod' hx hm
  have hhalf := ComputableInPolyTime.binary_div' hm (ComputableInPolyTime.const 2)
  have hrcast := ComputableInPolyTime.intBin_natCast.comp hr
  have hmcast := ComputableInPolyTime.intBin_natCast.comp hm
  dsimp only [Function.comp_def] at hrcast hmcast
  exact ComputableInPolyTime.ite_decide (hm.decide_eq' (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.intBin_natCast.comp hx)
    (ComputableInPolyTime.ite_decide (ComputableInPolyTime.binary_le' hr hhalf)
      hrcast (ComputableInPolyTime.intBin_sub' hrcast hmcast))

/-- `Power2Round` on a binary residue with a unary shift width `d`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.power2RoundResidue {d x : α → ℕ}
    (hd : ComputableInPolyTime d input encUnary) (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => power2RoundResidue (d a) (x a)) input
      (encPair encIntBin encIntBin) := by
  unfold Cslib.Crypto.MLDSA.power2RoundResidue
  have hpow := ComputableInPolyTime.binary_two_pow.comp hd
  dsimp only [Function.comp_def] at hpow
  have hr₀ := ComputableInPolyTime.centeredMod hpow hx
  have hdiff := ComputableInPolyTime.intBin_sub' (ComputableInPolyTime.intBin_natCast.comp hx) hr₀
  have hpowZ := ComputableInPolyTime.intBin_natCast.comp hpow
  dsimp only [Function.comp_def] at hpowZ
  exact (ComputableInPolyTime.intBin_div' hdiff hpowZ).prod hr₀

/-- `Decompose` on a binary residue with binary `q` and `γ₂`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.decomposeResidue {q γ₂ x : α → ℕ}
    (hq : ComputableInPolyTime q input encNat) (hγ₂ : ComputableInPolyTime γ₂ input encNat)
    (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => decomposeResidue (q a) (γ₂ a) (x a)) input
      (encPair encIntBin encIntBin) := by
  unfold Cslib.Crypto.MLDSA.decomposeResidue
  have h2γ := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hγ₂
  have hr₀ := ComputableInPolyTime.centeredMod h2γ hx
  have hdiff := ComputableInPolyTime.intBin_sub' (ComputableInPolyTime.intBin_natCast.comp hx) hr₀
  have hq1 := ComputableInPolyTime.intBin_sub'
    (ComputableInPolyTime.intBin_natCast.comp hq) (ComputableInPolyTime.const 1)
  have h2γZ := ComputableInPolyTime.intBin_natCast.comp h2γ
  dsimp only [Function.comp_def] at h2γZ
  exact ComputableInPolyTime.ite_decide (hdiff.decide_eq' hq1)
    ((ComputableInPolyTime.const 0).prod
      (ComputableInPolyTime.intBin_sub' hr₀ (ComputableInPolyTime.const 1)))
    ((ComputableInPolyTime.intBin_div' hdiff h2γZ).prod hr₀)

/-- `HighBits` on a binary residue with binary `q` and `γ₂`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.highBitsResidue {q γ₂ x : α → ℕ}
    (hq : ComputableInPolyTime q input encNat) (hγ₂ : ComputableInPolyTime γ₂ input encNat)
    (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => highBitsResidue (q a) (γ₂ a) (x a)) input encIntBin :=
  (ComputableInPolyTime.decomposeResidue hq hγ₂ hx).fst'

/-- `LowBits` on a binary residue with binary `q` and `γ₂`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.lowBitsResidue {q γ₂ x : α → ℕ}
    (hq : ComputableInPolyTime q input encNat) (hγ₂ : ComputableInPolyTime γ₂ input encNat)
    (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => lowBitsResidue (q a) (γ₂ a) (x a)) input encIntBin :=
  (ComputableInPolyTime.decomposeResidue hq hγ₂ hx).snd'

/-- `UseHint` on a hint bit and binary residue with binary `q` and `γ₂`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.useHintResidue {q γ₂ x : α → ℕ}
    {h : α → Bool} (hq : ComputableInPolyTime q input encNat)
    (hγ₂ : ComputableInPolyTime γ₂ input encNat) (hh : ComputableInPolyTime h input encBool)
    (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => useHintResidue (q a) (γ₂ a) (h a) (x a)) input encIntBin := by
  unfold Cslib.Crypto.MLDSA.useHintResidue
  have hm := ComputableInPolyTime.binary_div'
    (ComputableInPolyTime.binary_sub' hq (ComputableInPolyTime.const 1))
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hγ₂)
  have hmZ := ComputableInPolyTime.intBin_natCast.comp hm
  dsimp only [Function.comp_def] at hmZ
  have hr₁ := ComputableInPolyTime.highBitsResidue hq hγ₂ hx
  have hr₀ := ComputableInPolyTime.lowBitsResidue hq hγ₂ hx
  have hpos := ComputableInPolyTime.intBin_lt' (ComputableInPolyTime.const 0) hr₀
  have hbr := ComputableInPolyTime.ite_decide hpos
    (ComputableInPolyTime.intBin_mod'
      (ComputableInPolyTime.intBin_add' hr₁ (ComputableInPolyTime.const 1)) hmZ)
    (ComputableInPolyTime.intBin_mod'
      (ComputableInPolyTime.intBin_sub' hr₁ (ComputableInPolyTime.const 1)) hmZ)
  exact ComputableInPolyTime.ite' hh hbr hr₁

/-- `hintResidual` on a hint bit and binary residue with binary `q` and `γ₂`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.hintResidualResidue {q γ₂ x : α → ℕ}
    {h : α → Bool} (hq : ComputableInPolyTime q input encNat)
    (hγ₂ : ComputableInPolyTime γ₂ input encNat) (hh : ComputableInPolyTime h input encBool)
    (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => hintResidualResidue (q a) (γ₂ a) (h a) (x a)) input encNat := by
  unfold Cslib.Crypto.MLDSA.hintResidualResidue
  have h2γZ := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hγ₂)
  dsimp only [Function.comp_def] at h2γZ
  exact ComputableInPolyTime.intBin_emodNat'
    (ComputableInPolyTime.intBin_sub'
      (ComputableInPolyTime.intBin_mul'
        (ComputableInPolyTime.useHintResidue hq hγ₂ hh hx) h2γZ)
      (ComputableInPolyTime.intBin_natCast.comp hx)) hq

/-- Decode public-key matrix and target residue lists from an encoded Module-LWE sample. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.decodePublicKeyResidues {P : α → Params}
    {sample : α → List Bool} (hP : ComputableInPolyTime P input encParams)
    (hsample : ComputableInPolyTime sample input encBits) :
    ComputableInPolyTime (fun a => decodePublicKeyResidues (P a) (sample a)) input
      (encPair encMatrixResidues encPolyVecResidues) := by
  unfold Cslib.Crypto.MLDSA.decodePublicKeyResidues
  have hk : ComputableInPolyTime (fun a => (P a).k) input encUnary := by fun_prop
  have hℓ : ComputableInPolyTime (fun a => (P a).ℓ) input encUnary := by fun_prop
  have hn : ComputableInPolyTime (fun a => (P a).n) input encUnary := by fun_prop
  have hs := ModuleLWE.sampleDecoder.computableInPolyTime.comp hsample
  have hrows := (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime.comp hs.fst'
  dsimp only [Function.comp_def] at hs hrows
  exact (ComputableInPolyTime.entryResidues hk hℓ hn hrows).prod
    (ComputableInPolyTime.chunkResidues hk hn hs.snd')

/-- Native `moduleSISMap` on residue lists with unary dimensions and binary modulus. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.moduleSISMapResidues {k n q : α → ℕ}
    {A : α → List (List (List ℕ))} {z : α → List (List ℕ)}
    (hk : ComputableInPolyTime k input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hq : ComputableInPolyTime q input encNat)
    (hA : ComputableInPolyTime A input encMatrixResidues)
    (hz : ComputableInPolyTime z input encPolyVecResidues) :
    ComputableInPolyTime (fun a => moduleSISMapResidues (k a) (n a) (q a) (A a) (z a)) input
      encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.moduleSISMapResidues
  have hfst := ComputableInPolyTime.fst input encUnary
  have hsnd := ComputableInPolyTime.snd input encUnary
  have hrow := ComputableInPolyTime.listGetDWithInput (hA.comp hfst) hsnd []
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hk)
    (ComputableInPolyTime.negacyclicInnerResidues (hn.comp hfst) (hq.comp hfst) hrow
      (hz.comp hfst))

/-- Left multiplication of each polynomial in a residue vector by `c`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.scaleVecResidues {n q : α → ℕ}
    {c : α → List ℕ} {v : α → List (List ℕ)}
    (hn : ComputableInPolyTime n input encUnary) (hq : ComputableInPolyTime q input encNat)
    (hc : ComputableInPolyTime c input (encList encNat))
    (hv : ComputableInPolyTime v input encPolyVecResidues) :
    ComputableInPolyTime (fun a => scaleVecResidues (n a) (q a) (c a) (v a)) input
      encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.scaleVecResidues
  have hfst := ComputableInPolyTime.fst input (encList encNat)
  have hsnd := ComputableInPolyTime.snd input (encList encNat)
  have hmul := Cslib.computableInPolyTime_negacyclicMulResidues.comp
    (((hn.comp hfst).prod (hq.comp hfst)).prod ((hc.comp hfst).prod hsnd))
  exact ComputableInPolyTime.mapWithInput hv hmul

/-- Coefficientwise addition of residue vectors modulo `q`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.addVecResidues {q : α → ℕ}
    {u v : α → List (List ℕ)} (hq : ComputableInPolyTime q input encNat)
    (hu : ComputableInPolyTime u input encPolyVecResidues)
    (hv : ComputableInPolyTime v input encPolyVecResidues) :
    ComputableInPolyTime (fun a => addVecResidues (q a) (u a) (v a)) input encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.addVecResidues
  have hzip := (ComputableInPolyTime.zip (encList encNat) (encList encNat)).comp (hu.prod hv)
  have hfst := ComputableInPolyTime.fst input (encPair (encList encNat) (encList encNat))
  have hsnd := ComputableInPolyTime.snd input (encPair (encList encNat) (encList encNat))
  exact ComputableInPolyTime.mapWithInput hzip
    (ComputableInPolyTime.addResidues (hq.comp hfst) hsnd.fst' hsnd.snd')

/-- Coefficientwise subtraction of residue vectors modulo `q`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.subVecResidues {q : α → ℕ}
    {u v : α → List (List ℕ)} (hq : ComputableInPolyTime q input encNat)
    (hu : ComputableInPolyTime u input encPolyVecResidues)
    (hv : ComputableInPolyTime v input encPolyVecResidues) :
    ComputableInPolyTime (fun a => subVecResidues (q a) (u a) (v a)) input encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.subVecResidues
  have hzip := (ComputableInPolyTime.zip (encList encNat) (encList encNat)).comp (hu.prod hv)
  have hfst := ComputableInPolyTime.fst input (encPair (encList encNat) (encList encNat))
  have hsnd := ComputableInPolyTime.snd input (encPair (encList encNat) (encList encNat))
  exact ComputableInPolyTime.mapWithInput hzip
    (ComputableInPolyTime.subResidues (hq.comp hfst) hsnd.fst' hsnd.snd')

/-- Native verifier commitment `A z - c t` on residue lists. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.verifierCommitmentResidues
    {P : α → Params} {A : α → List (List (List ℕ))} {t z : α → List (List ℕ)} {c : α → List ℕ}
    (hP : ComputableInPolyTime P input encParams)
    (hA : ComputableInPolyTime A input encMatrixResidues)
    (ht : ComputableInPolyTime t input encPolyVecResidues)
    (hz : ComputableInPolyTime z input encPolyVecResidues)
    (hc : ComputableInPolyTime c input (encList encNat)) :
    ComputableInPolyTime
      (fun a => verifierCommitmentResidues (P a) (A a) (t a) (z a) (c a))
      input encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.verifierCommitmentResidues
  have hk : ComputableInPolyTime (fun a => (P a).k) input encUnary := by fun_prop
  have hn : ComputableInPolyTime (fun a => (P a).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun a => (P a).q) input encNat := by fun_prop
  exact ComputableInPolyTime.subVecResidues hq
    (ComputableInPolyTime.moduleSISMapResidues hk hn hq hA hz)
    (ComputableInPolyTime.scaleVecResidues hn hq hc ht)

/-- Native `publicKeyHighTerm` (`t₁ 2^d mod q`) on residue lists with unary `d`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.publicKeyHighTermResidues {q d : α → ℕ}
    {t : α → List (List ℕ)} (hq : ComputableInPolyTime q input encNat)
    (hd : ComputableInPolyTime d input encUnary)
    (ht : ComputableInPolyTime t input encPolyVecResidues) :
    ComputableInPolyTime (fun a => publicKeyHighTermResidues (q a) (d a) (t a)) input
      encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.publicKeyHighTermResidues
  let I₁ := encPair input (encList encNat)
  have hfst₁ := ComputableInPolyTime.fst input (encList encNat)
  have hsnd₁ := ComputableInPolyTime.snd input (encList encNat)
  have hfst₂ := ComputableInPolyTime.fst I₁ encNat
  have hsnd₂ := ComputableInPolyTime.snd I₁ encNat
  have hq₂ := (hq.comp hfst₁).comp hfst₂
  have hd₂ := (hd.comp hfst₁).comp hfst₂
  have hpowZ := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.binary_two_pow.comp hd₂)
  dsimp only [Function.comp_def] at hq₂ hd₂ hpowZ
  have hcoeff := ComputableInPolyTime.intBin_emodNat'
    (ComputableInPolyTime.intBin_mul'
      (ComputableInPolyTime.power2RoundResidue hd₂ hsnd₂).fst' hpowZ) hq₂
  exact ComputableInPolyTime.mapWithInput ht (ComputableInPolyTime.mapWithInput hsnd₁ hcoeff)

/-- Native `publicKeyLowPart` (`t₀ mod q`) on residue lists with unary `d`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.publicKeyLowPartResidues {q d : α → ℕ}
    {t : α → List (List ℕ)} (hq : ComputableInPolyTime q input encNat)
    (hd : ComputableInPolyTime d input encUnary)
    (ht : ComputableInPolyTime t input encPolyVecResidues) :
    ComputableInPolyTime (fun a => publicKeyLowPartResidues (q a) (d a) (t a)) input
      encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.publicKeyLowPartResidues
  let I₁ := encPair input (encList encNat)
  have hfst₁ := ComputableInPolyTime.fst input (encList encNat)
  have hsnd₁ := ComputableInPolyTime.snd input (encList encNat)
  have hfst₂ := ComputableInPolyTime.fst I₁ encNat
  have hsnd₂ := ComputableInPolyTime.snd I₁ encNat
  have hq₂ := (hq.comp hfst₁).comp hfst₂
  have hd₂ := (hd.comp hfst₁).comp hfst₂
  dsimp only [Function.comp_def] at hq₂ hd₂
  have hcoeff := ComputableInPolyTime.intBin_emodNat'
    (ComputableInPolyTime.power2RoundResidue hd₂ hsnd₂).snd' hq₂
  exact ComputableInPolyTime.mapWithInput ht (ComputableInPolyTime.mapWithInput hsnd₁ hcoeff)

/-- Native compressed verifier commitment `A z - c (t₁ 2^d)` on residue lists with unary `d`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.compressedVerifierCommitmentResidues
    {P : α → Params} {d : α → ℕ} {A : α → List (List (List ℕ))} {t z : α → List (List ℕ)}
    {c : α → List ℕ} (hP : ComputableInPolyTime P input encParams)
    (hd : ComputableInPolyTime d input encUnary)
    (hA : ComputableInPolyTime A input encMatrixResidues)
    (ht : ComputableInPolyTime t input encPolyVecResidues)
    (hz : ComputableInPolyTime z input encPolyVecResidues)
    (hc : ComputableInPolyTime c input (encList encNat)) :
    ComputableInPolyTime
      (fun a => compressedVerifierCommitmentResidues (P a) (d a) (A a) (t a) (z a) (c a))
      input encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.compressedVerifierCommitmentResidues
  have hk : ComputableInPolyTime (fun a => (P a).k) input encUnary := by fun_prop
  have hn : ComputableInPolyTime (fun a => (P a).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun a => (P a).q) input encNat := by fun_prop
  exact ComputableInPolyTime.subVecResidues hq
    (ComputableInPolyTime.moduleSISMapResidues hk hn hq hA hz)
    (ComputableInPolyTime.scaleVecResidues hn hq hc
      (ComputableInPolyTime.publicKeyHighTermResidues hq hd ht))

/-- Coefficientwise `HighBits` on residue vectors. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.highBitsVecResidues {q γ₂ : α → ℕ}
    {w : α → List (List ℕ)} (hq : ComputableInPolyTime q input encNat)
    (hγ₂ : ComputableInPolyTime γ₂ input encNat)
    (hw : ComputableInPolyTime w input encPolyVecResidues) :
    ComputableInPolyTime (fun a => highBitsVecResidues (q a) (γ₂ a) (w a)) input encIntPolyVec := by
  unfold Cslib.Crypto.MLDSA.highBitsVecResidues
  let I₁ := encPair input (encList encNat)
  have hfst₁ := ComputableInPolyTime.fst input (encList encNat)
  have hsnd₁ := ComputableInPolyTime.snd input (encList encNat)
  have hfst₂ := ComputableInPolyTime.fst I₁ encNat
  have hsnd₂ := ComputableInPolyTime.snd I₁ encNat
  exact ComputableInPolyTime.mapWithInput hw
    (ComputableInPolyTime.mapWithInput hsnd₁
      (ComputableInPolyTime.highBitsResidue
        ((hq.comp hfst₁).comp hfst₂) ((hγ₂.comp hfst₁).comp hfst₂) hsnd₂))

/-- Coefficientwise `UseHint` on hint bit grids and residue vectors. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.useHintGridResidues {q γ₂ : α → ℕ}
    {h : α → List (List Bool)} {r : α → List (List ℕ)}
    (hq : ComputableInPolyTime q input encNat) (hγ₂ : ComputableInPolyTime γ₂ input encNat)
    (hh : ComputableInPolyTime h input encBoolGrid)
    (hr : ComputableInPolyTime r input encPolyVecResidues) :
    ComputableInPolyTime (fun a => useHintGridResidues (q a) (γ₂ a) (h a) (r a)) input
      encIntPolyVec := by
  unfold Cslib.Crypto.MLDSA.useHintGridResidues
  let encRow := encPair encBits (encList encNat)
  let I₁ := encPair input encRow
  have hrows := (ComputableInPolyTime.zip encBits (encList encNat)).comp (hh.prod hr)
  have hfst₁ := ComputableInPolyTime.fst input encRow
  have hsnd₁ := ComputableInPolyTime.snd input encRow
  have hbitsList := (bits_encList_polyTime encBool).1.comp hsnd₁.fst'
  have hrowZip := (ComputableInPolyTime.zip encBool encNat).comp (hbitsList.prod hsnd₁.snd')
  dsimp only [Function.comp_def] at hrowZip
  have hfst₂ := ComputableInPolyTime.fst I₁ (encPair encBool encNat)
  have hsnd₂ := ComputableInPolyTime.snd I₁ (encPair encBool encNat)
  exact ComputableInPolyTime.mapWithInput hrows
    (ComputableInPolyTime.mapWithInput hrowZip
      (ComputableInPolyTime.useHintResidue ((hq.comp hfst₁).comp hfst₂)
        ((hγ₂.comp hfst₁).comp hfst₂) hsnd₂.fst' hsnd₂.snd'))

/-- Native `ResponseShort` check on residue vectors. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.responseShortResidues {P : α → Params}
    {z : α → List (List ℕ)} (hP : ComputableInPolyTime P input encParams)
    (hz : ComputableInPolyTime z input encPolyVecResidues) :
    ComputableInPolyTime (fun a => responseShortResidues (P a) (z a)) input encBool := by
  unfold Cslib.Crypto.MLDSA.responseShortResidues
  have hℓ : ComputableInPolyTime (fun a => (P a).ℓ) input encUnary := by fun_prop
  have hn : ComputableInPolyTime (fun a => (P a).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun a => (P a).q) input encNat := by fun_prop
  have hγ₁ : ComputableInPolyTime (fun a => (P a).γ₁) input encNat := by fun_prop
  have hβ : ComputableInPolyTime (fun a => (P a).β) input encNat := by fun_prop
  let I₁ := encPair input encUnary
  have hfst₁ := ComputableInPolyTime.fst input encUnary
  have hsnd₁ := ComputableInPolyTime.snd input encUnary
  have hfst₂ := ComputableInPolyTime.fst I₁ encUnary
  have hsnd₂ := ComputableInPolyTime.snd I₁ encUnary
  have hzi := ComputableInPolyTime.listGetDWithInput (hz.comp hfst₁) hsnd₁ []
  have hzij := ComputableInPolyTime.listGetDWithInput (hzi.comp hfst₂) hsnd₂ 0
  have hq₂ := (hq.comp hfst₁).comp hfst₂
  have hbound₂ := ComputableInPolyTime.intBin_sub'
    (ComputableInPolyTime.intBin_natCast.comp ((hγ₁.comp hfst₁).comp hfst₂))
    (ComputableInPolyTime.intBin_natCast.comp ((hβ.comp hfst₁).comp hfst₂))
  have habs₂ := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.intBin_natAbs.comp (ComputableInPolyTime.centeredMod hq₂ hzij))
  dsimp only [Function.comp_def] at habs₂ hbound₂
  have hinner := ComputableInPolyTime.allWithEncoding (encA := encUnary)
    (ComputableInPolyTime.intBin_lt' habs₂ hbound₂) ComputableInPolyTime.id'
    (ComputableInPolyTime.range.comp (hn.comp hfst₁))
  exact ComputableInPolyTime.allWithEncoding (encA := encUnary) hinner
    ComputableInPolyTime.id' (ComputableInPolyTime.range.comp hℓ)

/-- Native `InBall` check on challenge residue lists. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.inBallResidues {n q τ : α → ℕ}
    {c : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hq : ComputableInPolyTime q input encNat) (hτ : ComputableInPolyTime τ input encNat)
    (hc : ComputableInPolyTime c input (encList encNat)) :
    ComputableInPolyTime (fun a => inBallResidues (n a) (q a) (τ a) (c a)) input encBool := by
  unfold Cslib.Crypto.MLDSA.inBallResidues
  have hfst := ComputableInPolyTime.fst input encUnary
  have hsnd := ComputableInPolyTime.snd input encUnary
  have hci := ComputableInPolyTime.listGetDWithInput (hc.comp hfst) hsnd 0
  have habs := ComputableInPolyTime.intBin_natAbs.comp
    (ComputableInPolyTime.centeredMod (hq.comp hfst) hci)
  dsimp only [Function.comp_def] at habs
  have hall := ComputableInPolyTime.allWithEncoding (encA := encUnary)
    (ComputableInPolyTime.binary_le' habs (ComputableInPolyTime.const 1))
    ComputableInPolyTime.id' (ComputableInPolyTime.range.comp hn)
  have hnz : ComputableInPolyTime (fun p : α × ℕ => (c p.1).getD p.2 0 % q p.1 != 0)
      (encPair input encUnary) encBool :=
    ComputableInPolyTime.bool_not.comp
      ((ComputableInPolyTime.binary_mod' hci (hq.comp hfst)).beq (ComputableInPolyTime.const 0))
  have hcnt := ComputableInPolyTime.countPWithInput
    (test := fun a i => (c a).getD i 0 % q a != 0) (ComputableInPolyTime.range.comp hn) hnz
  exact ComputableInPolyTime.bool_and' hall
    ((ComputableInPolyTime.unary_to_binary.comp hcnt).beq hτ)

/-- Final verification check given `(z, c)` and challenge residues `cHash`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.verifyFromHashResidues {P : α → Params}
    {z : α → List (List ℕ)} {c cHash : α → List ℕ}
    (hP : ComputableInPolyTime P input encParams)
    (hz : ComputableInPolyTime z input encPolyVecResidues)
    (hc : ComputableInPolyTime c input (encList encNat))
    (hcHash : ComputableInPolyTime cHash input (encList encNat)) :
    ComputableInPolyTime (fun a => verifyFromHashResidues (P a) (z a) (c a) (cHash a)) input
      encBool := by
  unfold Cslib.Crypto.MLDSA.verifyFromHashResidues
  have hn : ComputableInPolyTime (fun a => (P a).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun a => (P a).q) input encNat := by fun_prop
  have hτ : ComputableInPolyTime (fun a => (P a).τ) input encNat := by fun_prop
  exact ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.responseShortResidues hP hz)
      (ComputableInPolyTime.inBallResidues hn hq hτ hc))
    (hcHash.beq hc)

/-- Native `forgeryLowPart` on residue lists. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.forgeryLowPartResidues {P : α → Params}
    {A : α → List (List (List ℕ))} {t z : α → List (List ℕ)} {c : α → List ℕ}
    (hP : ComputableInPolyTime P input encParams)
    (hA : ComputableInPolyTime A input encMatrixResidues)
    (ht : ComputableInPolyTime t input encPolyVecResidues)
    (hz : ComputableInPolyTime z input encPolyVecResidues)
    (hc : ComputableInPolyTime c input (encList encNat)) :
    ComputableInPolyTime (fun a => forgeryLowPartResidues (P a) (A a) (t a) (z a) (c a)) input
      encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.forgeryLowPartResidues
  have hq : ComputableInPolyTime (fun a => (P a).q) input encNat := by fun_prop
  have hγ₂ : ComputableInPolyTime (fun a => (P a).γ₂) input encNat := by fun_prop
  have hw := ComputableInPolyTime.verifierCommitmentResidues hP hA ht hz hc
  let I₁ := encPair input (encList encNat)
  have hfst₁ := ComputableInPolyTime.fst input (encList encNat)
  have hsnd₁ := ComputableInPolyTime.snd input (encList encNat)
  have hfst₂ := ComputableInPolyTime.fst I₁ encNat
  have hsnd₂ := ComputableInPolyTime.snd I₁ encNat
  have hq₂ := (hq.comp hfst₁).comp hfst₂
  have hγ₂₂ := (hγ₂.comp hfst₁).comp hfst₂
  have hneg := ComputableInPolyTime.intBin_neg.comp
    (ComputableInPolyTime.lowBitsResidue hq₂ hγ₂₂ hsnd₂)
  dsimp only [Function.comp_def] at hneg hq₂
  exact ComputableInPolyTime.mapWithInput hw
    (ComputableInPolyTime.mapWithInput hsnd₁ (ComputableInPolyTime.intBin_emodNat' hneg hq₂))

/-- Native `compressedForgeryLowPart` on residue lists with unary `d`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.compressedForgeryLowPartResidues
    {P : α → Params} {d : α → ℕ} {A : α → List (List (List ℕ))} {t z : α → List (List ℕ)}
    {h : α → List (List Bool)} {c : α → List ℕ}
    (hP : ComputableInPolyTime P input encParams)
    (hd : ComputableInPolyTime d input encUnary)
    (hA : ComputableInPolyTime A input encMatrixResidues)
    (ht : ComputableInPolyTime t input encPolyVecResidues)
    (hz : ComputableInPolyTime z input encPolyVecResidues)
    (hh : ComputableInPolyTime h input encBoolGrid)
    (hc : ComputableInPolyTime c input (encList encNat)) :
    ComputableInPolyTime
      (fun a => compressedForgeryLowPartResidues (P a) (d a) (A a) (t a) (z a) (h a) (c a))
      input encPolyVecResidues := by
  unfold Cslib.Crypto.MLDSA.compressedForgeryLowPartResidues
  have hn : ComputableInPolyTime (fun a => (P a).n) input encUnary := by fun_prop
  have hq : ComputableInPolyTime (fun a => (P a).q) input encNat := by fun_prop
  have hγ₂ : ComputableInPolyTime (fun a => (P a).γ₂) input encNat := by fun_prop
  have hr := ComputableInPolyTime.compressedVerifierCommitmentResidues hP hd hA ht hz hc
  let encRow := encPair encBits (encList encNat)
  let I₁ := encPair input encRow
  have hrows := (ComputableInPolyTime.zip encBits (encList encNat)).comp (hh.prod hr)
  have hfst₁ := ComputableInPolyTime.fst input encRow
  have hsnd₁ := ComputableInPolyTime.snd input encRow
  have hbitsList := (bits_encList_polyTime encBool).1.comp hsnd₁.fst'
  have hrowZip := (ComputableInPolyTime.zip encBool encNat).comp (hbitsList.prod hsnd₁.snd')
  dsimp only [Function.comp_def] at hrowZip
  have hfst₂ := ComputableInPolyTime.fst I₁ (encPair encBool encNat)
  have hsnd₂ := ComputableInPolyTime.snd I₁ (encPair encBool encNat)
  have hres : ComputableInPolyTime
      (fun a => ((h a).zip
        (compressedVerifierCommitmentResidues (P a) (d a) (A a) (t a) (z a) (c a))).map
        fun row => (row.1.zip row.2).map fun x => hintResidualResidue (P a).q (P a).γ₂ x.1 x.2)
      input encPolyVecResidues :=
    ComputableInPolyTime.mapWithInput hrows
      (ComputableInPolyTime.mapWithInput hrowZip
        (ComputableInPolyTime.hintResidualResidue ((hq.comp hfst₁).comp hfst₂)
          ((hγ₂.comp hfst₁).comp hfst₂) hsnd₂.fst' hsnd₂.snd'))
  exact ComputableInPolyTime.addVecResidues hq hres
    (ComputableInPolyTime.scaleVecResidues hn hq hc
      (ComputableInPolyTime.publicKeyLowPartResidues hq hd ht))

/-- Extract `(HighBits(A z - c t), M)` from encoded public-key sample and forgery words. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.verifierHighBitsWord {P : α → Params}
    {sample forgery : α → List Bool} (hP : ComputableInPolyTime P input encParams)
    (hsample : ComputableInPolyTime sample input encBits)
    (hforgery : ComputableInPolyTime forgery input encBits) :
    ComputableInPolyTime (fun a => verifierHighBitsWord (P a) (sample a) (forgery a)) input
      (encPair encIntPolyVec encBits) := by
  unfold Cslib.Crypto.MLDSA.verifierHighBitsWord
  have hq : ComputableInPolyTime (fun a => (P a).q) input encNat := by fun_prop
  have hγ₂ : ComputableInPolyTime (fun a => (P a).γ₂) input encNat := by fun_prop
  have hpk := ComputableInPolyTime.decodePublicKeyResidues hP hsample
  have hfg := forgeryDecoder.computableInPolyTime.comp hforgery
  dsimp only [Function.comp_def] at hfg
  have hzc := hfg.snd'
  exact (ComputableInPolyTime.highBitsVecResidues hq hγ₂
    (ComputableInPolyTime.verifierCommitmentResidues hP hpk.fst' hpk.snd' hzc.fst' hzc.snd')).prod
    hfg.fst'

/-- Check an encoded uncompressed forgery against challenge residues `cHash`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.verifyWithHashWord {P : α → Params}
    {forgery : α → List Bool} {cHash : α → List ℕ}
    (hP : ComputableInPolyTime P input encParams)
    (hforgery : ComputableInPolyTime forgery input encBits)
    (hcHash : ComputableInPolyTime cHash input (encList encNat)) :
    ComputableInPolyTime (fun a => verifyWithHashWord (P a) (forgery a) (cHash a)) input
      encBool := by
  unfold Cslib.Crypto.MLDSA.verifyWithHashWord
  have hzc := (forgeryDecoder.computableInPolyTime.comp hforgery).snd'
  dsimp only [Function.comp_def] at hzc
  exact ComputableInPolyTime.verifyFromHashResidues hP hzc.fst' hzc.snd' hcHash

/-- Extract `(UseHint(h, A z - c t₁ 2^d), M)` from encoded public-key and compressed forgery
words. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.compressedVerifierHighBitsWord
    {P : α → Params} {d : α → ℕ} {sample forgery : α → List Bool}
    (hP : ComputableInPolyTime P input encParams)
    (hd : ComputableInPolyTime d input encUnary)
    (hsample : ComputableInPolyTime sample input encBits)
    (hforgery : ComputableInPolyTime forgery input encBits) :
    ComputableInPolyTime (fun a => compressedVerifierHighBitsWord (P a) (d a) (sample a)
      (forgery a)) input (encPair encIntPolyVec encBits) := by
  unfold Cslib.Crypto.MLDSA.compressedVerifierHighBitsWord
  have hq : ComputableInPolyTime (fun a => (P a).q) input encNat := by fun_prop
  have hγ₂ : ComputableInPolyTime (fun a => (P a).γ₂) input encNat := by fun_prop
  have hpk := ComputableInPolyTime.decodePublicKeyResidues hP hsample
  have hfg := compressedForgeryDecoder.computableInPolyTime.comp hforgery
  dsimp only [Function.comp_def] at hfg
  have hzhc := hfg.snd'
  have hhc := hzhc.snd'
  exact (ComputableInPolyTime.useHintGridResidues hq hγ₂ hhc.fst'
    (ComputableInPolyTime.compressedVerifierCommitmentResidues hP hd hpk.fst' hpk.snd'
      hzhc.fst' hhc.snd')).prod hfg.fst'

/-- Check an encoded compressed forgery against challenge residues `cHash`. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.compressedVerifyWithHashWord
    {P : α → Params} {forgery : α → List Bool} {cHash : α → List ℕ}
    (hP : ComputableInPolyTime P input encParams)
    (hforgery : ComputableInPolyTime forgery input encBits)
    (hcHash : ComputableInPolyTime cHash input (encList encNat)) :
    ComputableInPolyTime (fun a => compressedVerifyWithHashWord (P a) (forgery a) (cHash a)) input
      encBool := by
  unfold Cslib.Crypto.MLDSA.compressedVerifyWithHashWord
  have hzhc := (compressedForgeryDecoder.computableInPolyTime.comp hforgery).snd'
  dsimp only [Function.comp_def] at hzhc
  have hhc := hzhc.snd'
  exact ComputableInPolyTime.verifyFromHashResidues hP hzhc.fst' hhc.snd' hcHash

end PolyTime

end Cslib.Crypto.MLDSA
