/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrProtocol
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.ProofOfKnowledge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Tactic.PPT

/-!
# Okamoto's Sigma protocol is a proof of knowledge of representations

Okamoto's Sigma protocol for knowledge of a representation (`SigmaProtocol.okamoto`,
[BonehShoup2023]) over a `PrimeOrderGroupFamily`, as a family indexed by a unary security
parameter `n` and a group description `d`. A statement is a pair `(h, u)` of group elements: the
second base `h` and the element `u` to be represented. A witness is a pair `(α, β)` of scalars with
`α • g + β • h = u`, for the generator `g` of the family. Group elements are encoded by the
family's encoding, scalars in binary, and pairs with the first component framed
(`okamotoEncoding`).

The extractor of special soundness is computed on words by `okamotoExtractWord`, which applies
`extractNat` to each coordinate of the two responses, so the generic rewinding knowledge extractor
of `CslibFrontier.Crypto.Protocols.SigmaProtocol.ProofOfKnowledge` is uniform strict PPT for
every uniform strict PPT prover (`isPPTOn_okamotoKnowledgeExtractor`). On every
statement, the honest verifier's acceptance probability `ε` and the extractor's success
probability `ε'` satisfy `ε ≤ 1 / q + 2 / 2 ^ n + √ε'` (`le_add_sqrt_okamotoExtractionGame`).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.okamotoFamily`,
  `Cslib.Crypto.PrimeOrderGroupFamily.okamotoEncoding`: the family and its word encodings.
* `Cslib.Crypto.PrimeOrderGroupFamily.okamotoExtract`,
  `Cslib.Crypto.PrimeOrderGroupFamily.okamotoExtractWord`: the extractor and its word function.
* `Cslib.Crypto.PrimeOrderGroupFamily.okamotoKnowledgeExtractor`: the rewinding knowledge
  extractor.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_okamoto`: efficient special
  soundness.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_okamotoKnowledgeExtractor`: the rewinding knowledge
  extractor is uniform strict PPT whenever the prover is.
* `Cslib.Crypto.PrimeOrderGroupFamily.le_add_sqrt_okamotoExtractionGame`:
  `ε ≤ 1 / q + 2 / 2 ^ n + √ε'` on every statement.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023]; `SigmaProtocol.okamoto` gives the locators.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-- Okamoto's Sigma protocol (`SigmaProtocol.okamoto`) in the group described by `i.2`,
with challenges in `ZMod q`. The statement `(h, u)` carries the second base `h`; a witness is a
representation `(α, β)` of `u`, meaning `α • g + β • h = u`. The security parameter `i.1` does not
change the protocol. -/
noncomputable def okamotoFamily (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2) × ZMod (F.order i.2)) (F.Carrier i.2 × F.Carrier i.2)
      (F.Carrier i.2) (ZMod (F.order i.2)) (ZMod (F.order i.2) × ZMod (F.order i.2)) :=
  linear (fun y => (LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2)
      (F.generator i.2)).coprod (LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2)
      y.1)) Prod.snd (Function.Embedding.refl _)

/-- The word encodings of `okamotoFamily`: the unary security parameter with the description,
group elements by the family's encoding, scalars in binary, and pairs with the first component
framed. -/
def okamotoEncoding :
    Encoding (ℕ × F.Desc) (fun i => F.Carrier i.2 × F.Carrier i.2) (fun i => F.Carrier i.2)
      (fun i => ZMod (F.order i.2)) (fun i => ZMod (F.order i.2) × ZMod (F.order i.2)) where
  index := encPair encUnary F.encDesc
  statement i := encPair (F.encodeEmbedding i.2) (F.encodeEmbedding i.2)
  commitment i := F.encodeEmbedding i.2
  challenge i := F.encScalar i.2
  response i := encPair (F.encScalar i.2) (F.encScalar i.2)

/-- Okamoto's extractor (`SigmaProtocol.linearExtract`), computed coordinatewise with
`extractNat`: it is `(c - c')⁻¹ • (z - z')` whenever `c ≠ c'`. -/
def okamotoExtract (i : ℕ × F.Desc) (_ : F.Carrier i.2 × F.Carrier i.2) (_ : F.Carrier i.2)
    (c : ZMod (F.order i.2)) (z : ZMod (F.order i.2) × ZMod (F.order i.2))
    (c' : ZMod (F.order i.2)) (z' : ZMod (F.order i.2) × ZMod (F.order i.2)) :
    ZMod (F.order i.2) × ZMod (F.order i.2) :=
  (extractNat (F.order i.2) c.val z.1.val c'.val z'.1.val,
    extractNat (F.order i.2) c.val z.2.val c'.val z'.2.val)

/-- Okamoto's extractor on words: on the index `(n, d)`, the binary challenges and the framed
pairs of binary responses of two conversations, return the framed pair of the two `extractNat`
values in binary. It computes `okamotoExtract` on encodings
(`extractorRealizedBy_okamotoExtractWord`). -/
def okamotoExtractWord :
    (ℕ × F.Desc) × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool →
      List Bool
  | ((_, d), _, _, c, z, c', z') =>
    encPair encBits encBits
      ((extractNat (F.order d) (ofBits c) (ofBits (unframe z)) (ofBits c')
          (ofBits (unframe z'))).bits,
        (extractNat (F.order d) (ofBits c) (ofBits (dropFrame z)) (ofBits c')
          (ofBits (dropFrame z'))).bits)

/-! ### Special soundness -/

/-- `okamotoExtractWord` is computable in polynomial time. -/
theorem computableInPolyTime_okamotoExtractWord :
    ComputableInPolyTime F.okamotoExtractWord (encPair (encPair encUnary F.encDesc)
      (encPair encBits (encPair encBits (encPair encBits (encPair encBits
        (encPair encBits encBits)))))) encBits := by
  unfold okamotoExtractWord
  fun_prop

/-- `okamotoExtractWord` computes Okamoto's extractor `okamotoExtract` on encodings. -/
theorem extractorRealizedBy_okamotoExtractWord :
    ExtractorRealizedBy F.okamotoEncoding (fun i => encPair (F.encScalar i.2) (F.encScalar i.2))
      F.okamotoExtract F.okamotoExtractWord := by
  intro i y t c ⟨z₁, z₂⟩ c' ⟨z₁', z₂'⟩
  simp only [okamotoExtractWord, okamotoEncoding, unframe_encPair, dropFrame_encPair]
  simp only [encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits, okamotoExtract,
    ZMod.val_natCast, extractNat, Nat.mod_mod, encPair_apply, encBits_apply]

/-- **Okamoto's protocol has efficient special soundness**, with `okamotoExtractWord` as its
polynomial-time word function. -/
theorem efficientSpecialSoundness_okamoto :
    EfficientSpecialSoundness F.okamotoFamily
      (fun i w y => w.1 • F.generator i.2 + w.2 • y.1 = y.2) F.okamotoEncoding
      (fun i => encPair (F.encScalar i.2) (F.encScalar i.2)) F.okamotoExtract where
  specialSoundness i y t c z c' z' hc hz hz' := by
    have hcast : ((c.val : ℕ) : ZMod (F.order i.2)) ≠ (c'.val : ℕ) := by
      simpa only [ZMod.natCast_zmod_val] using hc
    have h := linear_specialSoundness (fun y : F.Carrier i.2 × F.Carrier i.2 =>
      (LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2) (F.generator i.2)).coprod
        (LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2) y.1)) Prod.snd
      (Function.Embedding.refl _) y t c z c' z' hc hz hz'
    simp only [linearExtract, Function.Embedding.refl_apply, LinearMap.coprod_apply,
      LinearMap.toSpanSingleton_apply, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul] at h
    simp only [okamotoExtract, extractNat_cast hcast, ZMod.natCast_zmod_val]
    exact h
  polyTime := ⟨F.okamotoExtractWord, F.computableInPolyTime_okamotoExtractWord,
    F.extractorRealizedBy_okamotoExtractWord⟩

/-! ### The rewinding knowledge extractor -/

/-- The rewinding knowledge extractor for Okamoto's protocol: run the prover `A` to its
commitment, answer two challenges sampled by `schnorrSampleChallenge` from the same state, and
apply `okamotoExtractWord` to the two conversations. -/
noncomputable def okamotoKnowledgeExtractor (A : MaliciousProver (ℕ × F.Desc)) :
    (ℕ × F.Desc) × List Bool → ProbComp (List Bool) :=
  knowledgeExtractor F.okamotoEncoding F.schnorrSampleChallenge F.okamotoExtractWord A

/-- **Okamoto's knowledge extractor is uniform strict PPT** whenever the prover is. -/
theorem isPPTOn_okamotoKnowledgeExtractor {A : MaliciousProver (ℕ × F.Desc)}
    (hA : A.IsPPT (encPair encUnary F.encDesc)) :
    IsPPTOn (encPair (encPair encUnary F.encDesc) encBits) encBits
      (F.okamotoKnowledgeExtractor A) :=
  isPPTOn_knowledgeExtractor (enc := F.okamotoEncoding) F.isPPTOn_schnorrSampleChallenge
    F.computableInPolyTime_okamotoExtractWord hA

/-- **Okamoto's protocol is a proof of knowledge of representations.** At the security parameter
`n`, in the group described by `d` of order `q`, and on every statement `(h, u)`, if the prover `A`
convinces the honest verifier with probability `ε`, the knowledge extractor outputs the encoding of
a representation of `u` with probability `ε'` such that `ε ≤ 1 / q + 2 / 2 ^ n + √ε'`. -/
theorem le_add_sqrt_okamotoExtractionGame (A : MaliciousProver (ℕ × F.Desc)) (n : ℕ)
    (d : F.Desc) (y : F.Carrier d × F.Carrier d) :
    (Game.succProbability (acceptanceGame F.okamotoFamily F.okamotoEncoding A (n, d) y
        (PMF.uniformOfFintype (ZMod (F.order d)))) : ℝ) ≤
      1 / F.order d + 2 / 2 ^ n +
        √(Game.succProbability (extractionGame F.okamotoEncoding
          (fun i => encPair (F.encScalar i.2) (F.encScalar i.2))
          (fun i w y => w.1 • F.generator i.2 + w.2 • y.1 = y.2)
          (F.okamotoKnowledgeExtractor A) (n, d) y)) := by
  have h := le_add_sqrt_extractionGame F.efficientSpecialSoundness_okamoto.specialSoundness
    F.extractorRealizedBy_okamotoExtractWord A (n, d) y (F.closeTo_schnorrSampleChallenge (n, d))
  simp only [ZMod.card, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_ofNat] at h
  refine h.trans_eq ?_
  rw [okamotoKnowledgeExtractor]
  ring

end Cslib.Crypto.PrimeOrderGroupFamily
