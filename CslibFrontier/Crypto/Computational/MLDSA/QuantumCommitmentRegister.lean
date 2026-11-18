/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.RandomXof
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.ValueQuery
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import CslibFrontier.Probability.PMF.UniformExtend

/-!
# Coherent access to the ML-DSA commitment digest register

Draw the SHAKE256 digest prefixes on all raw words of the FIPS commitment length as independent
bit strings before key generation. The joint distribution of the register and the full raw XOFs is
preserved. A placed coherent gate on the resulting SHAKE pair uses two XOR queries to this
register, with one fixed reversible response computation between them.

The digest widths and little-endian packing follow [NISTFIPS204], Algorithms 7 and 8, and
[NISTFIPS202], Appendix B.1. The finite oracle decomposition and gate comparison are original.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability Cslib.Quantum ExtendableOutput

private def registerBits (d : ℕ) : FixedBytes d ≃ BitString (8 * d) where
  toFun D := BitString.ofList _ (Keccak.bytesToBitsLE D.toList)
  invFun bits :=
    let bytes := ((List.ofFn bits).toChunks 8).map Keccak.bitsToByteLE
    fun i => bytes.getD i 0
  left_inv D := by
    have bits : List.ofFn (BitString.ofList (8 * d) (Keccak.bytesToBitsLE D.toList)) =
        Keccak.bytesToBitsLE D.toList :=
      BitString.ofFn_ofList (by rw [Keccak.length_bytesToBitsLE, FixedBytes.length_toList])
    funext i
    simp only [bits]
    have chunks := Keccak.bytesToBitsLE_toChunks
      (bits := Keccak.bytesToBitsLE D.toList) (by simp [Keccak.length_bytesToBitsLE])
    have bytes := Keccak.bytesToBitsLE_injective chunks
    rw [bytes]
    simp [FixedBytes.toList, List.getD_eq_getElem?_getD]
  right_inv bits := by
    have unpack := Keccak.bytesToBitsLE_toChunks (bits := List.ofFn bits) (by simp)
    have len := congrArg List.length unpack
    rw [Keccak.length_bytesToBitsLE, List.length_ofFn] at len
    have size : ((List.ofFn bits).toChunks 8).length = d := by
      simp only [List.length_map] at len
      lia
    have read : (List.ofFn fun i : Fin d =>
        (((List.ofFn bits).toChunks 8).map Keccak.bitsToByteLE).getD i 0) =
        ((List.ofFn bits).toChunks 8).map Keccak.bitsToByteLE := by
      apply List.ext_getElem
      · simp [size]
      · intro i hi _
        simp [List.getD_eq_getElem?_getD, size] at *
    apply List.ofFn_inj.mp
    dsimp only [FixedBytes.toList]
    rw [read, unpack, BitString.ofFn_ofList (by simp)]


/-- Bit length of the 512-bit representative followed by FIPS 204's packed high bits.
It is 6656 at ML-DSA-44 and -65, and 8704 at ML-DSA-87. -/
@[expose] def Level.commitmentInputBits (s : Level) : ℕ :=
  512 + 8 * (32 * (((s.params.q - 1) / (2 * s.params.γ₂) - 1).log2 + 1) * s.params.k)

private theorem commitmentInput_length (s : Level) (w : Fin s.params.k → Fin 256 → ℤ)
    {μ : List Bool} (hμ : μ.length = 512) :
    (commitmentInput s w μ).length = s.commitmentInputBits := by
  simp only [commitmentInput, List.length_append, hμ, Keccak.length_bytesToBitsLE,
    Level.commitmentInputBits]
  exact congrArg (fun n => 512 + 8 * n)
    (length_packCoeffs (rows := s.params.k) (width := _) fun i j => (w i j).toNat)

/-- Install a literal digest prefix on every SHAKE256 word of the FIPS commitment length,
including words that are also queried in another role. Long-read suffixes and SHAKE128
remain in the supplied XOF pair. -/
def Xofs.withDigestRegister (H : Xofs) (s : Level)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) : Xofs :=
  { H with h256 := H.h256.withPrefixes fun x =>
      if x.length = s.commitmentInputBits then
        some (((registerBits _).symm (D (BitString.ofList _ x))).toList) else none }

/-- Digest bits at a raw commitment-length input, in SHAKE's little-endian order. -/
def Xofs.readDigestRegister (H : Xofs) (s : Level) (x : BitString s.commitmentInputBits) :
    BitString (8 * digestBytes s) :=
  registerBits _ (fun j => H.h256.byteAt (List.ofFn x) j)

private def digestCells {a b : ℕ} (s : Level) (ha : s.commitmentInputBits ≤ a)
    (hb : digestBytes s ≤ b) : BitString s.commitmentInputBits × Fin (digestBytes s) ↪
      RawWord a × Fin b :=
  (show BitString s.commitmentInputBits ↪ RawWord a from
    ⟨fun x => word (List.ofFn x) (List.length_ofFn.le.trans ha), fun _ _ h =>
      List.ofFn_inj.mp (word_inj h)⟩).prodMap (Fin.castLEEmb hb)

private abbrev flatten (s : Level) :=
  ((Equiv.refl (BitString s.commitmentInputBits)).arrowCongr
    (registerBits (digestBytes s)).symm).trans (Equiv.curry _ _ Byte).symm

private theorem overwrite {a b : ℕ} (s : Level) (ha : s.commitmentInputBits ≤ a)
    (hb : digestBytes s ≤ b) (H : ExtendableOutput) (t : Table a b)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) :
    (install H t).withPrefixes (fun x =>
      if x.length = s.commitmentInputBits then
        some (((registerBits _).symm (D (BitString.ofList _ x))).toList) else none) =
      install H (Function.extend (digestCells s ha hb) (flatten s D) t) := by
  apply ext_byteAt
  intro x j
  rw [byteAt_withPrefixes, byteAt_install, byteAt_install]
  by_cases hx : x.length = s.commitmentInputBits ∧ j < digestBytes s
  · obtain ⟨len, small⟩ := hx
    let v := BitString.ofList s.commitmentInputBits x
    let p := (v, (⟨j, small⟩ : Fin (digestBytes s)))
    have atCell : digestCells s ha hb p =
        (word x (len.le.trans ha), ⟨j, small.trans_le hb⟩) := by
      refine Prod.ext ?_ rfl
      change word (List.ofFn (BitString.ofList s.commitmentInputBits x))
        (List.length_ofFn.le.trans ha) = word x (len.le.trans ha)
      simp only [BitString.ofFn_ofList len]
    simp only [len, small, ↓reduceIte, Option.bind_some, FixedBytes.toList, List.getElem?_ofFn,
      ↓reduceDIte, Option.getD_some, ha, small.trans_le hb, and_self]
    rw [← atCell, (digestCells s ha hb).injective.extend_apply]
    rfl
  · have miss {fit : x.length ≤ a} {idx : j < b} :
        ¬ ∃ p, digestCells s ha hb p = (word x fit, ⟨j, idx⟩) := by
      rintro ⟨⟨r, k⟩, h⟩
      have eq : List.ofFn r = x := word_inj (hx := List.length_ofFn.le.trans ha) (hy := fit)
        (congrArg Prod.fst h)
      have off : k.val = j := congrArg (fun z => z.2.val) h
      exact hx ⟨eq ▸ List.length_ofFn, off ▸ k.isLt⟩
    have off : ((if x.length = s.commitmentInputBits then
        some (((registerBits _).symm (D (BitString.ofList _ x))).toList) else none).bind
        (fun r => r[j]?)) = none := by
      by_cases len : x.length = s.commitmentInputBits
      · have far : ¬ j < digestBytes s := fun small => hx ⟨len, small⟩
        simp [len, FixedBytes.toList, far]
      · simp [len]
    rw [off, Option.getD_none]
    split
    · exact (Function.extend_apply' _ _ _ miss).symm
    · rfl

/-- Draw all SHAKE256 commitment-length digest prefixes independently before key generation.
The register and the resulting full raw oracle pair have exactly their joint law in the
finite random-XOF experiment, including all cross-role and longer coherent reads. -/
theorem Xofs.uniformPrefixes_digestRegister (base : Xofs) (s : Level) {a b : ℕ}
    (ha : s.commitmentInputBits ≤ a) (hb : digestBytes s ≤ b) :
    ((base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (BitString s.commitmentInputBits → BitString (8 * digestBytes s))).map
        fun D => (D, H.withDigestRegister s D)) =
      (base.uniformPrefixes a b).map fun H => (H.readDigestRegister s, H) := by
  let e := digestCells s ha hb
  let close (u t : Table a b) :=
    ((fun x => registerBits (digestBytes s) (fun i => t (e (x, i)))),
      (⟨install base.h128 u, install base.h256 t⟩ : Xofs))
  have read (u t : Table a b) :
      close u t = ((⟨install base.h128 u, install base.h256 t⟩ : Xofs).readDigestRegister s,
        ⟨install base.h128 u, install base.h256 t⟩) := by
    refine Prod.ext ?_ rfl
    funext x
    apply congrArg (registerBits _)
    funext i
    simp only [byteAt_install, List.length_ofFn, ha, i.isLt.trans_le hb, and_self, ↓reduceDIte]
    rfl
  have restore (u t : Table a b) (D : BitString s.commitmentInputBits → _) :
      close u (Function.extend e (flatten s D) t) =
        (D, (⟨install base.h128 u, install base.h256 t⟩ : Xofs).withDigestRegister s D) := by
    apply Prod.ext
    · funext x
      dsimp only [close]
      simp only [e.injective.extend_apply]
      exact (registerBits _).apply_symm_apply (D x)
    · exact congrArg (Xofs.mk (install base.h128 u) ·) (overwrite s ha hb _ _ D).symm
  rw [independent_tables]
  simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  conv_lhs => rw [PMF.bind_comm]
  conv_rhs => simp only [← PMF.bind_pure_comp]; rw [PMF.bind_comm]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (Table a b)) ·)
  funext u
  have law := PMF.uniformOfFintype_bind_bind_extend (κ := Byte) e (fun t => PMF.pure (close u t))
  rw [← PMF.uniformOfFintype_map_equiv (flatten s)] at law
  simp only [PMF.bind_map, Function.comp_def, restore] at law
  simpa only [← PMF.bind_pure_comp, Function.comp_def, read] using law

/-- FIPS 204 signing and verification read precisely the installed digest at their packed
commitment. The representative may contain any 512 bits. -/
theorem Xofs.commitmentDigest_withDigestRegister (H : Xofs) (s : Level)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (w : Fin s.params.k → Fin 256 → ℤ) {μ : List Bool} (hμ : μ.length = 512) :
    Keccak.bytesToBitsLE ((H.withDigestRegister s D).commitmentDigest s w μ) =
      List.ofFn (D (BitString.ofList _ (commitmentInput s w μ))) := by
  let v := D (BitString.ofList _ (commitmentInput s w μ))
  have bits := congrArg List.ofFn ((registerBits (digestBytes s)).apply_symm_apply v)
  change List.ofFn (BitString.ofList (8 * digestBytes s)
    (Keccak.bytesToBitsLE (((registerBits _).symm v).toList))) = _ at bits
  rw [BitString.ofFn_ofList (by rw [Keccak.length_bytesToBitsLE, FixedBytes.length_toList])] at bits
  simpa only [Xofs.commitmentDigest, Xofs.withDigestRegister, ExtendableOutput.withPrefixes,
    commitmentInput_length s w hμ, ↓reduceIte, ExtendableOutput.readWithPrefix,
    List.take_of_length_le (FixedBytes.length_toList _).le, FixedBytes.length_toList,
    List.drop_eq_nil_of_le (H.h256.length_read ..).le, List.append_nil, v] using bits

/-- The digest address decoded from a coherent device input. Queries at other lengths,
at malformed addresses and to SHAKE128 ignore the loaded digest. -/
def Xofs.digestLookup (s : Level) {a : ℕ} (x : BitString (a + 2)) :
    BitString s.commitmentInputBits :=
  match Xofs.unpad (List.ofFn fun i : Fin (a + 1) => x i.succ) with
  | none => 0
  | some word => BitString.ofList _ word

/-- Compute the native SHAKE response using one loaded digest. The same raw query decoder
handles both variants, shorter requests, suffixes and missing delimiters. -/
def Xofs.digestResponse (H : Xofs) (s : Level) (a b : ℕ) (x : BitString (a + 2))
    (v : BitString (8 * digestBytes s)) : BitString (8 * b) :=
  (H.withDigestRegister s fun _ => v).queryTable a b x

private theorem queryTable_register (H : Xofs) (s : Level)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) (a b : ℕ) :
    (H.withDigestRegister s D).queryTable a b =
      fun x => H.digestResponse s a b x (D (Xofs.digestLookup s x)) := by
  funext x
  unfold Xofs.digestResponse Xofs.queryTable Xofs.digestLookup
  split
  · rfl
  · rename_i word hw
    cases tag : x 0 <;> by_cases h : word.length = s.commitmentInputBits <;>
      simp only [hw, h, Bool.false_eq_true, ↓reduceIte, Xofs.withDigestRegister,
        ExtendableOutput.withPrefixes]

/-- Realize the actual placed SHAKE XOR gate by two queries to the independent digest register.
The same two scratch registers return to zero for every placement, including when the native
state is entangled across the addressed and unused wires. -/
theorem Xofs.xorQuery_withDigestRegister (H : Xofs) (s : Level)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) (a b m : ℕ)
    (wires : Fin (a + 2 + 8 * b) ↪ Fin m) (ψ : Qubits m) :
    lookupXor wires (Xofs.digestLookup s) (H.digestResponse s a b) D (cleanLookupState ψ) =
      cleanLookupState ((xorQuery ((H.withDigestRegister s D).queryTable a b) wires).eval ψ) := by
  rw [lookupXor_cleanLookupState, queryTable_register H s]

end Cslib.Crypto.MLDSA.FIPS204
