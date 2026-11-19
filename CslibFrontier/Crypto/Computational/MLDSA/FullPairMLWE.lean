/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SecretExpansionLaw
public import CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXofMatrix
import all CslibFrontier.Crypto.Computational.MLDSA.ExpandAProgramming
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.MatrixOracle
import all CslibFrontier.Crypto.Computational.MLDSA.KeyOnly
import CslibFrontier.Probability.PMF.Bool

/-!
# The short-secret key switch after separating FIPS secret expansion

The private view of Algorithm 6 takes its 66-byte secret-expansion inputs from a separate
SHAKE256 stream. The public-pair signer and its quantum forger keep the ambient streams.
The reduction installs the decision-MLWE matrix at the public FIPS seed before running them.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204
open Cslib.Probability

/-- Private key-generation view with the 66-byte inputs of Algorithm 33 supplied by `secret`.
Algorithm 6's 34-byte seed-expansion input and its public-key hash still use `H`. -/
def Xofs.withExpandSStream (H secret : Xofs) : Xofs :=
  {H with h256 := {
    read x n := if x.length = 528 then secret.h256.read x n else H.h256.read x n
    length_read x n := by split <;> exact ExtendableOutput.length_read _ _ _
    take_read x m n h := by
      by_cases same : x.length = 528 <;> simp only [same, ↓reduceIte]
      · exact secret.h256.take_read x h
      · exact H.h256.take_read x h }}

private theorem seed_keep (H G : Xofs) (s : Level) (seed : FixedBytes 32) :
    (H.withExpandSStream G).expandKeySeed s seed = H.expandKeySeed s seed := by
  simp [Xofs.expandKeySeed, Xofs.withExpandSStream, length_keySeedInput]

private theorem separate_secret (H G : Xofs) (s : Level) (rho : List Byte) (hr : rho.length = 64) :
    (H.withExpandSStream G).expandS s rho = G.expandS s rho := by
  obtain ⟨r, rfl⟩ := FixedBytes.exists_toList hr
  have agree (i : ℕ) :
      (H.withExpandSStream G).secretPoly s r.toList i = G.secretPoly s r.toList i := by
    simp only [Xofs.secretPoly, ExtendableOutput.readBytes, Xofs.withExpandSStream,
      length_nonceInput_bits, ↓reduceIte]
  simp only [Xofs.expandS, agree]

private abbrev PostKey (s : Level) := Xofs → FixedBytes 32 → MLDSA.PublicKey s.params → Game

private noncomputable def observePair {s : Level} (matrix : Option (PublicMatrix s))
    (vectors : Option ((Fin s.params.ℓ → Poly) × (Fin s.params.k → Poly)))
    (run : MLDSA.PublicKey s.params → Game) : Game :=
  ((do let A ← matrix
       let (x, e) ← vectors
       return run ⟨A, ModuleLWE.sample A x e⟩) : Option Game).getD (PMF.pure false)

private noncomputable def idealShortPair {s : Level} (matrix : Option (PublicMatrix s))
    (run : MLDSA.PublicKey s.params → Game) : Game :=
  (MatrixOracle.shortVectorLaw s s.params.ℓ).bind fun x =>
    (MatrixOracle.shortVectorLaw s s.params.k).bind fun e =>
      observePair matrix (some (x, e)) run

private theorem expandS_observe_le (s : Level) (base : Xofs) (rho : List Byte)
    (hr : rho.length = 64) {a b : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b)
    (matrix : Option (PublicMatrix s)) (run : MLDSA.PublicKey s.params → Game) :
    let R := base.uniformPrefixes a b
    ((R.bind fun G => observePair matrix (G.expandS s rho) run) true) ≤
      idealShortPair matrix run true := by
  intro R
  obtain ⟨r, rfl⟩ := FixedBytes.exists_toList hr
  let use v := observePair matrix v run
  have eq := congrArg (PMF.bind · use) (uniformPrefixes_expandS base s r ha hb)
  simp only [PMF.bind_map, Function.comp_def, PMF.bind_bind] at eq
  rw [eq]
  rw [← PMF.bind_const (p := R) (q := idealShortPair matrix run)]
  apply PMF.bind_apply_mono_on_support
  intro G _
  split_ifs
  · simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, idealShortPair, use, le_refl]
  · cases matrix <;> simp [use, observePair, PMF.pure_apply]

private noncomputable def sourceGame {s : Level} (base : Xofs) (a b : ℕ)
    (run : PostKey s) : Game :=
  let R := base.uniformPrefixes a b
  R.bind fun H => R.bind fun G => (H.withExpandSStream G).fullPairExperiment s (run H)

private noncomputable def matrixGame {s : Level} (H : Xofs) (seed : FixedBytes 32)
    (run : PostKey s) : Game :=
  let rho := (H.expandKeySeed s seed).take 32
  idealShortPair (H.expandA s rho) (run H (fun j => rho[j.val]!))

private theorem source_le_matrixGame {s : Level} (base : Xofs) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b) (run : PostKey s) :
    sourceGame base a b run true ≤ ((base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed => matrixGame H seed run) true := by
  unfold sourceGame
  apply PMF.bind_apply_mono_on_support
  intro H _
  simp_rw [Xofs.fullPairExperiment_eq_expand, seed_keep]
  rw [PMF.bind_comm]
  apply PMF.bind_apply_mono_on_support
  intro seed _
  let ex := H.expandKeySeed s seed
  have hlen : ex.length = 128 := H.h256.length_read ..
  let rs := (ex.drop 32).take 64
  have hr : rs.length = 64 := by simp [rs, hlen]
  let A := H.expandA s (ex.take 32)
  let finish := run H (fun j => (ex.take 32)[j.val]!)
  change ((base.uniformPrefixes a b).bind fun G =>
    observePair A ((H.withExpandSStream G).expandS s rs) finish) true ≤ _
  simp_rw [separate_secret H _ s rs hr]
  exact expandS_observe_le s base rs hr ha hb A finish

-- A supplied pair provides both the matrix installed in the SHAKE128 rows and the full
-- vector rounded for the forger. The original row pattern decides matrix exhaustion.
private noncomputable def atChallenge {s : Level} (H : Xofs) (seed : FixedBytes 32)
    (run : PostKey s) (pk : MLDSA.PublicKey s.params) : Game :=
  let rho := (H.expandKeySeed s seed).take 32
  (PMF.uniformOfFintype (MatrixPrefixes s)).bind fun rows =>
    if ((H.withMatrixPrefixes s rho rows).expandA s rho).isSome then
      run (H.withMatrixPrefixes s rho (programMatrixPrefixes s rows pk.A))
        (fun j => rho[j.val]!) pk
    else PMF.pure false

private theorem planted_real {s : Level} (H : Xofs) (seed : FixedBytes 32) (run : PostKey s) :
    let rho := (H.expandKeySeed s seed).take 32
    ((PMF.uniformOfFintype (MatrixPrefixes s)).bind fun t =>
      matrixGame (H.withMatrixPrefixes s rho t) seed run) =
      (MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)).bind
        (atChallenge H seed run) := by
  intro rho
  let U := PMF.uniformOfFintype (MatrixPrefixes s)
  let M := PMF.uniformOfFintype (PublicMatrix s)
  let S := MatrixOracle.shortVectorLaw s s.params.ℓ
  let E := MatrixOracle.shortVectorLaw s s.params.k
  let use (p : Xofs × Option (PublicMatrix s)) :=
    idealShortPair p.2 (run p.1 (fun j => rho[j.val]!))
  have eq := congrArg (PMF.bind · use) (uniform_expandA_programMatrixPrefixes H s rho)
  simp only [PMF.bind_map, Function.comp_def] at eq
  apply eq.symm.trans
  rw [← PMF.uniformOfFintype_prod]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  simp only [MLDSA.keyLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  let v (A : PublicMatrix s) (x : Fin s.params.ℓ → Poly) (e : Fin s.params.k → Poly) :
      MLDSA.PublicKey s.params := ⟨A, ModuleLWE.sample A x e⟩
  let g (A : PublicMatrix s) (t : MatrixPrefixes s) := H.withMatrixPrefixes s rho
    (programMatrixPrefixes s t A)
  let mat (t : MatrixPrefixes s) := (H.withMatrixPrefixes s rho t).expandA s rho
  change (U.bind fun t => M.bind fun A => S.bind fun x => E.bind fun e =>
    observePair ((mat t).map fun _ => A) (some (x, e)) (run (g A t) (fun j => rho[j.val]!))) =
    M.bind fun A => S.bind fun x => E.bind fun e => U.bind fun t =>
      if (mat t).isSome then run (g A t) (fun j => rho[j.val]!) (v A x e) else PMF.pure false
  rw [PMF.bind_comm U M]
  apply congrArg (PMF.bind M ·)
  funext A
  rw [PMF.bind_comm U S]
  apply congrArg (PMF.bind S ·)
  funext x
  rw [PMF.bind_comm U E]
  apply congrArg (PMF.bind E ·)
  funext e
  apply congrArg (PMF.bind U ·)
  funext t
  cases mat t <;> rfl

private theorem resample_matrixGame {s : Level} (base : Xofs) {a b : ℕ}
    (ha : 272 ≤ a) (hb : 894 ≤ b) (run : PostKey s) :
    let R := base.uniformPrefixes a b
    let S := PMF.uniformOfFintype (FixedBytes 32)
    (R.bind fun H => S.bind fun seed =>
      (PMF.uniformOfFintype (MatrixPrefixes s)).bind fun t =>
        matrixGame (H.withMatrixPrefixes s ((H.expandKeySeed s seed).take 32) t) seed run) =
      R.bind fun H => S.bind fun seed => matrixGame H seed run := by
  intro R S
  let U := PMF.uniformOfFintype (Table a b)
  simp only [R, independent_tables, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (PMF.bind U ·)
  funext t
  rw [PMF.bind_comm U S, PMF.bind_comm U S]
  apply congrArg (PMF.bind S ·)
  funext seed
  let G : Xofs := {base with h256 := install base.h256 t}
  let rho := (G.expandKeySeed s seed).take 32
  have len : rho.length ≤ 32 := List.length_take_le ..
  exact resample_at_seed (s := s) G rho (by lia) hb (fun H => matrixGame H seed run)

private noncomputable def challengeTest {s : Level} (base : Xofs) (a b : ℕ)
    (run : PostKey s) (pk : MLDSA.PublicKey s.params) : Game :=
  (base.uniformPrefixes a b).bind fun H =>
    (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed => atChallenge H seed run pk

private theorem matrixGame_eq_real {s : Level} (base : Xofs) {a b : ℕ}
    (ha : 272 ≤ a) (hb : 894 ≤ b) (run : PostKey s) :
    ((base.uniformPrefixes a b).bind fun H => (PMF.uniformOfFintype (FixedBytes 32)).bind
      fun seed => matrixGame H seed run) =
      (MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)).bind
        (challengeTest base a b run) := by
  rw [← resample_matrixGame base ha hb run]
  simp_rw [planted_real]
  let K := MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)
  let R := base.uniformPrefixes a b
  let U := PMF.uniformOfFintype (FixedBytes 32)
  change (R.bind fun H => U.bind fun seed => K.bind (atChallenge H seed run)) = _
  simp_rw [PMF.bind_comm U K]
  rw [PMF.bind_comm R K]
  rfl

namespace QuantumSigningForger

private noncomputable def freshDigestTest (C : QuantumSigningForger) (s : Level) : PostKey s :=
  fun H rho pk => (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin)

/-- Fresh-digest success with native key generation using an independent secret-expansion stream.
The public-pair signer and the quantum forger share the ambient XOFs. -/
noncomputable def independentExpandSGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) : Game :=
  sourceGame base a b (freshDigestTest C s)

/-- Test a supplied MLWE pair by installing its matrix in the public-seed SHAKE128 rows
and running the adaptive public-pair signer with that same pair. -/
noncomputable def fullPairMLWETest (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) (pk : MLDSA.PublicKey s.params) : Game :=
  challengeTest base a b (freshDigestTest C s) pk

/-- In the independent secret-expansion game, switching the public pair to uniform costs
at most the decision-MLWE advantage of the displayed pair test. Failed key expansion cannot
win. The comparison is a statement about probability laws. -/
theorem independentExpandSGame_le_uniform_add_mlwe (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b : ℕ} (ha : 528 ≤ a) (hb : 894 ≤ b) :
    let test := C.fullPairMLWETest s base a b
    let uniformGame := (MLDSA.uniformKeyLaw s.params).bind test
    let realGame := (MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)).bind test
    (C.independentExpandSGame s base a b).succProbability ≤
      Game.succProbability uniformGame + Game.advantage realGame uniformGame := by
  intro test uniformGame realGame
  have h := source_le_matrixGame base ha (by lia : 481 ≤ b) (freshDigestTest C s)
  rw [matrixGame_eq_real base (by lia : 272 ≤ a) hb] at h
  exact (Game.succProbability_mono h).trans (Game.succProbability_le_add_of_advantage_le le_rfl)

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
