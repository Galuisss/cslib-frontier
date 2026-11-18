/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.MatrixOracle
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Memoize
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Sum
import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PMFSwap

/-!
# The ML-DSA key-only game with shared classical matrix and commitment oracles

For a published rounded byte key, the corrected witness in [BaiEtAl2021Dilithium], §6.2.1,
equation (10), has its low component, response and challenge in the columns of
`[I | A | -t]`. The verifier queries its reconstructed commitment, and that commitment times
`2γ₂` is the module product of the witness.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.SharedDigest

open Probability OracleComp

attribute [local instance 2000] instBEqOfDecidableEq

/-- Systematic self-target instance on the full (unrounded) Module-LWE challenge. -/
def systematic (s : Level) (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly := fun i =>
  Fin.snoc (Fin.append (fun j => if i = j then (1 : Negacyclic (ZMod 8380417) 256).coeffs else 0)
    (A i)) (-t i)

/-- Integer lift of the three blocks of a self-target witness, with the challenge last. -/
def liftWitness (s : Level) (y : SelfTargetCandidate s.params) :
    Fin (s.params.k + s.params.ℓ + 1) → Fin 256 → ℤ :=
  fun i j => ((Fin.snoc (α := fun _ => Poly) (Fin.append y.u y.z) y.c i) j).valMinAbs

/-- Multiplying the three lifted blocks by the systematic matrix gives the full self-target
product, including the public-key rounding correction in any corrected low block. -/
theorem systematic_liftWitness (s : Level) (A : PublicMatrix s) (t : Fin s.params.k → Poly)
    (y : SelfTargetCandidate s.params) :
    moduleSISMap (systematic s A t) (fun i j => (liftWitness s y i j : ZMod 8380417)) =
      selfTargetMap s.params ⟨A, t⟩ y.u y.z y.c := by
  funext i
  have hid : (∑ j, negacyclicMul
      (if i = j then (1 : Negacyclic (ZMod 8380417) 256).coeffs else 0) (y.u j)) = y.u i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  simp only [moduleSISMap, systematic, liftWitness, ZMod.coe_valMinAbs, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    neg_negacyclicMul, selfTargetMap, verifierCommitment, Pi.add_apply, Pi.neg_apply, hid,
    sub_eq_add_neg, add_assoc, negacyclicMul_comm (t i) y.c]

private theorem liftWitness_bound {s : Level} {y : SelfTargetCandidate s.params} {radius : ℕ}
    (hu : ModuleSIS.inInfNormBound radius y.u) (hz : ModuleSIS.inInfNormBound radius y.z)
    (hc : InBall s.params.τ y.c) (hr : 1 ≤ radius) :
    ∀ i j, |liftWitness s y i j| ≤ radius := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa [liftWitness] using (hc.1 j).trans (show (1 : ℤ) ≤ (radius : ℤ) by exact_mod_cast hr)
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · change |(Fin.snoc (α := fun _ => Poly) (Fin.append y.u y.z) y.c
          ((Fin.castAdd _ a).castSucc) j).valMinAbs| ≤ _
      simpa only [Fin.snoc_castSucc, Fin.append_left] using hu a j
    · change |(Fin.snoc (α := fun _ => Poly) (Fin.append y.u y.z) y.c
          ((Fin.natAdd _ b).castSucc) j).valMinAbs| ≤ _
      simpa only [Fin.snoc_castSucc, Fin.append_right] using hz b j

private abbrev MatrixInstance (s : Level) :=
  Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly

private def fullKey (s : Level) (M : MatrixInstance s) : MLDSA.PublicKey s.params where
  A i j := M i ((Fin.natAdd _ j).castSucc)
  t i := -M i (Fin.last _)

private theorem fullKey_systematic (s : Level) (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    fullKey s (systematic s A t) = ⟨A, t⟩ := by
  simp only [fullKey, systematic, Fin.snoc_castSucc, Fin.append_right, Fin.snoc_last, neg_neg]

private structure Opening (s : Level) where
  signature : Signature s
  challenge : Poly

private def opening (s : Level) (f : Forgery) : Option (Opening s) := do
  guard (f.context.length ≤ 255)
  let σ ← sigDecode s f.signature
  let c ← sampleInBall s σ.digest
  guard (ResponseShort s.params σ.z)
  return ⟨σ, c⟩

private theorem opening_spec {s : Level} {f : Forgery} {o : Opening s}
    (h : opening s f = some o) :
    sampleInBall s o.signature.digest = some o.challenge ∧
      ResponseShort s.params o.signature.z := by
  by_cases hctx : f.context.length ≤ 255
  · cases hd : sigDecode s f.signature with
    | none => simp [opening, guard, hctx, hd] at h
    | some σ =>
      cases hc : sampleInBall s σ.digest with
      | none => simp [opening, guard, hctx, hd, hc] at h
      | some c =>
        by_cases hz : ResponseShort s.params σ.z
        · have he : (⟨σ, c⟩ : Opening s) = o := by
            simpa [opening, guard, hctx, hd, hc, hz] using h
          subst o
          exact ⟨hc, hz⟩
        · simp [opening, guard, hctx, hd, hc, hz] at h
  · simp [opening, guard, hctx] at h

private abbrev Digest (s : Level) := FixedBytes (digestBytes s)
private abbrev Point (s : Level) := ModuleSIS.SelfTarget.Point s.params.k 256 8380417

private def commitmentPoint (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) (o : Opening s) : Point s :=
  (messageRepresentative bytes (formattedMessage f), fun i j =>
    ((hintedCommitment s (publicKey s bytes A) o.signature o.challenge i j *
      (2 * s.params.γ₂ : ℕ) : ℤ) : ZMod 8380417))

/-- Key-only byte verification with a classical commitment query. The query contains the
message representative and the hinted high commitment on its canonical `2γ₂` grid.
The digest bytes in the signature must match the oracle reply exactly. -/
def verify (s : Level) (bytes : List Byte) (A : PublicMatrix s) (f : Forgery) :
    OracleComp (fun _ : ModuleSIS.SelfTarget.Point s.params.k 256 8380417 =>
      FixedBytes (digestBytes s)) Bool :=
  if bytes.length = 32 + 320 * s.params.k then
    match opening s f with
    | none => pure false
    | some o => do
      let digest ← query (commitmentPoint s bytes A f o)
      return decide (digest.toList = o.signature.digest)
  else pure false

/-- The concrete SHAKE digest at a grid point, represented by the parameter set's number of
bytes. This is the deterministic oracle used to recover the FIPS byte verifier. -/
def shakeReply (s : Level) (p : ModuleSIS.SelfTarget.Point s.params.k 256 8380417) :
    FixedBytes (digestBytes s) := fun i =>
  (commitmentDigest s (highBitsVec s.params p.2) p.1).get
    (i.cast (length_commitmentDigest s _ _).symm)

private theorem toList_shakeReply (s : Level) (p : Point s) :
    (shakeReply s p).toList = commitmentDigest s (highBitsVec s.params p.2) p.1 := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [FixedBytes.toList, List.getElem_ofFn, shakeReply]
    rfl

private theorem shakeReply_at (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) (o : Opening s) :
    (shakeReply s (commitmentPoint s bytes A f o)).toList =
      commitmentDigest s (hintedCommitment s (publicKey s bytes A) o.signature o.challenge)
        (messageRepresentative bytes (formattedMessage f)) := by
  have hq : 4 * s.params.γ₂ < s.params.q := by cases s <;> decide
  have hw : highBitsVec s.params (commitmentPoint s bytes A f o).2 =
      hintedCommitment s (publicKey s bytes A) o.signature o.challenge := by
    funext i j
    exact highBits_intCast_mul s.valid.γ₂_pos s.valid.two_mul_γ₂_dvd
      (useHint_nonneg s.valid.γ₂_pos hq _ _)
      (useHint_lt s.valid.γ₂_pos s.valid.two_mul_γ₂_dvd hq _ _)
  rw [toList_shakeReply, hw]
  rfl

/-- Supplying concrete SHAKE replies to the oracle verifier reproduces acceptance of
Algorithm 3 on the same byte key, context, message and signature. -/
theorem verify_shakeReply_iff (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) :
    interpret (m := Id) (shakeReply s) (verify s bytes A f) = true ↔
      verifyWithExpansion s (fun _ => some A) bytes f.message f.context f.signature =
        some true := by
  rw [verifyWithMatrix_eq_some_true_iff]
  by_cases hlen : bytes.length = 32 + 320 * s.params.k
  · by_cases hctx : f.context.length ≤ 255
    · cases hd : sigDecode s f.signature with
      | none => simp [verify, opening, guard, hctx, hlen, hd]
      | some σ =>
        cases hc : sampleInBall s σ.digest with
        | none => simp [verify, opening, guard, hctx, hlen, hd, hc]
        | some c =>
          by_cases hz : ResponseShort s.params σ.z
          · have hopen : opening s f = some ⟨σ, c⟩ := by
              simp [opening, guard, hctx, hd, hc, hz]
            simp only [verify, hlen, ite_true, hopen, bind_pure_comp, interpret_map,
              interpret_query]
            change decide ((shakeReply s (commitmentPoint s bytes A f ⟨σ, c⟩)).toList = σ.digest) =
              true ↔ _
            simp [shakeReply_at, hctx, hc, hz]
          · simp [verify, opening, guard, hctx, hlen, hd, hc, hz]
    · simp [verify, opening, guard, hctx, hlen]
  · simp [verify, hlen]

private def witness (s : Level) (pk : MLDSA.PublicKey s.params) (bytes : List Byte)
    (f : Forgery) (o : Opening s) : SelfTargetCandidate s.params :=
  SelfTargetCandidate.ofCompressedForgery s.params 13 pk
    (messageRepresentative bytes (formattedMessage f)) ⟨o.signature.z, o.signature.h, o.challenge⟩

private theorem product_witness (s : Level) (rho : FixedBytes 32) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) (f : Forgery) (o : Opening s) :
    let bytes := encodePublic s rho.toList t
    let y := witness s ⟨A, t⟩ bytes f o
    (y.msg, moduleSISMap (systematic s A t) (fun i j => (liftWitness s y i j : ZMod 8380417))) =
      commitmentPoint s bytes A f o := by
  dsimp only
  rw [systematic_liftWitness]
  simp only [witness, SelfTargetCandidate.ofCompressedForgery]
  rw [selfTargetMap_compressedForgeryLowPart]
  unfold commitmentPoint hintedCommitment compressedVerifierCommitment
  rw [decode_encodePublic, publicKey_matrix]
  rfl

private theorem short_witness {s : Level} {pk : MLDSA.PublicKey s.params} {bytes : List Byte}
    {f : Forgery} {o : Opening s} (h : opening s f = some o) :
    ∀ i j, |liftWitness s (witness s pk bytes f o) i j| ≤
      compressedSelfTargetRadius s.params 13 := by
  obtain ⟨hc, hz⟩ := opening_spec h
  have hball := inBall_of_sampleInBall hc
  have hv : compressedVerify s.params 13 (fun _ => o.challenge) pk
      (messageRepresentative bytes (formattedMessage f))
      ⟨o.signature.z, o.signature.h, o.challenge⟩ := by
    simp [compressedVerify, hz, hball]
  have hy := isSelfTargetSolution_of_compressedVerify s.valid (by cases s <;> decide)
    (by decide : 0 < 13) hv
  exact liftWitness_bound hy.1 hy.2.1 hball (by unfold compressedSelfTargetRadius; omega)

/-- Adversary with saved private randomness and a joint interface for matrix-seed and
commitment-digest queries. -/
abbrev Forger (s : Level) (Coins : Type) :=
  List Byte → Coins → OracleComp
    ((fun _ : FixedBytes 32 => PublicMatrix s) ⊕ₒ
      (fun _ : ModuleSIS.SelfTarget.Point s.params.k 256 8380417 => FixedBytes (digestBytes s)))
    Forgery

/-- Saved randomness used by the two runs of the fork. Every query has a fresh independent
matrix available, and cached seeds keep their original answer. -/
structure Saved (s : Level) (Coins : Type) where
  /-- The forger's private coins. -/
  coins : Coins
  /-- Public matrix seed sampled independently of the challenge. -/
  seed : FixedBytes 32
  /-- An independent matrix for each query position up to the forger's budget. -/
  matrices : List (PublicMatrix s)

private def sampleBytes (n : ℕ) : ProbComp (FixedBytes n) := replicateFin n (ProbComp.unifFin 255)

private theorem eval_sampleBytes (n : ℕ) :
    (sampleBytes n).eval = PMF.uniformOfFintype (FixedBytes n) := by
  simp only [sampleBytes, ProbComp.eval_replicateFin, ProbComp.eval_unifFin,
    PMF.pi_uniformOfFintype]

/-- Draw private coins, a fresh matrix seed, and at most `Q` independent matrix responses. -/
def sampleSaved {Coins : Type} (s : Level) (Q : ℕ) (coins : ProbComp Coins) :
    ProbComp (Saved s Coins) := do
  let r ← coins
  let rho ← sampleBytes 32
  let tape ← replicateFin Q (MatrixOracle.sampleMatrix s)
  return ⟨r, rho, List.ofFn tape⟩

private abbrev Cache (s : Level) := List (FixedBytes 32 × PublicMatrix s)
private abbrev DigestOracle (s : Level) := fun _ : Point s => Digest s

private def handler (s : Level) (matrix : PublicMatrix s) :
    (q : FixedBytes 32 ⊕ Point s) → StateT (Cache s) (OracleComp (DigestOracle s))
      (((fun _ : FixedBytes 32 => PublicMatrix s) ⊕ₒ DigestOracle s) q) := sumHandler
  (fun rho : FixedBytes 32 => memoize (m := OracleComp (DigestOracle s))
    (fun _ => pure matrix) rho)
  (fun p : Point s => (fun cache : Cache s => (fun d => (d, cache)) <$> query p))

private def runForger {Coins : Type} (s : Level) (adv : Forger s Coins)
    (r : Saved s Coins) (pk : MLDSA.PublicKey s.params) :
    OracleComp (DigestOracle s) Forgery :=
  Prod.fst <$> (interpret (withSampleList 0 (handler s))
    (adv (encodePublic s r.seed.toList pk.t) r.coins)).run ([(r.seed, pk.A)], r.matrices)

private def candidateOutput (s : Level) (pk : MLDSA.PublicKey s.params) (bytes : List Byte)
    (f : Forgery) : List Bool × (Fin (s.params.k + s.params.ℓ + 1) → Fin 256 → ℤ) :=
  match opening s f with
  | none => ([], 0)
  | some o =>
    let y := witness s pk bytes f o
    (y.msg, liftWitness s y)

/-- Run the byte-key adversary on the original matrix seed and rounded bytes while it
queries the same digest oracle as the final self-target check. -/
def solver {Coins : Type} (s : Level) (adv : Forger s Coins) :
    ModuleSIS.SelfTarget.Adversary s.params.k (s.params.k + s.params.ℓ) 256 8380417
      (FixedBytes (digestBytes s)) (Saved s Coins) := fun M r =>
  let pk := fullKey s M
  (candidateOutput s pk (encodePublic s r.seed.toList pk.t)) <$> runForger s adv r pk

private theorem solver_bounded {Coins : Type} {s : Level} {adv : Forger s Coins} {Q : ℕ}
    (hQ : ∀ bytes r, (adv bytes r).IsQueryBounded Q) (M) (r) :
    (solver s adv M r).IsQueryBounded Q := by
  apply (isCostBounded_map_iff _ _ _).mpr
  apply (isCostBounded_map_iff _ _ _).mpr
  apply IsCostBounded.run_interpret _ (hQ _ _)
  intro q state
  rcases state with ⟨cache, tape⟩
  rcases q with rho | p
  · apply (isCostBounded_map_iff _ _ _).mpr
    change IsCostBounded _ (memoize (fun _ => pure (tape.headD 0)) rho cache) 1
    cases he : cache.lookup rho with
    | none => rw [memoize_of_none _ _ _ he, pure_bind]; exact .pure _ _
    | some v => rw [memoize_of_some _ _ _ _ he]; exact .pure _ _
  · apply (isCostBounded_map_iff _ _ _).mpr
    apply (isCostBounded_map_iff _ _ _).mpr
    exact IsCostBounded.query p

private def runDigest (s : Level) (program : OracleComp (DigestOracle s) Bool) : ProbComp Bool :=
  Prod.fst <$> (interpret (memoize fun _ => sampleBytes (digestBytes s)) program).run []

private theorem memoize_digest (s : Level) (p : Point s) (cache : List (Point s × Digest s)) :
      memoize (fun _ => PMF.uniformOfFintype (Digest s)) p cache =
        Protocols.ROMSignature.oracle (Digest s) p cache := by
  change _ = (Protocols.ROMSignature.oracle (Digest s) p).run cache
  cases h : cache.lookup p with
  | none =>
    rw [memoize_of_none _ _ _ h, Protocols.ROMSignature.run_oracle_of_lookup_eq_none h]
    rfl
  | some d =>
    rw [memoize_of_some _ _ _ _ h, Protocols.ROMSignature.run_oracle_of_lookup_eq_some h]
    rfl

private theorem eval_runDigest (s : Level) (program : OracleComp (DigestOracle s) Bool) :
    (runDigest s program).eval = ((interpret (Protocols.ROMSignature.oracle (Digest s))
      program).run []).map Prod.fst := by
  simp only [runDigest, ProbComp.eval_map, map_run_interpret ProbComp.isMonadHom_eval,
    ProbComp.eval_memoize, eval_sampleBytes]
  simp only [memoize_digest]

private abbrev Both (s : Level) :=
  (fun _ : FixedBytes 32 => PublicMatrix s) ⊕ₒ DigestOracle s

private abbrev DigestCache (s : Level) := List (Point s × Digest s)

private noncomputable def stepAt (s : Level) (v : PublicMatrix s) :=
  RandomOracle.memoizeSum (fun _ : FixedBytes 32 => PMF.pure v)
    (fun _ : Point s => PMF.uniformOfFintype (Digest s))

private theorem tape_run {s : Level} {α : Type} (program : OracleComp (Both s) α)
    (mc : Cache s) (dc : DigestCache s) (tape : List (PublicMatrix s)) :
    ((interpret (Protocols.ROMSignature.oracle (Digest s))
      ((interpret (withSampleList 0 (handler s)) program).run (mc, tape))).run dc).map
      (fun ((a, (mc', tape')), dc') => (a, (mc', dc'), tape')) =
    (interpret (withSampleList 0 (stepAt s)) program).run ((mc, dc), tape) := by
  rw [run_interpret_run_interpret]
  simp only [PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
  refine run_interpret_map_state _ _ (fun st => ((st.1.1, st.2), st.1.2)) ?_ program
    ((mc, tape), dc)
  rintro (k | p) ⟨⟨m, t⟩, d⟩
  · cases h : m.lookup k <;>
      simp only [StateT.run, withSampleList, handler, sumHandler, memoize, h, bind_pure_comp,
        map_pure, interpret_pure, stepAt, RandomOracle.memoizeSum_inl, pmf_norm, Function.comp_def]
    all_goals
      change PMF.map _ (PMF.pure _) = _
      simp
  · simp only [StateT.run, withSampleList, handler, sumHandler, interpret_map, interpret_query,
      stepAt, RandomOracle.memoizeSum_inr, memoize_digest, Functor.map_map, pmf_norm,
      Function.comp_def]
    change PMF.map _ ((Protocols.ROMSignature.oracle (Digest s) p d).map
      (fun (a, state) => ((a, m, t.tail), state))) = _
    rw [PMF.map_comp]
    rfl

private theorem run_both {s : Level} {α : Type} {program : OracleComp (Both s) α} {Q : ℕ}
    (hQ : program.IsQueryBounded Q) (mc : Cache s) (dc : DigestCache s) :
    ((PMF.iid (PMF.uniformOfFintype (PublicMatrix s)) Q).map List.ofFn).bind (fun tape =>
      (interpret (Protocols.ROMSignature.oracle (Digest s))
        (Prod.fst <$> (interpret (withSampleList 0 (handler s)) program).run (mc, tape))).run dc) =
      ((interpret (RandomOracle.memoizeSum
        (fun _ : FixedBytes 32 => PMF.uniformOfFintype (PublicMatrix s))
        (fun _ : Point s => PMF.uniformOfFintype (Digest s))) program).run (mc, dc)).map
        fun (a, _, dc') => (a, dc') := by
  let fresh := PMF.uniformOfFintype (PublicMatrix s)
  have hp := hQ.run_interpret_presample fresh 0 (stepAt s) (mc, dc)
  have online (q : FixedBytes 32 ⊕ Point s) (state : Cache s × DigestCache s) :
      (fresh.bind fun v => stepAt s v q state) = RandomOracle.memoizeSum
        (fun _ : FixedBytes 32 => fresh) (fun _ : Point s => PMF.uniformOfFintype (Digest s))
        q state := by
    rcases state with ⟨m, d⟩
    rcases q with k | p
    · cases h : m.lookup k with
      | none => simp [stepAt, RandomOracle.memoizeSum_inl, memoize_of_none _ k m h, pmf_norm]
      | some v => simp [stepAt, RandomOracle.memoizeSum_inl, memoize_of_some _ k m v h, pmf_norm]
    · simp only [stepAt, RandomOracle.memoizeSum_inr, PMF.bind_const]
  simp only [online] at hp
  rw [← hp, PMF.map_bind]
  congr 1 with tape
  rw [run_interpret_map, ← tape_run]
  simp only [PMF.map_comp, PMF.monad_map_eq_map, Function.comp_def]
  rfl

private def trial {Coins : Type} (s : Level) (adv : Forger s Coins) (r : Saved s Coins)
    (A : PublicMatrix s) (t : Fin s.params.k → Poly) : ProbComp Bool :=
  runDigest s (do
    let f ← runForger s adv r ⟨A, t⟩
    verify s (encodePublic s r.seed.toList t) A f)

/-- The distinguisher on the full Module-LWE challenge. It publishes the rounded bytes, binds
the challenge matrix to the public seed, and runs the adversary and verifier with one digest
cache. -/
def distinguisher {Coins : Type} (s : Level) (Q : ℕ) (coins : ProbComp Coins)
    (adv : Forger s Coins) (A : PublicMatrix s) (t : Fin s.params.k → Poly) : ProbComp Bool := do
  let r ← sampleSaved s Q coins
  trial s adv r A t

private theorem fixed_le {Coins : Type} (s : Level) (adv : Forger s Coins) (r : Saved s Coins)
    (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    (trial s adv r A t).eval true ≤
        ModuleSIS.SelfTarget.game (expandDigest s) (compressedSelfTargetRadius s.params 13)
          (PMF.pure r) (solver s adv) (systematic s A t) true := by
  simp only [trial, eval_runDigest, run_interpret_bind, ModuleSIS.SelfTarget.game, solver,
    fullKey_systematic, interpret_map, StateT.run_map, pmf_norm, Function.comp_def]
  apply Probability.PMF.bind_apply_mono_on_support
  intro result _
  obtain ⟨f, cache⟩ := result
  by_cases hlen : (encodePublic s r.seed.toList t).length = 32 + 320 * s.params.k
  · cases ho : opening s f with
    | none => simp [verify, hlen, ho]
    | some o =>
      have hp := product_witness s r.seed A t f o
      have hz := short_witness (pk := ⟨A, t⟩) (bytes := encodePublic s r.seed.toList t) ho
      simp only [verify, hlen, ite_true, ho, candidateOutput, ModuleSIS.SelfTarget.product, hp,
        run_interpret_bind, run_interpret_query, run_interpret_pure, pmf_norm]
      apply Probability.PMF.bind_apply_mono_on_support
      intro result _
      obtain ⟨d, cache'⟩ := result
      by_cases he : d.toList = o.signature.digest
      · have hc := (opening_spec ho).1
        have hec : expandDigest s d = some o.challenge := by
          simpa only [expandDigest, he] using hc
        have hwin : ModuleSIS.SelfTarget.accepts (expandDigest s)
            (compressedSelfTargetRadius s.params 13)
            (liftWitness s (witness s ⟨A, t⟩ (encodePublic s r.seed.toList t) f o)) d := by
          apply decide_eq_true
          refine ⟨hz, ?_⟩
          simp [hec, liftWitness, witness, SelfTargetCandidate.ofCompressedForgery]
        simp [he, hwin]
      · simp [he]
  · simp [verify, hlen]

private noncomputable def matrixDigestOracle (s : Level) :=
  RandomOracle.memoizeSum (fun _ : FixedBytes 32 => PMF.uniformOfFintype (PublicMatrix s))
    (fun _ : Point s => PMF.uniformOfFintype (Digest s))

private noncomputable def onlineTrial {Coins : Type} (s : Level) (adv : Forger s Coins) (r : Coins)
    (rho : FixedBytes 32) (A : PublicMatrix s) (t : Fin s.params.k → Poly)
    (cache : Cache s × DigestCache s) : Game := do
  let bytes := encodePublic s rho.toList t
  let (f, _, dc) ← (interpret (matrixDigestOracle s) (adv bytes r)).run cache
  ((interpret (Protocols.ROMSignature.oracle (Digest s)) (verify s bytes A f)).run dc).map Prod.fst

private theorem trial_eq_online {Coins : Type} (s : Level) (Q : ℕ) (adv : Forger s Coins)
    (hQ : ∀ bytes r, (adv bytes r).IsQueryBounded Q) (r : Coins) (rho : FixedBytes 32)
    (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    (PMF.iid (PMF.uniformOfFintype (PublicMatrix s)) Q).bind (fun tape =>
      (trial s adv ⟨r, rho, List.ofFn tape⟩ A t).eval) =
      onlineTrial s adv r rho A t ([(rho, A)], []) := by
  let bytes := encodePublic s rho.toList t
  let finish (x : Forgery × DigestCache s) :=
    ((interpret (Protocols.ROMSignature.oracle (Digest s))
      (verify s bytes A x.1)).run x.2).map Prod.fst
  have h := congrArg (fun μ => PMF.bind μ finish)
    (run_both (hQ bytes r) [(rho, A)] [])
  simpa only [trial, eval_runDigest, runForger, onlineTrial, matrixDigestOracle, bytes, finish,
    run_interpret_bind, pmf_norm, Function.comp_def] using h

/-- Run the byte forger and final digest check with the matrix cache left by key generation
and an initially empty digest cache. Both share all digest entries throughout the trial. -/
noncomputable def observe {Coins : Type} (s : Level) (coins : ProbComp Coins)
    (adv : Forger s Coins) : MatrixOracle.Observable s := fun rho A t cache => do
  let r ← coins.eval
  onlineTrial s adv r rho A t (cache, [])

/-- Structured Module-SIS distribution used in Dilithium v3.1, §6.1: independently uniform
`A,t` in the systematic matrix `[I | A | -t]`. -/
noncomputable def instances (s : Level) : PMF
    (Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly) := do
  let A ← PMF.uniformOfFintype (PublicMatrix s)
  let t ← PMF.uniformOfFintype (Fin s.params.k → Poly)
  return systematic s A t

/-- The real Module-LWE challenge with the explicit distinguisher reproduces the entire
online key-only acceptance law, including adaptive seed lookups and continued verification
with the digest cache. The query bound justifies presampling the reduction's matrix tape. -/
theorem keyOnlyGame_eq_moduleLWE_realGame {Coins : Type} (s : Level) (Q : ℕ)
    (coins : ProbComp Coins) (adv : Forger s Coins)
    (hQ : ∀ bytes r, (adv bytes r).IsQueryBounded Q) :
    MatrixOracle.realKeyGame s (observe s coins adv) =
      ModuleLWE.realGame (MatrixOracle.shortVectorLaw s s.params.ℓ)
        (MatrixOracle.shortVectorLaw s s.params.k) (distinguisher s Q coins adv) := by
  apply MatrixOracle.realKeyGame_eq_realGame_of_planted
  intro A t
  simp only [MatrixOracle.planted, observe, distinguisher, sampleSaved, ProbComp.eval_bind,
    ProbComp.eval_pure, eval_sampleBytes, ProbComp.eval_replicateFin,
    MatrixOracle.eval_sampleMatrix,
    ← PMF.iid_eq_pi, pmf_norm, trial_eq_online s Q adv hQ]
  pmf_swap

private theorem random_le_selfTarget {Coins : Type} (s : Level) (Q : ℕ) (coins : ProbComp Coins)
    (adv : Forger s Coins) :
    ModuleLWE.randomGame (distinguisher s Q coins adv) true ≤
      ((instances s).bind (ModuleSIS.SelfTarget.game (expandDigest s)
        (compressedSelfTargetRadius s.params 13) (sampleSaved s Q coins).eval
        (solver s adv))) true := by
  simp only [ModuleLWE.randomGame, ModuleLWE.eval_randomExperiment, distinguisher,
    ProbComp.eval_bind, instances, ModuleSIS.SelfTarget.game, pmf_norm]
  apply Probability.PMF.bind_apply_mono_on_support
  intro A _
  apply Probability.PMF.bind_apply_mono_on_support
  intro t _
  apply Probability.PMF.bind_apply_mono_on_support
  intro r _
  simpa only [ModuleSIS.SelfTarget.game, pmf_norm] using fixed_le s adv r A t

/-- Shared-oracle key-only forgery is bounded by short-secret MLWE, a two-run systematic
Module-SIS experiment and the unbounded collision term for concrete Algorithm 29 on SHAKE256
digests. One final digest lookup accounts for a forgery on a fresh point. -/
theorem keyOnly_le_moduleLWE_add_fork {Coins : Type} (s : Level) (Q : ℕ) (coins : ProbComp Coins)
    (adv : Forger s Coins) (hQ : ∀ bytes r, (adv bytes r).IsQueryBounded Q) :
    let radius := compressedSelfTargetRadius s.params 13
    ((MatrixOracle.realKeyGame s (observe s coins adv)) true).toReal ≤
      ModuleLWE.advantage (MatrixOracle.shortVectorLaw s s.params.ℓ)
        (MatrixOracle.shortVectorLaw s s.params.k) (distinguisher s Q coins adv) +
      ((Q + 1 : ℕ) / ((256 : ℝ) ^ digestBytes s) + Real.sqrt ((Q + 1 : ℕ) *
        (((instances s).bind fun M => (ModuleSIS.SelfTarget.reduction (expandDigest s) radius Q
          (sampleSaved s Q coins).eval (solver s adv) M).map
            fun z => decide (ModuleSIS.IsSolution M (2 * radius) z)) true +
              ModuleSIS.SelfTarget.collisionMass (expandDigest s)).toReal)) := by
  have hs := selfTarget_digest_fork s Q (instances s) (sampleSaved s Q coins).eval
    (solver s adv) (solver_bounded hQ)
  have hr := (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (random_le_selfTarget s Q coins adv)).trans hs
  have hl := Game.coe_succProbability_le_add_of_advantage_le
    (g₀ := MatrixOracle.realKeyGame s (observe s coins adv))
    (g₁ := ModuleLWE.randomGame (distinguisher s Q coins adv)) (le_refl _)
  rw [Game.coe_succProbability, Game.coe_succProbability,
    keyOnlyGame_eq_moduleLWE_realGame s Q coins adv hQ] at hl
  rw [keyOnlyGame_eq_moduleLWE_realGame s Q coins adv hQ]
  exact hl.trans (by rw [add_comm]; exact add_le_add le_rfl hr)

end Cslib.Crypto.MLDSA.FIPS204.SharedDigest
