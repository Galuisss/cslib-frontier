/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Crypto.Game.Order

/-!
# The Module-LWE key switch for ML-DSA with a public matrix oracle

For each FIPS parameter set, the public matrix seed selects a value of a classical random
function from 32-byte strings to matrices. The key generator and the byte-key forger share
this oracle. By `verifyWithExpansion_encodePublic` the verifier can reuse this oracle answer.
The short secret and error are independent, uniform coefficientwise on
`[-η,η]`. This is the short-secret MLWE law in §§6.1–6.2.1 of the Dilithium v3.1
specification [BaiEtAl2021Dilithium]. Public-key rounding, encoding and the digest check
use FIPS 204, Algorithms 3, 6 and 8 [NISTFIPS204].

The self-target solver receives the full independent uniform matrix and vector, publishes their
rounded byte key, and corrects its witness by the product of the challenge and the discarded
low vector. Its success and the MLWE advantage bound key-only forgery in this experiment.

The reduction starts its lazy oracle cache with the challenge matrix at the public seed.
The advantage for replacing the unrounded public vector by uniform is exactly the standard
Module-LWE advantage of this program, including adaptive queries at the published seed.
This finite game idealizes matrix expansion and the key-generation seed expansion. The
concrete SHAKE key generation and its possible rejection exhaustion are in `FIPS204.keyOnlyGame`.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.MatrixOracle

open Cslib.Probability
open OracleComp

/-- A byte-key forger with private coins and classical adaptive queries to the 32-byte matrix
expansion oracle. -/
abbrev Forger (s : Level) :=
  List Byte → ProbOracleComp (fun _ : FixedBytes 32 => PublicMatrix s) Forgery

/-- The Dilithium short-vector law: every coefficient independently uniform in
`{-η,…,η}`, represented in the negacyclic ring modulo 8380417. -/
noncomputable def shortVectorLaw (s : Level) (rows : ℕ) : PMF (Fin rows → Poly) :=
  PMF.pi fun _ => PMF.pi fun _ =>
    (PMF.uniformOfFintype (Fin (2 * s.params.η + 1))).map fun i =>
      (i.val : ZMod 8380417) - s.params.η

private def sampleSeed : ProbComp (FixedBytes 32) :=
  replicateFin 32 (ProbComp.unifFin 255)

private def sampleMatrix (s : Level) : ProbComp (PublicMatrix s) :=
  replicateFin s.params.k (replicateFin s.params.ℓ (replicateFin 256 (ProbComp.unifFin 8380416)))

private theorem eval_sampleMatrix (s : Level) :
    (sampleMatrix s).eval = PMF.uniformOfFintype (PublicMatrix s) := by
  change ProbComp.eval (replicateFin s.params.k (replicateFin s.params.ℓ
    (replicateFin 256 (ProbComp.unifFin 8380416)))) =
    PMF.uniformOfFintype (Fin s.params.k → Fin s.params.ℓ → Fin 256 → Fin (8380416 + 1))
  simp only [ProbComp.eval_replicateFin, ProbComp.eval_unifFin, PMF.pi_uniformOfFintype]

private def trial (s : Level) (adv : Forger s) (rho : FixedBytes 32)
    (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    ProbOracleComp (fun _ : FixedBytes 32 => PublicMatrix s) Bool := do
  let bytes := encodePublic s rho.toList t
  let f ← adv bytes
  return (verifyWithExpansion s (fun _ => some A) bytes f.message f.context f.signature).getD false

/-- The post-key computation sees the published seed, the matrix, the full vector for
rounding and the matrix-oracle cache left by key generation. The concrete SHAKE and the
shared digest-oracle experiments supply different verification computations here. -/
abbrev Observable (s : Level) := FixedBytes 32 → PublicMatrix s → (Fin s.params.k → Poly) →
  List (FixedBytes 32 × PublicMatrix s) → Game

/-- Use a matrix query to generate the key and continue with the resulting oracle cache. -/
private noncomputable def withVector (s : Level) (observe : Observable s)
    (vector : PublicMatrix s → Fin s.params.k → Poly) : Game := do
  let rho ← PMF.uniformOfFintype (FixedBytes 32)
  let (A, cache) ← memoize (fun _ => PMF.uniformOfFintype (PublicMatrix s)) rho []
  observe rho A (vector A) cache

/-- The key generator samples its short secret and error, obtains its matrix through the
public seed oracle and passes the populated cache to the supplied post-key computation. -/
noncomputable def realKeyGame (s : Level) (observe : Observable s) : Game := do
  let s₁ ← shortVectorLaw s s.params.ℓ
  let s₂ ← shortVectorLaw s s.params.k
  withVector s observe fun A => moduleSISMap A s₁ + s₂

/-- The uniform-vector hybrid performs exactly the same matrix query as key generation. -/
noncomputable def uniformKeyGame (s : Level) (observe : Observable s) : Game := do
  let t ← PMF.uniformOfFintype (Fin s.params.k → Poly)
  withVector s observe fun _ => t

/-- Given the full challenger instance, sample a fresh seed and plant its matrix as the first
cache entry. All later oracle and verification operations belong to the same observable. -/
@[expose] noncomputable def planted (s : Level) (observe : Observable s) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) : Game := do
  let rho ← PMF.uniformOfFintype (FixedBytes 32)
  observe rho A t [(rho, A)]

private theorem withVector_eq (s : Level) (observe : Observable s)
    (vector : PublicMatrix s → Fin s.params.k → Poly) :
    withVector s observe vector = (PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
      planted s observe A (vector A) := by
  simp only [withVector, planted, memoize_of_none _ _ [] rfl, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  exact PMF.bind_comm _ _ _

/-- The post-key computation runs in the real Module-LWE experiment whenever the supplied
program realizes its behavior at a planted seed. The seed and short-vector sampling laws
and the initial matrix lookup are discharged here for every such program. -/
theorem realKeyGame_eq_realGame_of_planted (s : Level) (observe : Observable s)
    (D : PublicMatrix s → (Fin s.params.k → Poly) → ProbComp Bool)
    (h : ∀ A t, planted s observe A t = (D A t).eval) :
    realKeyGame s observe = ModuleLWE.realGame (shortVectorLaw s s.params.ℓ)
      (shortVectorLaw s s.params.k) D := by
  simp only [realKeyGame, withVector_eq, h, ModuleLWE.realGame, ModuleLWE.eval_realExperiment,
    PMF.monad_bind_eq_bind]
  rfl

/-- Run the byte-key forger with its matrix cache and verify its signature using concrete SHAKE. -/
noncomputable def concreteSHAKE (s : Level) (adv : Forger s) : Observable s := fun rho A t cache =>
  (ProbOracleComp.runWith (memoize fun _ => PMF.uniformOfFintype (PublicMatrix s))
    (trial s adv rho A t) cache).map Prod.fst

private def runAtSeed {α : Type} (s : Level) (rho : FixedBytes 32) (A : PublicMatrix s)
    (client : ProbOracleComp (fun _ : FixedBytes 32 => PublicMatrix s) α) : ProbComp α :=
  Prod.fst <$> (OracleComp.interpret
    (sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (memoize fun _ => sampleMatrix s))
    client).run [(rho, A)]

/-- The Module-LWE distinguisher on a challenge `(A,t)`. It samples a fresh public seed,
initializes its cache with `(ρ,A)`, and generates each new queried matrix coefficientwise. -/
def distinguisher (s : Level) (adv : Forger s) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) : ProbComp Bool := do
  let rho ← sampleSeed
  runAtSeed s rho A (trial s adv rho A t)

private theorem planted_concreteSHAKE (s : Level) (adv : Forger s)
    (A : PublicMatrix s) (t : Fin s.params.k → Poly) :
    planted s (concreteSHAKE s adv) A t = (distinguisher s adv A t).eval := by
  simp only [planted, concreteSHAKE, PMF.monad_bind_eq_bind, distinguisher, runAtSeed,
    ProbComp.eval_bind,
    sampleSeed, ProbComp.eval_replicateFin, ProbComp.eval_unifFin, PMF.pi_uniformOfFintype,
    ProbComp.eval_map, ProbOracleComp.eval_run_interpret_eq_runWith, ProbComp.eval_memoize,
    eval_sampleMatrix]

/-- Exact finite advantage of the seeded public-key switch. Both experiments give the forger
the same matrix oracle used by key generation and check its full digest against the rounded
public-key bytes. The distinguisher runs the forger once. -/
theorem advantage_eq_moduleLWE (s : Level) (adv : Forger s) :
    Game.advantage (realKeyGame s (concreteSHAKE s adv))
      (uniformKeyGame s (concreteSHAKE s adv)) =
      ModuleLWE.advantage (shortVectorLaw s s.params.ℓ) (shortVectorLaw s s.params.k)
        (distinguisher s adv) := by
  unfold ModuleLWE.advantage
  apply congrArg₂ Game.advantage
  · exact realKeyGame_eq_realGame_of_planted s _ _ (planted_concreteSHAKE s adv)
  · simp only [uniformKeyGame, withVector_eq, planted_concreteSHAKE, ModuleLWE.randomGame,
      ModuleLWE.eval_randomExperiment, PMF.monad_bind_eq_bind]
    exact PMF.bind_comm _ _ _


/-- On a full challenge `(A,t)`, publish the seed and rounded vector, run the byte forger
using a shared matrix oracle initialized at `(ρ,A)`, and return the corrected self-target
candidate. A parsing failure produces the all-zero candidate. -/
def selfTargetSolver (s : Level) (adv : Forger s) (pk : MLDSA.PublicKey s.params) :
    ProbComp (SelfTargetCandidate s.params) := do
  let rho ← sampleSeed
  let f ← runAtSeed s rho pk.A (adv (encodePublic s rho.toList pk.t))
  return (extractFull s rho pk.A pk.t f).getD ⟨[], 0, 0, 0⟩

private theorem fixed_le (s : Level) (adv : Forger s) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) :
    (distinguisher s adv A t).eval true ≤
      (selfTargetExperiment s.params (selfTargetHash s.params (algebraicHash s))
        (compressedSelfTargetRadius s.params 13) ⟨A, t⟩ (selfTargetSolver s adv)).eval true := by
  simp only [distinguisher, selfTargetExperiment, selfTargetSolver, runAtSeed, trial,
    ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_map, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_pure, PMF.map_bind, PMF.pure_map,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_map, Function.comp_apply]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun rho _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun ⟨f, _⟩ _ => ?_
  cases hv : verifyWithExpansion s (fun _ => some A) (encodePublic s rho.toList t)
    f.message f.context f.signature with
  | none => simp
  | some b =>
    cases b with
    | false => simp
    | true =>
      obtain ⟨y, hy, hw⟩ := extractFull_of_verifyWithExpansion (rho := rho) rfl hv
      simp [hy, hw]

/-- A byte forgery under a uniform unrounded vector yields a candidate in the original
self-target experiment with independent uniform `A,t`. The target hashes the same message
representative and commitment with concrete SHAKE. -/
theorem uniformVectorGame_le_selfTarget (s : Level) (adv : Forger s) :
    (uniformKeyGame s (concreteSHAKE s adv)).succProbability ≤
      (selfTargetGame s.params (uniformKeyLaw s.params) (selfTargetHash s.params (algebraicHash s))
        (compressedSelfTargetRadius s.params 13) (selfTargetSolver s adv)).succProbability := by
  apply Game.succProbability_mono
  simp only [uniformKeyGame, withVector_eq, planted_concreteSHAKE, selfTargetGame, uniformKeyLaw,
    PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin s.params.k → Poly))]
  exact Probability.PMF.bind_apply_mono_on_support _ _ fun A _ =>
    Probability.PMF.bind_apply_mono_on_support _ _ fun t _ => fixed_le s adv A t

/-- Finite key-only bound in the public-matrix-oracle game: the cost of replacing the genuine
short-law Module-LWE vector plus the success of the constructed solver against the actual
full uniform challenge. Both terms use the same byte-key forger. -/
theorem keyOnlyGame_le_moduleLWE_add_selfTarget (s : Level) (adv : Forger s) :
    (realKeyGame s (concreteSHAKE s adv)).succProbability ≤
      ModuleLWE.advantage (shortVectorLaw s s.params.ℓ) (shortVectorLaw s s.params.k)
        (distinguisher s adv) +
      (selfTargetGame s.params (uniformKeyLaw s.params) (selfTargetHash s.params (algebraicHash s))
        (compressedSelfTargetRadius s.params 13) (selfTargetSolver s adv)).succProbability := by
  rw [add_comm]
  exact (Game.succProbability_le_add_of_advantage_le (advantage_eq_moduleLWE s adv).le).trans
    (add_le_add_left (uniformVectorGame_le_selfTarget s adv) _)

end Cslib.Crypto.MLDSA.FIPS204.MatrixOracle
