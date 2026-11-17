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

/-!
# The Module-LWE key switch for ML-DSA with a public matrix oracle

For each FIPS parameter set, the public matrix seed selects a value of a classical random
function from 32-byte strings to matrices. The key generator and the byte-key forger share
this oracle. By `verifyWithExpansion_encodePublic` the verifier can reuse this oracle answer.
The short secret and error are independent, uniform coefficientwise on
`[-η,η]`. This is the short-secret MLWE law in §§6.1–6.2.1 of the Dilithium v3.1
specification [BaiEtAl2021Dilithium]. Public-key rounding, encoding and the digest check
use FIPS 204, Algorithms 3, 6 and 8 [NISTFIPS204].

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

/-- The honest matrix query starts from the empty cache. The forger sees the seed and rounded
bytes and continues with the cache populated by that key-generation query. -/
private noncomputable def withVector (s : Level) (adv : Forger s)
    (vector : PublicMatrix s → Fin s.params.k → Poly) : Game := do
  let rho ← PMF.uniformOfFintype (FixedBytes 32)
  let client : ProbOracleComp (fun _ : FixedBytes 32 => PublicMatrix s) Bool := do
    let A ← ProbOracleComp.query rho
    trial s adv rho A (vector A)
  (ProbOracleComp.runWith (memoize fun _ => PMF.uniformOfFintype (PublicMatrix s))
    client []).map Prod.fst

/-- Key-only forgery under the matrix oracle. The two short vectors are sampled
independently; the public bytes encode the high part of `A s₁ + s₂`. -/
noncomputable def keyOnlyGame (s : Level) (adv : Forger s) : Game := do
  let s₁ ← shortVectorLaw s s.params.ℓ
  let s₂ ← shortVectorLaw s s.params.k
  withVector s adv fun A => moduleSISMap A s₁ + s₂

/-- The uniform-vector hybrid publishes the high part of an independent uniform ring vector.
Rounding is performed after sampling the full vector. -/
noncomputable def uniformVectorGame (s : Level) (adv : Forger s) : Game := do
  let t ← PMF.uniformOfFintype (Fin s.params.k → Poly)
  withVector s adv fun _ => t

/-- The Module-LWE distinguisher on a challenge `(A,t)`. It samples a fresh public seed,
initializes its cache with `(ρ,A)`, and generates each new queried matrix coefficientwise. -/
def distinguisher (s : Level) (adv : Forger s) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) : ProbComp Bool := do
  let rho ← sampleSeed
  Prod.fst <$> (OracleComp.interpret
    (sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (memoize fun _ => sampleMatrix s))
    (trial s adv rho A t)).run [(rho, A)]

private theorem withVector_eq (s : Level) (adv : Forger s)
    (vector : PublicMatrix s → Fin s.params.k → Poly) :
    withVector s adv vector = (PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
      (distinguisher s adv A (vector A)).eval := by
  simp only [withVector, PMF.monad_bind_eq_bind, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, memoize_of_none _ _ [] rfl, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.bind_bind, PMF.pure_bind, distinguisher, ProbComp.eval_bind,
    sampleSeed, ProbComp.eval_replicateFin, ProbComp.eval_unifFin, PMF.pi_uniformOfFintype,
    ProbComp.eval_map, ProbOracleComp.eval_run_interpret_eq_runWith, ProbComp.eval_memoize,
    eval_sampleMatrix]
  exact PMF.bind_comm _ _ _

/-- Exact finite advantage of the seeded public-key switch. Both experiments give the forger
the same matrix oracle used by key generation and check its full digest against the rounded
public-key bytes. The distinguisher runs the forger once. -/
theorem advantage_eq_moduleLWE (s : Level) (adv : Forger s) :
    Game.advantage (keyOnlyGame s adv) (uniformVectorGame s adv) =
      ModuleLWE.advantage (shortVectorLaw s s.params.ℓ) (shortVectorLaw s s.params.k)
        (distinguisher s adv) := by
  unfold ModuleLWE.advantage
  apply congrArg₂ Game.advantage
  · simp only [keyOnlyGame, withVector_eq, ModuleLWE.realGame, ModuleLWE.eval_realExperiment,
      PMF.monad_bind_eq_bind]
    rfl
  · simp only [uniformVectorGame, withVector_eq, ModuleLWE.randomGame,
      ModuleLWE.eval_randomExperiment, PMF.monad_bind_eq_bind]
    exact PMF.bind_comm _ _ _

end Cslib.Crypto.MLDSA.FIPS204.MatrixOracle
