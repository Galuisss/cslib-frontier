/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RSATrapdoor
public import CslibFrontier.Crypto.Computational.TrapdoorFunction

/-!
# The RSA trapdoor permutation scheme

`rsaTrapdoor gen` is the scheme `T_RSA` of [BonehShoup2023], Section 10.3 (p. 403), as a
`TrapdoorFunction`, for a program `gen` that generates RSA parameters. The three statements of
this file connect it to what `RSATrapdoor.lean` has: the scheme is correct
(`rsaTrapdoor_correct`), its one-way attack game is the RSA inversion game
(`eval_owExperiment_rsaTrapdoor`), and so it is one way against probabilistic polynomial-time
inverters exactly when the RSA assumption holds for the law of `gen` (`oneWay_rsaTrapdoor_iff`).
No security result is proved here.

## Main definitions

* `Cslib.Crypto.rsaTrapdoor`: the RSA scheme, whose domain and range at the public key `(N, e)`
  are the residues `Fin N`.

## Differences from [BonehShoup2023]

* The generator is a parameter: any program that outputs an `RSADesc`. The book's `G` runs
  `RSAGen(ℓ, e)`, which draws two `ℓ`-bit primes for a fixed odd `e > 2`. An `RSADesc` has no
  length parameter, allows `p = 2` and `e = 1`, and its exponent may change with the key. No
  efficient generator is constructed here.
* The secret key is the whole `RSADesc`, with `p`, `q`, `e` and `d`, where the book's is `(n, d)`.
  Inversion reads only the modulus and `d`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 10.3 (the scheme `T_RSA`, p. 403; Attack Game 10.3 and Definition 10.5, pp. 404–405).
-/

public section

namespace Cslib.Crypto

open Probability

/-- The RSA trapdoor permutation scheme `T_RSA` ([BonehShoup2023], Section 10.3, p. 403) for a
generator `gen` of RSA parameters: the public key is `(N, e)`, `F(pk, x) = x ^ e` and
`I(sk, y) = y ^ d` on residues modulo `N`. The secret key is the whole `RSADesc`. -/
@[expose] def rsaTrapdoor (gen : ProbComp RSADesc) :
    TrapdoorFunction RSAPublicKey RSADesc (fun pk => Fin pk.N) (fun pk => Fin pk.N) where
  keyGen := gen
  publicKey := RSADesc.publicKey
  eval := RSAPublicKey.eval
  invert desc y := ⟨rsaInvert desc.modulus desc.d y, Nat.mod_lt _ desc.modulus_pos⟩
  domain_nonempty desc := ⟨⟨0, desc.modulus_pos⟩⟩

/-- `T_RSA` satisfies the correctness property of a trapdoor function scheme. -/
theorem rsaTrapdoor_correct (gen : ProbComp RSADesc) : (rsaTrapdoor gen).Correct :=
  fun desc _ x => Fin.ext (rsaInvert_rsaEval desc x.isLt)

/-- Attack Game 10.2 for `T_RSA` is the RSA inversion game for the law of the generator. -/
theorem eval_owExperiment_rsaTrapdoor (gen : ℕ → ProbComp RSADesc) (A : RSAInverter) (n : ℕ) :
    ProbComp.eval ((rsaTrapdoor (gen n)).owExperiment (A n)) =
      rsaInversionGame (fun n => ProbComp.eval (gen n)) A n := by
  rw [rsaInversionGame_eq]
  simp only [TrapdoorFunction.owExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure]
  rfl

/-- `T_RSA` is one way against probabilistic polynomial-time inverters exactly when the RSA
assumption `RSAOneWay` holds for the law of its generator. -/
theorem oneWay_rsaTrapdoor_iff (gen : ℕ → ProbComp RSADesc) :
    TrapdoorFunction.OneWay (fun n => rsaTrapdoor (gen n)) RSAInverter.IsPPT ↔
      RSAOneWay fun n => ProbComp.eval (gen n) := by
  simp only [TrapdoorFunction.OneWay, RSAOneWay, Experiment.succProbability,
    eval_owExperiment_rsaTrapdoor]

end Cslib.Crypto
