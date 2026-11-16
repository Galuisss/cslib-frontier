/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Experiment

/-!
# Trapdoor function schemes

A trapdoor function scheme `(G, F, I)` ([BonehShoup2023], Section 10.2, Definition 10.2) has a key
generator `G`, a function `F(pk, ·)` for each public key, and an algorithm `I` that inverts it with
the secret key. `TrapdoorFunction.owExperiment` is its one-way attack game (Attack Game 10.2), and
`TrapdoorFunction.OneWay` says that a family of schemes is one way against a class of adversaries
(Definition 10.3). This file has these definitions and the two remarks that follow
Definition 10.2. It proves no security result. The RSA scheme is in
`CslibFrontier/Crypto/Computational/TrapdoorFunction/RSA.lean`.

## Main definitions

* `Cslib.Crypto.TrapdoorFunction`: a trapdoor function scheme with typed keys, whose domain and
  range may depend on the public key.
* `Cslib.Crypto.TrapdoorFunction.Correct`: inversion with the secret key recovers every point of
  the domain. `Correct.injective` and `Correct.bijective` are its two consequences on p. 401.
* `Cslib.Crypto.TrapdoorFunction.owExperiment`: the one-way attack game against a
  `TrapdoorFunction.Inverter`.
* `Cslib.Crypto.TrapdoorFunction.OneWay`: one-wayness of a family of schemes against the
  adversaries of a class that the caller supplies.

## Differences from [BonehShoup2023]

* The domain `X pk` and the range `Y pk` depend on the public key, where Definition 10.2 fixes two
  sets. The RSA scheme needs this, since its functions act on the residues modulo the key's
  modulus. The book names this generalization and does not adopt it (pp. 404–405). For constant
  families the structure, `Correct` and `owExperiment` are the printed definition, property and
  game.
* `keyGen` draws a secret key and `publicKey` reads the public key from it, where the book's `G`
  outputs a pair. A generator of pairs is the case in which the secret key is the pair and
  `publicKey` is its first component.
* The field `domain_nonempty` is added. The attack game draws a uniform point of the domain, and
  Definition 10.2 asks only that the sets are finite. The field speaks of the public keys that
  some secret key names, not of every public key.
* `owExperiment` needs `Fintype` and `DecidableEq` on the domain of every public key, including
  keys that `keyGen` never outputs. Nothing is asked of the range.
* Efficiency is not part of the notion. Definition 10.4 also requires that `G`, `F` and `I` are
  efficient and that the families of sets are efficiently recognizable and, for the domain,
  sampleable (its items 1–5). `OneWay` restricts only the adversary, through the class.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 10.2 (Definitions 10.2–10.4 and Attack Game 10.2, pp. 400–403) and the remarks on RSA
  in Section 10.3 (pp. 404–405).
-/

public section

namespace Cslib.Crypto

open Probability

/-- A trapdoor function scheme `(G, F, I)` ([BonehShoup2023], Definition 10.2, pp. 400–401) with
public keys `PK`, secret keys `SK`, and a domain `X pk` and range `Y pk` that may depend on the
public key. The book fixes the two sets; it names the key-dependent form for RSA and does not
adopt it (pp. 404–405). -/
structure TrapdoorFunction (PK SK : Type) (X Y : PK → Type) where
  /-- `G`: draw the secret key. -/
  keyGen : ProbComp SK
  /-- The public key that `G` outputs together with a secret key. -/
  publicKey : SK → PK
  /-- `F`: evaluate the function of a public key. -/
  eval : (pk : PK) → X pk → Y pk
  /-- `I`: invert the function with the secret key. -/
  invert : (sk : SK) → Y (publicKey sk) → X (publicKey sk)
  /-- The domain of every public key that a secret key names is nonempty. -/
  domain_nonempty : ∀ sk, Nonempty (X (publicKey sk))

namespace TrapdoorFunction

variable {PK SK : Type} {X Y : PK → Type}

/-- The correctness property of Definition 10.2: `I(sk, F(pk, x)) = x` for every key pair that `G`
can output and every `x` in the domain. -/
@[expose] def Correct (T : TrapdoorFunction PK SK X Y) : Prop :=
  ∀ sk ∈ (ProbComp.eval T.keyGen).support, ∀ x, T.invert sk (T.eval (T.publicKey sk) x) = x

/-- The correctness property makes `F(pk, ·)` one-to-one ([BonehShoup2023], p. 401). -/
theorem Correct.injective {T : TrapdoorFunction PK SK X Y} (h : T.Correct) {sk : SK}
    (hsk : sk ∈ (ProbComp.eval T.keyGen).support) : Function.Injective (T.eval (T.publicKey sk)) :=
  Function.LeftInverse.injective (h sk hsk)

/-- In a correct trapdoor permutation scheme, where the range is the domain and the domain is
finite, `F(pk, ·)` is a permutation of the domain ([BonehShoup2023], p. 401). -/
theorem Correct.bijective {X : PK → Type} {T : TrapdoorFunction PK SK X X} (h : T.Correct)
    {sk : SK} [Finite (X (T.publicKey sk))] (hsk : sk ∈ (ProbComp.eval T.keyGen).support) :
    Function.Bijective (T.eval (T.publicKey sk)) :=
  Finite.injective_iff_bijective.mp (h.injective hsk)

/-- An adversary of Attack Game 10.2: given a public key and a point of its range, it outputs a
point of its domain. -/
abbrev Inverter (PK : Type) (X Y : PK → Type) : Type :=
  (pk : PK) → Y pk → ProbComp (X pk)

/-- Attack Game 10.2 ([BonehShoup2023], p. 401): draw the keys, draw `x` uniformly from the domain
of the public key, and give the adversary the public key and `F(pk, x)`; the adversary wins when
it outputs `x`. The advantage `OWadv[A, T]` is `(T.owExperiment A).succProbability`. The domain of
every public key must be a `Fintype` with decidable equality, also at keys that `G` never
outputs. -/
@[expose] noncomputable def owExperiment [∀ pk, Fintype (X pk)] [∀ pk, DecidableEq (X pk)]
    (T : TrapdoorFunction PK SK X Y) (A : Inverter PK X Y) : Experiment := do
  let sk ← T.keyGen
  have := T.domain_nonempty sk
  let x ← ProbComp.uniform (X (T.publicKey sk))
  let x' ← A (T.publicKey sk) (T.eval (T.publicKey sk) x)
  return decide (x' = x)

/-- A family of trapdoor function schemes, indexed by the security parameter, is one way against
the adversaries in `Admissible`: each of them wins Attack Game 10.2 with negligible probability
([BonehShoup2023], Definition 10.3, p. 401, read with the security parameter as on p. 403).

Definition 10.3 is the instance at a class of efficient adversaries. Nothing here checks
efficiency: the class is the caller's, and against the empty class every family is one way. Each
instance supplies its own class of probabilistic polynomial-time adversaries, as
`RSAInverter.IsPPT` does for RSA, and a theorem that assumes `OneWay` names the class it uses.

Two further differences from the book: the domain and range may depend on the public key, and the
efficiency of `G`, `F` and `I` (Definition 10.4, items 1–5) is not part of the notion. -/
@[expose] def OneWay {PK SK : ℕ → Type} {X Y : (n : ℕ) → PK n → Type}
    [∀ n pk, Fintype (X n pk)] [∀ n pk, DecidableEq (X n pk)]
    (T : (n : ℕ) → TrapdoorFunction (PK n) (SK n) (X n) (Y n))
    (Admissible : ((n : ℕ) → Inverter (PK n) (X n) (Y n)) → Prop) : Prop :=
  ∀ A, Admissible A → Negligible fun n => ((T n).owExperiment (A n)).succProbability

end TrapdoorFunction

end Cslib.Crypto
