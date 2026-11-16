/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.TrapdoorFunction.RSA
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import Mathlib.Tactic.NormNum.Prime

/-!
# Trapdoor function schemes: checked instances

Checks for `CslibFrontier/Crypto/Computational/TrapdoorFunction.lean` and
`CslibFrontier/Crypto/Computational/TrapdoorFunction/RSA.lean`:

* The printed form. For a generator of pairs and sets that do not depend on the key
  (`ofKeyPairs`), the adversary's type, `Correct` and `owExperiment` are the type, property and
  game of [BonehShoup2023], Definition 10.2 and Attack Game 10.2.
* The remarks of p. 401. In a correct permutation scheme the secret key also inverts on the other
  side and the challenge is uniform; for a correct scheme the game has the law of the library's
  `inversionExperiment`, which accepts any preimage.
* The hypotheses. `Correct.bijective` needs the finite domain (`succScheme` on `ℕ` is correct and
  not onto), and the RSA domain is empty at the key `(0, e)`, so nonemptiness cannot be asked at
  every public key.
* `OneWay` can fail and can hold. The identity scheme is not one way against any class that
  contains the adversary returning its challenge (`not_oneWay_idScheme`); a family that hides `x`
  is one way against every adversary (`oneWay_hidingScheme`); against the empty class every family
  is one way.
* The RSA scheme. It is a correct permutation scheme, its `F` and `I` are `rsaEval` and
  `rsaInvert` on values, `computableInPolyTime_rsaEval` applies to its `F` on the inverter's
  input, the RSA assumption gives negligible success of PPT inverters, and `F(2) = 8`,
  `I(8) = 2` at `N = 33`, `e = 3`, `d = 7`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.TrapdoorFunction

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### The book's form of the definitions -/

/-- Definition 10.2 as printed: `G` outputs a pair `(pk, sk)` and the sets `X`, `Y` do not depend
on the key. It is the case where the secret key of the structure is the pair and the public key is
its first component. -/
def ofKeyPairs {PK SK X Y : Type} [Nonempty X] (G : ProbComp (PK × SK)) (F : PK → X → Y)
    (I : SK → Y → X) : TrapdoorFunction PK (PK × SK) (fun _ => X) (fun _ => Y) where
  keyGen := G
  publicKey := Prod.fst
  eval := F
  invert keys := I keys.2
  domain_nonempty _ := inferInstance

/-- The adversary's type is then the printed one: from `pk` and `y` to a point of `X`. -/
example {PK X Y : Type} :
    TrapdoorFunction.Inverter PK (fun _ => X) (fun _ => Y) = (PK → Y → ProbComp X) :=
  rfl

/-- `Correct` is the book's property: `I(sk, F(pk, x)) = x` for all possible outputs `(pk, sk)`
of `G` and all `x`. -/
example {PK SK X Y : Type} [Nonempty X] (G : ProbComp (PK × SK)) (F : PK → X → Y)
    (I : SK → Y → X) :
    (ofKeyPairs G F I).Correct ↔
      ∀ pk sk, (pk, sk) ∈ (ProbComp.eval G).support → ∀ x, I sk (F pk x) = x :=
  Prod.forall

/-- `owExperiment` is Attack Game 10.2 as printed. -/
example {PK SK X Y : Type} [Nonempty X] [Fintype X] [DecidableEq X] (G : ProbComp (PK × SK))
    (F : PK → X → Y) (I : SK → Y → X) (A : PK → Y → ProbComp X) :
    (ofKeyPairs G F I).owExperiment A = (do
      let keys ← G
      let x ← ProbComp.uniform X
      let x' ← A keys.1 (F keys.1 x)
      return decide (x' = x)) :=
  rfl

/-- When the domain does not depend on the key it is nonempty, because `G` outputs some key. A
construction that samples from the domain under an arbitrary public key can use this. -/
example {PK SK X Y : Type} (T : TrapdoorFunction PK SK (fun _ => X) (fun _ => Y)) : Nonempty X :=
  let ⟨sk, _⟩ := (ProbComp.eval T.keyGen).support_nonempty
  T.domain_nonempty sk

/-! ### The remarks after Definitions 10.2 and 10.3 -/

/-- In a correct permutation scheme the secret key also inverts `F(pk, ·)` on the other side:
`F(pk, I(sk, y)) = y`. -/
example {PK SK : Type} {X : PK → Type} {T : TrapdoorFunction PK SK X X} (h : T.Correct)
    {sk : SK} [Finite (X (T.publicKey sk))] (hsk : sk ∈ (ProbComp.eval T.keyGen).support)
    (y : X (T.publicKey sk)) : T.eval (T.publicKey sk) (T.invert sk y) = y :=
  Function.LeftInverse.rightInverse_of_surjective (h sk hsk) (h.bijective hsk).surjective y

/-- The note after Definition 10.3: in a correct permutation scheme the challenge `F(pk, x)` is
uniform on the domain, so a game that draws `x` and uses only `F(pk, x)` may draw `y` instead. -/
example {PK SK : Type} {X : PK → Type} [∀ pk, Fintype (X pk)] [∀ pk, Nonempty (X pk)]
    {T : TrapdoorFunction PK SK X X} (h : T.Correct) {sk : SK}
    (hsk : sk ∈ (ProbComp.eval T.keyGen).support) {β : Type} (g : X (T.publicKey sk) → PMF β) :
    ((PMF.uniformOfFintype (X (T.publicKey sk))).bind fun x => g (T.eval (T.publicKey sk) x)) =
      (PMF.uniformOfFintype (X (T.publicKey sk))).bind g :=
  PMF.uniformOfFintype_bind_bijective (h.bijective hsk) fun _ => rfl

/-- For a correct scheme, Attack Game 10.2 has the law of the library's inversion experiment,
which accepts any preimage, run on the keys of `G`. -/
example {PK SK : Type} {X Y : PK → Type} [∀ pk, Fintype (X pk)] [∀ pk, DecidableEq (X pk)]
    [∀ pk, DecidableEq (Y pk)] {T : TrapdoorFunction PK SK X Y} (h : T.Correct)
    (A : TrapdoorFunction.Inverter PK X Y) :
    ProbComp.eval (T.owExperiment A) = ProbComp.eval (do
      let sk ← T.keyGen
      have := T.domain_nonempty sk
      inversionExperiment (ProbComp.uniform (X (T.publicKey sk))) (T.eval (T.publicKey sk))
        (A (T.publicKey sk))) := by
  simp only [TrapdoorFunction.owExperiment, ProbComp.eval_bind]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  rw [inversionExperiment_eq_of_injective _ (h.injective hsk)]
  simp only [ProbComp.eval_bind]
  rfl

/-! ### The hypotheses are needed -/

/-- The successor scheme on `ℕ`: `F = (· + 1)`, `I = (· - 1)`. -/
def succScheme : TrapdoorFunction Unit Unit (fun _ => ℕ) (fun _ => ℕ) where
  keyGen := pure ()
  publicKey := id
  eval _ x := x + 1
  invert _ y := y - 1
  domain_nonempty _ := ⟨0⟩

/-- `Correct.bijective` needs the finite domain: the successor scheme is correct. -/
example : succScheme.Correct := fun _ _ x => Nat.add_sub_cancel x 1

/-- … and its function is not onto. -/
example : ¬ Function.Bijective (succScheme.eval (succScheme.publicKey ())) :=
  fun h => by
    obtain ⟨x, hx⟩ := h.surjective 0
    exact Nat.succ_ne_zero x hx

/-- Why the nonempty domain is a field indexed by the secret key and not an instance for every
public key: the RSA domain of the key `(0, e)`, which no generator outputs, is empty. -/
example : ¬ ∀ pk : RSAPublicKey, Nonempty (Fin pk.N) :=
  fun h => (h ⟨0, 3⟩).elim Fin.elim0

/-! ### A scheme that is not one way, and a family that is -/

/-- The identity scheme on bits. -/
def idScheme : TrapdoorFunction Unit Unit (fun _ => Bool) (fun _ => Bool) where
  keyGen := pure ()
  publicKey := id
  eval _ x := x
  invert _ y := y
  domain_nonempty _ := ⟨false⟩

/-- The identity scheme is correct, so correctness does not give one-wayness. -/
example : idScheme.Correct := fun _ _ _ => rfl

/-- The adversary that returns its challenge wins Attack Game 10.2 for the identity scheme. -/
theorem eval_owExperiment_idScheme :
    ProbComp.eval (idScheme.owExperiment fun _ y => pure y) = PMF.pure true := by
  simp only [TrapdoorFunction.owExperiment, idScheme, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind, eq_self, decide_true, PMF.bind_const]

/-- The identity scheme is not one way against any class that contains that adversary. -/
theorem not_oneWay_idScheme
    (Admissible : (ℕ → TrapdoorFunction.Inverter Unit (fun _ => Bool) (fun _ => Bool)) → Prop)
    (h : Admissible fun _ _ y => pure y) :
    ¬ TrapdoorFunction.OneWay (fun _ => idScheme) Admissible := by
  intro hT
  have hneg := hT _ h
  simp only [Experiment.succProbability, eval_owExperiment_idScheme] at hneg
  have h1 : Game.succProbability (PMF.pure true) = 1 := by simp [Game.succProbability]
  simp only [h1] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- The class is the caller's: against the empty class even the identity scheme is one way. -/
example : TrapdoorFunction.OneWay (fun _ => idScheme) fun _ => False :=
  fun _ h => h.elim

/-- The scheme that maps `n`-bit numbers to a point: the adversary learns nothing about `x`. -/
def hidingScheme (n : ℕ) :
    TrapdoorFunction Unit Unit (fun _ => Fin (2 ^ n)) (fun _ => Unit) where
  keyGen := pure ()
  publicKey := id
  eval _ _ := ()
  invert _ _ := ⟨0, Nat.two_pow_pos n⟩
  domain_nonempty _ := ⟨⟨0, Nat.two_pow_pos n⟩⟩

/-- Every adversary wins Attack Game 10.2 for the hiding scheme with probability `2⁻ⁿ`. -/
theorem succProbability_owExperiment_hidingScheme (n : ℕ)
    (A : TrapdoorFunction.Inverter Unit (fun _ => Fin (2 ^ n)) (fun _ => Unit)) :
    ((hidingScheme n).owExperiment A).succProbability = ((2 : NNReal) ^ n)⁻¹ := by
  have h : ProbComp.eval ((hidingScheme n).owExperiment A) = (ProbComp.eval (A () ())).bind
      fun x' => (PMF.uniformOfFintype (Fin (2 ^ n))).bind fun x => PMF.pure (decide (x' = x)) := by
    simp only [TrapdoorFunction.owExperiment, hidingScheme, ProbComp.eval_bind,
      ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind]
    exact PMF.bind_comm _ _ _
  rw [Experiment.succProbability, Game.succProbability, h, PMF.bind_apply]
  simp only [PMF.uniformOfFintype_bind_decide_eq_apply_true, ENNReal.tsum_mul_right,
    PMF.tsum_coe, one_mul, Fintype.card_fin]
  rw [show ((2 ^ n : ℕ) : ENNReal) = (((2 : NNReal) ^ n : NNReal) : ENNReal) by push_cast; rfl,
    ← ENNReal.coe_inv (pow_ne_zero n two_ne_zero), ENNReal.toNNReal_coe]

/-- The hiding family is one way against every adversary, and nothing is asked of its cost. -/
theorem oneWay_hidingScheme : TrapdoorFunction.OneWay hidingScheme fun _ => True := by
  intro A _
  simp only [succProbability_owExperiment_hidingScheme]
  exact negligible_inv_two_pow

/-! ### The RSA scheme -/

/-- An `RSAInverter` is a family of adversaries of Attack Game 10.2 for the RSA sets, so
`RSAInverter.IsPPT` is a class for `TrapdoorFunction.OneWay`. -/
example : RSAInverter =
    ((n : ℕ) → TrapdoorFunction.Inverter RSAPublicKey (fun pk => Fin pk.N) (fun pk => Fin pk.N)) :=
  rfl

/-- `T_RSA` is a correct trapdoor permutation scheme: `F(pk, ·)` is a permutation of `Fin N`. -/
example (gen : ProbComp RSADesc) {desc : RSADesc}
    (h : desc ∈ (ProbComp.eval (rsaTrapdoor gen).keyGen).support) :
    Function.Bijective ((rsaTrapdoor gen).eval ((rsaTrapdoor gen).publicKey desc)) :=
  (rsaTrapdoor_correct gen).bijective h

/-- `F` of `T_RSA` is, on values, the function `rsaEval`. -/
example (gen : ProbComp RSADesc) (pk : RSAPublicKey) (x : Fin pk.N) :
    ((rsaTrapdoor gen).eval pk x : ℕ) = rsaEval pk.N pk.e x :=
  rfl

/-- `I` of `T_RSA` is, on values, the function `rsaInvert` at the modulus and `d` of the secret
key, whose polynomial-time certificate is `computableInPolyTime_rsaInvert`. -/
example (gen : ProbComp RSADesc) (desc : RSADesc) (y : Fin desc.publicKey.N) :
    ((rsaTrapdoor gen).invert desc y : ℕ) = rsaInvert desc.modulus desc.d y :=
  rfl

/-- `F` of `T_RSA`, as a function of the inverter's input `(1ⁿ, pk, y)`, is computable in
polynomial time. -/
example (gen : ProbComp RSADesc) : ComputableInPolyTime
    (fun x : RSAInput => (((rsaTrapdoor gen).eval x.publicKey x.challenge : Fin x.publicKey.N) : ℕ))
    encRSAInput encNat :=
  computableInPolyTime_rsaEval (by fun_prop) (by fun_prop) (by fun_prop) fun x => x.challenge.pos

/-- Under the RSA assumption for the law of the generator, a PPT inverter wins Attack Game 10.2
for `T_RSA` negligibly. -/
example (gen : ℕ → ProbComp RSADesc) (h : RSAOneWay fun n => ProbComp.eval (gen n))
    (A : RSAInverter) (hA : A.IsPPT) :
    Negligible fun n => ((rsaTrapdoor (gen n)).owExperiment (A n)).succProbability :=
  (oneWay_rsaTrapdoor_iff gen).mpr h A hA

/-- The modulus `3 · 11` with `e = 3`, `d = 7`. -/
def desc33 : RSADesc where
  p := 3
  q := 11
  e := 3
  d := 7
  hp := by norm_num
  hq := by norm_num
  hpq := by decide
  he := by decide
  hed := by decide

/-- `F` of `T_RSA` on a small key: `2 ^ 3 = 8`. -/
example : ((rsaTrapdoor (pure desc33)).eval desc33.publicKey ⟨2, by decide⟩).val = 8 := by
  decide

/-- `I` of `T_RSA` on the same key: `8 ^ 7 ≡ 2 (mod 33)`. -/
example : ((rsaTrapdoor (pure desc33)).invert desc33 ⟨8, by decide⟩).val = 2 := by
  decide

end CslibFrontierTests.Crypto.TrapdoorFunction
