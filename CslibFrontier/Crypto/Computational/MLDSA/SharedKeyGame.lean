/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SecretRowServices
public import CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import all CslibFrontier.Crypto.Computational.MLDSA.SecretRowServices
import all CslibFrontier.Crypto.Computational.MLDSA.SecretRowPrediction
import all CslibFrontier.Crypto.Computational.MLDSA.SharedSecretExpansion
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.SigningSimulation
import all CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery

/-!
# The key-distribution switch for the adaptive ML-DSA public-pair signer

After signing simulation the native seeded key and the forger still share SHAKE. Compare its
coherent query device and the independent-expansion device to the same refreshed device.
Signing uses the same classical service in all three games. Every terminal signing write updates
the table for the next coherent query, and intermediate measurements retain the conditional state.

The query-magnitude argument of [Bennett et al.][BBBV1997], §3.1, bounds the squared change
in square-root success by the sum of measured query disturbances times four times the query
budget. Here it applies to the full public-pair signing service, whose randomized replies and
writes have finite support. The private-input estimates give an increment of `4m / 2^128`
on the square root, plus a single `2^-512` probability for the public-key hash exception.

The resulting probability comparison is an original step toward strong unforgeability of
[FIPS 204][NISTFIPS204]. The distinguishing term is evaluated on the constructed test. Certifying
its resource overhead and producing the standard sparse-oracle solver are separate obligations.
-/

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
open Cslib.Probability Cslib.Quantum

private theorem finite_bind {α β : Type} {p : PMF α} (hp : p.support.Finite)
    {k : α → PMF β} (hk : ∀ a ∈ p.support, (k a).support.Finite) :
    (p.bind k).support.Finite := by
  rw [PMF.support_bind]
  exact hp.biUnion hk

private theorem finite_draw (s : Level) (pair : MLDSA.PublicKey s.params) (H : Xofs) :
    (publicDraw s pair H).support.Finite := by
  classical
  have : NeZero s.params.q := ⟨by cases s <;> decide⟩
  unfold publicDraw draw
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  apply finite_bind (Set.toFinite _)
  intro d _
  split
  · apply finite_bind (Set.toFinite _)
    intro _ _
    simp
  · apply finite_bind
    · unfold simulateFreshSigningAttempt
      rw [PMF.support_map]
      exact (Set.toFinite _).image _
    · intro _ _
      simp

private theorem finite_retries {α ι : Type} (p : PMF (Option α)) (hp : p.support.Finite)
    (l : List ι) : (l.findSomeM? fun _ => p).support.Finite := by
  induction l with
  | nil => simp [List.findSomeM?_nil, PMF.monad_pure_eq_pure]
  | cons _ l ih =>
    rw [List.findSomeM?_cons, PMF.monad_bind_eq_bind]
    apply finite_bind hp
    rintro (_ | x) _
    · exact ih
    · simp [PMF.monad_pure_eq_pure]

private theorem finite_signingCall (s : Level) (pair : MLDSA.PublicKey s.params) {H : Xofs}
    (tr : List Byte) (q : SigningQuery) (st : History s H tr) :
    (signingCall s tr (publicDraw s pair) q st).support.Finite := by
  classical
  unfold signingCall
  split
  · simp [PMF.monad_pure_eq_pure]
  · simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    apply finite_bind (finite_retries _ (finite_draw ..) _)
    rintro (_ | w) _
    all_goals simp

private theorem support_law {α : Type} (p : PMF α) :
    ∃ r : PMF p.support, r.map Subtype.val = p := by
  classical
  let fallback : p.support := ⟨p.support_nonempty.choose, p.support_nonempty.choose_spec⟩
  let cast (x : α) : p.support := if h : x ∈ p.support then ⟨x, h⟩ else fallback
  refine ⟨p.map cast, ?_⟩
  rw [PMF.map_comp]
  refine (PMF.map_congr_on_support p _ id fun x hx => ?_).trans (PMF.map_id p)
  simp only [Function.comp_apply, cast, dite_eq_left hx, id_eq]

variable {C : QuantumSigningForger} {s : Level} {H : Xofs} {tr : List Byte}
  (pair : MLDSA.PublicKey s.params) (raw : History s H tr → Xofs)

private noncomputable def measured (pair : MLDSA.PublicKey s.params)
    (raw : History s H tr → Xofs) {α : Type} (prog : Program C α)
    (test : α → History s H tr → Test C) (d : Device C) (st : History s H tr) : PMF Bool :=
  (ProbOracleComp.runWith (C.programmedCommands s H tr (publicDraw s pair) raw)
    prog (d, st)).bind fun (x, dev, t) => (test x t).measureDensity dev.density dev.isDensityMatrix

private theorem measured_step {α : Type} {q : Request C} {k : _ → Program C α}
    (test : α → History s H tr → Test C) (d : Device C) (st : History s H tr) :
    measured pair raw (OracleComp.query q >>= k) test d st =
      (OracleComp.sumHandler (m := StateT (Device C × History s H tr) PMF)
        (fun n z => (ProbComp.unifOracle n).map (·, z))
        (C.programmedCommands s H tr (publicDraw s pair) raw) q (d, st)).bind
        fun (x, dev, t) => measured pair raw (k x) test dev t := by
  simp only [measured, ProbOracleComp.runWith, OracleComp.runWith_bind, OracleComp.runWith_query,
    PMF.bind_bind]
  rfl

private theorem measured_pure {α : Type} (x : α) (test : α → History s H tr → Test C)
    (d : Device C) (st : History s H tr) :
    measured pair raw (pure x) test d st =
      (test x st).measureDensity d.density d.isDensityMatrix := by
  simp [measured, ProbOracleComp.runWith_pure]

private theorem measured_coin {α : Type} {coin : ℕ} {k : Fin (coin + 1) → Program C α}
    (test : α → History s H tr → Test C) (d : Device C) (st : History s H tr) :
    measured pair raw (OracleComp.query (.inl coin) >>= k) test d st =
      (ProbComp.unifOracle coin).bind fun i => measured pair raw (k i) test d st := by
  rw [measured_step]
  simp [OracleComp.sumHandler, pmf_norm]

private theorem measured_gate {α : Type} {g : PhaseGateCode} {k : List Bool → Program C α}
    (test : α → History s H tr → Test C) (d : Device C) (st : History s H tr) :
    measured pair raw (OracleComp.query (.inr (.inl (.gate g))) >>= k) test d st =
      measured pair raw (k []) test
        (d.instruction ((raw st).queryTable C.addressBits C.responseBytes) (.gate g)) st := by
  rw [measured_step]
  simp [programmedCommands, OracleComp.sumHandler, deviceCommand, deviceHandler_gate, pmf_norm]

private theorem measured_query {α : Type} {k : List Bool → Program C α}
    (test : α → History s H tr → Test C) (d : Device C) (st : History s H tr) :
    measured pair raw (OracleComp.query (.inr (.inl .query)) >>= k) test d st =
      measured pair raw (k []) test
        (d.instruction ((raw st).queryTable C.addressBits C.responseBytes) .query) st := by
  rw [measured_step]
  simp [programmedCommands, OracleComp.sumHandler, deviceCommand, deviceHandler_query, pmf_norm]

private theorem measured_measure {α : Type} {wire : Fin (Width C)} {k : List Bool → Program C α}
    (test : α → History s H tr → Test C) (d : Device C) (st : History s H tr) :
    measured pair raw (OracleComp.query (.inr (.inl (.measure wire))) >>= k) test d st =
      (d.measure (fun x => x wire)).bind fun (y, dev) => measured pair raw (k [y]) test dev st := by
  rw [measured_step]
  simp [programmedCommands, OracleComp.sumHandler, deviceCommand, deviceHandler_measure, pmf_norm]

private theorem measured_sign {α : Type} {ask : SigningQuery}
    {k : Option (List Byte) → Program C α}
    (test : α → History s H tr → Test C) (d : Device C) (st : History s H tr) :
    measured pair raw (OracleComp.query (.inr (.inr ask)) >>= k) test d st =
      (signingCall s tr (publicDraw s pair) ask st).bind fun (r, t) =>
        measured pair raw (k r) test d t := by
  rw [measured_step]
  simp [programmedCommands, OracleComp.sumHandler, pmf_norm]

private theorem measured_readout {α : Type} (p : Program C α)
    (test : α → History s H tr → Test C) (st : History s H tr) :
    ∃ M : Test C, ∀ d, measured pair raw p test d st =
      M.measureDensity d.density d.isDensityMatrix := by
  classical
  induction p generalizing st with
  | pure x =>
    exact ⟨test x st, fun d => by simp [measured, interp_norm, pmf_norm]⟩
  | liftBind q k ih =>
    choose M eq using ih
    change ∃ M : Test C, ∀ d, measured _ _ (OracleComp.query q >>= k) _ d st = _
    simp only [measured_step, programmedCommands, OracleComp.sumHandler]
    rcases q with coin | cmd | ask
    · exact ⟨POVM.mixture (ProbComp.unifOracle coin) (fun i => M i st), fun d => by
        simp only [PMF.bind_map, Function.comp_def, eq, POVM.measureDensity_mixture]⟩
    · cases cmd with
      | service op _ => exact op.elim
      | gate g =>
        simpa only [deviceCommand, deviceHandler_gate, PMF.pure_map, PMF.pure_bind, eq,
          StateT.run] using test_instruction (raw st) (.gate g) (M [] st)
      | query =>
        simpa only [deviceCommand, deviceHandler_query, PMF.pure_map, PMF.pure_bind, eq,
          StateT.run] using test_instruction (raw st) .query (M [] st)
      | measure wire =>
        let f := fun (z : (Fin (Width C) → Bool) × Unit) => z.1 wire
        refine ⟨POVM.afterRead f (fun y => M [y] st), fun d => ?_⟩
        simp only [deviceCommand, deviceHandler_measure, PMF.bind_map,
          Function.comp_def, eq, POVM.measureDensity_afterRead]
        exact DeviceState.measure_bind (fun x => x wire) d
          (fun y dev => (M [y] st).measureDensity dev.density dev.isDensityMatrix)
    · let p := signingCall s tr (publicDraw s pair) ask st
      obtain ⟨r, law⟩ := support_law p
      let _ := (finite_signingCall s pair tr ask st).fintype
      refine ⟨POVM.mixture r (fun z => M z.1.1 z.1.2), fun d => ?_⟩
      simp only [PMF.bind_map, Function.comp_def, eq, POVM.measureDensity_mixture]
      change p.bind _ = _
      conv_lhs => rw [← law, PMF.bind_map]
      rfl

private noncomputable def changedAt {α : Type} (G R : History s H tr → Xofs)
    (p : Program C α) (d : Device C) (st : History s H tr) (j : ℕ) : PMF Bool :=
  measured pair R (queryPrefix p j) (fun b t => detector C (G t) (R t) b) d st

private theorem changedAt_skip {α : Type} (G R : History s H tr → Xofs)
    (q : Request C) (k : _ → Program C α) (hq : isXofQuery q = false)
    (d : Device C) (st : History s H tr) (j : ℕ) :
    changedAt pair G R (OracleComp.query q >>= k) d st j =
      measured pair R (OracleComp.query q >>= fun x => queryPrefix (C := C) (k x) j)
        (fun found t => detector C (G t) (R t) found) d st := by
  change measured pair R (queryPrefix (C := C) (.liftBind q k) j) _ _ _ = _
  rw [queryPrefix]
  simp only [hq, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.sub_zero]
  rfl

private theorem finite_gap {β : Type} (p : PMF β) (hp : p.support.Finite)
    (x y : β → PMF Bool) (hits : β → ℕ → PMF Bool) (n : ℕ)
    (h : ∀ b, gap (x b) (y b) ≤ 4 * n * ∑ j ∈ Finset.range n, (hits b j true).toReal) :
    gap (p.bind x) (p.bind y) ≤
      4 * n * ∑ j ∈ Finset.range n, ((p.bind fun b => hits b j) true).toReal := by
  obtain ⟨r, law⟩ := support_law p
  let _ := hp.fintype
  have eq {γ : Type} (k : β → PMF γ) : p.bind k = r.bind (k ∘ Subtype.val) := by
    conv_lhs => rw [← law, PMF.bind_map]
  simp only [eq]
  exact gap_bind_le r _ _ (fun b => hits b.val) n fun b => h b

private theorem measured_gap {α : Type} (G R : History s H tr → Xofs)
    {p : Program C α} {m : ℕ}
    (cost : OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) p m)
    (test : α → History s H tr → Test C) (d : Device C) (st : History s H tr) :
    gap (measured pair G p test d st) (measured pair R p test d st) ≤
      4 * m * ∑ j ∈ Finset.range m, (changedAt pair G R p d st j true).toReal := by
  classical
  induction cost generalizing d st with
  | pure x n =>
    simp only [measured_pure, gap, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    positivity
  | liftBind q k n _ ih =>
    rcases q with coin | cmd | ask
    · have runPrefix (j : ℕ) := (changedAt_skip pair G R (.inl coin) k rfl d st j).trans
          (measured_coin pair R (coin := coin) (k := fun x => queryPrefix (k x) j) _ d st)
      rw [measured_coin pair G (k := k), measured_coin pair R (k := k)]
      simp only [runPrefix, isXofQuery, Bool.toNat_false, Nat.add_zero]
      exact gap_bind_le _ _ _ (fun i j => changedAt pair G R (k i) d st j) n fun i => ih i d st
    · cases cmd with
      | service op _ => exact op.elim
      | gate g =>
        let dev := d.instruction ((R st).queryTable C.addressBits C.responseBytes) (.gate g)
        have runPrefix (j : ℕ) :=
          (changedAt_skip pair G R (.inr (.inl (.gate g))) k rfl d st j).trans
            (measured_gate pair R (g := g) (k := fun x => queryPrefix (k x) j) _ d st)
        rw [measured_gate pair G (k := k), measured_gate pair R (k := k)]
        simp only [runPrefix, isXofQuery, Bool.toNat_false, Nat.add_zero]
        simpa only [changedAt, dev, DeviceState.instruction_apply, OracleGateCode.toPlacedGate?]
          using ih [] dev st
      | measure wire =>
        obtain ⟨r, next, hm⟩ := measure_map d wire
        have runPrefix (j : ℕ) :=
          (changedAt_skip pair G R (.inr (.inl (.measure wire))) k rfl d st j).trans
            (measured_measure pair R (wire := wire) (k := fun x => queryPrefix (k x) j) _ d st)
        rw [measured_measure pair G (k := k), measured_measure pair R (k := k)]
        simp only [runPrefix, hm, PMF.bind_map, Function.comp_def, isXofQuery, Bool.toNat_false,
          Nat.add_zero]
        exact gap_bind_le _ _ _ (fun y j => changedAt pair G R (k [y]) (next y) st j) n
          fun y => ih [y] (next y) st
      | query =>
        let next (T : History s H tr → Xofs) :=
          d.instruction ((T st).queryTable C.addressBits C.responseBytes) .query
        let h :=
          ((detector C (G st) (R st) true).measureDensity d.density d.isDensityMatrix true).toReal
        have hz : changedAt pair G R (OracleComp.query (.inr (.inl .query)) >>= k) d st 0 =
            (detector C (G st) (R st) true).measureDensity d.density d.isDensityMatrix := by
          change measured pair R
            (queryPrefix (C := C) (.liftBind (.inr (.inl .query)) k) 0) _ _ _ = _
          rw [queryPrefix]
          simp [isXofQuery, measured, interp_norm, pmf_norm]
        have hs (j : ℕ) :
            changedAt pair G R (OracleComp.query (.inr (.inl .query)) >>= k) d st (j + 1) =
              changedAt pair G R (k []) (next R) st j := by
          change measured pair R
            (queryPrefix (C := C) (.liftBind (.inr (.inl .query)) k) (j + 1)) _ _ _ = _
          rw [queryPrefix]
          simp only [isXofQuery, Nat.succ_ne_zero, beq_iff_eq, Bool.true_and, Bool.toNat_true,
            ↓reduceIte, Nat.add_sub_cancel]
          change measured pair R (OracleComp.query _ >>= _) _ _ _ = _
          simp only [measured_query (C := C) pair
            (k := fun x => queryPrefix (C := C) (k x) j)]
          rfl
        obtain ⟨M, eq⟩ := measured_readout pair G (k []) test st
        have one : gap (measured pair G (k []) test (next G) st)
            (measured pair G (k []) test (next R) st) ≤ 4 * h := by
          simpa only [eq, h, next] using single_gap C (G st) (R st) d M
        have rest := ih [] (next R) st
        simp only [measured_query (C := C) pair (k := k), isXofQuery, Bool.toNat_true,
          Finset.sum_range_succ', hs, hz]
        rw [add_comm (∑ _ ∈ _, _)]
        exact gap_step n (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) one rest
    · have runPrefix (j : ℕ) := (changedAt_skip pair G R (.inr (.inr ask)) k rfl d st j).trans
          (measured_sign pair R (ask := ask) (k := fun x => queryPrefix (k x) j) _ d st)
      rw [measured_sign pair G (k := k), measured_sign pair R (k := k)]
      simp only [runPrefix, isXofQuery, Bool.toNat_false, Nat.add_zero]
      exact finite_gap _ (finite_signingCall ..) _ _
        (fun z j => changedAt pair G R (k z.1) d z.2 j) n fun z => ih z.1 d z.2

private theorem publicPair_gap (C : QuantumSigningForger) (s : Level) (G H : Xofs)
    (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) {m : ℕ} (cost : C.XofCallsLe m) :
    gap (C.publicPairWinWithDevice s G H rho pair) (C.publicPairWinWithDevice s H H rho pair) ≤
      4 * m * ∑ j ∈ Finset.range m,
        (C.publicPairResponseChange s j G H rho pair true).toReal := by
  let pk := encodePublic s rho.toList pair.t
  let tr := H.h256.readBytes pk 64
  let start : History s H tr := ⟨H, [], [], .initial, by simp, by simp⟩
  let raw (D : Xofs) (t : History s H tr) := TerminalSigningWrite.replay D t.writes
  have honest : raw H = (·.xofs) := funext fun t => t.trace.replay_eq
  let test (f : Forgery) (t : History s H tr) : Test C := POVM.const
    (SignedMatrixTrial.newDigestWin ⟨t.xofs, pair.A, pk, f, t.log⟩)
  have win (D : Xofs) : C.publicPairWinWithDevice s D H rho pair =
      measured pair (raw D) (C.program pk) test C.initial.1 start := by
    simp only [publicPairWinWithDevice, scoreProgram, measured, test, POVM.measureDensity_const,
      PMF.map, Function.comp_def]
    rfl
  have hit (j : ℕ) : C.publicPairResponseChange s j G H rho pair =
      changedAt pair (raw G) (raw H) (C.program pk) C.initial.1 start j := by
    simp only [publicPairResponseChange, queryWrites, changedAt, measured, runSigningProgram,
      PMF.map_bind, PMF.map_comp, Function.comp_def, honest]
    apply congrArg (PMF.bind _ ·)
    funext ⟨found, dev, t⟩
    have eq : (fun a => C.queryChanged G H (t.writes, a)) =
        fun a => a.any (changed C (raw G t) t.xofs) := by
      funext a
      cases a with
      | none => rfl
      | some a => simp only [queryChanged, Option.any_some, changed, raw, t.trace.replay_eq]
    rw [eq]
    exact addressTest_law C _ found (dev, t.log)
  simp only [win, hit]
  exact measured_gap pair (raw G) (raw H) (cost pk) test C.initial.1 start

private theorem secretRow_sq_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b m : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) (cost : C.XofCallsLe m) (share : Bool) :
    let ref := (base.sampleSecretExpansionViews s ha hb).bind fun v =>
      if v.publicHashMatch then PMF.pure false else v.refreshKeySeed.bind fun H =>
        (v.pair.map (C.publicPairWinWithDevice s H H v.publicSeed)).getD (PMF.pure false)
    gap (C.secretRowDeviceGame s base ha hb share) ref ≤ (2 * (m : ℝ) / 2^128)^2 := by
  classical
  intro ref
  let V := base.sampleSecretExpansionViews s ha hb
  let hits (v : SecretExpansionViews s) (H : Xofs) (j : ℕ) : Game := match v.pair with
    | none => PMF.pure false
    | some pk => C.publicPairResponseChange s j (if share then v.shared else v.background)
        H v.publicSeed pk
  have fin : V.support.Finite := by
    dsimp only [V, Xofs.sampleSecretExpansionViews]
    apply finite_bind (Set.toFinite _)
    intro _ _
    apply finite_bind (Set.toFinite _)
    intro _ _
    apply finite_bind (Set.toFinite _)
    intro _ _
    rw [PMF.support_map]
    exact (Set.toFinite _).image _
  have bound : gap (C.secretRowDeviceGame s base ha hb share) ref ≤ 4 * m *
      ∑ j ∈ Finset.range m,
        ((V.bind fun v => v.refreshKeySeed.bind fun H => hits v H j) true).toReal := by
    apply finite_gap V fin
    intro v
    by_cases h : v.publicHashMatch = true
    · simp only [h, ↓reduceIte, gap, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      positivity
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    have hv : v.refreshKeySeed.support.Finite := by
      rw [SecretExpansionViews.refreshKeySeed, PMF.support_map]
      exact (Set.toFinite _).image _
    apply finite_gap _ hv
    intro H
    cases hp : v.pair with
    | none => simp [hits, hp, gap]
    | some pk =>
      simpa only [hits, hp, Option.map_some, Option.getD_some] using
        publicPair_gap C s (if share then v.shared else v.background) H v.publicSeed pk cost
  apply bound.trans
  calc
    _ ≤ 4 * (m : ℝ) * ∑ _j ∈ Finset.range m, ((2 : ℝ) ^ 256)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      have p := C.secretRow_changedResponse_le s base ha hb share j
      change ((V.bind fun v => v.refreshKeySeed.bind fun H => hits v H j) true) ≤ _ at p
      exact (ENNReal.toReal_mono (by norm_num : (2 ^ 256 : ENNReal)⁻¹ ≠ ⊤) p).trans_eq (by
        rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat])
    _ = _ := by
      simp
      ring

private theorem nativeFullPair_le_independentExpandS (C : QuantumSigningForger) (s : Level)
    (base : Xofs)
    {a b m : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) (cost : C.XofCallsLe m) :
    let native := (base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s
      (fun rho pk => (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin))
    (native true).toReal ≤ (√((C.independentExpandSGame s base a b true).toReal) +
      4 * (m : ℝ) / 2^128)^2 + ((2 : ℝ)^512)⁻¹ := by
  intro native
  obtain ⟨left, right⟩ := C.secretRowDeviceGame_bounds s base ha hb
  have h₁ := C.secretRow_sq_le s base ha hb cost true
  have h₂ := C.secretRow_sq_le s base ha hb cost false
  dsimp only [gap] at h₁ h₂
  have u := le_of_sq_le_sq h₁ (by positivity)
  rw [sub_sq_comm] at h₂
  have v := le_of_sq_le_sq h₂ (by positivity)
  have inc := Real.sqrt_le_sqrt (ENNReal.toReal_mono
    ((C.independentExpandSGame s base a b).apply_ne_top true) right)
  have roots : √((C.secretRowDeviceGame s base ha hb true true).toReal) ≤
      √((C.independentExpandSGame s base a b true).toReal) + 4 * (m : ℝ) / 2^128 := by
    linarith only [u, v, inc]
  have sq := pow_le_pow_left₀ (Real.sqrt_nonneg _) roots 2
  rw [Real.sq_sqrt ENNReal.toReal_nonneg] at sq
  have e := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨(C.secretRowDeviceGame s base ha hb true).apply_ne_top true,
      by norm_num⟩) left
  rw [ENNReal.toReal_add ((C.secretRowDeviceGame s base ha hb true).apply_ne_top true)
    (by norm_num),
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at e
  exact e.trans (add_le_add_left sq _)

/-- Transfer fresh-digest success of the native-key public-pair signer to a uniform MLWE pair
plus the real-versus-uniform advantage of its explicit test. Each coherent query contributes
to the square-root loss. Both branches use the same public-pair test and retain setup failure. -/
public theorem nativeFullPair_le_uniformPair (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b m : ℕ} (ha : 528 ≤ a) (hb : 894 ≤ b) (cost : C.XofCallsLe m) :
    let native := (base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s
      (fun rho pk => (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin))
    let test := C.fullPairMLWETest s base a b
    let real := (MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)).bind test
    let uniform := (MLDSA.uniformKeyLaw s.params).bind test
    (native true).toReal ≤ (√((uniform true).toReal + (Game.advantage real uniform : ℝ)) +
      4 * (m : ℝ) / 2^128)^2 + ((2 : ℝ)^512)⁻¹ := by
  intro native test real uniform
  have bound := C.nativeFullPair_le_independentExpandS s base ha (by lia : 481 ≤ b) cost
  rw [C.independentExpandSGame_eq_mlwe s base ha hb] at bound
  apply bound.trans
  apply add_le_add_left
  apply pow_le_pow_left₀ (by positivity)
  apply add_le_add_left
  apply Real.sqrt_le_sqrt
  exact Game.coe_succProbability_le_add_of_advantage_le (g₀ := real) (g₁ := uniform) le_rfl

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
