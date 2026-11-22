/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Median
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ordering a cubic multigraph by matched-edge pair insertion

In `CslibFrontier.Computability.Circuit.Frontier.Layouts.Median`, every vertex of a loopless
cubic multigraph is placed at the median of the three scores of its incident edges, yielding a cut
bound of `#(vertices straddling t)` at each threshold `t`.

Keeping a matching `M : Set E` (a set of pairwise vertex-disjoint edges) *unsubdivided* yields a
strictly sharper layout. Each unpaired vertex `v` keeps its `median3` key, while each matched edge
`e ∈ M` with endpoints `u = G.src e` and `v = G.tgt e` and outer incident pairs `G.incidenceSet u \
{e} = {a, b}` and `G.incidenceSet v \ {e} = {c, d}` places `u` and `v` at the single pair keys
`pairKey (score a) (score b) (score c) (score d)` and
`pairKey (score c) (score d) (score a) (score b)`, where
`pairKey a b c d := min (max a b) (max (min a b) (min c d))`.

This single pair of real keys *simultaneously attains the optimal two-vertex cut energy at every
threshold `t`* (`twoVertexEnergy_pairKey`):

* cost `0` when all four outer edge scores lie on the same side of `t`;
* cost `1` when at least one outer pair `{a, b}` or `{c, d}` does not straddle `t` (covering the
  `(1, 0)`, `(0, 1)`, `(2, 1)`, `(1, 2)`, `(2, 0)`, and `(0, 2)` splits);
* cost `2` only when both outer pairs straddle `t` (`(1, 1)`).

Decomposing `twoVertexCost` into the two binary events `Multigraph.PairStraddlesAny` (the four outer
edges straddle `t`) and `Multigraph.PairStraddlesBoth` (both outer pairs straddle `t`) avoids any
ordering choice on incident edges, handles parallel edges without requiring a simple graph, and
lets every cut of a threshold layout be bounded pointwise by `Multigraph.matchingCost`, which is
always at most the naive straddling count (`Multigraph.matchingCost_le_edgeStraddles`) and strictly
smaller whenever a matched pair has a `(1, 0)` or `(2, 1)` outer split whose shared edge lands on
the minority side (`exists_twoVertexCost_lt_starCost_add`).

This adapts the deterministic pair-insertion key (`pairKey` / `pairColor`) from the Apache 2.0
companion repository `SamuelSchlesinger/the-frontier-method` (modules `Frontier.Layouts.Pair` and
`Frontier.Layouts.MatchingLayout`) to the loopless cubic `Multigraph` setting used in this library
(allowing parallel edges). It is also the combinatorial layout mechanism underlying the `4.6155n`
matched-edge branch-and-bound bound (`rrwilliams0/circuit-lb-4.6155n`).

## Main definitions

* `Cslib.Circuits.Frontier.pairKey`, `Cslib.Circuits.Frontier.pairColor`: canonical threshold keys
  and optimal Boolean color for a matched edge pair.
* `Cslib.Circuits.Frontier.starEnergy`, `Cslib.Circuits.Frontier.starCost`: single-vertex cubic star
  disagreement energy and optimal cost.
* `Cslib.Circuits.Frontier.twoVertexEnergy`, `Cslib.Circuits.Frontier.twoVertexCost`: two-vertex
  matched-edge energy and optimal cost.
* `Cslib.Circuits.Frontier.Multigraph.IsMatching`: pairwise vertex-disjoint edge set.
* `Cslib.Circuits.Frontier.Multigraph.matchedVertices`: vertices incident to a matching edge.
* `Cslib.Circuits.Frontier.Multigraph.PairStraddlesAny`,
  `Cslib.Circuits.Frontier.Multigraph.PairStraddlesBoth`: binary events whose sum is
  `twoVertexCost` at a matched edge.
* `Cslib.Circuits.Frontier.Multigraph.matchingCost`: exact threshold cost of a matching.
* `Cslib.Circuits.Frontier.Multigraph.matchingKey`: vertex keys combining `median3` and `pairKey`.

## Main results

* `Cslib.Circuits.Frontier.twoVertexEnergy_pairKey`: one pair of keys achieves the optimal
  two-vertex cost simultaneously at every threshold `t`.
* `Cslib.Circuits.Frontier.twoVertexCost_le_starCost_add`,
  `Cslib.Circuits.Frontier.exists_twoVertexCost_lt_starCost_add`: pair insertion is always at most
  the sum of the two naive star costs, and strictly saves `1` on mismatched `(1, 0)` / `(2, 1)`
  splits.
* `Cslib.Circuits.Frontier.Multigraph.matchingCost_le_edgeStraddles`: matching cost is bounded by
  the naive straddling count from `Median`.
* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_threshold_le_matchingCost`: exact cut bound at
  every threshold `t`.
* `Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_matching_edgeScore`: deterministic layout
  width bound over any grid of edge-score windows.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-! ### Boolean energy and canonical pair keys -/

/-- Boolean disagreement indicator: `1` if `x ≠ y`, `0` otherwise. -/
private def boolDiff (x y : Bool) : ℕ := if x = y then 0 else 1

private theorem boolDiff_triangle (x y m : Bool) :
    boolDiff x y ≤ boolDiff x m + boolDiff y m := by
  cases x <;> cases y <;> cases m <;> decide

/-- Optimal Boolean color for the first endpoint of a matched pair with outer colors `(a, b)` at
the first endpoint and `(c, d)` at the second. Swap `(a, b)` and `(c, d)` for the other
endpoint. -/
def pairColor (a b c d : Bool) : Bool :=
  (a && b) || ((a || b) && (c || d))

/-- Canonical real threshold key for the first endpoint of a matched pair with outer edge scores
`a, b` at that endpoint and `c, d` at its mate. Swapping `a ↔ b` or `c ↔ d` leaves it unchanged. -/
def pairKey {α : Type*} [LinearOrder α] (a b c d : α) : α :=
  min (max a b) (max (min a b) (min c d))

theorem pairKey_comm_left {α : Type*} [LinearOrder α] (a b c d : α) :
    pairKey a b c d = pairKey b a c d := by
  simp only [pairKey, max_comm a b, min_comm a b]

theorem pairKey_comm_right {α : Type*} [LinearOrder α] (a b c d : α) :
    pairKey a b c d = pairKey a b d c := by
  simp only [pairKey, min_comm c d]

/-- A pair key is always equal to one of the four outer edge scores. -/
theorem pairKey_mem {α : Type*} [LinearOrder α] (a b c d : α) :
    pairKey a b c d = a ∨ pairKey a b c d = b ∨
      pairKey a b c d = c ∨ pairKey a b c d = d := by
  unfold pairKey
  rcases min_choice (max a b) (max (min a b) (min c d)) with h | h
  · rw [h]
    rcases max_choice a b with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rw [h]
    rcases max_choice (min a b) (min c d) with h' | h'
    · rw [h']
      rcases min_choice a b with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (Or.inl h'')
    · rw [h']
      rcases min_choice c d with h'' | h''
      · exact Or.inr (Or.inr (Or.inl h''))
      · exact Or.inr (Or.inr (Or.inr h''))

/-- Disagreement count at a single cubic vertex with three incident edge colors `a, b, c` and
vertex color `x`. -/
def starEnergy (a b c x : Bool) : ℕ :=
  (if x = a then 0 else 1) + (if x = b then 0 else 1) + (if x = c then 0 else 1)

/-- Minimum cut cost of a single cubic vertex: `0` when all three incident edges share a color,
`1` when they straddle. -/
def starCost (a b c : Bool) : ℕ :=
  if a = b ∧ b = c then 0 else 1

/-- Total disagreement count of a matched edge `{u, v}` with outer edge colors `a, b` at `u` and
`c, d` at `v`, when `u` receives color `x` and `v` receives color `y`. -/
def twoVertexEnergy (a b c d x y : Bool) : ℕ :=
  (if x = a then 0 else 1) + (if x = b then 0 else 1) +
    (if x = y then 0 else 1) +
    (if y = c then 0 else 1) + (if y = d then 0 else 1)

/-- Minimum disagreement cost of a matched edge pair over all choices of `(x, y : Bool)`:
`0` when all four outer colors match, `2` when both pairs disagree (`a ≠ b` and `c ≠ d`), and `1`
otherwise. -/
def twoVertexCost (a b c d : Bool) : ℕ :=
  (if a = b ∧ b = c ∧ c = d then 0 else 1) +
    (if a ≠ b ∧ c ≠ d then 1 else 0)

/-- `median3` thresholds to majority vote at every threshold `t`. -/
theorem decide_median3_lt {α : Type*} [LinearOrder α] (a b c t : α) :
    decide (median3 a b c < t) =
      ((decide (a < t) && decide (b < t)) ||
        (decide (a < t) && decide (c < t)) ||
        (decide (b < t) && decide (c < t))) := by
  by_cases ha : a < t <;> by_cases hb : b < t <;> by_cases hc : c < t <;>
    simp [median3, ha, hb, hc, max_lt_iff, min_lt_iff]

/-- The median of three incident edge scores attains `starCost` at every threshold `t`. -/
theorem starEnergy_median3 {α : Type*} [LinearOrder α] (a b c t : α) :
    starEnergy (decide (a < t)) (decide (b < t)) (decide (c < t))
      (decide (median3 a b c < t)) =
      starCost (decide (a < t)) (decide (b < t)) (decide (c < t)) := by
  rw [decide_median3_lt]
  cases decide (a < t) <;> cases decide (b < t) <;> cases decide (c < t) <;> decide

/-- Thresholding `pairKey` yields `pairColor` simultaneously at every threshold `t`. -/
theorem decide_pairKey_lt {α : Type*} [LinearOrder α] (a b c d t : α) :
    decide (pairKey a b c d < t) =
      pairColor (decide (a < t)) (decide (b < t)) (decide (c < t)) (decide (d < t)) := by
  by_cases ha : a < t <;> by_cases hb : b < t <;>
    by_cases hc : c < t <;> by_cases hd : d < t <;>
    simp [pairKey, pairColor, min_lt_iff, max_lt_iff, ha, hb, hc, hd]

/-- The pair coloring attains `twoVertexCost` and is minimal over all `(x, y : Bool)`. -/
theorem twoVertexEnergy_pairColor (a b c d : Bool) :
    twoVertexEnergy a b c d (pairColor a b c d) (pairColor c d a b) =
      twoVertexCost a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- `twoVertexCost` is the minimum of `twoVertexEnergy` over all vertex colorings `(x, y)`. -/
theorem twoVertexCost_le_twoVertexEnergy (a b c d x y : Bool) :
    twoVertexCost a b c d ≤ twoVertexEnergy a b c d x y := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> cases y <;> decide

/-- **Simultaneous optimality.** One pair of real keys attains the optimal two-vertex cut cost at
every threshold `t` at once. -/
theorem twoVertexEnergy_pairKey {α : Type*} [LinearOrder α] (a b c d t : α) :
    twoVertexEnergy (decide (a < t)) (decide (b < t)) (decide (c < t)) (decide (d < t))
      (decide (pairKey a b c d < t)) (decide (pairKey c d a b < t)) =
      twoVertexCost (decide (a < t)) (decide (b < t)) (decide (c < t)) (decide (d < t)) := by
  simp only [decide_pairKey_lt, twoVertexEnergy_pairColor]

/-- For every choice of shared-edge color `m`, the pair cost is at most the sum of the two
endpoint star costs. -/
theorem twoVertexCost_le_starCost_add (a b c d m : Bool) :
    twoVertexCost a b c d ≤ starCost a b m + starCost c d m := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases m <;> decide

/-- On a `(1, 0)` outer split whose shared edge receives the minority color (`m = true`), keeping
the matched edge unsubdivided strictly saves `1` over naive median-of-3 edge scores (`1 < 2`). -/
theorem exists_twoVertexCost_lt_starCost_add :
    twoVertexCost true false false false <
      starCost true false true + starCost false false true := by
  decide

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-! ### Matchings in a multigraph -/

/-- A set of edges `M` is a *matching* when its edges are pairwise vertex-disjoint: no vertex is
incident to two distinct edges in `M`. -/
def IsMatching (M : Set E) : Prop :=
  M.Pairwise fun e f => Disjoint ({G.src e, G.tgt e} : Set V) {G.src f, G.tgt f}

/-- The set of vertices incident to some edge in `M`. -/
def matchedVertices (M : Set E) : Set V :=
  {v | ∃ e ∈ M, e ∈ G.incidenceSet v}

/-- `PairStraddlesAny` holds at a matched edge `e` when the four outer edges at `G.src e` and
`G.tgt e` (excluding `e`) straddle `t`: one scores below `t` and one at least `t`. -/
def PairStraddlesAny {α : Type*} [LinearOrder α] (score : E → α) (t : α) (e : E) : Prop :=
  (∃ f ∈ (G.incidenceSet (G.src e) \ {e}) ∪ (G.incidenceSet (G.tgt e) \ {e}), score f < t) ∧
    (∃ f ∈ (G.incidenceSet (G.src e) \ {e}) ∪ (G.incidenceSet (G.tgt e) \ {e}), t ≤ score f)

/-- `PairStraddlesBoth` holds at a matched edge `e` when *both* outer pairs
`G.incidenceSet (G.src e) \ {e}` and `G.incidenceSet (G.tgt e) \ {e}` straddle `t`. -/
def PairStraddlesBoth {α : Type*} [LinearOrder α] (score : E → α) (t : α) (e : E) : Prop :=
  (∃ f ∈ G.incidenceSet (G.src e) \ {e}, score f < t) ∧
    (∃ f ∈ G.incidenceSet (G.src e) \ {e}, t ≤ score f) ∧
    (∃ f ∈ G.incidenceSet (G.tgt e) \ {e}, score f < t) ∧
    (∃ f ∈ G.incidenceSet (G.tgt e) \ {e}, t ≤ score f)

/-- The threshold cost of a matching `M` at threshold `t`: each unpaired straddling vertex pays
`1`, each matched edge whose outer edges straddle `t` pays `1`, and each matched edge whose two
outer pairs *both* straddle `t` pays an additional `1` (matching `twoVertexCost`). -/
noncomputable def matchingCost {α : Type*} [LinearOrder α] (M : Set E) (score : E → α)
    (t : α) : ℕ :=
  {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v}.ncard +
    {e | e ∈ M ∧ G.PairStraddlesAny score t e}.ncard +
    {e | e ∈ M ∧ G.PairStraddlesBoth score t e}.ncard

theorem isMatching_empty : G.IsMatching (∅ : Set E) := by
  simp [IsMatching]

theorem matchedVertices_empty : G.matchedVertices (∅ : Set E) = ∅ := by
  ext v; simp [matchedVertices]

theorem matchingCost_empty {α : Type*} [LinearOrder α] (score : E → α) (t : α) :
    G.matchingCost ∅ score t = {v | G.EdgeStraddles score t v}.ncard := by
  simp [matchingCost, matchedVertices_empty]

theorem pairStraddlesAny_congr {α : Type*} [LinearOrder α] {score score' : E → α} {t : α}
    {e : E} (h : ∀ f ∈ (G.incidenceSet (G.src e) \ {e}) ∪ (G.incidenceSet (G.tgt e) \ {e}),
      score f = score' f) :
    G.PairStraddlesAny score t e ↔ G.PairStraddlesAny score' t e := by
  constructor <;> rintro ⟨⟨f, hf, hlt⟩, ⟨g, hg, hle⟩⟩
  · exact ⟨⟨f, hf, by rwa [← h f hf]⟩, ⟨g, hg, by rwa [← h g hg]⟩⟩
  · exact ⟨⟨f, hf, by rwa [h f hf]⟩, ⟨g, hg, by rwa [h g hg]⟩⟩

theorem pairStraddlesBoth_congr {α : Type*} [LinearOrder α] {score score' : E → α} {t : α}
    {e : E} (h : ∀ f ∈ (G.incidenceSet (G.src e) \ {e}) ∪ (G.incidenceSet (G.tgt e) \ {e}),
      score f = score' f) :
    G.PairStraddlesBoth score t e ↔ G.PairStraddlesBoth score' t e := by
  constructor <;> rintro ⟨⟨f₁, hf₁, hlt₁⟩, ⟨g₁, hg₁, hle₁⟩, ⟨f₂, hf₂, hlt₂⟩, ⟨g₂, hg₂, hle₂⟩⟩
  · exact ⟨⟨f₁, hf₁, by rwa [← h f₁ (Or.inl hf₁)]⟩,
      ⟨g₁, hg₁, by rwa [← h g₁ (Or.inl hg₁)]⟩,
      ⟨f₂, hf₂, by rwa [← h f₂ (Or.inr hf₂)]⟩,
      ⟨g₂, hg₂, by rwa [← h g₂ (Or.inr hg₂)]⟩⟩
  · exact ⟨⟨f₁, hf₁, by rwa [h f₁ (Or.inl hf₁)]⟩,
      ⟨g₁, hg₁, by rwa [h g₁ (Or.inl hg₁)]⟩,
      ⟨f₂, hf₂, by rwa [h f₂ (Or.inr hf₂)]⟩,
      ⟨g₂, hg₂, by rwa [h g₂ (Or.inr hg₂)]⟩⟩

variable {G}

private theorem eq_of_mem_isMatching {M : Set E} (hM : G.IsMatching M) {e f : E}
    (he : e ∈ M) (hf : f ∈ M) {v : V} (hev : e ∈ G.incidenceSet v) (hfv : f ∈ G.incidenceSet v) :
    e = f := by
  by_contra hne
  have hdis := hM he hf hne
  have hv1 : v ∈ ({G.src e, G.tgt e} : Set V) := by
    rcases hev with h | h <;> simp [h]
  have hv2 : v ∈ ({G.src f, G.tgt f} : Set V) := by
    rcases hfv with h | h <;> simp [h]
  exact disjoint_left.mp hdis hv1 hv2

/-- Mate of a vertex `v` under matching `M` (returning `v` when `v` is unmatched). -/
noncomputable def mate (G : Multigraph V E) (M : Set E) (v : V) : V :=
  letI := Classical.dec
  if h : ∃ e ∈ M, e ∈ G.incidenceSet v then
    if G.src h.choose = v then G.tgt h.choose else G.src h.choose
  else v

private theorem mate_src {M : Set E} (hM : G.IsMatching M)
    {e : E} (he : e ∈ M) : G.mate M (G.src e) = G.tgt e := by
  have hex : ∃ f ∈ M, f ∈ G.incidenceSet (G.src e) := ⟨e, he, Or.inl rfl⟩
  have huniq : hex.choose = e :=
    eq_of_mem_isMatching hM hex.choose_spec.1 he hex.choose_spec.2 (Or.inl rfl)
  simp only [mate, hex, ↓reduceDIte, huniq, ↓reduceIte]

private theorem mate_tgt {M : Set E} (hM : G.IsMatching M) (hloop : G.Loopless)
    {e : E} (he : e ∈ M) : G.mate M (G.tgt e) = G.src e := by
  have hex : ∃ f ∈ M, f ∈ G.incidenceSet (G.tgt e) := ⟨e, he, Or.inr rfl⟩
  have huniq : hex.choose = e :=
    eq_of_mem_isMatching hM hex.choose_spec.1 he hex.choose_spec.2 (Or.inr rfl)
  simp only [mate, hex, ↓reduceDIte, huniq, hloop e, ↓reduceIte]

/-- Canonical threshold key for a vertex of a cubic multigraph under edge scores `score` and
matching `M`: unpaired vertices use `median3` of their three incident edge scores; endpoints of
`e ∈ M` use `pairKey` of their outer pair and their mate's outer pair. -/
noncomputable def matchingKey {α : Type*} [LinearOrder α] [Inhabited α]
    (G : Multigraph V E) (M : Set E) (score : E → α) (v : V) : α :=
  letI := Classical.dec
  if h : ∃ e ∈ M, e ∈ G.incidenceSet v then
    let e := h.choose
    let u := if G.src e = v then G.tgt e else G.src e
    if hs : (G.incidenceSet v \ {e}).ncard = 2 ∧ (G.incidenceSet u \ {e}).ncard = 2 then
      let p₁ := (ncard_eq_two.mp hs.1).choose
      let q₁ := (ncard_eq_two.mp hs.1).choose_spec.choose
      let p₂ := (ncard_eq_two.mp hs.2).choose
      let q₂ := (ncard_eq_two.mp hs.2).choose_spec.choose
      pairKey (score p₁) (score q₁) (score p₂) (score q₂)
    else default
  else if h3 : (G.incidenceSet v).ncard = 3 then
    let e₀ := (ncard_eq_three.mp h3).choose
    let e₁ := (ncard_eq_three.mp h3).choose_spec.choose
    let e₂ := (ncard_eq_three.mp h3).choose_spec.choose_spec.choose
    median3 (score e₀) (score e₁) (score e₂)
  else default

private theorem ncard_sdiff_singleton_eq_two [Finite E] {v : V} {e : E}
    (h3 : (G.incidenceSet v).ncard = 3) (he : e ∈ G.incidenceSet v) :
    (G.incidenceSet v \ {e}).ncard = 2 := by
  have := ncard_sdiff_singleton_add_one he (s := G.incidenceSet v)
  omega

private theorem pairKey_eq_of_eq_pair {α : Type*} [LinearOrder α] (score : E → α)
    {S₁ S₂ : Set E} {a b a' b' c d c' d' : E}
    (h1 : S₁ = {a, b}) (h1' : S₁ = {a', b'}) (hab' : a' ≠ b')
    (h2 : S₂ = {c, d}) (h2' : S₂ = {c', d'}) (hcd' : c' ≠ d') :
    pairKey (score a) (score b) (score c) (score d) =
      pairKey (score a') (score b') (score c') (score d') := by
  have hset1 : ({a, b} : Set E) = {a', b'} := h1.symm.trans h1'
  have hset2 : ({c, d} : Set E) = {c', d'} := h2.symm.trans h2'
  have ha' : a' = a ∨ a' = b := by
    have : a' ∈ ({a, b} : Set E) := hset1 ▸ by simp
    simpa using this
  have hb' : b' = a ∨ b' = b := by
    have : b' ∈ ({a, b} : Set E) := hset1 ▸ by simp
    simpa using this
  have hc' : c' = c ∨ c' = d := by
    have : c' ∈ ({c, d} : Set E) := hset2 ▸ by simp
    simpa using this
  have hd' : d' = c ∨ d' = d := by
    have : d' ∈ ({c, d} : Set E) := hset2 ▸ by simp
    simpa using this
  have hcd_case : ∀ x y, (x = c ∨ x = d) → (y = c ∨ y = d) → x ≠ y →
      ∀ u v : α, pairKey u v (score c) (score d) = pairKey u v (score x) (score y) := by
    intro x y hx hy hxy u v
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · rfl
    · exact pairKey_comm_right u v (score y) (score x)
    · exact (hxy rfl).elim
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact (hab' rfl).elim
  · exact hcd_case c' d' hc' hd' hcd' (score a') (score b')
  · rw [pairKey_comm_left (score b') (score a')]
    exact hcd_case c' d' hc' hd' hcd' (score a') (score b')
  · exact (hab' rfl).elim

private theorem matchingKey_matched [Finite E] {α : Type*} [LinearOrder α] [Inhabited α]
    {M : Set E} (hM : G.IsMatching M) (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (score : E → α)
    {e a b c d : E} (he : e ∈ M)
    (hsrc : G.incidenceSet (G.src e) \ {e} = {a, b})
    (htgt : G.incidenceSet (G.tgt e) \ {e} = {c, d}) :
    G.matchingKey M score (G.src e) = pairKey (score a) (score b) (score c) (score d) ∧
      G.matchingKey M score (G.tgt e) = pairKey (score c) (score d) (score a) (score b) := by
  have hex_s : ∃ f ∈ M, f ∈ G.incidenceSet (G.src e) := ⟨e, he, Or.inl rfl⟩
  have hex_t : ∃ f ∈ M, f ∈ G.incidenceSet (G.tgt e) := ⟨e, he, Or.inr rfl⟩
  have huniq_s : hex_s.choose = e :=
    eq_of_mem_isMatching hM hex_s.choose_spec.1 he hex_s.choose_spec.2 (Or.inl rfl)
  have huniq_t : hex_t.choose = e :=
    eq_of_mem_isMatching hM hex_t.choose_spec.1 he hex_t.choose_spec.2 (Or.inr rfl)
  have hns : (G.incidenceSet (G.src e) \ {e}).ncard = 2 :=
    ncard_sdiff_singleton_eq_two (h3 _) (Or.inl rfl)
  have hnt : (G.incidenceSet (G.tgt e) \ {e}).ncard = 2 :=
    ncard_sdiff_singleton_eq_two (h3 _) (Or.inr rfl)
  classical
  constructor
  · have hhs : (G.incidenceSet (G.src e) \ {hex_s.choose}).ncard = 2 ∧
        (G.incidenceSet
          (if G.src hex_s.choose = G.src e then G.tgt hex_s.choose else G.src hex_s.choose) \
          {hex_s.choose}).ncard = 2 := by
      simp only [huniq_s, ↓reduceIte]; exact ⟨hns, hnt⟩
    simp only [matchingKey, hex_s, ↓reduceDIte, hhs]
    have hp := (ncard_eq_two.mp hhs.1).choose_spec.choose_spec
    have hq := (ncard_eq_two.mp hhs.2).choose_spec.choose_spec
    have h1 : G.incidenceSet (G.src e) \ {e} =
        {(ncard_eq_two.mp hhs.1).choose, (ncard_eq_two.mp hhs.1).choose_spec.choose} := by
      simpa only [huniq_s] using hp.2
    have h2 : G.incidenceSet (G.tgt e) \ {e} =
        {(ncard_eq_two.mp hhs.2).choose, (ncard_eq_two.mp hhs.2).choose_spec.choose} := by
      simpa only [huniq_s, ↓reduceIte] using hq.2
    exact (pairKey_eq_of_eq_pair score hsrc h1 hp.1 htgt h2 hq.1).symm
  · have hht : (G.incidenceSet (G.tgt e) \ {hex_t.choose}).ncard = 2 ∧
        (G.incidenceSet
          (if G.src hex_t.choose = G.tgt e then G.tgt hex_t.choose else G.src hex_t.choose) \
          {hex_t.choose}).ncard = 2 := by
      simp only [huniq_t, hloop e, ↓reduceIte]; exact ⟨hnt, hns⟩
    simp only [matchingKey, hex_t, ↓reduceDIte, hht]
    have hp := (ncard_eq_two.mp hht.1).choose_spec.choose_spec
    have hq := (ncard_eq_two.mp hht.2).choose_spec.choose_spec
    have h1 : G.incidenceSet (G.tgt e) \ {e} =
        {(ncard_eq_two.mp hht.1).choose, (ncard_eq_two.mp hht.1).choose_spec.choose} := by
      simpa only [huniq_t] using hp.2
    have h2 : G.incidenceSet (G.src e) \ {e} =
        {(ncard_eq_two.mp hht.2).choose, (ncard_eq_two.mp hht.2).choose_spec.choose} := by
      simpa only [huniq_t, hloop e, ↓reduceIte] using hq.2
    exact (pairKey_eq_of_eq_pair score htgt h1 hp.1 hsrc h2 hq.1).symm

private theorem matchingKey_unmatched {α : Type*} [LinearOrder α] [Inhabited α]
    {M : Set E} (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (score : E → α)
    {v : V} (hv : v ∉ G.matchedVertices M) :
    ∃ e₀ e₁ e₂ : E, e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
      G.incidenceSet v = {e₀, e₁, e₂} ∧
      G.matchingKey M score v = median3 (score e₀) (score e₁) (score e₂) := by
  have hnot : ¬∃ e ∈ M, e ∈ G.incidenceSet v := hv
  have hnc := h3 v
  have hspec := (ncard_eq_three.mp hnc).choose_spec.choose_spec.choose_spec
  refine ⟨_, _, _, hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2, ?_⟩
  simp only [matchingKey, hnot, ↓reduceDIte, hnc]

/-- Helper connecting `starCost` to `EdgeStraddles`. -/
private theorem starCost_eq_ite_edgeStraddles {α : Type*} [LinearOrder α]
    (score : E → α) (t : α) {v : V} {e₀ e₁ e₂ : E}
    (hs : G.incidenceSet v = {e₀, e₁, e₂}) :
    starCost (decide (score e₀ < t)) (decide (score e₁ < t)) (decide (score e₂ < t)) =
      letI := Classical.propDecidable
      if G.EdgeStraddles score t v then 1 else 0 := by
  have hiff : G.EdgeStraddles score t v ↔
      ¬(decide (score e₀ < t) = decide (score e₁ < t) ∧
        decide (score e₁ < t) = decide (score e₂ < t)) := by
    simp only [EdgeStraddles, hs, mem_insert_iff, mem_singleton_iff]
    by_cases h0 : score e₀ < t <;> by_cases h1 : score e₁ < t <;> by_cases h2 : score e₂ < t <;>
      simp [h0, h1, h2, not_lt.mp]
  simp only [starCost]
  split_ifs with h1 h2 h2
  · exact (hiff.mp h2 h1).elim
  · rfl
  · rfl
  · exact (h2 (hiff.mpr h1)).elim

/-- Helper expressing `twoVertexCost` in terms of `PairStraddlesAny` and `PairStraddlesBoth`. -/
private theorem twoVertexCost_eq_pairStraddles {α : Type*} [LinearOrder α]
    (score : E → α) (t : α) {e a b c d : E}
    (hsrc : G.incidenceSet (G.src e) \ {e} = {a, b})
    (htgt : G.incidenceSet (G.tgt e) \ {e} = {c, d}) :
    twoVertexCost (decide (score a < t)) (decide (score b < t))
        (decide (score c < t)) (decide (score d < t)) =
      letI := Classical.propDecidable
      (if G.PairStraddlesAny score t e then 1 else 0) +
        (if G.PairStraddlesBoth score t e then 1 else 0) := by
  have hany : G.PairStraddlesAny score t e ↔
      ¬(decide (score a < t) = decide (score b < t) ∧
        decide (score b < t) = decide (score c < t) ∧
        decide (score c < t) = decide (score d < t)) := by
    simp only [PairStraddlesAny, hsrc, htgt, mem_union, mem_insert_iff, mem_singleton_iff]
    have hlt : (∃ f, ((f = a ∨ f = b) ∨ f = c ∨ f = d) ∧ score f < t) ↔
        score a < t ∨ score b < t ∨ score c < t ∨ score d < t := by
      constructor
      · rintro ⟨f, (rfl | rfl) | (rfl | rfl), h⟩ <;> simp [h]
      · rintro (h | h | h | h)
        · exact ⟨a, Or.inl (Or.inl rfl), h⟩
        · exact ⟨b, Or.inl (Or.inr rfl), h⟩
        · exact ⟨c, Or.inr (Or.inl rfl), h⟩
        · exact ⟨d, Or.inr (Or.inr rfl), h⟩
    have hge : (∃ f, ((f = a ∨ f = b) ∨ f = c ∨ f = d) ∧ t ≤ score f) ↔
        t ≤ score a ∨ t ≤ score b ∨ t ≤ score c ∨ t ≤ score d := by
      constructor
      · rintro ⟨f, (rfl | rfl) | (rfl | rfl), h⟩ <;> simp [h]
      · rintro (h | h | h | h)
        · exact ⟨a, Or.inl (Or.inl rfl), h⟩
        · exact ⟨b, Or.inl (Or.inr rfl), h⟩
        · exact ⟨c, Or.inr (Or.inl rfl), h⟩
        · exact ⟨d, Or.inr (Or.inr rfl), h⟩
    rw [hlt, hge]
    by_cases ha : score a < t <;> by_cases hb : score b < t <;>
      by_cases hc : score c < t <;> by_cases hd : score d < t <;>
      simp [ha, hb, hc, hd, not_lt.mp]
  have hboth : G.PairStraddlesBoth score t e ↔
      (decide (score a < t) ≠ decide (score b < t) ∧
        decide (score c < t) ≠ decide (score d < t)) := by
    simp only [PairStraddlesBoth, hsrc, htgt, mem_insert_iff, mem_singleton_iff]
    by_cases ha : score a < t <;> by_cases hb : score b < t <;>
      by_cases hc : score c < t <;> by_cases hd : score d < t <;>
      simp [ha, hb, hc, hd, not_lt.mp]
  simp only [twoVertexCost]
  congr 1
  · split_ifs with h1 h2 h2
    · exact (hany.mp h2 h1).elim
    · rfl
    · rfl
    · exact (h2 (hany.mpr h1)).elim
  · split_ifs with h1 h2 h2
    · rfl
    · exact (h2 (hboth.mpr h1)).elim
    · exact (h1 (hboth.mp h2)).elim
    · rfl

/-- **Comparison with median edge scores.** For every matching `M` in a loopless cubic multigraph,
`matchingCost M score t` is at most the total number of vertices straddling `t`. -/
theorem matchingCost_le_edgeStraddles [Finite V] [Finite E] {α : Type*} [LinearOrder α]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → α) (t : α) :
    G.matchingCost M score t ≤ {v | G.EdgeStraddles score t v}.ncard := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  have hsum_ncard (P : V → Prop) [DecidablePred P] :
      {v | P v}.ncard = ∑ v : V, if P v then 1 else 0 := by
    have : {v | P v} = (Finset.univ.filter P : Set V) := by ext v; simp
    rw [this, ncard_coe_finset, Finset.card_filter]
  have hsum_encard (P : E → Prop) [DecidablePred P] :
      {e | P e}.ncard = ∑ e : E, if P e then 1 else 0 := by
    have : {e | P e} = (Finset.univ.filter P : Set E) := by ext e; simp
    rw [this, ncard_coe_finset, Finset.card_filter]
  set Mfin : Finset E := Finset.univ.filter (· ∈ M)
  have hMmem : ∀ e, e ∈ Mfin ↔ e ∈ M := fun e => by simp [Mfin]
  have hpart : ∑ v : V, (if G.EdgeStraddles score t v then 1 else 0) =
      (∑ v : V, if v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v then 1 else 0) +
      ∑ e ∈ Mfin, ((if G.EdgeStraddles score t (G.src e) then 1 else 0) +
        (if G.EdgeStraddles score t (G.tgt e) then 1 else 0)) := by
    have hsplit : ∑ v : V, (if G.EdgeStraddles score t v then 1 else 0) =
        (∑ v : V, if v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v then 1 else 0) +
        (∑ v : V, if v ∈ G.matchedVertices M then
          (if G.EdgeStraddles score t v then 1 else 0) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v ∈ G.matchedVertices M <;> by_cases hs : G.EdgeStraddles score t v <;>
        simp [hv, hs]
    rw [hsplit]
    congr 1
    let g : V → ℕ := fun v => if G.EdgeStraddles score t v then 1 else 0
    have hbi : Finset.univ.filter (· ∈ G.matchedVertices M) =
        Mfin.biUnion fun e => ({G.src e, G.tgt e} : Finset V) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, matchedVertices, mem_ofPred_eq,
        Finset.mem_biUnion, hMmem, Finset.mem_insert, Finset.mem_singleton, mem_incidenceSet]
      constructor
      · rintro ⟨e, he, h | h⟩ <;> exact ⟨e, he, by simp [h]⟩
      · rintro ⟨e, he, h | h⟩ <;> exact ⟨e, he, by simp [h]⟩
    have hdisj : (Mfin : Set E).PairwiseDisjoint
        (fun e => ({G.src e, G.tgt e} : Finset V)) := by
      intro e he f hf hne
      exact Finset.disjoint_left.mpr fun u hu hv => by
        have heM : e ∈ M := by simpa [Mfin] using he
        have hfM : f ∈ M := by simpa [Mfin] using hf
        exact disjoint_left.mp (hM heM hfM hne) (by simpa using hu) (by simpa using hv)
    rw [← Finset.sum_filter, hbi, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun e _ => ?_
    exact Finset.sum_pair (hloop e)
  rw [matchingCost, hsum_ncard, hsum_encard, hsum_encard, hsum_ncard, hpart]
  have hmerge :
      (∑ e : E, if e ∈ M ∧ G.PairStraddlesAny score t e then 1 else 0) +
      (∑ e : E, if e ∈ M ∧ G.PairStraddlesBoth score t e then 1 else 0) =
      ∑ e ∈ Mfin, ((if G.PairStraddlesAny score t e then 1 else 0) +
        (if G.PairStraddlesBoth score t e then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    simp only [Mfin, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : e ∈ M <;> simp [he]
  rw [add_assoc, hmerge]
  refine Nat.add_le_add_left (Finset.sum_le_sum fun e he => ?_) _
  have hns : (G.incidenceSet (G.src e) \ {e}).ncard = 2 :=
    ncard_sdiff_singleton_eq_two (h3 _) (Or.inl rfl)
  have hnt : (G.incidenceSet (G.tgt e) \ {e}).ncard = 2 :=
    ncard_sdiff_singleton_eq_two (h3 _) (Or.inr rfl)
  obtain ⟨a, b, _, hsrc⟩ := ncard_eq_two.mp hns
  obtain ⟨c, d, _, htgt⟩ := ncard_eq_two.mp hnt
  have hinc_s : G.incidenceSet (G.src e) = {a, b, e} := by
    ext f
    have hmem : e ∈ G.incidenceSet (G.src e) := Or.inl rfl
    have hdiff : f ∈ G.incidenceSet (G.src e) \ {e} ↔ f = a ∨ f = b := by
      simp [hsrc]
    constructor
    · intro hf
      by_cases hfe : f = e
      · simp [hfe]
      · rcases hdiff.mp ⟨hf, hfe⟩ with rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl)
      · exact (hdiff.mpr (Or.inl rfl)).1
      · exact (hdiff.mpr (Or.inr rfl)).1
      · exact hmem
  have hinc_t : G.incidenceSet (G.tgt e) = {c, d, e} := by
    ext f
    have hmem : e ∈ G.incidenceSet (G.tgt e) := Or.inr rfl
    have hdiff : f ∈ G.incidenceSet (G.tgt e) \ {e} ↔ f = c ∨ f = d := by
      simp [htgt]
    constructor
    · intro hf
      by_cases hfe : f = e
      · simp [hfe]
      · rcases hdiff.mp ⟨hf, hfe⟩ with rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl)
      · exact (hdiff.mpr (Or.inl rfl)).1
      · exact (hdiff.mpr (Or.inr rfl)).1
      · exact hmem
  rw [← twoVertexCost_eq_pairStraddles score t hsrc htgt,
    ← starCost_eq_ite_edgeStraddles score t hinc_s,
    ← starCost_eq_ite_edgeStraddles score t hinc_t]
  exact twoVertexCost_le_starCost_add _ _ _ _ _

/-- **Threshold cut bound.** For every threshold `t`, the cut of `{v | matchingKey G M score v < t}`
in a loopless cubic multigraph (parallel edges allowed) is at most `G.matchingCost M score t`. -/
theorem ncard_edgeCut_threshold_le_matchingCost [Finite V] [Finite E]
    {α : Type*} [LinearOrder α] [Inhabited α]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → α) (t : α) :
    (G.edgeCut {v | G.matchingKey M score v < t}).ncard ≤ G.matchingCost M score t := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  let col : V → Bool := fun v => decide (G.matchingKey M score v < t)
  let ecol : E → Bool := fun e => decide (score e < t)
  let Mfin : Finset E := Finset.univ.filter (· ∈ M)
  have hcut : (G.edgeCut {v | G.matchingKey M score v < t}).ncard =
      ∑ e : E, boolDiff (col (G.src e)) (col (G.tgt e)) := by
    have hset : G.edgeCut {v | G.matchingKey M score v < t} =
        ((Finset.univ.filter (· ∈ G.edgeCut {v | G.matchingKey M score v < t})) : Set E) := by
      ext e; simp
    rw [hset, ncard_coe_finset, Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [col, boolDiff, mem_edgeCut, mem_ofPred_eq]
    by_cases hs : G.matchingKey M score (G.src e) < t <;>
      by_cases ht : G.matchingKey M score (G.tgt e) < t <;>
      simp [hs, ht]
  -- Split edges into matched edges `M` (kept directly) and unmatched edges (split by triangle
  -- inequality across their endpoint incidences).
  have hstep1 : ∑ e : E, boolDiff (col (G.src e)) (col (G.tgt e)) ≤
      (∑ e ∈ Mfin, boolDiff (col (G.src e)) (col (G.tgt e))) +
      ∑ e ∈ Mfinᶜ, (boolDiff (col (G.src e)) (ecol e) + boolDiff (col (G.tgt e)) (ecol e)) := by
    have hpart := (Finset.sum_add_sum_compl Mfin
      (fun e => boolDiff (col (G.src e)) (col (G.tgt e)))).symm
    rw [hpart]
    exact Nat.add_le_add_left (Finset.sum_le_sum fun e _ => boolDiff_triangle _ _ (ecol e)) _
  -- Group the endpoint incidences of unmatched edges by vertex.
  have hgroup :
      ∑ e ∈ Mfinᶜ, (boolDiff (col (G.src e)) (ecol e) + boolDiff (col (G.tgt e)) (ecol e)) =
      ∑ v : V, ∑ e ∈ Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v),
        boolDiff (col v) (ecol e) := by
    have hinner (e : E) :
        boolDiff (col (G.src e)) (ecol e) + boolDiff (col (G.tgt e)) (ecol e) =
        ∑ v : V, if e ∈ G.incidenceSet v then boolDiff (col v) (ecol e) else 0 := by
      have hpair : (Finset.univ.filter fun v : V => e ∈ G.incidenceSet v) =
          {G.src e, G.tgt e} := by
        ext v; simp [mem_incidenceSet, eq_comm]
      rw [← Finset.sum_filter, hpair, Finset.sum_pair (hloop e)]
    calc ∑ e ∈ Mfinᶜ, (boolDiff (col (G.src e)) (ecol e) + boolDiff (col (G.tgt e)) (ecol e))
        = ∑ e : E, if e ∉ M then
            ∑ v : V, if e ∈ G.incidenceSet v then boolDiff (col v) (ecol e) else 0 else 0 := by
          have hmf : Mfinᶜ = Finset.univ.filter (· ∉ M) := by
            ext e; simp [Mfin]
          rw [hmf, Finset.sum_filter]
          refine Finset.sum_congr rfl fun e _ => ?_
          by_cases he : e ∈ M <;> simp [he, hinner]
      _ = ∑ e : E, ∑ v : V, if e ∉ M ∧ e ∈ G.incidenceSet v then
            boolDiff (col v) (ecol e) else 0 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          by_cases he : e ∈ M <;> simp [he]
      _ = ∑ v : V, ∑ e : E, if e ∉ M ∧ e ∈ G.incidenceSet v then
            boolDiff (col v) (ecol e) else 0 := Finset.sum_comm
      _ = ∑ v : V, ∑ e ∈ Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v),
            boolDiff (col v) (ecol e) := by
          refine Finset.sum_congr rfl fun v _ => (Finset.sum_filter _ _).symm
  -- Split vertex sum into unmatched vertices and matched pairs.
  let vsum (v : V) : ℕ :=
    ∑ e ∈ Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v), boolDiff (col v) (ecol e)
  have hbi : Finset.univ.filter (· ∈ G.matchedVertices M) =
      Mfin.biUnion fun e => ({G.src e, G.tgt e} : Finset V) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, matchedVertices, mem_ofPred_eq,
      Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, mem_incidenceSet, Mfin]
    constructor
    · rintro ⟨e, he, h | h⟩ <;> exact ⟨e, he, by simp [h]⟩
    · rintro ⟨e, he, h | h⟩ <;> exact ⟨e, he, by simp [h]⟩
  have hdisj : (Mfin : Set E).PairwiseDisjoint
      (fun e => ({G.src e, G.tgt e} : Finset V)) := by
    intro e he f hf hne
    exact Finset.disjoint_left.mpr fun u hu hv => by
      have heM : e ∈ M := by simpa [Mfin] using he
      have hfM : f ∈ M := by simpa [Mfin] using hf
      exact disjoint_left.mp (hM heM hfM hne) (by simpa using hu) (by simpa using hv)
  have hvsplit : ∑ v : V, vsum v =
      (∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), vsum v) +
      ∑ e ∈ Mfin, (vsum (G.src e) + vsum (G.tgt e)) := by
    have hcompl := (Finset.sum_add_sum_compl (Finset.univ.filter (· ∈ G.matchedVertices M))
      vsum).symm
    have hcf : (Finset.univ.filter (· ∈ G.matchedVertices M))ᶜ =
        Finset.univ.filter (· ∉ G.matchedVertices M) := by ext v; simp
    rw [hcompl, hcf, add_comm, hbi, Finset.sum_biUnion hdisj]
    congr 1
    exact Finset.sum_congr rfl fun e _ => Finset.sum_pair (hloop e)
  -- Evaluate `vsum` at every unpaired vertex (`starCost`).
  have hsingle : ∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), vsum v =
      {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v}.ncard := by
    have hnc : {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v}.ncard =
        ∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M),
          if G.EdgeStraddles score t v then 1 else 0 := by
      have hset : {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles score t v} =
          ((Finset.univ.filter fun v => v ∉ G.matchedVertices M ∧
            G.EdgeStraddles score t v) : Set V) := by ext v; simp
      rw [hset, ncard_coe_finset, Finset.card_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v ∈ G.matchedVertices M <;> simp [hv]
    rw [hnc]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' : v ∉ G.matchedVertices M := (Finset.mem_filter.mp hv).2
    obtain ⟨e₀, e₁, e₂, h01, h02, h12, hinc, hkey⟩ := matchingKey_unmatched h3 score hv'
    have hfilt : Finset.univ.filter (fun e => e ∉ M ∧ e ∈ G.incidenceSet v) = {e₀, e₁, e₂} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro ⟨_, hmem⟩; rwa [hinc] at hmem
      · intro hmem
        have hmem' : e ∈ G.incidenceSet v := by rwa [hinc]
        refine ⟨fun heM => hv' ⟨e, heM, hmem'⟩, hmem'⟩
    dsimp [vsum]
    rw [hfilt, Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
      Finset.sum_singleton]
    have hcol : col v = decide (median3 (score e₀) (score e₁) (score e₂) < t) := by
      simp [col, hkey]
    rw [← starCost_eq_ite_edgeStraddles score t hinc, ← starEnergy_median3]
    simp only [starEnergy, boolDiff, ecol, hcol, add_assoc]
  -- Evaluate each matched edge pair (`twoVertexCost`).
  have hpair : ∑ e ∈ Mfin, (boolDiff (col (G.src e)) (col (G.tgt e)) +
        (vsum (G.src e) + vsum (G.tgt e))) =
      {e | e ∈ M ∧ G.PairStraddlesAny score t e}.ncard +
        {e | e ∈ M ∧ G.PairStraddlesBoth score t e}.ncard := by
    have hncA : {e | e ∈ M ∧ G.PairStraddlesAny score t e}.ncard =
        ∑ e ∈ Mfin, if G.PairStraddlesAny score t e then 1 else 0 := by
      have hset : {e | e ∈ M ∧ G.PairStraddlesAny score t e} =
          ((Finset.univ.filter fun e => e ∈ M ∧ G.PairStraddlesAny score t e) : Set E) := by
        ext e; simp
      rw [hset, ncard_coe_finset, Finset.card_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e ∈ M <;> simp [he]
    have hncB : {e | e ∈ M ∧ G.PairStraddlesBoth score t e}.ncard =
        ∑ e ∈ Mfin, if G.PairStraddlesBoth score t e then 1 else 0 := by
      have hset : {e | e ∈ M ∧ G.PairStraddlesBoth score t e} =
          ((Finset.univ.filter fun e => e ∈ M ∧ G.PairStraddlesBoth score t e) : Set E) := by
        ext e; simp
      rw [hset, ncard_coe_finset, Finset.card_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e ∈ M <;> simp [he]
    rw [hncA, hncB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    have heM : e ∈ M := (Finset.mem_filter.mp he).2
    have hns : (G.incidenceSet (G.src e) \ {e}).ncard = 2 :=
      ncard_sdiff_singleton_eq_two (h3 _) (Or.inl rfl)
    have hnt : (G.incidenceSet (G.tgt e) \ {e}).ncard = 2 :=
      ncard_sdiff_singleton_eq_two (h3 _) (Or.inr rfl)
    obtain ⟨a, b, hab, hsrc⟩ := ncard_eq_two.mp hns
    obtain ⟨c, d, hcd, htgt⟩ := ncard_eq_two.mp hnt
    have hfil_s : Finset.univ.filter (fun f => f ∉ M ∧ f ∈ G.incidenceSet (G.src e)) =
        {a, b} := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have hd : f ∈ G.incidenceSet (G.src e) \ {e} ↔ f = a ∨ f = b := by simp [hsrc]
      rw [← hd]
      constructor
      · exact fun ⟨hfM, hfi⟩ => ⟨hfi, fun hfe => hfM (hfe ▸ heM)⟩
      · exact fun ⟨hfi, hfe⟩ => ⟨fun hfM => hfe (eq_of_mem_isMatching hM hfM heM hfi (Or.inl rfl)),
          hfi⟩
    have hfil_t : Finset.univ.filter (fun f => f ∉ M ∧ f ∈ G.incidenceSet (G.tgt e)) =
        {c, d} := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have hd : f ∈ G.incidenceSet (G.tgt e) \ {e} ↔ f = c ∨ f = d := by simp [htgt]
      rw [← hd]
      constructor
      · exact fun ⟨hfM, hfi⟩ => ⟨hfi, fun hfe => hfM (hfe ▸ heM)⟩
      · exact fun ⟨hfi, hfe⟩ => ⟨fun hfM => hfe (eq_of_mem_isMatching hM hfM heM hfi (Or.inr rfl)),
          hfi⟩
    obtain ⟨hks, hkt⟩ := matchingKey_matched hM hloop h3 score heM hsrc htgt
    have hsval : vsum (G.src e) =
        boolDiff (col (G.src e)) (ecol a) + boolDiff (col (G.src e)) (ecol b) := by
      dsimp [vsum]; rw [hfil_s, Finset.sum_pair hab]
    have htval : vsum (G.tgt e) =
        boolDiff (col (G.tgt e)) (ecol c) + boolDiff (col (G.tgt e)) (ecol d) := by
      dsimp [vsum]; rw [hfil_t, Finset.sum_pair hcd]
    rw [hsval, htval, ← twoVertexCost_eq_pairStraddles score t hsrc htgt,
      ← twoVertexEnergy_pairKey (score a) (score b) (score c) (score d) t]
    simp only [twoVertexEnergy, col, ecol, boolDiff, hks, hkt]
    omega
  rw [hcut]
  calc ∑ e : E, boolDiff (col (G.src e)) (col (G.tgt e))
      ≤ (∑ e ∈ Mfin, boolDiff (col (G.src e)) (col (G.tgt e))) +
          ∑ e ∈ Mfinᶜ, (boolDiff (col (G.src e)) (ecol e) + boolDiff (col (G.tgt e)) (ecol e)) :=
        hstep1
    _ = (∑ v ∈ Finset.univ.filter (· ∉ G.matchedVertices M), vsum v) +
          ∑ e ∈ Mfin, (boolDiff (col (G.src e)) (col (G.tgt e)) +
            (vsum (G.src e) + vsum (G.tgt e))) := by
        rw [hgroup]
        change (∑ e ∈ Mfin, boolDiff (col (G.src e)) (col (G.tgt e))) + ∑ v : V, vsum v = _
        rw [hvsplit, Finset.sum_add_distrib, add_left_comm]
        simp only [Finset.sum_add_distrib]
    _ = G.matchingCost M score t := by
        rw [hsingle, hpair, matchingCost, add_assoc]

/-! ### Prefix cuts and grid layout bound -/

/-- Every vertex whose `matchingKey` lies in a predicate `p` is either an endpoint or the `M`-mate
of an endpoint of some edge whose score satisfies `p`. Thus each such edge produces at most `4`
vertices. -/
private theorem ncard_matchingKey_pred_le [Finite V] [Finite E]
    {α : Type*} [LinearOrder α] [Inhabited α]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → α) (p : α → Prop) :
    {v | p (G.matchingKey M score v)}.ncard ≤ 4 * {e | p (score e)}.ncard := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  let Efin : Finset E := Finset.univ.filter fun e => p (score e)
  let hit (e : E) : Finset V :=
    {G.src e, G.tgt e, G.mate M (G.src e), G.mate M (G.tgt e)}
  have hsub : (Finset.univ.filter fun v => p (G.matchingKey M score v)) ⊆ Efin.biUnion hit := by
    intro v hv
    have hpv : p (G.matchingKey M score v) := (Finset.mem_filter.mp hv).2
    by_cases hmat : v ∈ G.matchedVertices M
    · obtain ⟨e, heM, hev⟩ := hmat
      have hns : (G.incidenceSet (G.src e) \ {e}).ncard = 2 :=
        ncard_sdiff_singleton_eq_two (h3 _) (Or.inl rfl)
      have hnt : (G.incidenceSet (G.tgt e) \ {e}).ncard = 2 :=
        ncard_sdiff_singleton_eq_two (h3 _) (Or.inr rfl)
      obtain ⟨a, b, hab, hsrc⟩ := ncard_eq_two.mp hns
      obtain ⟨c, d, hcd, htgt⟩ := ncard_eq_two.mp hnt
      obtain ⟨hks, hkt⟩ := matchingKey_matched hM hloop h3 score heM hsrc htgt
      have hinc_a : a ∈ G.incidenceSet (G.src e) :=
        ((show a ∈ G.incidenceSet (G.src e) \ {e} by rw [hsrc]; simp)).1
      have hinc_b : b ∈ G.incidenceSet (G.src e) :=
        ((show b ∈ G.incidenceSet (G.src e) \ {e} by rw [hsrc]; simp)).1
      have hinc_c : c ∈ G.incidenceSet (G.tgt e) :=
        ((show c ∈ G.incidenceSet (G.tgt e) \ {e} by rw [htgt]; simp)).1
      have hinc_d : d ∈ G.incidenceSet (G.tgt e) :=
        ((show d ∈ G.incidenceSet (G.tgt e) \ {e} by rw [htgt]; simp)).1
      have hmem_s (f : E) (hf : f ∈ G.incidenceSet (G.src e)) : G.src e ∈ hit f := by
        rcases hf with h | h <;> simp [hit, h]
      have hmem_t (f : E) (hf : f ∈ G.incidenceSet (G.tgt e)) : G.tgt e ∈ hit f := by
        rcases hf with h | h <;> simp [hit, h]
      have hmem_ms (f : E) (hf : f ∈ G.incidenceSet (G.tgt e)) : G.src e ∈ hit f := by
        rcases hf with h | h
        · simp [hit, h, mate_tgt hM hloop heM]
        · simp [hit, h, mate_tgt hM hloop heM]
      have hmem_mt (f : E) (hf : f ∈ G.incidenceSet (G.src e)) : G.tgt e ∈ hit f := by
        rcases hf with h | h
        · simp [hit, h, mate_src hM heM]
        · simp [hit, h, mate_src hM heM]
      rcases hev with hvs | hvt
      · rw [← hvs, hks] at hpv
        rw [← hvs]
        rcases pairKey_mem (score a) (score b) (score c) (score d) with h | h | h | h
        · exact Finset.mem_biUnion.mpr
            ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hmem_s a hinc_a⟩
        · exact Finset.mem_biUnion.mpr
            ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hmem_s b hinc_b⟩
        · exact Finset.mem_biUnion.mpr
            ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hmem_ms c hinc_c⟩
        · exact Finset.mem_biUnion.mpr
            ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hmem_ms d hinc_d⟩
      · rw [← hvt, hkt] at hpv
        rw [← hvt]
        rcases pairKey_mem (score c) (score d) (score a) (score b) with h | h | h | h
        · exact Finset.mem_biUnion.mpr
            ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hmem_t c hinc_c⟩
        · exact Finset.mem_biUnion.mpr
            ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hmem_t d hinc_d⟩
        · exact Finset.mem_biUnion.mpr
            ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hmem_mt a hinc_a⟩
        · exact Finset.mem_biUnion.mpr
            ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩, hmem_mt b hinc_b⟩
    · obtain ⟨e₀, e₁, e₂, _, _, _, hinc, hkey⟩ := matchingKey_unmatched h3 score hmat
      rw [hkey] at hpv
      have hmed : median3 (score e₀) (score e₁) (score e₂) = score e₀ ∨
          median3 (score e₀) (score e₁) (score e₂) = score e₁ ∨
          median3 (score e₀) (score e₁) (score e₂) = score e₂ := by
        unfold median3
        rcases max_choice (min (score e₀) (score e₁)) (min (max (score e₀) (score e₁)) (score e₂))
          with h | h
        · rw [h]; rcases min_choice (score e₀) (score e₁) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
        · rw [h]; rcases min_choice (max (score e₀) (score e₁)) (score e₂) with h' | h'
          · rw [h']; rcases max_choice (score e₀) (score e₁) with h'' | h''
            · exact Or.inl h''
            · exact Or.inr (Or.inl h'')
          · exact Or.inr (Or.inr h')
      have hmem_v (f : E) (hf : f ∈ G.incidenceSet v) : v ∈ hit f := by
        rcases hf with h | h <;> simp [hit, h]
      rcases hmed with h | h | h
      · exact Finset.mem_biUnion.mpr
          ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩,
            hmem_v e₀ (by rw [hinc]; simp)⟩
      · exact Finset.mem_biUnion.mpr
          ⟨e₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩,
            hmem_v e₁ (by rw [hinc]; simp)⟩
      · exact Finset.mem_biUnion.mpr
          ⟨e₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hpv⟩,
            hmem_v e₂ (by rw [hinc]; simp)⟩
  have hcard_hit (e : E) : (hit e).card ≤ 4 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
    refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
    simp
  have h1 : {v | p (G.matchingKey M score v)}.ncard =
      (Finset.univ.filter fun v => p (G.matchingKey M score v)).card := by
    have : {v | p (G.matchingKey M score v)} =
        ((Finset.univ.filter fun v => p (G.matchingKey M score v)) : Set V) := by ext v; simp
    rw [this, ncard_coe_finset]
  have h2 : {e | p (score e)}.ncard = Efin.card := by
    have : {e | p (score e)} = (Efin : Set E) := by ext e; simp [Efin]
    rw [this, ncard_coe_finset]
  rw [h1, h2]
  calc (Finset.univ.filter fun v => p (G.matchingKey M score v)).card
      ≤ (Efin.biUnion hit).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ Efin, (hit e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ Efin, 4 := Finset.sum_le_sum fun e _ => hcard_hit e
    _ = 4 * Efin.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Adding vertices `P \ P₀` to a vertex set `P₀ ⊆ P` increases the edge cut by at most
`3 * (P \ P₀).ncard`. -/
private theorem ncard_edgeCut_le_of_subset [Finite V] [Finite E]
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {P₀ P : Set V} (hsub : P₀ ⊆ P) :
    (G.edgeCut P).ncard ≤ (G.edgeCut P₀).ncard + 3 * (P \ P₀).ncard := by
  have he : G.edgeCut P ⊆ G.edgeCut P₀ ∪ G.touching (P \ P₀) := by
    intro e heP
    by_cases ht : e ∈ G.touching (P \ P₀)
    · exact Or.inr ht
    · left
      rw [mem_touching, not_or] at ht
      have hsrc : G.src e ∈ P ↔ G.src e ∈ P₀ :=
        ⟨fun h => by_contra fun hn => ht.1 ⟨h, hn⟩, fun h => hsub h⟩
      have htgt : G.tgt e ∈ P ↔ G.tgt e ∈ P₀ :=
        ⟨fun h => by_contra fun hn => ht.2 ⟨h, hn⟩, fun h => hsub h⟩
      simpa [mem_edgeCut, hsrc, htgt] using heP
  exact (ncard_le_ncard he).trans ((ncard_union_le _ _).trans
    (Nat.add_le_add_left (G.ncard_touching_le (fun v => (h3 v).le) _) _))

/-- **Cut bound for a threshold prefix.** For any set `P` separated by a threshold `m` of
`matchingKey`, its cut size is bounded by a lower tail, upper tail, or the matching cost at the
grid threshold below `m` plus `12` times the window edge count. -/
theorem ncard_edgeCut_le_matchingCost_add [Finite V] [Finite E]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → ℝ)
    {P : Set V} {m : ℝ}
    (hP : ∀ v ∈ P, G.matchingKey M score v ≤ m)
    (hPc : ∀ v ∉ P, m ≤ G.matchingKey M score v)
    {a δ : ℝ} (hδ : 0 < δ) {K : ℕ} {B : ℝ}
    (low : 12 * ({e | score e < a}.ncard : ℝ) ≤ B)
    (high : 12 * ({e | a + K * δ ≤ score e}.ncard : ℝ) ≤ B)
    (mid : ∀ i < K, (G.matchingCost M score (a + i * δ) : ℝ) +
      12 * ({e | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ((G.edgeCut P).ncard : ℝ) ≤ B := by
  rcases lt_or_ge m a with hlow | hge
  · have hsub : P ⊆ {v | G.matchingKey M score v < a} := fun v hv => (hP v hv).trans_lt hlow
    have hcut : (G.edgeCut P).ncard ≤ 12 * {e | score e < a}.ncard := by
      calc (G.edgeCut P).ncard
          ≤ (G.touching P).ncard := ncard_le_ncard (G.edgeCut_subset_touching P)
        _ ≤ 3 * P.ncard := G.ncard_touching_le (fun v => (h3 v).le) P
        _ ≤ 3 * {v | G.matchingKey M score v < a}.ncard :=
            Nat.mul_le_mul_left 3 (ncard_le_ncard hsub)
        _ ≤ 3 * (4 * {e | score e < a}.ncard) :=
            Nat.mul_le_mul_left 3 (ncard_matchingKey_pred_le hloop h3 hM score (· < a))
        _ = 12 * {e | score e < a}.ncard := by ring
    exact (Nat.cast_le.mpr hcut).trans (by push_cast; exact low)
  set top := a + K * δ
  rcases le_or_gt top m with htop | hlt
  · have hsub : Pᶜ ⊆ {v | top ≤ G.matchingKey M score v} := fun v hv => htop.trans (hPc v hv)
    have hcompl : G.edgeCut P = G.edgeCut Pᶜ := by
      ext e; simp [mem_edgeCut, not_iff_not]
    have hcut : (G.edgeCut P).ncard ≤ 12 * {e | top ≤ score e}.ncard := by
      rw [hcompl]
      calc (G.edgeCut Pᶜ).ncard
          ≤ (G.touching Pᶜ).ncard := ncard_le_ncard (G.edgeCut_subset_touching Pᶜ)
        _ ≤ 3 * Pᶜ.ncard := G.ncard_touching_le (fun v => (h3 v).le) Pᶜ
        _ ≤ 3 * {v | top ≤ G.matchingKey M score v}.ncard :=
            Nat.mul_le_mul_left 3 (ncard_le_ncard hsub)
        _ ≤ 3 * (4 * {e | top ≤ score e}.ncard) :=
            Nat.mul_le_mul_left 3 (ncard_matchingKey_pred_le hloop h3 hM score (top ≤ ·))
        _ = 12 * {e | top ≤ score e}.ncard := by ring
    exact (Nat.cast_le.mpr hcut).trans (by push_cast; exact high)
  obtain ⟨i, hiK, ht, ht'⟩ := exists_grid_index hδ hge hlt
  set t := a + i * δ
  set t' := a + (i + 1) * δ
  set P₀ : Set V := {v | G.matchingKey M score v < t}
  have hP₀ : P₀ ⊆ P := fun v hv =>
    by_contra fun hvn => not_lt.mpr (ht.trans (hPc v hvn)) hv
  have hdiff : P \ P₀ ⊆ {v | t ≤ G.matchingKey M score v ∧ G.matchingKey M score v < t'} :=
    fun v ⟨hv, hvn⟩ => ⟨not_lt.mp hvn, (hP v hv).trans_lt ht'⟩
  have hcut : (G.edgeCut P).ncard ≤ G.matchingCost M score t +
      12 * {e | t ≤ score e ∧ score e < t'}.ncard := by
    calc (G.edgeCut P).ncard
        ≤ (G.edgeCut P₀).ncard + 3 * (P \ P₀).ncard := ncard_edgeCut_le_of_subset h3 hP₀
      _ ≤ G.matchingCost M score t +
          3 * {v | t ≤ G.matchingKey M score v ∧ G.matchingKey M score v < t'}.ncard :=
          Nat.add_le_add (ncard_edgeCut_threshold_le_matchingCost hloop h3 hM score t)
            (Nat.mul_le_mul_left 3 (ncard_le_ncard hdiff))
      _ ≤ G.matchingCost M score t +
          3 * (4 * {e | t ≤ score e ∧ score e < t'}.ncard) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 3
            (ncard_matchingKey_pred_le hloop h3 hM score fun x => t ≤ x ∧ x < t')) _
      _ = G.matchingCost M score t + 12 * {e | t ≤ score e ∧ score e < t'}.ncard := by ring
  calc ((G.edgeCut P).ncard : ℝ)
      ≤ (G.matchingCost M score t : ℝ) +
          12 * ({e | t ≤ score e ∧ score e < t'}.ncard : ℝ) := by exact_mod_cast hcut
    _ ≤ B := mid i hiK

/-- **The matched-edge pair-insertion layout.** Given a loopless cubic multigraph (parallel edges
allowed), any matching `M`, any edge scores `score : E → ℝ`, and a grid `a, a + δ, ..., a + K δ`,
sorting vertices by `matchingKey` gives a layout whose width is bounded by the worst tail bound
`12 * tail` and window bound `matchingCost + 12 * window`. -/
theorem exists_width_le_of_matching_edgeScore [Finite V] [Finite E]
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {M : Set E} (hM : G.IsMatching M) (score : E → ℝ) {a δ : ℝ} (hδ : 0 < δ) (K : ℕ) {B : ℝ}
    (low : 12 * ({e | score e < a}.ncard : ℝ) ≤ B)
    (high : 12 * ({e | a + K * δ ≤ score e}.ncard : ℝ) ≤ B)
    (mid : ∀ i < K, (G.matchingCost M score (a + i * δ) : ℝ) +
      12 * ({e | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ∃ π : Layout V, (G.width π : ℝ) ≤ B := by
  obtain ⟨π, hπ⟩ := Layout.exists_threshold (G.matchingKey M score)
  refine ⟨π, G.width_le_of_ncard_frontier_le π (le_trans (by positivity) low) fun t ht => ?_⟩
  obtain ⟨m, hP, hPc⟩ := hπ t ht
  exact ncard_edgeCut_le_matchingCost_add hloop h3 hM score hP hPc hδ low high mid

end Multigraph

end Cslib.Circuits.Frontier
