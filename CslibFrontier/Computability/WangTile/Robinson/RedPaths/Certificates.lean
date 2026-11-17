/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.RedPaths.Basic
import Mathlib.Tactic.FinCases

/-!
# Checked red-path connectivity through substitution

Finite predecessor forests certify red-port connectivity in every corrected Robinson
parent's two-substitution block. Each row stores one edge to an earlier row, with its
crossing parity. The checks cover every live port, including the central base region;
the same forests certify the even east and north connectors. No search algorithm is
part of the logical interface.

## Main definitions

* `refinedPort`: side-sensitive port embedding through two substitutions.
* `sources`: new-cycle and inherited sources for local coverage.

## Main results

* `livePortPath`: live old ports reach their refined images
  with even crossing parity.
* `exists_boundedPath`: every live fine port is reached
  from the new cycle or an inherited live old port.
* `odd_base_exists_boundedPath`: every live port in the depth-four odd base has a
  bounded path from a cycle corner.
* `Path.refine`: arbitrary red paths preserve parity through
  two substitutions.

## References

The corrected construction is after [JeandelVanier2020], §§3.2–3.3, Figures 16–18
(manuscript pp. 26–28).
Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`, `RedShadeGraphCertificate`,
`RedShadeGraphLocalCoverage`, `RedShadeGraphRefinement`, `RedShadeGraphPathRefinement`,
`RedShadeGraphTranslation`, `RedShadeGraphCoarsening` and `CanonicalOddShadeBase`.
The predecessor compression is original; its finite input derives from that revision's
`RedShadeGraphPathWitnesses` (including `oddNodes`) and keeps every port and crossing
parity unchanged.
-/

public section
namespace Cslib.WangTile.Robinson

/-- The two exits of a quarter macrocell needing a connector. -/
private inductive ExitSide where
  | east | north
  deriving DecidableEq

private instance : Fintype ExitSide :=
  Fintype.ofList [.east, .north] (by intro side; cases side <;> simp)

/-- Constant grid with the specified parent tile. -/
@[expose] def coarseGrid (parent : Index) : Nat → Nat → Index := fun _ _ => parent

/-- The grid obtained by substituting a constant parent grid twice. -/
@[expose] def fineGrid (parent : Index) : Nat → Nat → Index :=
  iterateRefine 2 (coarseGrid parent)

/-- Two substitution steps depend only on the containing parent and local block coordinates. -/
theorem iterateRefine_two_local (grid : ℕ → ℕ → Index) (x y : ℕ) :
    iterateRefine 2 grid x y = fineGrid (grid (x / 4) (y / 4)) (x % 4) (y % 4) := by
  have coords (z : ℕ) : z / 2 / 2 = z / 4 ∧
      (z % 4) / 2 = z / 2 % 2 ∧ (z % 4) % 2 = z % 2 := by omega
  obtain ⟨hx₀, hx₁, hx₂⟩ := coords x
  obtain ⟨hy₀, hy₁, hy₂⟩ := coords y
  simp only [iterateRefine, refineIndexGrid, fineGrid, coarseGrid,
    hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, Nat.mod_mod]

/-- A live exit of the old southwest quarter block. -/
private def internalPort (side : ExitSide) (offset : Nat) : Port :=
  match side with
  | .east => ⟨1, offset, .east⟩
  | .north => ⟨offset, 1, .north⟩

/-- The corresponding exit on the boundary of the substituted macrocell. -/
private def externalPort (side : ExitSide) (offset : Nat) : Port :=
  match side with
  | .east => ⟨7, offset, .east⟩
  | .north => ⟨offset, 7, .north⟩

/-- Embed an old quarter coordinate into its macrocell's southwest two positions. -/
@[expose] def sparseCoordinate (coordinate : Nat) : Nat :=
  8 * (coordinate / 2) + coordinate % 2

/-- The sparse embedded old port, retaining its side. -/
@[expose] def sparsePort (port : Port) : Port :=
  ⟨sparseCoordinate port.x, sparseCoordinate port.y, port.side⟩

/-- All ports in the specified quarter rectangle. -/
@[expose] def portsIn (width height : Nat) : List Port :=
  (List.range height).flatMap fun y => (List.range width).flatMap fun x =>
    [⟨x, y, .west⟩, ⟨x, y, .east⟩, ⟨x, y, .south⟩, ⟨x, y, .north⟩]

/-- A port is listed in a rectangle exactly when both its coordinates are in bounds. -/
theorem mem_portsIn_iff {p : Port} {width height : Nat} :
    p ∈ portsIn width height ↔ PortInBounds p width height := by
  simp only [portsIn, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨y, hy, x, hx, rfl | rfl | rfl | rfl⟩ <;> exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    rcases p with ⟨px, py, side⟩
    refine ⟨py, hy, px, hx, ?_⟩
    cases side <;> simp

/-- A strict bottom-side port of the cycle created in a depth-two block. -/
@[expose] def cycleSource : Port := ⟨4, 3, .west⟩

/-- The new cycle source and the sparse copies of every live old port. -/
@[expose] def sources (parent : Index) : List Port :=
  cycleSource :: ((portsIn 2 2).filter (portPresent (coarseGrid parent))).map sparsePort

namespace RedPathCertificate

private inductive Kind where
  | horizontalMatch | verticalMatch | horizontal | vertical
  | westNorth | westSouth | eastNorth | eastSouth | crossing
  deriving DecidableEq

private structure Move where
  x : Nat
  y : Nat
  kind : Kind
  reverse : Bool

private def decodePort (width code : Nat) : Port :=
  ⟨code / 4 % width, code / 4 / width,
    match code % 4 with | 0 => .west | 1 => .east | 2 => .south | _ => .north⟩

private def decodeMove (width code : Nat) : Move :=
  ⟨code / 2 / 9 % width, code / 2 / 9 / width,
    match code / 2 % 9 with
    | 0 => .horizontalMatch | 1 => .verticalMatch | 2 => .horizontal | 3 => .vertical
    | 4 => .westNorth | 5 => .westSouth | 6 => .eastNorth | 7 => .eastSouth | _ => .crossing,
    code % 2 == 1⟩

private def Move.baseFirst (m : Move) : Port :=
  ⟨m.x, m.y, match m.kind with
    | .horizontalMatch | .eastNorth | .eastSouth => .east
    | .verticalMatch => .north | .vertical => .south | _ => .west⟩

private def Move.baseSecond (m : Move) : Port :=
  match m.kind with
  | .horizontalMatch => ⟨m.x + 1, m.y, .west⟩
  | .verticalMatch => ⟨m.x, m.y + 1, .south⟩
  | .horizontal => ⟨m.x, m.y, .east⟩
  | .vertical | .westNorth | .eastNorth => ⟨m.x, m.y, .north⟩
  | .westSouth | .eastSouth | .crossing => ⟨m.x, m.y, .south⟩

private def Move.first (m : Move) : Port := if m.reverse then m.baseSecond else m.baseFirst
private def Move.second (m : Move) : Port := if m.reverse then m.baseFirst else m.baseSecond
private def Move.parity (m : Move) : Bool := m.kind == .crossing

private def Move.valid (grid : Nat → Nat → Index) (m : Move) : Bool :=
  let component := componentAt grid m.x m.y
  let q := quadrantAt m.x m.y
  match m.kind with
  | .horizontalMatch | .verticalMatch => true
  | .horizontal => hasHorizontal component q | .vertical => hasVertical component q
  | .westNorth => cornerWest component q && cornerNorth component q
  | .westSouth => cornerWest component q && cornerSouth component q
  | .eastNorth => cornerEast component q && cornerNorth component q
  | .eastSouth => cornerEast component q && cornerSouth component q
  | .crossing => hasHorizontal component q && hasVertical component q

private theorem Move.link {grid : Nat → Nat → Index} (m : Move)
    (h : m.valid grid = true) : Link grid m.first m.second m.parity := by
  rcases m with ⟨x, y, kind, reverse⟩
  cases kind <;> cases reverse <;>
    simp only [Move.valid, Move.first, Move.second, Move.baseFirst,
      Move.baseSecond, Move.parity, Bool.false_eq_true, Bool.and_eq_true,
      beq_self_eq_true] at h ⊢
  · exact Link.horizontalMatch x y
  · exact Link.symm (Link.horizontalMatch x y)
  · exact Link.verticalMatch x y
  · exact Link.symm (Link.verticalMatch x y)
  · exact Link.horizontal x y h
  · exact Link.symm (Link.horizontal x y h)
  · exact Link.vertical x y h
  · exact Link.symm (Link.vertical x y h)
  · exact Link.westNorth x y h.1 h.2
  · exact Link.symm (Link.westNorth x y h.1 h.2)
  · exact Link.westSouth x y h.1 h.2
  · exact Link.symm (Link.westSouth x y h.1 h.2)
  · exact Link.eastNorth x y h.1 h.2
  · exact Link.symm (Link.eastNorth x y h.1 h.2)
  · exact Link.eastSouth x y h.1 h.2
  · exact Link.symm (Link.eastSouth x y h.1 h.2)
  · exact Link.crossing x y h.1 h.2
  · exact Link.symm (Link.crossing x y h.1 h.2)

/-- One predecessor edge in a finite red-path certificate. Port codes use row-major
coordinates with four sides in west/east/south/north order; move codes use row-major
coordinates, then one of the nine link kinds, then the reversal bit. -/
private structure Row where
  /-- Encoded endpoint of this row. -/
  port : Nat
  /-- Crossing parity of the path from the forest root. -/
  parity : Bool
  /-- Index of an earlier row whose endpoint starts the edge. -/
  predecessor : Nat
  /-- Encoded edge from the predecessor to this endpoint. -/
  move : Nat

/-- A predecessor forest whose encoded coordinates have the given row width. -/
private structure Forest (width : Nat) where
  /-- Encoded starting port common to all certified paths. -/
  root : Nat
  /-- Rows in predecessor order. -/
  rows : List Row

/-- The starting port obtained by decoding the forest's root. -/
private def Forest.rootPort {width : Nat} (f : Forest width) : Port :=
  decodePort width f.root

private def Forest.row {width : Nat} (f : Forest width) (i : Nat) : Row :=
  f.rows.getD i ⟨0, false, 0, 0⟩

/-- Each row is either the root or a valid edge from an earlier row, and all ports
stay inside the square of the forest width. -/
private def Forest.Valid {width : Nat} (grid : Nat → Nat → Index) (f : Forest width) : Prop :=
  PortInBounds (decodePort width f.root) width width ∧
  ∀ i : Fin f.rows.length,
    let r := f.row i
    PortInBounds (decodePort width r.port) width width ∧
    ((r.port = f.root ∧ r.parity = false) ∨
      (r.predecessor < i.val ∧
       (decodeMove width r.move).valid grid = true ∧
       (decodeMove width r.move).first = decodePort width (f.row r.predecessor).port ∧
       (decodeMove width r.move).second = decodePort width r.port ∧
       r.parity = ((f.row r.predecessor).parity ^^ (decodeMove width r.move).parity)))

private theorem Forest.sound {width : Nat} {grid : Nat → Nat → Index} {f : Forest width}
    (valid : f.Valid grid) (i : Nat) (hi : i < f.rows.length) :
    BoundedPath grid width width (decodePort width f.root) (decodePort width (f.row i).port)
      (f.row i).parity := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    obtain ⟨bounds, root | ⟨decreases, edge, first, second, parity⟩⟩ := valid.2 ⟨i, hi⟩
    · rcases root with ⟨hp, hb⟩
      rw [hp, hb]
      exact BoundedPath.refl _ valid.1
    · have predecessorBounds := (valid.2 ⟨(f.row i).predecessor, lt_trans decreases hi⟩).1
      have step := BoundedPath.ofLink ((decodeMove width (f.row i).move).link edge)
        (first.symm ▸ predecessorBounds) (second.symm ▸ bounds)
      rw [first, second] at step
      rw [parity]
      exact BoundedPath.trans (ih _ decreases (lt_trans decreases hi)) step

private theorem Forest.sound_mem {width : Nat} {grid : Nat → Nat → Index} {f : Forest width}
    (valid : f.Valid grid) {r : Row} (hr : r ∈ f.rows) :
    BoundedPath grid width width (decodePort width f.root) (decodePort width r.port) r.parity := by
  obtain ⟨i, hi, equal⟩ := List.mem_iff_getElem.mp hr
  have rowEq : f.row i = r := by
    simp only [Forest.row, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some, equal]
  simpa only [rowEq] using Forest.sound valid i hi

private def sideCode : Side → Nat
  | .west => 0
  | .east => 1
  | .south => 2
  | .north => 3

private def codeToSide : Nat → Side
  | 0 => .west
  | 1 => .east
  | 2 => .south
  | _ => .north

private theorem sideCode_codeToSide {r : Nat} (hr : r < 4) : sideCode (codeToSide r) = r := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

private def encodePort (width : Nat) (p : Port) : Nat :=
  4 * (width * p.y + p.x) + sideCode p.side

private theorem decodePort_encodePort {width : Nat} {p : Port} (hx : p.x < width) :
    decodePort width (encodePort width p) = p := by
  rcases p with ⟨x, y, s⟩
  have hw : 0 < width := Nat.lt_of_le_of_lt (Nat.zero_le x) hx
  have hs : sideCode s < 4 := by cases s <;> decide
  have hdiv : (4 * (width * y + x) + sideCode s) / 4 = width * y + x := by omega
  have hmod : (4 * (width * y + x) + sideCode s) % 4 = sideCode s := by omega
  simp only [decodePort, encodePort, hdiv, hmod, Nat.mul_add_mod, Nat.mod_eq_of_lt hx,
    Nat.mul_add_div hw, Nat.div_eq_of_lt hx, Nat.add_zero, Port.mk.injEq]
  refine ⟨trivial, trivial, ?_⟩
  cases s <;> rfl

private theorem decodePort_add (width cell r : Nat) (hr : r < 4) :
    decodePort width (4 * cell + r) = ⟨cell % width, cell / width, codeToSide r⟩ := by
  have hdiv : (4 * cell + r) / 4 = cell := by omega
  have hmod : (4 * cell + r) % 4 = r := by omega
  simp only [decodePort, hdiv, hmod, Port.mk.injEq]
  refine ⟨trivial, trivial, ?_⟩
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

private theorem portInBounds_decodePort {width code : Nat} (hw : 0 < width)
    (hcode : code < 4 * width * width) :
    PortInBounds (decodePort width code) width width := by
  refine ⟨Nat.mod_lt _ hw, ?_⟩
  show code / 4 / width < width
  rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.mul_pos (by decide) hw)]
  have : width * (4 * width) = 4 * width * width := Nat.mul_comm width (4 * width)
  omega

private theorem unpack_insert_lt_gen {stride table entry i j : Nat} (hj : j < i) :
    ((table ||| (entry <<< (stride * i))) >>> (stride * j)) &&& (2 ^ stride - 1) =
      (table >>> (stride * j)) &&& (2 ^ stride - 1) := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  by_cases hb : b < stride
  · have hlt : ¬ (stride * i ≤ stride * j + b) := by
      have : stride * (j + 1) ≤ stride * i := Nat.mul_le_mul_left stride hj
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    simp only [hlt, decide_false, Bool.false_and, Bool.or_false]
  · simp only [hb, decide_false, Bool.and_false]

private theorem unpack_insert_eq_gen {stride table entry i : Nat}
    (ht : table < 2 ^ (stride * i)) (he : entry < 2 ^ stride) :
    ((table ||| (entry <<< (stride * i))) >>> (stride * i)) &&& (2 ^ stride - 1) = entry := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  by_cases hb : b < stride
  · have ht0 : table.testBit (stride * i + b) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ht
        (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
    have hle : stride * i ≤ stride * i + b := by omega
    have hsub : stride * i + b - stride * i = b := by omega
    simp only [ht0, hle, decide_true, hsub, Bool.true_and, Bool.false_or, hb, Bool.and_true]
  · have he0 : entry.testBit b = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le he
        (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
    simp only [hb, decide_false, Bool.and_false, he0]

private theorem insert_lt_gen {stride table entry i : Nat}
    (ht : table < 2 ^ (stride * i)) (he : entry < 2 ^ stride) :
    table ||| (entry <<< (stride * i)) < 2 ^ (stride * (i + 1)) := by
  have hle : stride * i ≤ stride * (i + 1) := Nat.mul_le_mul_left stride (Nat.le_succ i)
  have h1 : table < 2 ^ (stride * (i + 1)) :=
    lt_of_lt_of_le ht (Nat.pow_le_pow_right (n := 2) (by decide) hle)
  have h2 : entry <<< (stride * i) < 2 ^ (stride * (i + 1)) := by
    rw [Nat.shiftLeft_eq, Nat.mul_add, Nat.mul_one, Nat.add_comm (stride * i) stride, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right he (Nat.pow_pos (by decide))
  exact Nat.or_lt_two_pow h1 h2

private def packFin (stride n : Nat) (f : Fin n → Nat) : Nat :=
  go n (Nat.le_refl n)
where
  go : (k : Nat) → k ≤ n → Nat
    | 0, _ => 0
    | k + 1, hk => go k (Nat.le_of_succ_le hk) ||| (f ⟨k, hk⟩ <<< (stride * k))

private theorem packFin_go_lt {stride n : Nat} {f : Fin n → Nat}
    (hf : ∀ i : Fin n, f i < 2 ^ stride) :
    ∀ (k : Nat) (hk : k ≤ n), packFin.go stride n f k hk < 2 ^ (stride * k)
  | 0, _ => by simp only [packFin.go, Nat.mul_zero, Nat.pow_zero]; decide
  | k + 1, hk =>
    insert_lt_gen (packFin_go_lt hf k (Nat.le_of_succ_le hk)) (hf ⟨k, hk⟩)

private theorem unpack_packFin {stride n : Nat} {f : Fin n → Nat}
    (hf : ∀ i : Fin n, f i < 2 ^ stride) (i : Fin n) :
    ((packFin stride n f >>> (stride * i.val)) &&& (2 ^ stride - 1)) = f i := by
  suffices ∀ (k : Nat) (hk : k ≤ n) (j : Fin n), j.val < k →
      ((packFin.go stride n f k hk >>> (stride * j.val)) &&& (2 ^ stride - 1)) = f j from
    this n (Nat.le_refl n) i i.isLt
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro hk j hj
    dsimp only [packFin.go]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · rw [unpack_insert_lt_gen hlt, ih (Nat.le_of_succ_le hk) j hlt]
    · have hjeq : j = ⟨k, hk⟩ := Fin.ext heq
      rw [hjeq]
      exact unpack_insert_eq_gen (packFin_go_lt hf k (Nat.le_of_succ_le hk)) (hf ⟨k, hk⟩)

private def bitIf (b : Bool) (k : Nat) : Nat :=
  if b then 1 <<< k else 0

private theorem bitIf_lt {b : Bool} {k m : Nat} (h : k < m) : bitIf b k < 2 ^ m := by
  cases b
  · exact Nat.pow_pos (by decide)
  · simp only [bitIf, ↓reduceIte, Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by decide) h

private theorem testBit_bitIf (b : Bool) (k j : Nat) :
    (bitIf b k).testBit j = (b && decide (k = j)) := by
  cases b
  · simp only [bitIf, Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.false_and]
  · simp only [bitIf, ↓reduceIte, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.true_and]

private def pick4 (a b c d : Bool) : Nat → Bool
  | 0 => a | 1 => b | 2 => c | _ => d

private theorem quad4_lt {s a b c d : Nat}
    (ha : a < 2 ^ s) (hb : b < 2 ^ s) (hc : c < 2 ^ s) (hd : d < 2 ^ s) :
    a ||| (b <<< s) ||| (c <<< (2 * s)) ||| (d <<< (3 * s)) < 2 ^ (4 * s) := by
  have h1 : a ||| (b <<< s) < 2 ^ (s * 2) := by
    simpa only [Nat.mul_one] using
      insert_lt_gen (stride := s) (i := 1) (by simpa only [Nat.mul_one] using ha) hb
  have h2 : a ||| (b <<< s) ||| (c <<< (2 * s)) < 2 ^ (s * 3) := by
    simpa only [Nat.mul_comm s 2] using insert_lt_gen (stride := s) (i := 2) h1 hc
  simpa only [Nat.mul_comm s 3, Nat.mul_comm s 4] using
    insert_lt_gen (stride := s) (i := 3) h2 hd

private theorem testBit_quad4 {s a b c d q r : Nat}
    (ha : a < 2 ^ s) (hb : b < 2 ^ s) (hc : c < 2 ^ s)
    (hq : q < 4) (hr : r < s) :
    (a ||| (b <<< s) ||| (c <<< (2 * s)) ||| (d <<< (3 * s))).testBit (s * q + r) =
      pick4 (a.testBit r) (b.testBit r) (c.testBit r) (d.testBit r) q := by
  have hlt : ∀ {x k : Nat}, x < 2 ^ s → s ≤ k → x.testBit k = false := fun hx hk =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (n := 2) (by decide) hk))
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl
  · simp only [pick4, Nat.mul_zero, Nat.zero_add, show ¬ s ≤ r by omega, show ¬ 2 * s ≤ r by omega,
      show ¬ 3 * s ≤ r by omega, decide_false, Bool.false_and, Bool.or_false]
  · simp only [pick4, Nat.mul_one, hlt ha (show s ≤ s + r by omega),
      show s ≤ s + r by omega, show s + r - s = r by omega,
      show ¬ 2 * s ≤ s + r by omega, show ¬ 3 * s ≤ s + r by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false]
  · simp only [pick4, hlt ha (show s ≤ s * 2 + r by omega),
      hlt hb (show s ≤ s * 2 + r - s by omega),
      show 2 * s ≤ s * 2 + r by omega, show s * 2 + r - 2 * s = r by omega,
      show ¬ 3 * s ≤ s * 2 + r by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_false,
      Bool.false_or, Bool.or_false]
  · simp only [pick4, hlt ha (show s ≤ s * 3 + r by omega),
      hlt hb (show s ≤ s * 3 + r - s by omega),
      hlt hc (show s ≤ s * 3 + r - 2 * s by omega),
      show 3 * s ≤ s * 3 + r by omega, show s * 3 + r - 3 * s = r by omega,
      decide_true, Bool.true_and, Bool.and_false, Bool.false_or]

private def thickCode : Thick → Nat
  | .a => 0 | .b => 1 | .c => 2 | .d => 3 | .e => 4
  | .f => 5 | .g => 6 | .h => 7 | .i => 8 | .j => 9
  | .k => 10 | .l => 11 | .m => 12 | .n => 13 | .o => 14
  | .p => 15 | .q => 16 | .r => 17 | .s => 18 | .t => 19

private def codeToThick : Nat → Thick
  | 0 => .a | 1 => .b | 2 => .c | 3 => .d | 4 => .e
  | 5 => .f | 6 => .g | 7 => .h | 8 => .i | 9 => .j
  | 10 => .k | 11 => .l | 12 => .m | 13 => .n | 14 => .o
  | 15 => .p | 16 => .q | 17 => .r | 18 => .s | _ => .t

private theorem codeToThick_thickCode (comp : Thick) : codeToThick (thickCode comp) = comp := by
  cases comp <;> rfl

private theorem thickCode_lt20 (comp : Thick) : thickCode comp < 20 := by
  cases comp <;> decide

private theorem thickCode_lt (comp : Thick) : thickCode comp < 2 ^ 5 :=
  lt_trans (thickCode_lt20 comp) (by decide)

private def thickTable : Nat :=
  packFin 5 104 fun p => thickCode (indexThick p)

private def childTable : Nat :=
  packFin 28 104 fun p =>
    (childBlock p 0 0).val |||
    ((childBlock p 1 0).val <<< 7) |||
    ((childBlock p 0 1).val <<< 14) |||
    ((childBlock p 1 1).val <<< 21)

private def childOf (ct idx dx dy : Nat) : Nat :=
  (ct >>> (28 * idx + 7 * (2 * dy + dx))) &&& 127

private def thickOf (tt idx : Nat) : Nat :=
  (tt >>> (5 * idx)) &&& 31

private theorem thickOf_thickTable (p : Index) :
    thickOf thickTable p.val = thickCode (indexThick p) :=
  unpack_packFin (stride := 5) (fun q => thickCode_lt (indexThick q)) p

private theorem childOf_childTable (p : Index) (dx dy : Fin 2) :
    childOf childTable p.val dx.val dy.val = (childBlock p dx dy).val := by
  have hlt : ∀ q : Index, ∀ x y : Fin 2, (childBlock q x y).val < 2 ^ 7 :=
    fun q x y => lt_trans (childBlock q x y).isLt (by decide)
  have hpack := unpack_packFin (stride := 28) (n := 104)
    (fun q => quad4_lt (s := 7) (hlt q 0 0) (hlt q 1 0) (hlt q 0 1) (hlt q 1 1)) p
  change ((childTable >>> (28 * p.val)) &&& (2 ^ 28 - 1)) = _ at hpack
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 7
  · have h28 : 7 * (2 * dy.val + dx.val) + b < 28 := by omega
    have hbit := congrArg (fun n => n.testBit (7 * (2 * dy.val + dx.val) + b)) hpack
    have hmask : (2 ^ 28 - 1).testBit (7 * (2 * dy.val + dx.val) + b) = true := by
      rw [Nat.testBit_two_pow_sub_one]; simp only [h28, decide_true]
    have h127 : (127 : Nat).testBit b = true := by
      rw [show (127 : Nat) = 2 ^ 7 - 1 by rfl, Nat.testBit_two_pow_sub_one]
      simp only [hb, decide_true]
    simp only [childOf, Nat.testBit_and, Nat.testBit_shiftRight, h127, hmask, Bool.and_true,
      show 28 * p.val + (7 * (2 * dy.val + dx.val) + b) =
        28 * p.val + 7 * (2 * dy.val + dx.val) + b by omega] at hbit ⊢
    rw [hbit]
    have h4 := testBit_quad4 (s := 7) (hlt p 0 0) (hlt p 1 0) (hlt p 0 1)
      (d := (childBlock p 1 1).val) (q := 2 * dy.val + dx.val) (r := b) (by omega) hb
    change ((childBlock p 0 0).val ||| ((childBlock p 1 0).val <<< 7) |||
      ((childBlock p 0 1).val <<< 14) ||| ((childBlock p 1 1).val <<< 21)).testBit
      (7 * (2 * dy.val + dx.val) + b) = _ at h4
    rw [h4]
    rcases dx with ⟨x, hx⟩; rcases dy with ⟨y, hy⟩
    rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
      rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> rfl
  · have h127 : (127 : Nat).testBit b = false := by
      rw [show (127 : Nat) = 2 ^ 7 - 1 by rfl, Nat.testBit_two_pow_sub_one]
      simp only [hb, decide_false]
    have hcb : (childBlock p dx dy).val.testBit b = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hlt p dx dy)
        (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
    simp only [childOf, Nat.testBit_and, h127, Bool.and_false, hcb]

private def fineGridNat (ct tt p : Nat) : Nat :=
  packFin 5 16 fun slot =>
    let tx := slot.val % 4
    let ty := slot.val / 4
    let mid := childOf ct p (tx / 2) (ty / 2)
    thickOf tt (childOf ct mid (tx % 2) (ty % 2))

private theorem unpack_fineGridNat (parent : Index) {x y : Nat} (hx : x < 8) (hy : y < 8) :
    ((fineGridNat childTable thickTable parent.val >>> (5 * (4 * (y / 2) + x / 2))) &&& 31) =
      thickCode (componentAt (fineGrid parent) x y) := by
  have hslot : 4 * (y / 2) + x / 2 < 16 := by omega
  have hlt : ∀ s : Fin 16,
      thickOf thickTable
        (childOf childTable (childOf childTable parent.val (s.val % 4 / 2) (s.val / 4 / 2))
          (s.val % 4 % 2) (s.val / 4 % 2)) < 2 ^ 5 := by
    intro s
    simp only [thickOf, show (31 : Nat) = 2 ^ 5 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hu := unpack_packFin (stride := 5) hlt ⟨4 * (y / 2) + x / 2, hslot⟩
  change ((fineGridNat childTable thickTable parent.val >>> (5 * (4 * (y / 2) + x / 2))) &&& 31) =
    _ at hu
  rw [hu]
  have htx : (4 * (y / 2) + x / 2) % 4 = x / 2 := by omega
  have hty : (4 * (y / 2) + x / 2) / 4 = y / 2 := by omega
  dsimp only
  rw [htx, hty]
  have hx1 : x / 2 / 2 < 2 := by omega
  have hy1 : y / 2 / 2 < 2 := by omega
  have hx0 : x / 2 % 2 < 2 := by omega
  have hy0 : y / 2 % 2 < 2 := by omega
  have hmid := childOf_childTable parent ⟨x / 2 / 2, hx1⟩ ⟨y / 2 / 2, hy1⟩
  have hleaf := childOf_childTable (childBlock parent ⟨x / 2 / 2, hx1⟩ ⟨y / 2 / 2, hy1⟩)
    ⟨x / 2 % 2, hx0⟩ ⟨y / 2 % 2, hy0⟩
  dsimp only at hmid hleaf
  rw [hmid, hleaf, thickOf_thickTable]
  simp only [componentAt, indexThick, fineGrid, coarseGrid, iterateRefine, refineIndexGrid,
    Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hy1]

private def baseFirstCode (cell k : Nat) : Nat :=
  4 * cell + match k with
    | 0 | 6 | 7 => 1
    | 1 => 3
    | 3 => 2
    | _ => 0

private def baseSecondCode (width cell k : Nat) : Nat :=
  match k with
  | 0 => 4 * (cell + 1)
  | 1 => 4 * (cell + width) + 2
  | 2 => 4 * cell + 1
  | 3 | 4 | 6 => 4 * cell + 3
  | _ => 4 * cell + 2

private def kindValid (comp : Thick) (q : Quadrant) (k : Nat) : Bool :=
  match k with
  | 2 => hasHorizontal comp q
  | 3 => hasVertical comp q
  | 4 => cornerWest comp q && cornerNorth comp q
  | 5 => cornerWest comp q && cornerSouth comp q
  | 6 => cornerEast comp q && cornerNorth comp q
  | 7 => cornerEast comp q && cornerSouth comp q
  | _ => hasHorizontal comp q && hasVertical comp q

private theorem decodePort_baseFirstCode (width move : Nat) :
    decodePort width (baseFirstCode (move / 2 / 9) (move / 2 % 9)) =
      (decodeMove width move).baseFirst := by
  have hk : move / 2 % 9 < 9 := Nat.mod_lt _ (by decide)
  dsimp only [decodeMove]
  generalize move / 2 / 9 = cell at *
  generalize move / 2 % 9 = k at *
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (decodePort_add width cell _ (by decide))

private theorem decodePort_baseSecondCode {width move : Nat} (hw : 0 < width)
    (hh : move / 2 % 9 = 0 → move / 2 / 9 % width + 1 < width) :
    decodePort width (baseSecondCode width (move / 2 / 9) (move / 2 % 9)) =
      (decodeMove width move).baseSecond := by
  have hk : move / 2 % 9 < 9 := Nat.mod_lt _ (by decide)
  dsimp only [decodeMove]
  generalize move / 2 / 9 = cell at *
  generalize move / 2 % 9 = k at *
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hlt := hh rfl
    have hcell : cell = width * (cell / width) + cell % width := (Nat.div_add_mod cell width).symm
    have hadd : cell + 1 = width * (cell / width) + (cell % width + 1) := by omega
    have hd : decodePort width (4 * (cell + 1)) =
        ⟨(cell + 1) % width, (cell + 1) / width, .west⟩ :=
      decodePort_add width (cell + 1) 0 (by decide)
    simp only [baseSecondCode, Move.baseSecond]
    rw [hd, Port.mk.injEq]
    refine ⟨?_, ?_, rfl⟩
    · rw [hadd, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    · rw [hadd, Nat.mul_add_div hw, Nat.div_eq_of_lt hlt, Nat.add_zero]
  · simp only [baseSecondCode, Move.baseSecond]
    rw [decodePort_add width (cell + width) 2 (by decide), Port.mk.injEq]
    exact ⟨Nat.add_mod_right cell width, Nat.add_div_right cell hw, rfl⟩
  all_goals exact (decodePort_add width cell _ (by decide))

private theorem four_mul_le_baseSecondCode (width cell k : Nat) :
    4 * cell ≤ baseSecondCode width cell k := by
  unfold baseSecondCode
  split <;> omega

private theorem move_valid_of_kindValid {width move : Nat} {grid : Nat → Nat → Index}
    (h : move / 2 % 9 < 2 ∨
      kindValid (componentAt grid (move / 2 / 9 % width) (move / 2 / 9 / width))
        (quadrantAt (move / 2 / 9 % width) (move / 2 / 9 / width)) (move / 2 % 9) = true) :
    (decodeMove width move).valid grid = true := by
  have hk : move / 2 % 9 < 9 := Nat.mod_lt _ (by decide)
  dsimp only [decodeMove]
  generalize move / 2 / 9 = cell at *
  generalize move / 2 % 9 = k at *
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  all_goals
    rcases h with hlt | hkv
    · omega
    · exact hkv

private theorem move_parity_eq (width move : Nat) :
    (decodeMove width move).parity = (move / 2 % 9 == 8) := by
  have hk : move / 2 % 9 < 9 := Nat.mod_lt _ (by decide)
  dsimp only [decodeMove]
  generalize move / 2 % 9 = k at *
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def packRow (port : Nat) (parity : Bool) : Nat :=
  2 * port + if parity then 1 else 0

private theorem packRow_lt {port : Nat} {parity : Bool} (hp : port < 2048) :
    packRow port parity < 2 ^ 12 := by
  cases parity <;> simp only [packRow, ↓reduceIte, Bool.false_eq_true] <;> omega

private theorem unpack_port (port : Nat) (parity : Bool) :
    packRow port parity >>> 1 = port := by
  rw [Nat.shiftRight_eq_div_pow]
  cases parity <;> simp only [packRow, ↓reduceIte, Bool.false_eq_true] <;> omega

private theorem unpack_parity (port : Nat) (parity : Bool) :
    ((packRow port parity &&& 1) == 1) = parity := by
  rw [Nat.and_one_is_mod]
  cases parity
  · have h : (2 * port + 0) % 2 = 0 := by omega
    simp only [packRow, Bool.false_eq_true, ↓reduceIte, h]
    rfl
  · have h : (2 * port + 1) % 2 = 1 := by omega
    simp only [packRow, ↓reduceIte, h]
    rfl

private def checkRowStruct (width root i table : Nat) (r : Row) : Bool :=
  (r.port == root && !r.parity) ||
  (Nat.blt r.predecessor i &&
    let packed := (table >>> (12 * r.predecessor)) &&& 4095
    let predPort := packed >>> 1
    let predParity := (packed &&& 1) == 1
    let half := r.move / 2
    let cell := half / 9
    let k := half % 9
    let rev := r.move % 2 == 1
    let okMatch := if k == 0 then Nat.blt (cell % width + 1) width else true
    let firstBase := baseFirstCode cell k
    let secondBase := baseSecondCode width cell k
    let firstCode := if rev then secondBase else firstBase
    let secondCode := if rev then firstBase else secondBase
    okMatch && firstCode == predPort && secondCode == r.port &&
      r.parity == (predParity ^^ (k == 8)))

private def checkRowsStruct (width limit root i table : Nat) : List Row → Bool
  | [] => true
  | r :: rs =>
    if Nat.blt r.port limit then
      if checkRowStruct width root i table r then
        checkRowsStruct width limit root (i + 1)
          (table ||| (packRow r.port r.parity <<< (12 * i))) rs
      else false
    else false

private def checkForestStruct (width : Nat) (f : Forest width) : Bool :=
  let limit := 4 * width * width
  Nat.blt f.root limit && checkRowsStruct width limit f.root 0 0 f.rows

private def Forest.StructValid {width : Nat} (f : Forest width) : Prop :=
  PortInBounds (decodePort width f.root) width width ∧
  ∀ i : Fin f.rows.length,
    let r := f.row i
    PortInBounds (decodePort width r.port) width width ∧
    ((r.port = f.root ∧ r.parity = false) ∨
      (r.predecessor < i.val ∧
       (r.move / 2 % 9 ≥ 2 → r.move / 2 / 9 < width * width) ∧
       (decodeMove width r.move).first = decodePort width (f.row r.predecessor).port ∧
       (decodeMove width r.move).second = decodePort width r.port ∧
       r.parity = ((f.row r.predecessor).parity ^^ (decodeMove width r.move).parity)))

private theorem checkRowsStruct_sound {width : Nat} {f : Forest width}
    (hw : 0 < width) (hw16 : width ≤ 16)
    {i table : Nat} {rs : List Row}
    (hlen : i + rs.length = f.rows.length)
    (hdrop : ∀ k (hk : k < rs.length), f.row (i + k) = rs[k])
    (htlt : table < 2 ^ (12 * i))
    (htval : ∀ j < i, (table >>> (12 * j)) &&& 4095 = packRow (f.row j).port (f.row j).parity)
    (hcheck : checkRowsStruct width (4 * width * width) f.root i table rs = true) :
    ∀ k (_hk : k < rs.length),
      let r := f.row (i + k)
      PortInBounds (decodePort width r.port) width width ∧
      ((r.port = f.root ∧ r.parity = false) ∨
        (r.predecessor < i + k ∧
         (r.move / 2 % 9 ≥ 2 → r.move / 2 / 9 < width * width) ∧
         (decodeMove width r.move).first = decodePort width (f.row r.predecessor).port ∧
         (decodeMove width r.move).second = decodePort width r.port ∧
         r.parity = ((f.row r.predecessor).parity ^^ (decodeMove width r.move).parity))) := by
  induction rs generalizing i table with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | cons r rs ih =>
    dsimp only [checkRowsStruct] at hcheck
    split at hcheck
    · rename_i hportB
      have hport : r.port < 4 * width * width := Nat.blt_eq.mp hportB
      split at hcheck
      · rename_i hok
        have hr0 : f.row i = r := by
          simpa only [Nat.add_zero, List.getElem_cons_zero] using hdrop 0 (Nat.zero_lt_succ _)
        have hlim : 4 * width * width ≤ 1024 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 hw16) hw16
        have hpack_lt : packRow r.port r.parity < 2 ^ 12 := packRow_lt (by omega)
        have hnext_lt : table ||| (packRow r.port r.parity <<< (12 * i)) < 2 ^ (12 * (i + 1)) :=
          insert_lt_gen htlt hpack_lt
        have hnext_val : ∀ j < i + 1,
            ((table ||| (packRow r.port r.parity <<< (12 * i))) >>> (12 * j)) &&& 4095 =
              packRow (f.row j).port (f.row j).parity := by
          intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · rw [show (4095 : Nat) = 2 ^ 12 - 1 by rfl, unpack_insert_lt_gen hlt]
            exact htval j hlt
          · rw [show (4095 : Nat) = 2 ^ 12 - 1 by rfl, unpack_insert_eq_gen htlt hpack_lt, hr0]
        have htail := ih (i := i + 1)
          (table := table ||| (packRow r.port r.parity <<< (12 * i)))
          (by simp only [List.length_cons] at hlen; omega)
          (fun k hk => by
            have := hdrop (k + 1) (Nat.succ_lt_succ hk)
            simpa only [show i + (k + 1) = i + 1 + k by omega, List.getElem_cons_succ] using this)
          hnext_lt hnext_val hcheck
        intro k hk
        cases k with
        | zero =>
          simp only [Nat.add_zero, hr0]
          refine ⟨portInBounds_decodePort hw hport, ?_⟩
          simp only [checkRowStruct, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
            Bool.not_eq_true', Nat.blt_eq] at hok
          rcases hok with ⟨hpr, hpar⟩ | ⟨hpred, ⟨⟨⟨hokMatch, hfirst⟩, hsecond⟩, hpar⟩⟩
          · exact Or.inl ⟨hpr, hpar⟩
          · right
            have hpk := htval r.predecessor hpred
            have hpp : ((table >>> (12 * r.predecessor)) &&& 4095) >>> 1 =
                (f.row r.predecessor).port := by
              rw [hpk, unpack_port]
            have hppar : (((table >>> (12 * r.predecessor)) &&& 4095) &&& 1 == 1) =
                (f.row r.predecessor).parity := by
              rw [hpk, unpack_parity]
            rw [hpp] at hfirst
            rw [hppar] at hpar
            set cell := r.move / 2 / 9
            set kv := r.move / 2 % 9
            have hh : kv = 0 → cell % width + 1 < width := by
              intro hk0
              simpa only [hk0, ↓reduceIte, Nat.blt_eq] using hokMatch
            have hbf := decodePort_baseFirstCode width r.move
            have hbs := decodePort_baseSecondCode hw hh
            have hfirstEq : (decodeMove width r.move).first =
                decodePort width (f.row r.predecessor).port := by
              unfold Move.first
              change (if (r.move % 2 == 1) = true then _ else _) = _
              by_cases hrev : r.move % 2 = 1
              · rw [ite_eq_left hrev] at hfirst
                simp only [beq_iff_eq, hrev, ↓reduceIte]
                rw [← hbs, hfirst]
              · rw [ite_eq_right hrev] at hfirst
                simp only [beq_iff_eq, hrev, ↓reduceIte]
                rw [← hbf, hfirst]
            have hsecondEq : (decodeMove width r.move).second = decodePort width r.port := by
              unfold Move.second
              change (if (r.move % 2 == 1) = true then _ else _) = _
              by_cases hrev : r.move % 2 = 1
              · rw [ite_eq_left hrev] at hsecond
                simp only [beq_iff_eq, hrev, ↓reduceIte]
                rw [← hbf, hsecond]
              · rw [ite_eq_right hrev] at hsecond
                simp only [beq_iff_eq, hrev, ↓reduceIte]
                rw [← hbs, hsecond]
            have hcellLt : kv ≥ 2 → cell < width * width := by
              intro _
              have hge4 : 4 * cell ≤ r.port := by
                have h1 : 4 * cell ≤ baseFirstCode cell kv := by
                  simp only [baseFirstCode]; omega
                have h2 : 4 * cell ≤ baseSecondCode width cell kv :=
                  four_mul_le_baseSecondCode width cell kv
                by_cases hrev : r.move % 2 = 1
                · rw [ite_eq_left hrev] at hsecond; omega
                · rw [ite_eq_right hrev] at hsecond; omega
              have : 4 * width * width = 4 * (width * width) := Nat.mul_assoc 4 width width
              omega
            refine ⟨hpred, hcellLt, hfirstEq, hsecondEq, ?_⟩
            rw [move_parity_eq]
            exact hpar
        | succ k' =>
          have hstep := htail k' (Nat.lt_of_succ_lt_succ hk)
          simpa only [show i + (k' + 1) = i + 1 + k' by omega] using hstep
      · exact absurd hcheck Bool.false_ne_true
    · exact absurd hcheck Bool.false_ne_true

private theorem checkForestStruct_sound {width : Nat} {f : Forest width}
    (hw : 0 < width) (hw16 : width ≤ 16)
    (h : checkForestStruct width f = true) : f.StructValid := by
  simp only [checkForestStruct, Bool.and_eq_true, Nat.blt_eq] at h
  refine ⟨portInBounds_decodePort hw h.1, fun i => ?_⟩
  have hrows := checkRowsStruct_sound (f := f) hw hw16 (i := 0) (table := 0) (rs := f.rows)
    (Nat.zero_add _)
    (fun k hk => by
      simp only [Nat.zero_add, Forest.row, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hk, Option.getD_some])
    (by decide)
    (fun j hj => by omega)
    h.2 i.val i.isLt
  simpa only [Nat.zero_add] using hrows

-- Shared by all 104 parents: one predecessor per port, without repeated path tails.
private def forest (id : Fin 32) : Forest 8 :=
  match id.val with
  | 0 => ⟨37, [
      ⟨37, false, 0, 0⟩, ⟨40, false, 0, 162⟩, ⟨41, false, 1, 184⟩,
      ⟨44, false, 2, 180⟩, ⟨45, false, 3, 202⟩, ⟨48, false, 4, 198⟩,
      ⟨49, false, 5, 220⟩, ⟨52, false, 6, 216⟩, ⟨53, false, 7, 238⟩,
      ⟨56, false, 8, 234⟩, ⟨57, false, 9, 256⟩, ⟨60, false, 10, 252⟩,
      ⟨61, false, 11, 274⟩
    ]⟩
  | 1 => ⟨39, [
      ⟨39, false, 0, 0⟩, ⟨70, false, 0, 164⟩, ⟨71, false, 1, 312⟩,
      ⟨102, false, 2, 308⟩, ⟨103, false, 3, 456⟩, ⟨134, false, 4, 452⟩,
      ⟨135, false, 5, 600⟩, ⟨166, false, 6, 596⟩, ⟨167, false, 7, 744⟩,
      ⟨198, false, 8, 740⟩, ⟨199, false, 9, 888⟩, ⟨230, false, 10, 884⟩,
      ⟨231, false, 11, 1032⟩
    ]⟩
  | 2 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨142, false, 3, 488⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 6, 636⟩,
      ⟨123, false, 7, 548⟩, ⟨174, false, 8, 632⟩, ⟨154, false, 9, 542⟩,
      ⟨175, false, 10, 780⟩, ⟨155, false, 11, 690⟩, ⟨206, false, 12, 776⟩,
      ⟨186, false, 13, 686⟩, ⟨205, false, 14, 933⟩, ⟨184, true, 15, 845⟩,
      ⟨187, false, 15, 834⟩, ⟨208, false, 16, 918⟩, ⟨181, true, 17, 811⟩,
      ⟨185, true, 17, 832⟩, ⟨209, false, 19, 940⟩, ⟨218, false, 18, 830⟩,
      ⟨183, true, 20, 822⟩, ⟨188, true, 21, 828⟩, ⟨212, false, 22, 936⟩,
      ⟨216, false, 23, 983⟩, ⟨189, true, 25, 850⟩, ⟨213, false, 27, 955⟩,
      ⟨214, true, 24, 812⟩, ⟨215, true, 30, 960⟩, ⟨246, true, 31, 956⟩,
      ⟨247, true, 32, 1104⟩
    ]⟩
  | 3 => ⟨32, [
      ⟨32, false, 0, 0⟩
    ]⟩
  | 4 => ⟨35, [
      ⟨35, false, 0, 0⟩, ⟨66, false, 0, 146⟩, ⟨67, false, 1, 294⟩,
      ⟨98, false, 2, 290⟩, ⟨99, false, 3, 438⟩, ⟨130, false, 4, 434⟩,
      ⟨131, false, 5, 582⟩, ⟨162, false, 6, 578⟩, ⟨163, false, 7, 726⟩,
      ⟨194, false, 8, 722⟩, ⟨195, false, 9, 870⟩, ⟨226, false, 10, 866⟩,
      ⟨227, false, 11, 1014⟩
    ]⟩
  | 5 => ⟨5, [
      ⟨5, false, 0, 0⟩, ⟨8, false, 0, 18⟩, ⟨9, false, 1, 40⟩,
      ⟨12, false, 2, 36⟩, ⟨13, false, 3, 58⟩, ⟨16, false, 4, 54⟩,
      ⟨17, false, 5, 76⟩, ⟨20, false, 6, 72⟩, ⟨21, false, 7, 94⟩,
      ⟨24, false, 8, 90⟩, ⟨25, false, 9, 112⟩, ⟨28, false, 10, 108⟩,
      ⟨29, false, 11, 130⟩
    ]⟩
  | 6 => ⟨6, [
      ⟨6, false, 0, 0⟩
    ]⟩
  | 7 => ⟨0, [
      ⟨0, false, 0, 0⟩
    ]⟩
  | 8 => ⟨2, [
      ⟨2, false, 0, 0⟩
    ]⟩
  | 9 => ⟨39, [
      ⟨39, false, 0, 0⟩, ⟨70, false, 0, 164⟩, ⟨71, false, 1, 312⟩,
      ⟨102, false, 2, 308⟩, ⟨103, false, 3, 456⟩, ⟨134, false, 4, 452⟩,
      ⟨132, true, 5, 611⟩, ⟨135, false, 5, 600⟩, ⟨129, true, 6, 577⟩,
      ⟨166, false, 7, 596⟩, ⟨128, true, 8, 581⟩, ⟨167, false, 9, 744⟩,
      ⟨198, false, 11, 740⟩, ⟨199, false, 12, 888⟩, ⟨230, false, 13, 884⟩,
      ⟨231, false, 14, 1032⟩
    ]⟩
  | 10 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨114, true, 0, 520⟩, ⟨83, true, 3, 363⟩, ⟨111, false, 1, 498⟩,
      ⟨115, true, 3, 510⟩, ⟨116, false, 2, 504⟩, ⟨82, true, 4, 367⟩,
      ⟨117, false, 7, 526⟩, ⟨142, false, 5, 488⟩, ⟨146, true, 6, 506⟩,
      ⟨51, true, 8, 219⟩, ⟨120, false, 9, 522⟩, ⟨140, true, 10, 647⟩,
      ⟨143, false, 10, 636⟩, ⟨144, true, 11, 659⟩, ⟨50, true, 12, 223⟩,
      ⟨123, false, 13, 548⟩, ⟨137, true, 14, 613⟩, ⟨141, true, 16, 631⟩,
      ⟨174, false, 15, 632⟩, ⟨19, true, 17, 75⟩, ⟨136, true, 19, 617⟩,
      ⟨154, false, 18, 542⟩, ⟨175, false, 21, 780⟩, ⟨18, true, 22, 79⟩,
      ⟨133, true, 23, 595⟩, ⟨155, false, 24, 690⟩, ⟨206, false, 25, 776⟩,
      ⟨186, false, 28, 686⟩, ⟨205, false, 29, 933⟩, ⟨187, false, 30, 834⟩,
      ⟨208, false, 31, 918⟩, ⟨209, false, 33, 940⟩, ⟨218, false, 32, 830⟩,
      ⟨212, false, 34, 936⟩, ⟨216, false, 35, 983⟩, ⟨213, false, 37, 955⟩
    ]⟩
  | 11 => ⟨35, [
      ⟨35, false, 0, 0⟩, ⟨66, false, 0, 146⟩, ⟨67, false, 1, 294⟩,
      ⟨98, false, 2, 290⟩, ⟨99, false, 3, 438⟩, ⟨130, false, 4, 434⟩,
      ⟨128, true, 5, 593⟩, ⟨131, false, 5, 582⟩, ⟨129, true, 6, 580⟩,
      ⟨162, false, 7, 578⟩, ⟨163, false, 9, 726⟩, ⟨194, false, 10, 722⟩,
      ⟨195, false, 11, 870⟩, ⟨226, false, 12, 866⟩, ⟨227, false, 13, 1014⟩
    ]⟩
  | 12 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨114, true, 0, 520⟩, ⟨83, true, 3, 363⟩, ⟨111, false, 1, 498⟩,
      ⟨115, true, 3, 510⟩, ⟨116, false, 2, 504⟩, ⟨82, true, 4, 367⟩,
      ⟨117, false, 7, 526⟩, ⟨142, false, 5, 488⟩, ⟨146, true, 6, 506⟩,
      ⟨51, true, 8, 219⟩, ⟨120, false, 9, 522⟩, ⟨140, true, 10, 647⟩,
      ⟨143, false, 10, 636⟩, ⟨144, true, 11, 659⟩, ⟨50, true, 12, 223⟩,
      ⟨123, false, 13, 548⟩, ⟨137, true, 14, 613⟩, ⟨141, true, 16, 631⟩,
      ⟨174, false, 15, 632⟩, ⟨19, true, 17, 75⟩, ⟨136, true, 19, 617⟩,
      ⟨154, false, 18, 542⟩, ⟨175, false, 21, 780⟩, ⟨18, true, 22, 79⟩,
      ⟨133, true, 23, 595⟩, ⟨155, false, 24, 690⟩, ⟨206, false, 25, 776⟩,
      ⟨132, true, 27, 599⟩, ⟨186, false, 28, 686⟩, ⟨205, false, 29, 933⟩,
      ⟨187, false, 31, 834⟩, ⟨208, false, 32, 918⟩, ⟨209, false, 34, 940⟩,
      ⟨218, false, 33, 830⟩, ⟨212, false, 35, 936⟩, ⟨216, false, 36, 983⟩,
      ⟨213, false, 38, 955⟩
    ]⟩
  | 13 => ⟨5, [
      ⟨5, false, 0, 0⟩, ⟨8, false, 0, 18⟩, ⟨9, false, 1, 40⟩,
      ⟨12, false, 2, 36⟩, ⟨13, false, 3, 58⟩, ⟨16, false, 4, 54⟩,
      ⟨17, false, 5, 76⟩, ⟨18, true, 5, 88⟩, ⟨20, false, 6, 72⟩,
      ⟨21, false, 8, 94⟩, ⟨24, false, 9, 90⟩, ⟨25, false, 10, 112⟩,
      ⟨28, false, 11, 108⟩, ⟨29, false, 12, 130⟩
    ]⟩
  | 14 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨114, true, 0, 520⟩, ⟨83, true, 3, 363⟩, ⟨111, false, 1, 498⟩,
      ⟨115, true, 3, 510⟩, ⟨116, false, 2, 504⟩, ⟨82, true, 4, 367⟩,
      ⟨117, false, 7, 526⟩, ⟨142, false, 5, 488⟩, ⟨146, true, 6, 506⟩,
      ⟨51, true, 8, 219⟩, ⟨120, false, 9, 522⟩, ⟨140, true, 10, 647⟩,
      ⟨143, false, 10, 636⟩, ⟨144, true, 11, 659⟩, ⟨50, true, 12, 223⟩,
      ⟨123, false, 13, 548⟩, ⟨137, true, 14, 613⟩, ⟨141, true, 16, 631⟩,
      ⟨174, false, 15, 632⟩, ⟨19, true, 17, 75⟩, ⟨136, true, 19, 617⟩,
      ⟨154, false, 18, 542⟩, ⟨175, false, 21, 780⟩, ⟨133, true, 23, 595⟩,
      ⟨155, false, 24, 690⟩, ⟨206, false, 25, 776⟩, ⟨132, true, 26, 599⟩,
      ⟨186, false, 27, 686⟩, ⟨205, false, 28, 933⟩, ⟨129, true, 29, 577⟩,
      ⟨187, false, 30, 834⟩, ⟨208, false, 31, 918⟩, ⟨128, true, 32, 581⟩,
      ⟨209, false, 34, 940⟩, ⟨218, false, 33, 830⟩, ⟨212, false, 36, 936⟩,
      ⟨216, false, 37, 983⟩, ⟨213, false, 39, 955⟩
    ]⟩
  | 15 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨114, true, 0, 520⟩, ⟨83, true, 3, 363⟩, ⟨111, false, 1, 498⟩,
      ⟨115, true, 3, 510⟩, ⟨116, false, 2, 504⟩, ⟨82, true, 4, 367⟩,
      ⟨117, false, 7, 526⟩, ⟨142, false, 5, 488⟩, ⟨146, true, 6, 506⟩,
      ⟨51, true, 8, 219⟩, ⟨120, false, 9, 522⟩, ⟨140, true, 10, 647⟩,
      ⟨143, false, 10, 636⟩, ⟨144, true, 11, 659⟩, ⟨50, true, 12, 223⟩,
      ⟨123, false, 13, 548⟩, ⟨137, true, 14, 613⟩, ⟨141, true, 16, 631⟩,
      ⟨174, false, 15, 632⟩, ⟨19, true, 17, 75⟩, ⟨136, true, 19, 617⟩,
      ⟨154, false, 18, 542⟩, ⟨175, false, 21, 780⟩, ⟨18, true, 22, 79⟩,
      ⟨133, true, 23, 595⟩, ⟨155, false, 24, 690⟩, ⟨206, false, 25, 776⟩,
      ⟨132, true, 27, 599⟩, ⟨186, false, 28, 686⟩, ⟨205, false, 29, 933⟩,
      ⟨129, true, 30, 577⟩, ⟨187, false, 31, 834⟩, ⟨208, false, 32, 918⟩,
      ⟨128, true, 33, 581⟩, ⟨209, false, 35, 940⟩, ⟨218, false, 34, 830⟩,
      ⟨212, false, 37, 936⟩, ⟨216, false, 38, 983⟩, ⟨213, false, 40, 955⟩
    ]⟩
  | 16 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨142, false, 3, 488⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 6, 636⟩,
      ⟨123, false, 7, 548⟩, ⟨174, false, 8, 632⟩, ⟨154, false, 9, 542⟩,
      ⟨172, true, 10, 791⟩, ⟨175, false, 10, 780⟩, ⟨155, false, 11, 690⟩,
      ⟨169, true, 12, 757⟩, ⟨173, true, 12, 778⟩, ⟨206, false, 13, 776⟩,
      ⟨168, true, 15, 761⟩, ⟨176, true, 16, 774⟩, ⟨186, false, 14, 686⟩,
      ⟨205, false, 17, 933⟩, ⟨165, true, 18, 739⟩, ⟨179, true, 19, 800⟩,
      ⟨187, false, 20, 834⟩, ⟨208, false, 21, 918⟩, ⟨164, true, 22, 743⟩,
      ⟨209, false, 25, 940⟩, ⟨210, true, 25, 952⟩, ⟨218, false, 24, 830⟩,
      ⟨161, true, 26, 721⟩, ⟨211, true, 28, 942⟩, ⟨212, false, 27, 936⟩,
      ⟨216, false, 29, 983⟩, ⟨160, true, 30, 725⟩, ⟨213, false, 33, 955⟩,
      ⟨242, true, 31, 938⟩, ⟨243, true, 36, 1086⟩
    ]⟩
  | 17 => ⟨1, [
      ⟨1, false, 0, 0⟩
    ]⟩
  | 18 => ⟨4, [
      ⟨4, false, 0, 0⟩
    ]⟩
  | 19 => ⟨7, [
      ⟨7, false, 0, 0⟩
    ]⟩
  | 20 => ⟨38, [
      ⟨38, false, 0, 0⟩
    ]⟩
  | 21 => ⟨39, [
      ⟨39, false, 0, 0⟩, ⟨70, false, 0, 164⟩, ⟨71, false, 1, 312⟩,
      ⟨102, false, 2, 308⟩, ⟨103, false, 3, 456⟩, ⟨134, false, 4, 452⟩,
      ⟨135, false, 5, 600⟩, ⟨166, false, 6, 596⟩, ⟨164, true, 7, 755⟩,
      ⟨167, false, 7, 744⟩, ⟨161, true, 8, 721⟩, ⟨198, false, 9, 740⟩,
      ⟨160, true, 10, 725⟩, ⟨199, false, 11, 888⟩, ⟨230, false, 13, 884⟩,
      ⟨231, false, 14, 1032⟩
    ]⟩
  | 22 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨142, false, 3, 488⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 6, 636⟩,
      ⟨123, false, 7, 548⟩, ⟨174, false, 8, 632⟩, ⟨154, false, 9, 542⟩,
      ⟨172, true, 10, 791⟩, ⟨175, false, 10, 780⟩, ⟨155, false, 11, 690⟩,
      ⟨169, true, 12, 757⟩, ⟨173, true, 12, 778⟩, ⟨206, false, 13, 776⟩,
      ⟨168, true, 15, 761⟩, ⟨176, true, 16, 774⟩, ⟨186, false, 14, 686⟩,
      ⟨205, false, 17, 933⟩, ⟨165, true, 18, 739⟩, ⟨179, true, 19, 800⟩,
      ⟨187, false, 20, 834⟩, ⟨208, false, 21, 918⟩, ⟨209, false, 25, 940⟩,
      ⟨210, true, 25, 952⟩, ⟨218, false, 24, 830⟩, ⟨211, true, 27, 942⟩,
      ⟨212, false, 26, 936⟩, ⟨216, false, 28, 983⟩, ⟨213, false, 31, 955⟩,
      ⟨242, true, 29, 938⟩, ⟨243, true, 33, 1086⟩
    ]⟩
  | 23 => ⟨33, [
      ⟨33, false, 0, 0⟩
    ]⟩
  | 24 => ⟨36, [
      ⟨36, false, 0, 0⟩
    ]⟩
  | 25 => ⟨3, [
      ⟨3, false, 0, 0⟩
    ]⟩
  | 26 => ⟨34, [
      ⟨34, false, 0, 0⟩
    ]⟩
  | 27 => ⟨35, [
      ⟨35, false, 0, 0⟩, ⟨66, false, 0, 146⟩, ⟨67, false, 1, 294⟩,
      ⟨98, false, 2, 290⟩, ⟨99, false, 3, 438⟩, ⟨130, false, 4, 434⟩,
      ⟨131, false, 5, 582⟩, ⟨162, false, 6, 578⟩, ⟨160, true, 7, 737⟩,
      ⟨163, false, 7, 726⟩, ⟨161, true, 8, 724⟩, ⟨194, false, 9, 722⟩,
      ⟨195, false, 11, 870⟩, ⟨226, false, 12, 866⟩, ⟨227, false, 13, 1014⟩
    ]⟩
  | 28 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨142, false, 3, 488⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 6, 636⟩,
      ⟨123, false, 7, 548⟩, ⟨174, false, 8, 632⟩, ⟨154, false, 9, 542⟩,
      ⟨172, true, 10, 791⟩, ⟨175, false, 10, 780⟩, ⟨155, false, 11, 690⟩,
      ⟨169, true, 12, 757⟩, ⟨173, true, 12, 778⟩, ⟨206, false, 13, 776⟩,
      ⟨168, true, 15, 761⟩, ⟨176, true, 16, 774⟩, ⟨186, false, 14, 686⟩,
      ⟨205, false, 17, 933⟩, ⟨165, true, 18, 739⟩, ⟨179, true, 19, 800⟩,
      ⟨187, false, 20, 834⟩, ⟨208, false, 21, 918⟩, ⟨164, true, 22, 743⟩,
      ⟨209, false, 25, 940⟩, ⟨210, true, 25, 952⟩, ⟨218, false, 24, 830⟩,
      ⟨211, true, 28, 942⟩, ⟨212, false, 27, 936⟩, ⟨216, false, 29, 983⟩,
      ⟨213, false, 32, 955⟩, ⟨242, true, 30, 938⟩, ⟨243, true, 34, 1086⟩
    ]⟩
  | 29 => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨118, true, 4, 538⟩, ⟨142, false, 3, 488⟩, ⟨87, true, 6, 381⟩,
      ⟨119, true, 6, 528⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 7, 636⟩,
      ⟨86, true, 8, 385⟩, ⟨123, false, 10, 548⟩, ⟨150, true, 9, 524⟩,
      ⟨174, false, 11, 632⟩, ⟨55, true, 12, 237⟩, ⟨149, true, 14, 681⟩,
      ⟨154, false, 13, 542⟩, ⟨175, false, 15, 780⟩, ⟨54, true, 16, 241⟩,
      ⟨152, true, 18, 701⟩, ⟨155, false, 18, 690⟩, ⟨206, false, 19, 776⟩,
      ⟨23, true, 20, 93⟩, ⟨153, true, 21, 688⟩, ⟨186, false, 22, 686⟩,
      ⟨205, false, 23, 933⟩, ⟨22, true, 24, 97⟩, ⟨156, true, 25, 684⟩,
      ⟨187, false, 26, 834⟩, ⟨208, false, 27, 918⟩, ⟨157, true, 29, 706⟩,
      ⟨209, false, 31, 940⟩, ⟨218, false, 30, 830⟩, ⟨212, false, 33, 936⟩,
      ⟨216, false, 34, 983⟩, ⟨213, false, 36, 955⟩
    ]⟩
  | 30 => ⟨5, [
      ⟨5, false, 0, 0⟩, ⟨8, false, 0, 18⟩, ⟨9, false, 1, 40⟩,
      ⟨12, false, 2, 36⟩, ⟨13, false, 3, 58⟩, ⟨16, false, 4, 54⟩,
      ⟨17, false, 5, 76⟩, ⟨20, false, 6, 72⟩, ⟨21, false, 7, 94⟩,
      ⟨22, true, 7, 106⟩, ⟨24, false, 8, 90⟩, ⟨25, false, 10, 112⟩,
      ⟨28, false, 11, 108⟩, ⟨29, false, 12, 130⟩
    ]⟩
  | _ => ⟨112, [
      ⟨112, false, 0, 0⟩, ⟨109, false, 0, 487⟩, ⟨113, false, 0, 508⟩,
      ⟨111, false, 1, 498⟩, ⟨116, false, 2, 504⟩, ⟨117, false, 4, 526⟩,
      ⟨118, true, 4, 538⟩, ⟨142, false, 3, 488⟩, ⟨87, true, 6, 381⟩,
      ⟨119, true, 6, 528⟩, ⟨120, false, 5, 522⟩, ⟨143, false, 7, 636⟩,
      ⟨86, true, 8, 385⟩, ⟨123, false, 10, 548⟩, ⟨150, true, 9, 524⟩,
      ⟨174, false, 11, 632⟩, ⟨55, true, 12, 237⟩, ⟨149, true, 14, 681⟩,
      ⟨154, false, 13, 542⟩, ⟨175, false, 15, 780⟩, ⟨54, true, 16, 241⟩,
      ⟨152, true, 18, 701⟩, ⟨155, false, 18, 690⟩, ⟨206, false, 19, 776⟩,
      ⟨23, true, 20, 93⟩, ⟨153, true, 21, 688⟩, ⟨186, false, 22, 686⟩,
      ⟨205, false, 23, 933⟩, ⟨156, true, 25, 684⟩, ⟨187, false, 26, 834⟩,
      ⟨208, false, 27, 918⟩, ⟨157, true, 28, 706⟩, ⟨209, false, 30, 940⟩,
      ⟨218, false, 29, 830⟩, ⟨212, false, 32, 936⟩, ⟨216, false, 33, 983⟩,
      ⟨213, false, 35, 955⟩
    ]⟩

private def selected (parent : Index) : List (Fin 32) :=
  match parent.val with
  | 0 => [0, 1, 2]
  | 1 => [3, 4, 2]
  | 2 => [5, 6, 2]
  | 3 => [7, 8, 2]
  | 4 => [0, 9, 10]
  | 5 => [3, 11, 12]
  | 6 => [13, 6, 14]
  | 7 => [7, 8, 15]
  | 8 | 9 | 20 | 21 | 24 | 25 | 28 | 29 => [16]
  | 10 | 11 | 26 | 27 => [7, 17, 18, 5, 16]
  | 12 | 14 => [6, 19, 20, 21, 22]
  | 13 => [6, 19, 3, 23, 24, 0, 20, 21, 22]
  | 15 => [7, 17, 18, 5, 6, 19, 20, 21, 22]
  | 16 | 18 => [8, 25, 26, 27, 28]
  | 17 => [8, 25, 3, 23, 26, 27, 24, 0, 28]
  | 19 => [7, 17, 8, 25, 18, 5, 26, 27, 28]
  | 22 | 23 | 30 | 31 => [3, 23, 24, 0, 16]
  | 32 | 33 | 44 | 45 | 48 | 49 | 52 | 53 | 92 | 93 | 95 | 96 | 98 | 99 | 101 | 102 => [2]
  | 36 | 38 | 80 | 81 | 83 | 84 => [6, 19, 20, 1, 2]
  | 37 | 82 => [6, 19, 3, 23, 24, 0, 20, 1, 2]
  | 39 | 85 => [7, 17, 18, 5, 6, 19, 20, 1, 2]
  | 40 | 42 | 86 | 87 | 89 | 90 => [8, 25, 26, 4, 2]
  | 41 | 88 => [8, 25, 3, 23, 26, 4, 24, 0, 2]
  | 43 | 91 => [7, 17, 8, 25, 18, 5, 26, 4, 2]
  | 46 | 47 | 54 | 55 | 94 | 100 => [3, 23, 24, 0, 2]
  | 56 | 57 | 59 | 60 => [6, 19, 20, 1, 29]
  | 58 => [6, 19, 3, 23, 24, 0, 20, 1, 29]
  | 61 => [7, 17, 18, 30, 6, 19, 20, 1, 31]
  | 62 | 63 | 65 | 66 => [8, 25, 26, 4, 29]
  | 64 => [8, 25, 3, 23, 26, 4, 24, 0, 29]
  | 67 => [7, 17, 8, 25, 18, 30, 26, 4, 31]
  | 68 | 69 | 71 | 72 | 74 | 75 | 77 | 78 => [29]
  | 70 | 76 => [3, 23, 24, 0, 29]
  | 73 | 79 => [7, 17, 18, 30, 31]
  | 34 | 35 | 50 | 51 | 97 | _ => [7, 17, 18, 5, 2]

/-- Whether one row of the forest ends at the target port. -/
private def Forest.reaches {width : Nat} (f : Forest width) (target : Port) : Bool :=
  f.rows.any fun r => decide (decodePort width r.port = target)

private def connects (f : Forest 8) (start finish : Port) : Bool :=
  decide (decodePort 8 f.root = start) &&
    f.rows.any fun r => decide (decodePort 8 r.port = finish ∧ r.parity = false)

private def connectsCode (f : Forest 8) (startCode finishCode : Nat) : Bool :=
  f.root == startCode && f.rows.any fun r => r.port == finishCode && !r.parity

private theorem connects_of_connectsCode {f : Forest 8} {startCode finishCode : Nat}
    (h : connectsCode f startCode finishCode = true) :
    connects f (decodePort 8 startCode) (decodePort 8 finishCode) = true := by
  simp only [connectsCode, Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨hroot, r, hr, hport, hpar⟩ := h
  simp only [connects, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  exact ⟨congrArg (decodePort 8) hroot, r, hr, congrArg (decodePort 8) hport, hpar⟩

private def rowsMask : List Row → Nat
  | [] => 0
  | r :: rs => (1 <<< r.port) ||| rowsMask rs

private theorem eq_of_testBit_one_shiftLeft {a b : Nat}
    (h : (1 <<< a).testBit b = true) : b = a := by
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hle, hbit⟩ := h
  by_contra hne
  have hgt : 1 ≤ b - a := by omega
  have h0 : (1 : Nat).testBit (b - a) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
      (Nat.pow_le_pow_right (n := 2) (by decide) hgt))
  rw [h0] at hbit
  exact Bool.false_ne_true hbit

private theorem exists_mem_of_testBit_rowsMask {rs : List Row} {code : Nat}
    (h : (rowsMask rs).testBit code = true) :
    ∃ r ∈ rs, r.port = code := by
  induction rs with
  | nil => exact absurd (by simpa only [rowsMask, Nat.zero_testBit] using h) Bool.false_ne_true
  | cons r rs ih =>
    simp only [rowsMask, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with hhead | htail
    · exact ⟨r, List.mem_cons_self, (eq_of_testBit_one_shiftLeft hhead).symm⟩
    · obtain ⟨r', hr', heq⟩ := ih htail
      exact ⟨r', List.mem_cons_of_mem _ hr', heq⟩

private theorem reaches_of_testBit_rowsMask {width : Nat} {f : Forest width} {p : Port}
    (hx : p.x < width) (h : (rowsMask f.rows).testBit (encodePort width p) = true) :
    f.reaches p = true := by
  obtain ⟨r, hr, heq⟩ := exists_mem_of_testBit_rowsMask h
  simp only [Forest.reaches, List.any_eq_true, decide_eq_true_eq]
  exact ⟨r, hr, by rw [heq, decodePort_encodePort hx]⟩

private def selectedMask : List (Fin 32) → Nat
  | [] => 0
  | id :: ids => rowsMask (forest id).rows ||| selectedMask ids

private theorem any_reaches_of_testBit_selectedMask {ids : List (Fin 32)} {p : Port}
    (hx : p.x < 8) (h : (selectedMask ids).testBit (encodePort 8 p) = true) :
    (ids.any fun id => (forest id).reaches p) = true := by
  induction ids with
  | nil => exact absurd (by simpa only [selectedMask, Nat.zero_testBit] using h) Bool.false_ne_true
  | cons id ids ih =>
    simp only [selectedMask, Nat.testBit_or, Bool.or_eq_true] at h
    simp only [List.any_cons, Bool.or_eq_true]
    rcases h with hhead | htail
    · exact Or.inl (reaches_of_testBit_rowsMask hx hhead)
    · exact Or.inr (ih htail)

private def forestsMask {width : Nat} : List (Forest width) → Nat
  | [] => 0
  | f :: fs => rowsMask f.rows ||| forestsMask fs

private theorem any_reaches_of_testBit_forestsMask {width : Nat} {fs : List (Forest width)}
    {p : Port} (hx : p.x < width)
    (h : (forestsMask fs).testBit (encodePort width p) = true) :
    (fs.any fun f => f.reaches p) = true := by
  induction fs with
  | nil => exact absurd (by simpa only [forestsMask, Nat.zero_testBit] using h) Bool.false_ne_true
  | cons f fs ih =>
    simp only [forestsMask, Nat.testBit_or, Bool.or_eq_true] at h
    simp only [List.any_cons, Bool.or_eq_true]
    rcases h with hhead | htail
    · exact Or.inl (reaches_of_testBit_rowsMask hx hhead)
    · exact Or.inr (ih htail)

private theorem testBit_of_land_eq {mask req i : Nat}
    (h : (mask &&& req) = req) (hbit : req.testBit i = true) :
    mask.testBit i = true := by
  have := congrArg (fun n => n.testBit i) h
  simp only [Nat.testBit_and, hbit, Bool.and_true] at this
  exact this

private theorem testBit_shiftLeft_add {m off k : Nat} (h : m.testBit k = true) :
    (m <<< off).testBit (off + k) = true := by
  simp only [Nat.testBit_shiftLeft, show off ≤ off + k by omega, decide_true,
    show off + k - off = k by omega, h, Bool.true_and]

private def rowsMoveMask (root : Nat) : List Row → Nat
  | [] => 0
  | r :: rs =>
    let rest := rowsMoveMask root rs
    if r.port == root && !r.parity then rest
    else
      let half := r.move / 2
      let k := half % 9
      if k == 0 || k == 1 then rest
      else (1 <<< (8 * (half / 9) + (k - 2))) ||| rest

private theorem testBit_rowsMoveMask_of_mem {root : Nat} {rs : List Row} {r : Row}
    (hr : r ∈ rs) (hnotRoot : ¬ (r.port = root ∧ r.parity = false))
    (hk : r.move / 2 % 9 ≥ 2) :
    (rowsMoveMask root rs).testBit (8 * (r.move / 2 / 9) + (r.move / 2 % 9 - 2)) = true := by
  induction rs with
  | nil => cases hr
  | cons r' rs ih =>
    dsimp only [rowsMoveMask]
    rcases List.mem_cons.mp hr with rfl | htail
    · have hnr : (r.port == root && !r.parity) = false := by
        cases hb : (r.port == root && !r.parity)
        · rfl
        · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hb
          exact absurd hb hnotRoot
      have hnk : (r.move / 2 % 9 == 0 || r.move / 2 % 9 == 1) = false := by
        have h0 : (r.move / 2 % 9 == 0) = false := beq_false_of_ne (by omega)
        have h1 : (r.move / 2 % 9 == 1) = false := beq_false_of_ne (by omega)
        simp only [h0, h1, Bool.or_false]
      simp only [hnr, hnk, Bool.false_eq_true, ↓reduceIte, Nat.testBit_or]
      have h1 : (1 <<< (8 * (r.move / 2 / 9) + (r.move / 2 % 9 - 2))).testBit
          (8 * (r.move / 2 / 9) + (r.move / 2 % 9 - 2)) = true := by
        simpa only [Nat.add_zero] using testBit_shiftLeft_add (k := 0) (m := 1)
          (off := 8 * (r.move / 2 / 9) + (r.move / 2 % 9 - 2)) rfl
      simp only [h1, Bool.true_or]
    · have hih := ih htail
      split
      · exact hih
      · split
        · exact hih
        · simp only [Nat.testBit_or, hih, Bool.or_true]

private def selectedMoveMask : List (Fin 32) → Nat
  | [] => 0
  | id :: ids =>
    let f := forest id
    rowsMoveMask f.root f.rows ||| selectedMoveMask ids

private theorem testBit_selectedMoveMask_of_mem {ids : List (Fin 32)} {id : Fin 32} {b : Nat}
    (hid : id ∈ ids) (h : (rowsMoveMask (forest id).root (forest id).rows).testBit b = true) :
    (selectedMoveMask ids).testBit b = true := by
  induction ids with
  | nil => cases hid
  | cons id' ids ih =>
    simp only [selectedMoveMask, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hid with rfl | htail
    · exact Or.inl h
    · exact Or.inr (ih htail)

private def quadrantCode : Quadrant → Nat
  | .southwest => 0 | .southeast => 1 | .northwest => 2 | .northeast => 3

private theorem quadrantCode_quadrantAt (x y : Nat) :
    quadrantCode (quadrantAt x y) = 2 * (y % 2) + x % 2 := by
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp only [quadrantAt, Quadrant.ofBits, quadrantCode, hx, hy] <;> rfl

private def portPresentAt (comp : Thick) (q : Quadrant) : Side → Bool
  | .west => hasWest comp q
  | .east => hasEast comp q
  | .south => hasSouth comp q
  | .north => hasNorth comp q

private theorem portPresent_eq_at (grid : Nat → Nat → Index) (x y : Nat) (s : Side) :
    portPresent grid ⟨x, y, s⟩ = portPresentAt (componentAt grid x y) (quadrantAt x y) s := by
  cases s <;> rfl

private def quadrantPortMask (comp : Thick) (q : Quadrant) : Nat :=
  bitIf (hasWest comp q) 0 |||
  bitIf (hasEast comp q) 1 |||
  bitIf (hasSouth comp q) 2 |||
  bitIf (hasNorth comp q) 3

private theorem quadrantPortMask_lt (comp : Thick) (q : Quadrant) :
    quadrantPortMask comp q < 2 ^ 4 :=
  Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow
    (bitIf_lt (by decide)) (bitIf_lt (by decide)))
    (bitIf_lt (by decide))) (bitIf_lt (by decide))

private theorem testBit_quadrantPortMask (comp : Thick) (q : Quadrant) (s : Side) :
    (quadrantPortMask comp q).testBit (sideCode s) = portPresentAt comp q s := by
  cases s <;>
    simp only [quadrantPortMask, sideCode, portPresentAt, Nat.testBit_or, testBit_bitIf,
      Nat.reduceEqDiff, decide_true, decide_false, Bool.and_false, Bool.and_true,
      Bool.or_false, Bool.false_or]

private def thickBytes (comp : Thick) : Nat :=
  quadrantPortMask comp .southwest |||
  (quadrantPortMask comp .southeast <<< 4) |||
  (quadrantPortMask comp .northwest <<< 8) |||
  (quadrantPortMask comp .northeast <<< 12)

private def tilePortBytesTable : Nat :=
  packFin 16 20 fun i => thickBytes (codeToThick i.val)

private def tileMaskFromBytes (rowStride tc : Nat) : Nat :=
  let bytes := (tilePortBytesTable >>> (16 * tc)) &&& 65535
  (bytes &&& 255) ||| ((bytes >>> 8) <<< rowStride)

private theorem unpack_tilePortBytesTable (comp : Thick) :
    ((tilePortBytesTable >>> (16 * thickCode comp)) &&& 65535) = thickBytes comp := by
  have hu := unpack_packFin (stride := 16) (n := 20)
    (f := fun i => thickBytes (codeToThick i.val))
    (fun i => quad4_lt (s := 4) (quadrantPortMask_lt _ _) (quadrantPortMask_lt _ _)
      (quadrantPortMask_lt _ _) (quadrantPortMask_lt _ _))
    ⟨thickCode comp, thickCode_lt20 comp⟩
  change ((tilePortBytesTable >>> (16 * thickCode comp)) &&& 65535) = _ at hu
  simpa only [codeToThick_thickCode] using hu

private theorem testBit_tilePortBytesTable (comp : Thick) (q : Quadrant) {r : Nat} (hr : r < 4) :
    tilePortBytesTable.testBit (16 * thickCode comp + 4 * quadrantCode q + r) =
      (quadrantPortMask comp q).testBit r := by
  have h16 : 4 * quadrantCode q + r < 16 := by cases q <;> simp only [quadrantCode] <;> omega
  have hu := congrArg (fun n => n.testBit (4 * quadrantCode q + r)) (unpack_tilePortBytesTable comp)
  have h65535 : (65535 : Nat).testBit (4 * quadrantCode q + r) = true := by
    rw [show (65535 : Nat) = 2 ^ 16 - 1 by rfl, Nat.testBit_two_pow_sub_one]
    simp only [h16, decide_true]
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, h65535, Bool.and_true,
    show 16 * thickCode comp + (4 * quadrantCode q + r) =
      16 * thickCode comp + 4 * quadrantCode q + r by omega] at hu
  rw [hu]
  have hq4 : quadrantCode q < 4 := by cases q <;> decide
  have h4 := testBit_quad4 (s := 4) (quadrantPortMask_lt comp .southwest)
    (quadrantPortMask_lt comp .southeast) (quadrantPortMask_lt comp .northwest)
    (d := quadrantPortMask comp .northeast) hq4 hr
  change (thickBytes comp).testBit (4 * quadrantCode q + r) = _ at h4
  rw [h4]
  cases q <;> rfl

private theorem tilePortBytes_south (comp : Thick) :
    ((tilePortBytesTable >>> (16 * thickCode comp)) &&& 65535) &&& 255 =
      quadrantPortMask comp .southwest ||| (quadrantPortMask comp .southeast <<< 4) := by
  rw [unpack_tilePortBytesTable]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_and, show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]
  by_cases hb : b < 8
  · have h4 := testBit_quad4 (s := 4) (quadrantPortMask_lt comp .southwest)
      (quadrantPortMask_lt comp .southeast) (quadrantPortMask_lt comp .northwest)
      (d := quadrantPortMask comp .northeast) (q := b / 4) (r := b % 4) (by omega)
      (Nat.mod_lt b (by decide))
    change (thickBytes comp).testBit (4 * (b / 4) + b % 4) = _ at h4
    rw [show 4 * (b / 4) + b % 4 = b by omega] at h4
    simp only [hb, decide_true, Bool.and_true, h4, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases (show b / 4 = 0 ∨ b / 4 = 1 by omega) with h0 | h1
    · simp only [h0, pick4, show b % 4 = b by omega, show ¬ 4 ≤ b by omega, decide_false,
        Bool.false_and, Bool.or_false]
    · have hsw : (quadrantPortMask comp .southwest).testBit b = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (quadrantPortMask_lt comp .southwest)
          (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
      simp only [h1, pick4, hsw, show 4 ≤ b by omega, decide_true, Bool.true_and, Bool.false_or,
        show b % 4 = b - 4 by omega]
  · have h8 : quadrantPortMask comp .southwest ||| (quadrantPortMask comp .southeast <<< 4) <
        2 ^ 8 := by
      simpa only [Nat.mul_one] using insert_lt_gen (stride := 4) (i := 1)
        (by simpa only [Nat.mul_one] using quadrantPortMask_lt comp .southwest)
        (quadrantPortMask_lt comp .southeast)
    have h0 : (quadrantPortMask comp .southwest |||
        (quadrantPortMask comp .southeast <<< 4)).testBit b = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h8
        (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
    simp only [hb, decide_false, Bool.and_false, h0]

private theorem tilePortBytes_north (comp : Thick) :
    (((tilePortBytesTable >>> (16 * thickCode comp)) &&& 65535) >>> 8) =
      quadrantPortMask comp .northwest ||| (quadrantPortMask comp .northeast <<< 4) := by
  rw [unpack_tilePortBytesTable]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_shiftRight]
  by_cases hb : b < 8
  · have h4 := testBit_quad4 (s := 4) (quadrantPortMask_lt comp .southwest)
      (quadrantPortMask_lt comp .southeast) (quadrantPortMask_lt comp .northwest)
      (d := quadrantPortMask comp .northeast) (q := 2 + b / 4) (r := b % 4) (by omega)
      (Nat.mod_lt b (by decide))
    change (thickBytes comp).testBit (4 * (2 + b / 4) + b % 4) = _ at h4
    rw [show 4 * (2 + b / 4) + b % 4 = 8 + b by omega] at h4
    simp only [h4, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases (show b / 4 = 0 ∨ b / 4 = 1 by omega) with h0 | h1
    · simp only [h0, pick4, show b % 4 = b by omega, show ¬ 4 ≤ b by omega, decide_false,
        Bool.false_and, Bool.or_false]
    · have hnw : (quadrantPortMask comp .northwest).testBit b = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (quadrantPortMask_lt comp .northwest)
          (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
      simp only [h1, pick4, hnw, show 4 ≤ b by omega, decide_true, Bool.true_and, Bool.false_or,
        show b % 4 = b - 4 by omega]
  · have htb : thickBytes comp < 2 ^ 16 :=
      quad4_lt (s := 4) (quadrantPortMask_lt _ _) (quadrantPortMask_lt _ _)
        (quadrantPortMask_lt _ _) (quadrantPortMask_lt _ _)
    have hl : (thickBytes comp).testBit (8 + b) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le htb
        (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
    have h8 : quadrantPortMask comp .northwest ||| (quadrantPortMask comp .northeast <<< 4) <
        2 ^ 8 := by
      simpa only [Nat.mul_one] using insert_lt_gen (stride := 4) (i := 1)
        (by simpa only [Nat.mul_one] using quadrantPortMask_lt comp .northwest)
        (quadrantPortMask_lt comp .northeast)
    have hr : (quadrantPortMask comp .northwest |||
        (quadrantPortMask comp .northeast <<< 4)).testBit b = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h8
        (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
    rw [hl, hr]

private theorem tilePortBytes_east_se (comp : Thick) :
    tilePortBytesTable.testBit (16 * thickCode comp + 5) = hasEast comp .southeast := by
  simpa only [quadrantCode, portPresentAt, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd] using
    (testBit_tilePortBytesTable comp .southeast (r := 1) (by decide)).trans
      (testBit_quadrantPortMask comp .southeast .east)

private theorem tilePortBytes_east_ne (comp : Thick) :
    tilePortBytesTable.testBit (16 * thickCode comp + 13) = hasEast comp .northeast := by
  simpa only [quadrantCode, portPresentAt, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd] using
    (testBit_tilePortBytesTable comp .northeast (r := 1) (by decide)).trans
      (testBit_quadrantPortMask comp .northeast .east)

private theorem tilePortBytes_north_nw (comp : Thick) :
    tilePortBytesTable.testBit (16 * thickCode comp + 11) = hasNorth comp .northwest := by
  simpa only [quadrantCode, portPresentAt, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd] using
    (testBit_tilePortBytesTable comp .northwest (r := 3) (by decide)).trans
      (testBit_quadrantPortMask comp .northwest .north)

private theorem tilePortBytes_north_ne (comp : Thick) :
    tilePortBytesTable.testBit (16 * thickCode comp + 15) = hasNorth comp .northeast := by
  simpa only [quadrantCode, portPresentAt, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd] using
    (testBit_tilePortBytesTable comp .northeast (r := 3) (by decide)).trans
      (testBit_quadrantPortMask comp .northeast .north)

private theorem testBit_tileMaskFromBytes_of_present {rowStride : Nat} {comp : Thick}
    {dx dy : Nat} {s : Side} (hdx : dx < 2) (hdy : dy < 2)
    (h : portPresentAt comp (quadrantAt dx dy) s = true) :
    (tileMaskFromBytes rowStride (thickCode comp)).testBit
      (rowStride * dy + 4 * dx + sideCode s) = true := by
  simp only [tileMaskFromBytes, tilePortBytes_south, tilePortBytes_north]
  rcases (show dx = 0 ∨ dx = 1 by omega) with rfl | rfl <;>
    rcases (show dy = 0 ∨ dy = 1 by omega) with rfl | rfl
  · have hq : (quadrantPortMask comp .southwest).testBit (sideCode s) = true := by
      rw [testBit_quadrantPortMask]; exact h
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.testBit_or, hq, Bool.true_or]
  · have hq : (quadrantPortMask comp .northwest).testBit (sideCode s) = true := by
      rw [testBit_quadrantPortMask]; exact h
    have hrow : (quadrantPortMask comp .northwest |||
        (quadrantPortMask comp .northeast <<< 4)).testBit (sideCode s) = true := by
      simp only [Nat.testBit_or, hq, Bool.true_or]
    have hsh := testBit_shiftLeft_add (off := rowStride) hrow
    simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.testBit_or, hsh, Bool.or_true]
  · have hq : (quadrantPortMask comp .southeast).testBit (sideCode s) = true := by
      rw [testBit_quadrantPortMask]; exact h
    have hsh := testBit_shiftLeft_add (off := 4) hq
    simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.testBit_or, hsh,
      Bool.or_true, Bool.true_or]
  · have hq : (quadrantPortMask comp .northeast).testBit (sideCode s) = true := by
      rw [testBit_quadrantPortMask]; exact h
    have hsh4 := testBit_shiftLeft_add (off := 4) hq
    have hrow : (quadrantPortMask comp .northwest |||
        (quadrantPortMask comp .northeast <<< 4)).testBit (4 + sideCode s) = true := by
      simp only [Nat.testBit_or, hsh4, Bool.or_true]
    have hsh := testBit_shiftLeft_add (off := rowStride) hrow
    have hidx : rowStride * 1 + 4 * 1 + sideCode s = rowStride + (4 + sideCode s) := by omega
    rw [hidx]
    simp only [Nat.testBit_or, hsh, Bool.or_true]

private def quadrantKindMask (comp : Thick) (q : Quadrant) : Nat :=
  bitIf (hasHorizontal comp q) 0 |||
  bitIf (hasVertical comp q) 1 |||
  bitIf (cornerWest comp q && cornerNorth comp q) 2 |||
  bitIf (cornerWest comp q && cornerSouth comp q) 3 |||
  bitIf (cornerEast comp q && cornerNorth comp q) 4 |||
  bitIf (cornerEast comp q && cornerSouth comp q) 5 |||
  bitIf (hasHorizontal comp q && hasVertical comp q) 6

private theorem quadrantKindMask_lt (comp : Thick) (q : Quadrant) :
    quadrantKindMask comp q < 2 ^ 8 :=
  Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow
    (Nat.or_lt_two_pow (Nat.or_lt_two_pow
      (bitIf_lt (by decide)) (bitIf_lt (by decide)))
      (bitIf_lt (by decide))) (bitIf_lt (by decide)))
    (bitIf_lt (by decide))) (bitIf_lt (by decide)))
    (bitIf_lt (by decide))

private theorem testBit_quadrantKindMask (comp : Thick) (q : Quadrant) {j : Nat} (hj : j < 7) :
    (quadrantKindMask comp q).testBit j = kindValid comp q (j + 2) := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [quadrantKindMask, kindValid, Nat.testBit_or, testBit_bitIf,
      Nat.reduceEqDiff, decide_true, decide_false, Bool.and_false, Bool.and_true,
      Bool.or_false, Bool.false_or]

private def thickKindMask (comp : Thick) : Nat :=
  quadrantKindMask comp .southwest |||
  (quadrantKindMask comp .southeast <<< 8) |||
  (quadrantKindMask comp .northwest <<< 16) |||
  (quadrantKindMask comp .northeast <<< 24)

private def kindValidTable : Nat :=
  packFin 32 20 fun i => thickKindMask (codeToThick i.val)

private def allFin (n : Nat) (p : Fin n → Bool) : Bool :=
  go n (Nat.le_refl n)
where
  go : (k : Nat) → k ≤ n → Bool
    | 0, _ => true
    | k + 1, hk => p ⟨k, hk⟩ && go k (Nat.le_of_succ_le hk)

private theorem allFin_sound {n : Nat} {p : Fin n → Bool}
    (h : allFin n p = true) (i : Fin n) : p i = true := by
  suffices ∀ (k : Nat) (hk : k ≤ n), allFin.go n p k hk = true →
      ∀ j : Fin n, j.val < k → p j = true from
    this n (Nat.le_refl n) h i i.isLt
  intro k
  induction k with
  | zero => intro _ _ j hj; omega
  | succ k ih =>
    intro hk hgo j hj
    simp only [allFin.go, Bool.and_eq_true] at hgo
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · exact ih (Nat.le_of_succ_le hk) hgo.2 j hlt
    · have hjeq : j = ⟨k, hk⟩ := Fin.ext heq
      rw [hjeq]
      exact hgo.1

private theorem testBit_kindValidTable (comp : Thick) (q : Quadrant) {j : Nat} (hj : j < 7) :
    kindValidTable.testBit (32 * thickCode comp + 8 * quadrantCode q + j) =
      kindValid comp q (j + 2) := by
  have hu := unpack_packFin (stride := 32) (n := 20)
    (f := fun i => thickKindMask (codeToThick i.val))
    (fun i => quad4_lt (s := 8) (quadrantKindMask_lt _ _) (quadrantKindMask_lt _ _)
      (quadrantKindMask_lt _ _) (quadrantKindMask_lt _ _))
    ⟨thickCode comp, thickCode_lt20 comp⟩
  change ((kindValidTable >>> (32 * thickCode comp)) &&& (2 ^ 32 - 1)) = _ at hu
  simp only [codeToThick_thickCode] at hu
  have h32 : 8 * quadrantCode q + j < 32 := by cases q <;> simp only [quadrantCode] <;> omega
  have hbit := congrArg (fun n => n.testBit (8 * quadrantCode q + j)) hu
  have hmask : (2 ^ 32 - 1).testBit (8 * quadrantCode q + j) = true := by
    rw [Nat.testBit_two_pow_sub_one]; simp only [h32, decide_true]
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, hmask, Bool.and_true,
    show 32 * thickCode comp + (8 * quadrantCode q + j) =
      32 * thickCode comp + 8 * quadrantCode q + j by omega] at hbit
  rw [hbit]
  have hq4 : quadrantCode q < 4 := by cases q <;> decide
  have h4 := testBit_quad4 (s := 8) (quadrantKindMask_lt comp .southwest)
    (quadrantKindMask_lt comp .southeast) (quadrantKindMask_lt comp .northwest)
    (d := quadrantKindMask comp .northeast) (r := j) hq4 (by omega)
  change (thickKindMask comp).testBit (8 * quadrantCode q + j) = _ at h4
  rw [h4]
  cases q <;> exact testBit_quadrantKindMask comp _ hj

private def tileMoveMaskFromTable (rowStride tc : Nat) : Nat :=
  let bits := (kindValidTable >>> (32 * tc)) &&& 4294967295
  (bits &&& 65535) ||| ((bits >>> 16) <<< rowStride)

private def rectPortMask (width tx0 ty0 nw nh gridNat : Nat) : Nat :=
  go (width / 2) (4 * width) (nw * nh)
where
  go (tw rowStride : Nat) : Nat → Nat
    | 0 => 0
    | k + 1 =>
      let tx := tx0 + k % nw
      let ty := ty0 + k / nw
      let tc := (gridNat >>> (5 * (tw * ty + tx))) &&& 31
      let bitOff := 4 * (width * (2 * ty) + 2 * tx)
      (tileMaskFromBytes rowStride tc <<< bitOff) ||| go tw rowStride k

private theorem testBit_rectPortMask_go {width tx0 ty0 nw gridNat : Nat}
    {m j bit : Nat} (hj : j < m)
    (h : (tileMaskFromBytes (4 * width)
        ((gridNat >>> (5 * ((width / 2) * (ty0 + j / nw) + (tx0 + j % nw)))) &&& 31) <<<
        (4 * (width * (2 * (ty0 + j / nw)) + 2 * (tx0 + j % nw)))).testBit bit = true) :
    (rectPortMask.go width tx0 ty0 nw gridNat (width / 2) (4 * width) m).testBit bit = true := by
  induction m with
  | zero => omega
  | succ k ih =>
    simp only [rectPortMask.go, Nat.testBit_or, Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact Or.inr (ih hlt)
    · exact Or.inl h

private theorem testBit_rectPortMask_of_present {width tx0 ty0 nw nh gridNat : Nat}
    {grid : Nat → Nat → Index} {x y : Nat} {s : Side}
    (hxlo : 2 * tx0 ≤ x) (hxhi : x < 2 * (tx0 + nw))
    (hylo : 2 * ty0 ≤ y) (hyhi : y < 2 * (ty0 + nh))
    (hgrid : ((gridNat >>> (5 * ((width / 2) * (y / 2) + x / 2))) &&& 31) =
      thickCode (componentAt grid x y))
    (hpres : portPresent grid ⟨x, y, s⟩ = true) :
    (rectPortMask width tx0 ty0 nw nh gridNat).testBit (encodePort width ⟨x, y, s⟩) = true := by
  have hnw : 0 < nw := by omega
  let j := nw * (y / 2 - ty0) + (x / 2 - tx0)
  have hjx : x / 2 - tx0 < nw := by omega
  have hjy : y / 2 - ty0 < nh := by omega
  have hj : j < nw * nh := by
    have h1 : nw * (y / 2 - ty0) + nw ≤ nw * nh := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left nw hjy
    omega
  have hjmod : tx0 + j % nw = x / 2 := by
    have : j % nw = x / 2 - tx0 := by
      simp only [j, Nat.mul_add_mod, Nat.mod_eq_of_lt hjx]
    omega
  have hjdiv : ty0 + j / nw = y / 2 := by
    have : j / nw = y / 2 - ty0 := by
      simp only [j, Nat.mul_add_div hnw, Nat.div_eq_of_lt hjx, Nat.add_zero]
    omega
  apply testBit_rectPortMask_go hj
  rw [hjmod, hjdiv, hgrid]
  rw [portPresent_eq_at] at hpres
  have hqa : quadrantAt x y = quadrantAt (x % 2) (y % 2) := by
    simp only [quadrantAt, Nat.mod_mod]
  rw [hqa] at hpres
  have htile := testBit_tileMaskFromBytes_of_present (rowStride := 4 * width)
    (Nat.mod_lt x (by decide)) (Nat.mod_lt y (by decide)) hpres
  have hcode : encodePort width ⟨x, y, s⟩ =
      4 * (width * (2 * (y / 2)) + 2 * (x / 2)) +
        (4 * width * (y % 2) + 4 * (x % 2) + sideCode s) := by
    have hx2 : 2 * (x / 2) + x % 2 = x := Nat.div_add_mod x 2
    have hy2 : 2 * (y / 2) + y % 2 = y := Nat.div_add_mod y 2
    simp only [encodePort]
    have hmul : width * y = width * (2 * (y / 2)) + width * (y % 2) := by
      conv_lhs => rw [← hy2]
      exact Nat.mul_add width _ _
    have h4mul : 4 * width * (y % 2) = 4 * (width * (y % 2)) := Nat.mul_assoc 4 width (y % 2)
    omega
  rw [hcode]
  exact testBit_shiftLeft_add htile

private def gridMoveMask (width gridNat : Nat) : Nat :=
  go (width / 2) (8 * width) ((width / 2) * (width / 2))
where
  go (tw rowStride : Nat) : Nat → Nat
    | 0 => 0
    | k + 1 =>
      let tx := k % tw
      let ty := k / tw
      let tc := (gridNat >>> (5 * (tw * ty + tx))) &&& 31
      let bitOff := 8 * (width * (2 * ty) + 2 * tx)
      (tileMoveMaskFromTable rowStride tc <<< bitOff) ||| go tw rowStride k

private theorem testBit_gridMoveMask_go {width gridNat m bit : Nat}
    (h : (gridMoveMask.go width gridNat (width / 2) (8 * width) m).testBit bit = true) :
    ∃ k < m,
      let tw := width / 2
      let tx := k % tw
      let ty := k / tw
      let tc := (gridNat >>> (5 * (tw * ty + tx))) &&& 31
      let bitOff := 8 * (width * (2 * ty) + 2 * tx)
      (tileMoveMaskFromTable (8 * width) tc <<< bitOff).testBit bit = true := by
  induction m with
  | zero => exact absurd (by simpa only [gridMoveMask.go, Nat.zero_testBit] using h) Bool.false_ne_true
  | succ k ih =>
    simp only [gridMoveMask.go, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with hhead | htail
    · exact ⟨k, Nat.lt_succ_self k, hhead⟩
    · obtain ⟨j, hj, hjh⟩ := ih htail
      exact ⟨j, Nat.lt_succ_of_lt hj, hjh⟩

private theorem cell_of_band {width tx ty dy x y j d : Nat}
    (heven : 2 * (width / 2) = width) (hx : x < width) (htx : tx < width / 2)
    (hdy : dy < 2) (hj : j < 7) (hd : d < 16)
    (hlo : 8 * (width * (2 * ty + dy) + 2 * tx) ≤ 8 * (width * y + x) + j)
    (hdef : d = 8 * (width * y + x) + j - 8 * (width * (2 * ty + dy) + 2 * tx)) :
    y = 2 * ty + dy ∧ tx = x / 2 ∧ ty = y / 2 ∧ d = 8 * (x % 2) + j := by
  have hcell : width * (2 * ty + dy) + 2 * tx ≤ width * y + x ∧
      width * y + x < width * (2 * ty + dy) + 2 * tx + 2 := by omega
  have hyEq : y = 2 * ty + dy := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hmul := Nat.mul_le_mul_left width hlt
      rw [Nat.mul_succ] at hmul; omega
    · have hmul := Nat.mul_le_mul_left width hgt
      rw [Nat.mul_succ] at hmul; omega
  have htxEq : tx = x / 2 := by rw [hyEq] at hcell; omega
  have htyEq : ty = y / 2 := by omega
  have hdEq : d = 8 * (x % 2) + j := by
    have : width * y = width * (2 * ty + dy) := by rw [hyEq]
    omega
  exact ⟨hyEq, htxEq, htyEq, hdEq⟩

private theorem kindValid_of_testBit_gridMoveMask {width gridNat : Nat}
    {grid : Nat → Nat → Index} {x y j : Nat}
    (heven : 2 * (width / 2) = width) (hx : x < width) (_hy : y < width) (hj : j < 7)
    (hgrid : ((gridNat >>> (5 * ((width / 2) * (y / 2) + x / 2))) &&& 31) =
      thickCode (componentAt grid x y))
    (hbit : (gridMoveMask width gridNat).testBit (8 * (width * y + x) + j) = true) :
    kindValid (componentAt grid x y) (quadrantAt x y) (j + 2) = true := by
  obtain ⟨k, _, hk⟩ := testBit_gridMoveMask_go hbit
  dsimp only at hk
  set tw := width / 2
  set tx := k % tw
  set ty := k / tw
  set tc := (gridNat >>> (5 * (tw * ty + tx))) &&& 31
  have htw : 0 < tw := by omega
  have htxlt : tx < tw := Nat.mod_lt k htw
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨hle, htile⟩ := hk
  have hle' : 8 * (width * (2 * ty) + 2 * tx) ≤ 8 * (width * y + x) + j := hle
  simp only [tileMoveMaskFromTable, Nat.testBit_or, Bool.or_eq_true] at htile
  rcases htile with hsouth | hnorth
  · set d := 8 * (width * y + x) + j - 8 * (width * (2 * ty) + 2 * tx)
    change (((kindValidTable >>> (32 * tc)) &&& 4294967295) &&& 65535).testBit d = true at hsouth
    have hd16 : d < 16 := by
      by_contra hge
      have hmask : (65535 : Nat).testBit d = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16)
          (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
      simp only [Nat.testBit_and, hmask, Bool.and_false] at hsouth
      exact Bool.false_ne_true hsouth
    obtain ⟨hyEq, htxEq, htyEq, hdEq⟩ := cell_of_band heven hx htxlt (dy := 0) (by decide) hj hd16
      (by simpa only [Nat.add_zero] using hle') (by simp only [Nat.add_zero]; rfl)
    have hkv : kindValidTable.testBit (32 * tc + (8 * (x % 2) + j)) = true := by
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true] at hsouth
      rw [← hdEq]; exact hsouth.1.1
    have htcEq : tc = thickCode (componentAt grid x y) := by simpa only [tc, htxEq, htyEq] using hgrid
    have hq : quadrantCode (quadrantAt x y) = x % 2 := by
      rw [quadrantCode_quadrantAt, hyEq, Nat.add_zero, Nat.mul_mod_right, Nat.mul_zero, Nat.zero_add]
    rw [← testBit_kindValidTable (componentAt grid x y) (quadrantAt x y) hj, hq, ← htcEq]
    simpa only [Nat.add_assoc] using hkv
  · simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hnorth
    obtain ⟨hle2, hnorthBit⟩ := hnorth
    have hle2' : 8 * width ≤ 8 * (width * y + x) + j - 8 * (width * (2 * ty) + 2 * tx) := hle2
    have hmul : width * (2 * ty + 1) = width * (2 * ty) + width := by rw [Nat.mul_add, Nat.mul_one]
    set d := 8 * (width * y + x) + j - 8 * (width * (2 * ty) + 2 * tx) - 8 * width
    change (((kindValidTable >>> (32 * tc)) &&& 4294967295) >>> 16).testBit d = true at hnorthBit
    have hd16 : d < 16 := by
      by_contra hge
      have hbits_lt : ((kindValidTable >>> (32 * tc)) &&& 4294967295) < 2 ^ 32 := by
        rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      have hsh_lt : ((kindValidTable >>> (32 * tc)) &&& 4294967295) >>> 16 < 2 ^ 16 := by
        rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by decide)]; exact hbits_lt
      have h0 : (((kindValidTable >>> (32 * tc)) &&& 4294967295) >>> 16).testBit d = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hsh_lt
          (Nat.pow_le_pow_right (n := 2) (by decide) (by omega)))
      rw [h0] at hnorthBit; exact Bool.false_ne_true hnorthBit
    obtain ⟨hyEq, htxEq, htyEq, hdEq⟩ := cell_of_band (tx := tx) (ty := ty) (dy := 1) (y := y)
      heven hx htxlt (by decide) hj hd16 (by omega) (by omega)
    have hkv : kindValidTable.testBit (32 * tc + (16 + 8 * (x % 2) + j)) = true := by
      simp only [Nat.testBit_shiftRight, Nat.testBit_and, Bool.and_eq_true] at hnorthBit
      rw [← show 32 * tc + (16 + d) = 32 * tc + (16 + 8 * (x % 2) + j) by omega]
      exact hnorthBit.1
    have htcEq : tc = thickCode (componentAt grid x y) := by simpa only [tc, htxEq, htyEq] using hgrid
    have hq : quadrantCode (quadrantAt x y) = 2 + x % 2 := by
      rw [quadrantCode_quadrantAt, hyEq, show (2 * ty + 1) % 2 = 1 by omega]
    rw [← testBit_kindValidTable (componentAt grid x y) (quadrantAt x y) hj, hq, ← htcEq]
    rw [show 32 * tc + 8 * (2 + x % 2) + j = 32 * tc + (16 + 8 * (x % 2) + j) by omega]
    exact hkv

private theorem forest_valid_of_struct_and_moves {width gridNat : Nat}
    {grid : Nat → Nat → Index} {f : Forest width}
    (heven : 2 * (width / 2) = width)
    (hgrid : ∀ x y, x < width → y < width →
      ((gridNat >>> (5 * ((width / 2) * (y / 2) + x / 2))) &&& 31) =
        thickCode (componentAt grid x y))
    (hstruct : f.StructValid)
    (hmoves : ∀ b, (rowsMoveMask f.root f.rows).testBit b = true →
      (gridMoveMask width gridNat).testBit b = true) :
    f.Valid grid := by
  refine ⟨hstruct.1, fun i => ?_⟩
  obtain ⟨hbounds, hrow⟩ := hstruct.2 i
  refine ⟨hbounds, ?_⟩
  by_cases hroot : (f.row i).port = f.root ∧ (f.row i).parity = false
  · exact Or.inl hroot
  · rcases hrow with hroot' | ⟨hpred, hcellLt, hfirst, hsecond, hpar⟩
    · exact Or.inl hroot'
    · right
      refine ⟨hpred, ?_, hfirst, hsecond, hpar⟩
      apply move_valid_of_kindValid
      by_cases hk : (f.row i).move / 2 % 9 < 2
      · exact Or.inl hk
      · right
        have hge : (f.row i).move / 2 % 9 ≥ 2 := by omega
        have hk9 : (f.row i).move / 2 % 9 < 9 := Nat.mod_lt _ (by decide)
        have hj7 : (f.row i).move / 2 % 9 - 2 < 7 := by omega
        have hmem : f.row i ∈ f.rows := by
          have : f.row i = f.rows[i.val] := by
            simp only [Forest.row, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem i.isLt, Option.getD_some]
          rw [this]
          exact List.getElem_mem i.isLt
        have hrm := testBit_rowsMoveMask_of_mem hmem hroot hge
        have hgm := hmoves _ hrm
        have hclt := hcellLt hge
        have hw : 0 < width := by
          by_contra h0
          have hw0 : width = 0 := by omega
          have hmul0 : width * width = 0 := by rw [hw0]
          omega
        have hmx : (f.row i).move / 2 / 9 % width < width := Nat.mod_lt _ hw
        have hmy : (f.row i).move / 2 / 9 / width < width :=
          (Nat.div_lt_iff_lt_mul hw).mpr hclt
        have hdiv : width * ((f.row i).move / 2 / 9 / width) + (f.row i).move / 2 / 9 % width =
            (f.row i).move / 2 / 9 := Nat.div_add_mod _ _
        rw [← hdiv] at hgm
        have hkv := kindValid_of_testBit_gridMoveMask heven hmx hmy hj7
          (hgrid _ _ hmx hmy) hgm
        simpa only [show (f.row i).move / 2 % 9 - 2 + 2 = (f.row i).move / 2 % 9 by omega] using hkv

private theorem mem_sources_of_testBit_quadrant {parent : Index} {dx dy code : Nat}
    (hdx : dx < 2) (hdy : dy < 2)
    (h : (quadrantPortMask (indexThick parent) (quadrantAt dx dy) <<<
      (32 * dy + 4 * dx)).testBit code = true) :
    decodePort 8 code ∈ sources parent := by
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hle, hbit⟩ := h
  set r := code - (32 * dy + 4 * dx)
  have hr : r < 4 := by
    by_contra hge
    have h4 : 4 ≤ r := by omega
    have h0 : (quadrantPortMask (indexThick parent) (quadrantAt dx dy)).testBit r = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (quadrantPortMask_lt _ _)
        (Nat.pow_le_pow_right (n := 2) (by decide) h4))
    rw [h0] at hbit
    exact Bool.false_ne_true hbit
  let side : Side := codeToSide r
  have hside : sideCode side = r := sideCode_codeToSide hr
  have hcode : code = encodePort 8 ⟨dx, dy, side⟩ := by
    simp only [encodePort, hside]; omega
  rw [hcode, decodePort_encodePort (show (⟨dx, dy, side⟩ : Port).x < 8 by dsimp only; omega)]
  have hpres : portPresent (coarseGrid parent) ⟨dx, dy, side⟩ = true := by
    rw [portPresent_eq_at]
    have hq := testBit_quadrantPortMask (indexThick parent) (quadrantAt dx dy) side
    rw [hside, hbit] at hq
    exact hq.symm
  have hsp : sparsePort ⟨dx, dy, side⟩ = ⟨dx, dy, side⟩ := by
    simp only [sparsePort, sparseCoordinate, Nat.div_eq_of_lt hdx, Nat.div_eq_of_lt hdy,
      Nat.mod_eq_of_lt hdx, Nat.mod_eq_of_lt hdy, Nat.mul_zero, Nat.zero_add]
  simp only [sources, List.mem_cons, List.mem_map, List.mem_filter]
  exact Or.inr ⟨⟨dx, dy, side⟩, ⟨mem_portsIn_iff.mpr ⟨hdx, hdy⟩, hpres⟩, hsp⟩

private theorem mem_sources_of_testBit_sourcesMask {parent : Index} {code : Nat}
    (h : (((1 <<< 112) ||| tileMaskFromBytes 32 (thickOf thickTable parent.val))).testBit code =
      true) :
    decodePort 8 code ∈ sources parent := by
  rw [thickOf_thickTable] at h
  simp only [tileMaskFromBytes, tilePortBytes_south, tilePortBytes_north,
    Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with hcyc | (hsw | hse) | hnorth
  · rw [eq_of_testBit_one_shiftLeft hcyc]
    exact List.mem_cons_self
  · exact mem_sources_of_testBit_quadrant (dx := 0) (dy := 0) (by decide) (by decide) (by
      change (quadrantPortMask (indexThick parent) .southwest <<< 0).testBit code = true
      rwa [Nat.shiftLeft_zero])
  · exact mem_sources_of_testBit_quadrant (dx := 1) (dy := 0) (by decide) (by decide) hse
  · simp only [Nat.testBit_shiftLeft, Nat.testBit_or, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq] at hnorth
    obtain ⟨hle, hnw | hne⟩ := hnorth
    · exact mem_sources_of_testBit_quadrant (dx := 0) (dy := 1) (by decide) (by decide) (by
        change (quadrantPortMask (indexThick parent) .northwest <<< 32).testBit code = true
        simp only [Nat.testBit_shiftLeft, hle, decide_true, hnw, Bool.true_and])
    · exact mem_sources_of_testBit_quadrant (dx := 1) (dy := 1) (by decide) (by decide) (by
        change (quadrantPortMask (indexThick parent) .northeast <<< 36).testBit code = true
        simp only [Nat.testBit_shiftLeft, show 36 ≤ code by omega, decide_true,
          show code - 36 = code - 32 - 4 by omega, hne.2, Bool.true_and])

private abbrev oddGrid := iterateRefine 4 (fun _ _ => (0 : Index))

private def oddForests : List (Forest 16) := [
  ⟨341, [
    ⟨341, false, 0, 0⟩, ⟨344, false, 0, 1530⟩, ⟨346, true, 1, 1564⟩,
    ⟨283, true, 2, 1263⟩, ⟨282, true, 3, 1267⟩, ⟨343, false, 0, 1542⟩,
    ⟨345, false, 1, 1552⟩, ⟨347, true, 2, 1554⟩, ⟨348, false, 6, 1548⟩,
    ⟨349, false, 8, 1570⟩, ⟨352, false, 9, 1566⟩, ⟨353, false, 10, 1588⟩,
    ⟨406, false, 5, 1532⟩, ⟨404, true, 12, 1835⟩, ⟨401, true, 13, 1801⟩,
    ⟨400, true, 14, 1805⟩, ⟨405, true, 13, 1822⟩, ⟨407, false, 12, 1824⟩,
    ⟨410, true, 7, 1550⟩, ⟨408, true, 18, 1847⟩, ⟨470, false, 17, 1820⟩,
    ⟨471, false, 20, 2112⟩, ⟨534, false, 21, 2108⟩, ⟨535, false, 22, 2400⟩
  ]⟩,
  ⟨368, [
    ⟨368, false, 0, 0⟩, ⟨365, false, 0, 1639⟩, ⟨364, false, 1, 1643⟩,
    ⟨366, true, 2, 1654⟩, ⟨303, true, 3, 1353⟩, ⟨302, true, 4, 1357⟩,
    ⟨361, false, 2, 1621⟩, ⟨360, false, 6, 1625⟩, ⟨357, false, 7, 1603⟩,
    ⟨356, false, 8, 1607⟩, ⟨367, true, 3, 1644⟩, ⟨371, false, 0, 1664⟩,
    ⟨434, false, 11, 1658⟩, ⟨432, true, 12, 1961⟩, ⟨429, true, 13, 1927⟩,
    ⟨430, true, 14, 1940⟩
  ]⟩,
  ⟨816, [
    ⟨816, false, 0, 0⟩, ⟨818, false, 0, 3682⟩, ⟨755, false, 1, 3387⟩,
    ⟨754, false, 2, 3391⟩, ⟨691, false, 3, 3099⟩, ⟨690, false, 4, 3103⟩,
    ⟨627, false, 5, 2811⟩, ⟨626, false, 6, 2815⟩, ⟨624, true, 7, 2825⟩,
    ⟨621, true, 8, 2791⟩, ⟨620, true, 9, 2795⟩, ⟨617, true, 10, 2773⟩,
    ⟨616, true, 11, 2777⟩, ⟨613, true, 12, 2755⟩, ⟨813, false, 0, 3655⟩,
    ⟨812, false, 14, 3659⟩, ⟨809, false, 15, 3637⟩, ⟨808, false, 16, 3641⟩,
    ⟨805, false, 17, 3619⟩, ⟨804, false, 18, 3623⟩, ⟨806, true, 19, 3634⟩,
    ⟨743, true, 20, 3333⟩, ⟨742, true, 21, 3337⟩, ⟨679, true, 22, 3045⟩,
    ⟨678, true, 23, 3049⟩, ⟨615, true, 24, 2757⟩, ⟨752, true, 3, 3401⟩,
    ⟨749, true, 26, 3367⟩, ⟨814, true, 15, 3670⟩, ⟨751, true, 28, 3369⟩
  ]⟩,
  ⟨789, [
    ⟨789, false, 0, 0⟩, ⟨790, false, 0, 3560⟩, ⟨727, false, 1, 3261⟩,
    ⟨726, false, 2, 3265⟩, ⟨663, false, 3, 2973⟩, ⟨662, false, 4, 2977⟩,
    ⟨599, false, 5, 2685⟩, ⟨598, false, 6, 2689⟩, ⟨724, true, 3, 3275⟩,
    ⟨721, true, 8, 3241⟩, ⟨720, true, 9, 3245⟩, ⟨792, false, 0, 3546⟩,
    ⟨794, true, 11, 3580⟩, ⟨731, true, 12, 3279⟩, ⟨728, true, 13, 3285⟩,
    ⟨725, true, 14, 3259⟩
  ]⟩
]

private def oddGridNat (ct tt : Nat) : Nat :=
  packFin 5 64 fun slot =>
    let tx := slot.val % 8
    let ty := slot.val / 8
    let c0 := childOf ct 0 0 0
    let c1 := childOf ct c0 (tx / 4) (ty / 4)
    let c2 := childOf ct c1 (tx / 2 % 2) (ty / 2 % 2)
    thickOf tt (childOf ct c2 (tx % 2) (ty % 2))

private theorem unpack_oddGridNat {x y : Nat} (hx : x < 16) (hy : y < 16) :
    ((oddGridNat childTable thickTable >>> (5 * (8 * (y / 2) + x / 2))) &&& 31) =
      thickCode (componentAt oddGrid x y) := by
  have hslot : 8 * (y / 2) + x / 2 < 64 := by omega
  have hlt : ∀ s : Fin 64,
      thickOf thickTable
        (childOf childTable
          (childOf childTable
            (childOf childTable (childOf childTable 0 0 0) (s.val % 8 / 4) (s.val / 8 / 4))
            (s.val % 8 / 2 % 2) (s.val / 8 / 2 % 2))
          (s.val % 8 % 2) (s.val / 8 % 2)) < 2 ^ 5 := by
    intro s
    simp only [thickOf, show (31 : Nat) = 2 ^ 5 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hu := unpack_packFin (stride := 5) hlt ⟨8 * (y / 2) + x / 2, hslot⟩
  change ((oddGridNat childTable thickTable >>> (5 * (8 * (y / 2) + x / 2))) &&& 31) = _ at hu
  rw [hu]
  have htx : (8 * (y / 2) + x / 2) % 8 = x / 2 := by omega
  have hty : (8 * (y / 2) + x / 2) / 8 = y / 2 := by omega
  dsimp only
  rw [htx, hty]
  have hx2 : x / 2 / 4 < 2 := by omega
  have hy2 : y / 2 / 4 < 2 := by omega
  have hx1 : x / 2 / 2 % 2 < 2 := by omega
  have hy1 : y / 2 / 2 % 2 < 2 := by omega
  have hx0 : x / 2 % 2 < 2 := by omega
  have hy0 : y / 2 % 2 < 2 := by omega
  let c0 := childBlock (0 : Index) 0 0
  let c1 := childBlock c0 ⟨x / 2 / 4, hx2⟩ ⟨y / 2 / 4, hy2⟩
  let c2 := childBlock c1 ⟨x / 2 / 2 % 2, hx1⟩ ⟨y / 2 / 2 % 2, hy1⟩
  have hc0 : childOf childTable 0 0 0 = c0.val := childOf_childTable (0 : Index) 0 0
  have hc1 : childOf childTable c0.val (x / 2 / 4) (y / 2 / 4) = c1.val :=
    childOf_childTable c0 ⟨x / 2 / 4, hx2⟩ ⟨y / 2 / 4, hy2⟩
  have hc2 : childOf childTable c1.val (x / 2 / 2 % 2) (y / 2 / 2 % 2) = c2.val :=
    childOf_childTable c1 ⟨x / 2 / 2 % 2, hx1⟩ ⟨y / 2 / 2 % 2, hy1⟩
  have hc3 : childOf childTable c2.val (x / 2 % 2) (y / 2 % 2) =
      (childBlock c2 ⟨x / 2 % 2, hx0⟩ ⟨y / 2 % 2, hy0⟩).val :=
    childOf_childTable c2 ⟨x / 2 % 2, hx0⟩ ⟨y / 2 % 2, hy0⟩
  rw [hc0, hc1, hc2, hc3, thickOf_thickTable]
  have hxa : x / 2 / 2 / 2 / 2 = 0 := by omega
  have hya : y / 2 / 2 / 2 / 2 = 0 := by omega
  have hxb : x / 2 / 2 / 2 % 2 = x / 2 / 4 := by omega
  have hyb : y / 2 / 2 / 2 % 2 = y / 2 / 4 := by omega
  simp only [componentAt, indexThick, oddGrid, iterateRefine, refineIndexGrid,
    hxa, hya, hxb, hyb, Nat.zero_mod]
  rfl

private def checkParent (ct tt : Nat) (parent : Index) : Bool :=
  let g := fineGridNat ct tt parent.val
  let tc := thickOf tt parent.val
  let sMask := (1 <<< 112) ||| tileMaskFromBytes 32 tc
  let ids := selected parent
  let expected := rectPortMask 8 0 0 4 4 g
  let validMoves := gridMoveMask 8 g
  let reached := selectedMask ids
  let reqMoves := selectedMoveMask ids
  let ce := thickOf tt (childOf ct (childOf ct parent.val 1 0) 1 0)
  let cn := thickOf tt (childOf ct (childOf ct parent.val 0 1) 0 1)
  (ids.all fun id => sMask.testBit (forest id).root) &&
  ((reached &&& expected) == expected) &&
  ((validMoves &&& reqMoves) == reqMoves) &&
  (!tilePortBytesTable.testBit (16 * tc + 5) || ids.any fun id => connectsCode (forest id) 5 29) &&
  (!tilePortBytesTable.testBit (16 * tc + 13) || ids.any fun id => connectsCode (forest id) 37 61) &&
  (!tilePortBytesTable.testBit (16 * tc + 11) || ids.any fun id => connectsCode (forest id) 35 227) &&
  (!tilePortBytesTable.testBit (16 * tc + 15) || ids.any fun id => connectsCode (forest id) 39 231) &&
  (tilePortBytesTable.testBit (16 * ce + 5) == tilePortBytesTable.testBit (16 * tc + 5)) &&
  (tilePortBytesTable.testBit (16 * ce + 13) == tilePortBytesTable.testBit (16 * tc + 13)) &&
  (tilePortBytesTable.testBit (16 * cn + 11) == tilePortBytesTable.testBit (16 * tc + 11)) &&
  (tilePortBytesTable.testBit (16 * cn + 15) == tilePortBytesTable.testBit (16 * tc + 15))

private def checkAll : Bool :=
  let ct := childTable
  let tt := thickTable
  let baseMask := rectPortMask 8 1 1 2 2 (fineGridNat ct tt 0)
  let oddG := oddGridNat ct tt
  let oddMoves := gridMoveMask 16 oddG
  let oddMask := rectPortMask 16 2 2 4 4 oddG
  allFin 32 (fun id => checkForestStruct 8 (forest id)) &&
  allFin 104 (checkParent ct tt) &&
  ((rowsMask (forest 2).rows &&& baseMask) == baseMask) &&
  (oddForests.all fun f =>
    checkForestStruct 16 f &&
    ((oddMoves &&& rowsMoveMask f.root f.rows) == rowsMoveMask f.root f.rows) &&
    (f.root == 341 || f.root == 368 || f.root == 816 || f.root == 789)) &&
  ((forestsMask oddForests &&& oddMask) == oddMask)

private theorem allCertificatesChecked : checkAll = true := by
  decide +kernel

private def Verified (parent : Index) : Prop :=
  (∀ id ∈ selected parent,
    (forest id).Valid (fineGrid parent) ∧ decodePort 8 (forest id).root ∈ sources parent) ∧
  (∀ x y : Fin 8, ∀ s : Side,
    portPresent (fineGrid parent) ⟨x, y, s⟩ = true →
    ((selected parent).any fun id => Forest.reaches (forest id) ⟨x, y, s⟩) = true) ∧
  (∀ exit : ExitSide, ∀ offset : Fin 2,
    portPresent (coarseGrid parent) (internalPort exit offset) = true →
    ((selected parent).any fun id =>
      connects (forest id) (internalPort exit offset) (externalPort exit offset)) = true)

private theorem verified_and_boundary (parent : Index) :
    Verified parent ∧
    (hasEast (indexThick (childBlock (childBlock parent 1 0) 1 0)) .southeast =
      hasEast (indexThick parent) .southeast ∧
     hasEast (indexThick (childBlock (childBlock parent 1 0) 1 0)) .northeast =
      hasEast (indexThick parent) .northeast ∧
     hasNorth (indexThick (childBlock (childBlock parent 0 1) 0 1)) .northwest =
      hasNorth (indexThick parent) .northwest ∧
     hasNorth (indexThick (childBlock (childBlock parent 0 1) 0 1)) .northeast =
      hasNorth (indexThick parent) .northeast) := by
  have hall := allCertificatesChecked
  simp only [checkAll, Bool.and_eq_true] at hall
  have hstruct := allFin_sound hall.1.1.1.1
  have hp := allFin_sound hall.1.1.1.2 parent
  simp only [checkParent, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hroots, hcov⟩, hmoves⟩, he0⟩, he1⟩, hn0⟩, hn1⟩, hbe0⟩, hbe1⟩, hbn0⟩, hbn1⟩ := hp
  have htc : thickOf thickTable parent.val = thickCode (indexThick parent) :=
    thickOf_thickTable parent
  have hce : thickOf thickTable
      (childOf childTable (childOf childTable parent.val 1 0) 1 0) =
      thickCode (indexThick (childBlock (childBlock parent 1 0) 1 0)) := by
    have h1 : childOf childTable parent.val 1 0 = (childBlock parent 1 0).val :=
      childOf_childTable parent 1 0
    have h2 : childOf childTable (childBlock parent 1 0).val 1 0 =
        (childBlock (childBlock parent 1 0) 1 0).val :=
      childOf_childTable (childBlock parent 1 0) 1 0
    rw [h1, h2, thickOf_thickTable]
  have hcn : thickOf thickTable
      (childOf childTable (childOf childTable parent.val 0 1) 0 1) =
      thickCode (indexThick (childBlock (childBlock parent 0 1) 0 1)) := by
    have h1 : childOf childTable parent.val 0 1 = (childBlock parent 0 1).val :=
      childOf_childTable parent 0 1
    have h2 : childOf childTable (childBlock parent 0 1).val 0 1 =
        (childBlock (childBlock parent 0 1) 0 1).val :=
      childOf_childTable (childBlock parent 0 1) 0 1
    rw [h1, h2, thickOf_thickTable]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro id hid
    refine ⟨forest_valid_of_struct_and_moves rfl
      (fun x y hx hy => unpack_fineGridNat parent hx hy)
      (checkForestStruct_sound (by decide) (by decide) (hstruct id))
      (fun b hb => testBit_of_land_eq hmoves (testBit_selectedMoveMask_of_mem hid hb)),
      mem_sources_of_testBit_sourcesMask (hroots id hid)⟩
  · intro x y s hpres
    have hexp := testBit_rectPortMask_of_present (width := 8) (tx0 := 0) (ty0 := 0)
      (nw := 4) (nh := 4) (Nat.zero_le _) x.isLt (Nat.zero_le _) y.isLt
      (unpack_fineGridNat parent x.isLt y.isLt) hpres
    exact any_reaches_of_testBit_selectedMask x.isLt (testBit_of_land_eq hcov hexp)
  · intro exit offset hpres
    rw [htc, tilePortBytes_east_se] at he0
    rw [htc, tilePortBytes_east_ne] at he1
    rw [htc, tilePortBytes_north_nw] at hn0
    rw [htc, tilePortBytes_north_ne] at hn1
    rcases offset with ⟨off, hoff⟩
    cases exit <;> rcases (show off = 0 ∨ off = 1 by omega) with rfl | rfl
    · rcases he0 with hfalse | hconn
      · simp only [internalPort, portPresent, componentAt, coarseGrid, quadrantAt,
          Quadrant.ofBits, hfalse] at hpres
        exact absurd hpres Bool.false_ne_true
      · obtain ⟨id, hid, hc⟩ := List.any_eq_true.mp hconn
        exact List.any_eq_true.mpr ⟨id, hid, connects_of_connectsCode hc⟩
    · rcases he1 with hfalse | hconn
      · simp only [internalPort, portPresent, componentAt, coarseGrid, quadrantAt,
          Quadrant.ofBits, hfalse] at hpres
        exact absurd hpres Bool.false_ne_true
      · obtain ⟨id, hid, hc⟩ := List.any_eq_true.mp hconn
        exact List.any_eq_true.mpr ⟨id, hid, connects_of_connectsCode hc⟩
    · rcases hn0 with hfalse | hconn
      · simp only [internalPort, portPresent, componentAt, coarseGrid, quadrantAt,
          Quadrant.ofBits, hfalse] at hpres
        exact absurd hpres Bool.false_ne_true
      · obtain ⟨id, hid, hc⟩ := List.any_eq_true.mp hconn
        exact List.any_eq_true.mpr ⟨id, hid, connects_of_connectsCode hc⟩
    · rcases hn1 with hfalse | hconn
      · simp only [internalPort, portPresent, componentAt, coarseGrid, quadrantAt,
          Quadrant.ofBits, hfalse] at hpres
        exact absurd hpres Bool.false_ne_true
      · obtain ⟨id, hid, hc⟩ := List.any_eq_true.mp hconn
        exact List.any_eq_true.mpr ⟨id, hid, connects_of_connectsCode hc⟩
  · simpa only [hce, htc, tilePortBytes_east_se] using hbe0
  · simpa only [hce, htc, tilePortBytes_east_ne] using hbe1
  · simpa only [hcn, htc, tilePortBytes_north_nw] using hbn0
  · simpa only [hcn, htc, tilePortBytes_north_ne] using hbn1

private theorem verified (parent : Index) : Verified parent :=
  (verified_and_boundary parent).1

private theorem baseChecked : ∀ x y : Fin 4, ∀ s : Side,
    portPresent (fineGrid 0) ⟨2 + x.val, 2 + y.val, s⟩ = true →
    Forest.reaches (forest 2) ⟨2 + x.val, 2 + y.val, s⟩ = true := by
  have hall := allCertificatesChecked
  simp only [checkAll, Bool.and_eq_true, beq_iff_eq] at hall
  have hbase := hall.1.1.2
  intro x y s hpres
  have hx : 2 + x.val < 8 := by omega
  have hy : 2 + y.val < 8 := by omega
  have hexp := testBit_rectPortMask_of_present (width := 8) (tx0 := 1) (ty0 := 1)
    (nw := 2) (nh := 2) (by omega) (by omega) (by omega) (by omega)
    (unpack_fineGridNat 0 hx hy) hpres
  rw [Fin.val_zero] at hexp
  have hbit := testBit_of_land_eq hbase hexp
  exact reaches_of_testBit_rowsMask hx hbit

private theorem oddChecked : ∀ forest ∈ oddForests, forest.Valid oddGrid ∧
    forest.rootPort ∈ ([⟨5, 5, .east⟩, ⟨12, 5, .west⟩,
      ⟨12, 12, .west⟩, ⟨5, 12, .east⟩] : List Port) := by
  have hall := allCertificatesChecked
  simp only [checkAll, Bool.and_eq_true, List.all_eq_true] at hall
  intro f hf
  have hfh := hall.1.2 f hf
  simp only [Bool.or_eq_true, beq_iff_eq] at hfh
  refine ⟨forest_valid_of_struct_and_moves rfl
    (fun x y hx hy => unpack_oddGridNat hx hy)
    (checkForestStruct_sound (by decide) (by decide) hfh.1.1)
    (fun b hb => testBit_of_land_eq hfh.1.2 hb), ?_⟩
  rcases hfh.2 with ((h341 | h368) | h816) | h789
  · simp only [Forest.rootPort, h341]; decide
  · simp only [Forest.rootPort, h368]; decide
  · simp only [Forest.rootPort, h816]; decide
  · simp only [Forest.rootPort, h789]; decide

private theorem oddCovers : ∀ x y : Fin 8, ∀ s : Side,
    portPresent oddGrid ⟨4 + x.val, 4 + y.val, s⟩ = true →
      (oddForests.any fun forest => forest.reaches ⟨4 + x.val, 4 + y.val, s⟩) = true := by
  have hall := allCertificatesChecked
  simp only [checkAll, Bool.and_eq_true, beq_iff_eq] at hall
  have hcov := hall.2
  intro x y s hpres
  have hx : 4 + x.val < 16 := by omega
  have hy : 4 + y.val < 16 := by omega
  have hexp := testBit_rectPortMask_of_present (width := 16) (tx0 := 2) (ty0 := 2)
    (nw := 4) (nh := 4) (by omega) (by omega) (by omega) (by omega)
    (unpack_oddGridNat hx hy) hpres
  exact any_reaches_of_testBit_forestsMask hx (testBit_of_land_eq hcov hexp)

/-- A valid forest that reaches a port supplies a bounded red path with some parity. -/
private theorem Forest.reaches_sound {width : Nat} {grid : Nat → Nat → Index} {f : Forest width}
    (valid : f.Valid grid) {target : Port} (h : f.reaches target = true) :
    ∃ parity, BoundedPath grid width width f.rootPort target parity := by
  obtain ⟨r, hr, eq⟩ := List.any_eq_true.mp h
  have targetEq : decodePort width r.port = target := of_decide_eq_true eq
  exact ⟨r.parity, targetEq ▸ Forest.sound_mem valid hr⟩

private theorem connects_sound {grid : Nat → Nat → Index} {f : Forest 8}
    (valid : f.Valid grid) {start finish : Port} (h : connects f start finish = true) :
    BoundedPath grid 8 8 start finish false := by
  simp only [connects, Bool.and_eq_true] at h
  obtain ⟨hroot, hnode⟩ := h
  have rootEq : decodePort 8 f.root = start := of_decide_eq_true hroot
  obtain ⟨r, hr, hend⟩ := List.any_eq_true.mp hnode
  obtain ⟨targetEq, parityEq⟩ := of_decide_eq_true hend
  simpa only [rootEq, targetEq, parityEq] using Forest.sound_mem valid hr

end RedPathCertificate
open RedPathCertificate

/-- Every live old east or north port reaches its macrocell boundary evenly,
with every intermediate port inside the `8 × 8` quarter block. -/
private theorem boundedConnectorPath (parent : Index) (exit : ExitSide)
    {offset : Nat} (hoffset : offset < 2)
    (present : portPresent (coarseGrid parent) (internalPort exit offset) = true) :
    BoundedPath (fineGrid parent) 8 8 (internalPort exit offset)
      (externalPort exit offset) false := by
  have checked := (verified parent).2.2
  have accepted : ((selected parent).any fun id =>
      connects (forest id) (internalPort exit offset) (externalPort exit offset)) = true :=
    checked exit ⟨offset, hoffset⟩ present
  obtain ⟨id, hid, h⟩ := List.any_eq_true.mp accepted
  exact connects_sound ((verified parent).1 id hid).1 h

/-- Every live port in a two-substitution block has a bounded path from the
new cycle or an inherited live old port. -/
theorem exists_boundedPath (parent : Index) {target : Port}
    (mem : target ∈ portsIn 8 8)
    (present : portPresent (fineGrid parent) target = true) :
    ∃ source ∈ sources parent, ∃ parity,
      BoundedPath (fineGrid parent) 8 8 source target parity := by
  obtain ⟨hx, hy⟩ := mem_portsIn_iff.mp mem
  have accepted := (verified parent).2.1 ⟨target.x, hx⟩ ⟨target.y, hy⟩ target.side
  obtain ⟨id, hid, hreach⟩ := List.any_eq_true.mp (accepted present)
  obtain ⟨valid, hsource⟩ := (verified parent).1 id hid
  exact ⟨_, hsource, Forest.reaches_sound valid hreach⟩

/-- Every live port in the central `4 × 4` region of parent zero's block
belongs to the newly created cycle component. -/
theorem base_exists_boundedPath {target : Port}
    (west : 2 ≤ target.x) (east : target.x < 6)
    (south : 2 ≤ target.y) (north : target.y < 6)
    (present : portPresent (fineGrid 0) target = true) :
    ∃ parity, BoundedPath (fineGrid 0) 8 8 cycleSource target parity := by
  have targetEq : (⟨2 + (target.x - 2), 2 + (target.y - 2), target.side⟩ : Port) = target := by
    have hx : 2 + (target.x - 2) = target.x := by omega
    have hy : 2 + (target.y - 2) = target.y := by omega
    cases target
    simp only [Port.mk.injEq]
    exact ⟨hx, hy, trivial⟩
  have h := baseChecked ⟨target.x - 2, by omega⟩ ⟨target.y - 2, by omega⟩ target.side
  rw [targetEq] at h
  exact Forest.reaches_sound ((verified 0).1 2 (by decide)).1 (h present)

/-- Every live port in the odd root's central square has a bounded path from a root corner.
This is the finite base case of the odd-phase shade comparison, after lean-wang's
`CanonicalOddShadeBase.exists_boundedPath` at revision `64268a3`. -/
theorem odd_base_exists_boundedPath {target : Port}
    (west : 4 ≤ target.x) (east : target.x < 12)
    (south : 4 ≤ target.y) (north : target.y < 12)
    (present : portPresent (iterateRefine 4 (fun _ _ => (0 : Index))) target = true) :
    ∃ source parity,
      source ∈ ([⟨5, 5, .east⟩, ⟨12, 5, .west⟩, ⟨12, 12, .west⟩, ⟨5, 12, .east⟩] : List Port) ∧
      BoundedPath (iterateRefine 4 (fun _ _ => (0 : Index))) 16 16 source target parity := by
  have target_eq : (⟨4 + (target.x - 4), 4 + (target.y - 4), target.side⟩ : Port) = target := by
    cases target
    dsimp only at *
    simp only [Port.mk.injEq]
    exact ⟨by omega, by omega, trivial⟩
  have h := oddCovers ⟨target.x - 4, by omega⟩ ⟨target.y - 4, by omega⟩ target.side
  rw [target_eq] at h
  obtain ⟨forest, mem, reached⟩ := List.any_eq_true.mp (h present)
  obtain ⟨valid, source⟩ := oddChecked forest mem
  obtain ⟨parity, path⟩ := Forest.reaches_sound valid reached
  exact ⟨forest.rootPort, parity, source, path⟩

/-- The two possible origins of a local coverage path. -/
theorem source_cases {parent : Index} {source : Port} (h : source ∈ sources parent) :
    source = cycleSource ∨ ∃ old ∈ portsIn 2 2,
      portPresent (coarseGrid parent) old = true ∧ source = sparsePort old := by
  simp only [sources, List.mem_cons, List.mem_map, List.mem_filter] at h
  rcases h with h | ⟨old, ⟨mem, live⟩, eq⟩
  · exact Or.inl h
  · exact Or.inr ⟨old, mem, live, eq.symm⟩

/-- Translate a quarter port without changing its side. -/
@[expose] def translatePort (port : Port) (offsetX offsetY : Nat) : Port :=
  ⟨offsetX + port.x, offsetY + port.y, port.side⟩

private theorem link_translate
    {grid other : Nat → Nat → Index} {width height offsetX offsetY : Nat}
    (hx : offsetX % 2 = 0) (hy : offsetY % 2 = 0)
    (componentsEq : ∀ x y, x < width → y < height →
      componentAt grid x y = componentAt other (offsetX + x) (offsetY + y))
    {first second : Port} {parity : Bool}
    (link : Link grid first second parity)
    (hfirst : PortInBounds first width height) (hsecond : PortInBounds second width height) :
    Link other (translatePort first offsetX offsetY)
      (translatePort second offsetX offsetY) parity := by
  have quadrant : ∀ x y,
      quadrantAt (offsetX + x) (offsetY + y) = quadrantAt x y := by
    intro x y
    simp [quadrantAt, Nat.add_mod, hx, hy]
  induction link with
  | horizontalMatch x y =>
    simpa only [translatePort, Nat.add_assoc] using
      Link.horizontalMatch (indexGrid := other) (offsetX + x) (offsetY + y)
  | verticalMatch x y =>
    simpa only [translatePort, Nat.add_assoc] using
      Link.verticalMatch (indexGrid := other) (offsetX + x) (offsetY + y)
  | horizontal x y hpath =>
    apply Link.horizontal
    rw [← componentsEq x y hfirst.1 hfirst.2, quadrant]
    exact hpath
  | vertical x y hpath =>
    apply Link.vertical
    rw [← componentsEq x y hfirst.1 hfirst.2, quadrant]
    exact hpath
  | westNorth x y hwest hnorth =>
    apply Link.westNorth <;> rw [← componentsEq x y hfirst.1 hfirst.2, quadrant]
    · exact hwest
    · exact hnorth
  | westSouth x y hwest hsouth =>
    apply Link.westSouth <;> rw [← componentsEq x y hfirst.1 hfirst.2, quadrant]
    · exact hwest
    · exact hsouth
  | eastNorth x y heast hnorth =>
    apply Link.eastNorth <;> rw [← componentsEq x y hfirst.1 hfirst.2, quadrant]
    · exact heast
    · exact hnorth
  | eastSouth x y heast hsouth =>
    apply Link.eastSouth <;> rw [← componentsEq x y hfirst.1 hfirst.2, quadrant]
    · exact heast
    · exact hsouth
  | crossing x y hhorizontal hvertical =>
    apply Link.crossing <;> rw [← componentsEq x y hfirst.1 hfirst.2, quadrant]
    · exact hhorizontal
    · exact hvertical
  | symm _ ih => exact Link.symm (ih hsecond hfirst)

/-- Transport a bounded path to any even translate with the same local components. -/
theorem boundedPath_translate
    {grid other : Nat → Nat → Index} {width height offsetX offsetY : Nat}
    (hx : offsetX % 2 = 0) (hy : offsetY % 2 = 0)
    (componentsEq : ∀ x y, x < width → y < height →
      componentAt grid x y = componentAt other (offsetX + x) (offsetY + y))
    {first second : Port} {parity : Bool}
    (path : BoundedPath grid width height first second parity) :
    Path other (translatePort first offsetX offsetY)
      (translatePort second offsetX offsetY) parity := by
  induction path with
  | refl _ _ => exact .refl _
  | ofLink link hfirst hsecond =>
    exact .ofLink (link_translate hx hy componentsEq link hfirst hsecond)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- A twice-substituted macrocell depends only on its old parent tile. -/
theorem componentAt_two_block (grid : Nat → Nat → Index) (bx by₀ x y : Nat)
    (hx : x < 8) (hy : y < 8) :
    componentAt (iterateRefine 2 grid) (8 * bx + x) (8 * by₀ + y) =
      componentAt (fineGrid (grid bx by₀)) x y := by
  have coords (b z : Nat) (hz : z < 8) :
      (8 * b + z) / 2 / 2 / 2 = b ∧
      (8 * b + z) / 2 % 2 = z / 2 % 2 ∧
      (8 * b + z) / 2 / 2 % 2 = z / 2 / 2 % 2 := by omega
  obtain ⟨hx₀, hx₁, hx₂⟩ := coords bx x hx
  obtain ⟨hy₀, hy₁, hy₂⟩ := coords by₀ y hy
  simp only [fineGrid, coarseGrid, componentAt, iterateRefine, refineIndexGrid,
    hx₀, hx₁, hx₂, hy₀, hy₁, hy₂]

/-- A checked local route transplanted into the corresponding arbitrary macrocell. -/
theorem boundedPath_two_block (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {first target : Port} {parity : Bool}
    (path : BoundedPath (fineGrid (grid blockX blockY)) 8 8 first target parity) :
    Path (iterateRefine 2 grid)
      (translatePort first (8 * blockX) (8 * blockY))
      (translatePort target (8 * blockX) (8 * blockY)) parity :=
  boundedPath_translate (by omega) (by omega)
    (fun x y hx hy => (componentAt_two_block grid blockX blockY x y hx hy).symm) path

private theorem southwest_component (parent : Index) :
    ∀ x y : Fin 2,
      componentAt (fineGrid parent) x y = componentAt (coarseGrid parent) x y := by
  intro x y
  simpa [indexThick, fineGrid, coarseGrid, componentAt, iterateRefine, refineIndexGrid,
    Nat.div_eq_of_lt x.isLt, Nat.div_eq_of_lt y.isLt, Nat.zero_div, Nat.zero_mod] using
    (childBlock_thick_southwest (childBlock parent 0 0)).trans
      (childBlock_thick_southwest parent)

/-- The sparse old quarters retain their exact thick component. -/
theorem componentAt_iterateRefine_two_sparse (grid : Nat → Nat → Index) (x y : Nat) :
    componentAt (iterateRefine 2 grid) (sparseCoordinate x) (sparseCoordinate y) =
      componentAt grid x y := by
  rw [sparseCoordinate, sparseCoordinate,
    componentAt_two_block grid (x / 2) (y / 2) (x % 2) (y % 2) (by omega) (by omega)]
  have old := southwest_component (grid (x / 2) (y / 2))
    ⟨x % 2, by omega⟩ ⟨y % 2, by omega⟩
  exact old

private theorem quadrantAt_sparse (x y : Nat) :
    quadrantAt (sparseCoordinate x) (sparseCoordinate y) = quadrantAt x y := by
  simp [quadrantAt, sparseCoordinate, Nat.add_mod, Nat.mul_mod]

/-- An east/north port is moved to the macrocell boundary when it exits an old tile. -/
@[expose] def exitCoordinate (coordinate : Nat) : Nat :=
  if coordinate % 2 = 1 then 8 * (coordinate / 2) + 7 else sparseCoordinate coordinate

/-- Side-sensitive refinement: west/south stay sparse, east/north reach the block boundary. -/
@[expose] def refinedPort (port : Port) : Port :=
  match port.side with
  | .east => ⟨exitCoordinate port.x, sparseCoordinate port.y, .east⟩
  | .north => ⟨sparseCoordinate port.x, exitCoordinate port.y, .north⟩
  | .west | .south => sparsePort port

private theorem exitCoordinate_succ (coordinate : Nat) :
    exitCoordinate coordinate + 1 = sparseCoordinate (coordinate + 1) := by
  unfold exitCoordinate sparseCoordinate
  split <;> omega

/-- Port incidence depends only on the containing tile and its local quarter. -/
theorem portPresent_local (grid : Nat → Nat → Index) (port : Port) :
    portPresent (coarseGrid (grid (port.x / 2) (port.y / 2)))
      ⟨port.x % 2, port.y % 2, port.side⟩ = portPresent grid port := by
  cases port with
  | mk x y s =>
    cases s <;> simp [portPresent, componentAt, coarseGrid, quadrantAt]

private theorem local_refinedPort_present (parent : Index) (x y : Fin 2) (s : Side) :
    portPresent (fineGrid parent) (refinedPort ⟨x, y, s⟩) =
      portPresent (coarseGrid parent) ⟨x, y, s⟩ := by
  obtain ⟨he0, he1, hn0, hn1⟩ := (verified_and_boundary parent).2
  cases s with
  | west =>
    have hsp : refinedPort ⟨x, y, .west⟩ = ⟨x, y, .west⟩ := by
      simp only [refinedPort, sparsePort, sparseCoordinate, Nat.div_eq_of_lt x.isLt,
        Nat.div_eq_of_lt y.isLt, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt,
        Nat.mul_zero, Nat.zero_add]
    rw [hsp]
    simp only [portPresent, southwest_component parent x y]
  | south =>
    have hsp : refinedPort ⟨x, y, .south⟩ = ⟨x, y, .south⟩ := by
      simp only [refinedPort, sparsePort, sparseCoordinate, Nat.div_eq_of_lt x.isLt,
        Nat.div_eq_of_lt y.isLt, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt,
        Nat.mul_zero, Nat.zero_add]
    rw [hsp]
    simp only [portPresent, southwest_component parent x y]
  | east =>
    rcases x with ⟨x, hx⟩; rcases y with ⟨y, hy⟩
    rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
      rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> dsimp only
    · rw [show refinedPort ⟨0, 0, .east⟩ = ⟨0, 0, .east⟩ by rfl]
      have hc : componentAt (fineGrid parent) 0 0 = componentAt (coarseGrid parent) 0 0 :=
        southwest_component parent 0 0
      simp only [portPresent, hc]
    · rw [show refinedPort ⟨0, 1, .east⟩ = ⟨0, 1, .east⟩ by rfl]
      have hc : componentAt (fineGrid parent) 0 1 = componentAt (coarseGrid parent) 0 1 :=
        southwest_component parent 0 1
      simp only [portPresent, hc]
    · rw [show refinedPort ⟨1, 0, .east⟩ = ⟨7, 0, .east⟩ by rfl]
      have hcomp : componentAt (fineGrid parent) 7 0 =
          indexThick (childBlock (childBlock parent 1 0) 1 0) := by
        simp only [componentAt, indexThick, fineGrid, coarseGrid, iterateRefine, refineIndexGrid]
        rfl
      simp only [portPresent, show quadrantAt 7 0 = .southeast by rfl,
        show quadrantAt 1 0 = .southeast by rfl]
      rw [hcomp]
      exact he0
    · rw [show refinedPort ⟨1, 1, .east⟩ = ⟨7, 1, .east⟩ by rfl]
      have hcomp : componentAt (fineGrid parent) 7 1 =
          indexThick (childBlock (childBlock parent 1 0) 1 0) := by
        simp only [componentAt, indexThick, fineGrid, coarseGrid, iterateRefine, refineIndexGrid]
        rfl
      simp only [portPresent, show quadrantAt 7 1 = .northeast by rfl,
        show quadrantAt 1 1 = .northeast by rfl]
      rw [hcomp]
      exact he1
  | north =>
    rcases x with ⟨x, hx⟩; rcases y with ⟨y, hy⟩
    rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
      rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> dsimp only
    · rw [show refinedPort ⟨0, 0, .north⟩ = ⟨0, 0, .north⟩ by rfl]
      have hc : componentAt (fineGrid parent) 0 0 = componentAt (coarseGrid parent) 0 0 :=
        southwest_component parent 0 0
      simp only [portPresent, hc]
    · rw [show refinedPort ⟨0, 1, .north⟩ = ⟨0, 7, .north⟩ by rfl]
      have hcomp : componentAt (fineGrid parent) 0 7 =
          indexThick (childBlock (childBlock parent 0 1) 0 1) := by
        simp only [componentAt, indexThick, fineGrid, coarseGrid, iterateRefine, refineIndexGrid]
        rfl
      simp only [portPresent, show quadrantAt 0 7 = .northwest by rfl,
        show quadrantAt 0 1 = .northwest by rfl]
      rw [hcomp]
      exact hn0
    · rw [show refinedPort ⟨1, 0, .north⟩ = ⟨1, 0, .north⟩ by rfl]
      have hc : componentAt (fineGrid parent) 1 0 = componentAt (coarseGrid parent) 1 0 :=
        southwest_component parent 1 0
      simp only [portPresent, hc]
    · rw [show refinedPort ⟨1, 1, .north⟩ = ⟨1, 7, .north⟩ by rfl]
      have hcomp : componentAt (fineGrid parent) 1 7 =
          indexThick (childBlock (childBlock parent 0 1) 0 1) := by
        simp only [componentAt, indexThick, fineGrid, coarseGrid, iterateRefine, refineIndexGrid]
        rfl
      simp only [portPresent, show quadrantAt 1 7 = .northeast by rfl,
        show quadrantAt 1 1 = .northeast by rfl]
      rw [hcomp]
      exact hn1

/-- Port incidence is preserved when a bounded local block is embedded in a refined grid. -/
theorem portPresent_two_block (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (port : Port) (hx : port.x < 8) (hy : port.y < 8) :
    portPresent (fineGrid (grid blockX blockY)) port =
      portPresent (iterateRefine 2 grid)
        (translatePort port (8 * blockX) (8 * blockY)) := by
  have quadrant : quadrantAt (8 * blockX + port.x) (8 * blockY + port.y) =
      quadrantAt port.x port.y := by simp [quadrantAt, Nat.add_mod, Nat.mul_mod]
  cases hs : port.side <;> simp only [portPresent, translatePort, hs] <;>
    rw [componentAt_two_block grid blockX blockY port.x port.y hx hy, quadrant]

/-- The side-sensitive refined image carries a red wire exactly when the old port does. -/
theorem refinedPort_present (grid : Nat → Nat → Index) (port : Port) :
    portPresent (iterateRefine 2 grid) (refinedPort port) = portPresent grid port := by
  let x : Fin 2 := ⟨port.x % 2, Nat.mod_lt _ (by decide)⟩
  let y : Fin 2 := ⟨port.y % 2, Nat.mod_lt _ (by decide)⟩
  let oldPort : Port := ⟨x, y, port.side⟩
  have localBounds : ∀ (i j : Fin 2) (s : Side),
      PortInBounds (refinedPort ⟨i, j, s⟩) 8 8 := by
    intro i j s
    cases s <;>
      simp only [refinedPort, sparsePort, exitCoordinate, sparseCoordinate, PortInBounds] <;>
      first | (split <;> omega) | omega
  have bounds : PortInBounds (refinedPort oldPort) 8 8 := localBounds x y port.side
  have image : refinedPort port =
      translatePort (refinedPort oldPort) (8 * (port.x / 2)) (8 * (port.y / 2)) := by
    have hx : port.x % 2 / 2 = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
    have hy : port.y % 2 / 2 = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
    cases hs : port.side <;>
      simp [refinedPort, sparsePort, exitCoordinate, sparseCoordinate,
        translatePort, oldPort, x, y, hs, hx, hy, apply_ite]
  rw [image, ← portPresent_two_block grid (port.x / 2) (port.y / 2)
    (refinedPort oldPort) bounds.1 bounds.2]
  rw [local_refinedPort_present (grid (port.x / 2) (port.y / 2)) x y port.side]
  exact portPresent_local grid port

/-- A live old port reaches its side-sensitive refined image with even parity. -/
theorem livePortPath (grid : Nat → Nat → Index) (port : Port)
    (live : portPresent grid port = true) :
    Path (iterateRefine 2 grid) (sparsePort port) (refinedPort port) false := by
  cases hs : port.side with
  | west | south => simpa only [refinedPort, hs] using Path.refl (sparsePort port)
  | east =>
    by_cases hx : port.x % 2 = 1
    · have present : portPresent (coarseGrid (grid (port.x / 2) (port.y / 2)))
        (internalPort .east (port.y % 2)) = true := by
        simpa only [internalPort, hs, hx] using (portPresent_local grid port).trans live
      have path := boundedPath_two_block grid (port.x / 2) (port.y / 2)
        (boundedConnectorPath _ .east (by omega) present)
      simpa [sparsePort, refinedPort, hs, exitCoordinate, hx,
        internalPort, externalPort, translatePort, sparseCoordinate] using path
    · simpa [refinedPort, hs, exitCoordinate, hx, sparsePort]
        using Path.refl (sparsePort port)
  | north =>
    by_cases hy : port.y % 2 = 1
    · have present : portPresent (coarseGrid (grid (port.x / 2) (port.y / 2)))
        (internalPort .north (port.x % 2)) = true := by
        simpa only [internalPort, hs, hy] using (portPresent_local grid port).trans live
      have path := boundedPath_two_block grid (port.x / 2) (port.y / 2)
        (boundedConnectorPath _ .north (by omega) present)
      simpa [sparsePort, refinedPort, hs, exitCoordinate, hy,
        internalPort, externalPort, translatePort, sparseCoordinate] using path
    · simpa [refinedPort, hs, exitCoordinate, hy, sparsePort]
        using Path.refl (sparsePort port)

private theorem path_of_sparseLink {grid : Nat → Nat → Index} {first second : Port}
    {parity : Bool} (hfirst : portPresent grid first = true)
    (hsecond : portPresent grid second = true)
    (link : Link (iterateRefine 2 grid) (sparsePort first) (sparsePort second) parity) :
    Path (iterateRefine 2 grid) (refinedPort first) (refinedPort second) parity := by
  simpa only [Bool.false_xor, Bool.xor_false] using
    Path.trans (livePortPath grid first hfirst).symm
      (Path.trans (.ofLink link) (livePortPath grid second hsecond))

/-- Every coarse link refines to a fine path with the same crossing parity. -/
theorem Link.refine {grid : Nat → Nat → Index} {first second : Port} {parity : Bool}
    (link : Link grid first second parity) :
    Path (iterateRefine 2 grid) (refinedPort first) (refinedPort second) parity := by
  induction link with
  | horizontalMatch x y =>
    simpa only [refinedPort, sparsePort, exitCoordinate_succ] using
      Path.ofLink (Link.horizontalMatch (indexGrid := iterateRefine 2 grid)
        (exitCoordinate x) (sparseCoordinate y))
  | verticalMatch x y =>
    simpa only [refinedPort, sparsePort, exitCoordinate_succ] using
      Path.ofLink (Link.verticalMatch (indexGrid := iterateRefine 2 grid)
        (sparseCoordinate x) (exitCoordinate y))
  | horizontal x y h =>
    apply path_of_sparseLink (by simp [portPresent, hasWest, h])
      (by simp [portPresent, hasEast, h])
    apply Link.horizontal
    simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using h
  | vertical x y h =>
    apply path_of_sparseLink (by simp [portPresent, hasSouth, h])
      (by simp [portPresent, hasNorth, h])
    apply Link.vertical
    simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using h
  | westNorth x y hw hn =>
    apply path_of_sparseLink (by simp [portPresent, hasWest, hw])
      (by simp [portPresent, hasNorth, hn])
    apply Link.westNorth
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using hw
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using hn
  | westSouth x y hw hs =>
    apply path_of_sparseLink (by simp [portPresent, hasWest, hw])
      (by simp [portPresent, hasSouth, hs])
    apply Link.westSouth
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using hw
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using hs
  | eastNorth x y he hn =>
    apply path_of_sparseLink (by simp [portPresent, hasEast, he])
      (by simp [portPresent, hasNorth, hn])
    apply Link.eastNorth
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using he
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using hn
  | eastSouth x y he hs =>
    apply path_of_sparseLink (by simp [portPresent, hasEast, he])
      (by simp [portPresent, hasSouth, hs])
    apply Link.eastSouth
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using he
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using hs
  | crossing x y hh hv =>
    apply path_of_sparseLink (by simp [portPresent, hasWest, hh])
      (by simp [portPresent, hasSouth, hv])
    apply Link.crossing
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using hh
    · simpa only [componentAt_iterateRefine_two_sparse, quadrantAt_sparse] using hv
  | symm _ ih => exact ih.symm

/-- Two substitutions preserve the crossing parity of every red path. -/
theorem Path.refine {grid : Nat → Nat → Index} {first second : Port} {parity : Bool}
    (path : Path grid first second parity) :
    Path (iterateRefine 2 grid) (refinedPort first) (refinedPort second) parity := by
  induction path with
  | refl _ => exact .refl _
  | ofLink link => exact Link.refine link
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

end Cslib.WangTile.Robinson
