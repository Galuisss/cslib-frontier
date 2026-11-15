/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation
public import Mathlib.Data.Tree.Get
import Mathlib.Tactic.FinCases

/-!
# Pointer-machine right rotation

The program promotes the left child of the cursor. It repairs both pivot parent links
and the middle subtree's parent link, including the empty-middle case. The caller must
reconnect the external parent's child link (or update its root register). Scalar payloads,
including cached heights, are unchanged; height recomputation belongs to AVL balancing.

The child rewiring adapts the program in Stefan Langerman's
`RotationBST.Models.RealWorld.PointerMachine.Rotation`, extended with parent links.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Promote the left child of cursor zero. Scratch pointers two, three and four
hold the promoted node, external parent and middle subtree. No scalar register changes. -/
@[expose] def rotateRight : List (Instr M (layout extra regs)) :=
  [.loadPtr 2 0 0, .loadPtr 3 2 0, .loadPtr 4 1 2,
   .storePtr 0 0 4, .storePtr 2 4 0, .storePtr 1 2 0,
   .storePtr 2 0 2, .storePtr 2 2 3, .movePtr 0 2, .halt]

private def tick (i : Instr M (layout extra regs)) (s : State M (layout extra regs)) :=
  { i.effect s with pc := s.pc + 1 }

private def finish (s : State M (layout extra regs)) : State M (layout extra regs) :=
  tick (.movePtr 0 2) (tick (.storePtr 2 2 3) (tick (.storePtr 2 0 2)
    (tick (.storePtr 1 2 0) (tick (.storePtr 2 4 0) (tick (.storePtr 0 0 4)
      (tick (.loadPtr 4 1 2) (tick (.loadPtr 3 2 0) (tick (.loadPtr 2 0 0) s))))))))

private theorem runs (s : State M (layout extra regs)) (pc : s.pc = 0) :
    Executes rotateRight s (finish s) 10 := by
  let s1 := tick (.loadPtr 2 0 0) s
  let s2 := tick (.loadPtr 3 2 0) s1
  let s3 := tick (.loadPtr 4 1 2) s2
  let s4 := tick (.storePtr 0 0 4) s3
  let s5 := tick (.storePtr 2 4 0) s4
  let s6 := tick (.storePtr 1 2 0) s5
  let s7 := tick (.storePtr 2 0 2) s6
  let s8 := tick (.storePtr 2 2 3) s7
  refine ⟨9, .head s s1 _ _ ?_ (.head s1 s2 _ _ ?_ (.head s2 s3 _ _ ?_
    (.head s3 s4 _ _ ?_ (.head s4 s5 _ _ ?_ (.head s5 s6 _ _ ?_
      (.head s6 s7 _ _ ?_ (.head s7 s8 _ _ ?_ (.single ?_)))))))), ?_, rfl⟩
  all_goals simp [step, rotateRight, finish, s1, s2, s3, s4, s5, s6, s7, s8, tick,
    Instr.next, pc]

/-- The exact heap writes of a right rotation, in execution order. A null middle
subtree requires no parent write. Pivot addresses are proof data, not machine inputs. -/
@[expose] def rightRewire (h : List (Record M (layout extra regs))) (x y : ℕ)
    (middle parent : Pointer) : List (Record M (layout extra regs)) :=
  let h := h.modify y fun r => { r with ptr := Function.update r.ptr 0 middle }
  let h := middle.elim h fun b =>
    h.modify b fun r => { r with ptr := Function.update r.ptr 2 (some y) }
  let h := h.modify x fun r => { r with ptr := Function.update r.ptr 1 (some y) }
  let h := h.modify y fun r => { r with ptr := Function.update r.ptr 2 (some x) }
  h.modify x fun r => { r with ptr := Function.update r.ptr 2 parent }

/-- A right rotation executes ten instructions, including halt. The heap is exactly
the five local pointer writes; all scalar registers and nonscratch pointers survive.
This is the machine execution lemma, not yet a whole-tree rotation invariant. -/
theorem rotateRight_executes (s : State M (layout extra regs)) (x y : ℕ)
    (rx ry : Record M (layout extra regs)) (pc : s.pc = 0)
    (cursor : s.ptr 0 = some y) (hy : s.heap[y]? = some ry)
    (hx : s.heap[x]? = some rx) (left : ry.ptr 0 = some x) :
    ∃ t, Executes rotateRight s t 10 ∧
      t.heap = rightRewire s.heap x y (rx.ptr 1) (ry.ptr 2) ∧
      t.ptr 0 = some x ∧ t.data = s.data ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → t.ptr i = s.ptr i) := by
  have keep : ∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 →
      (finish s).ptr i = s.ptr i := by
    intro i h0 h2 h3 h4
    cases mid : rx.ptr 1 <;>
      simp [finish, tick, Instr.effect, State.deref, State.setPtr, State.modify,
        cursor, hy, hx, left, mid, h0, h2, h3, h4]
  refine ⟨finish s, runs s pc, ?_, ?_, ?_, keep⟩
  all_goals cases mid : rx.ptr 1 <;>
    simp [finish, tick, Instr.effect, State.deref, State.setPtr, State.modify,
      cursor, hy, hx, left, mid, rightRewire]

/-- Records outside the pivots and the middle root are unchanged. -/
theorem rightRewire_frame (h : List (Record M (layout extra regs))) (x y a : ℕ)
    (middle parent : Pointer) (ax : a ≠ x) (ay : a ≠ y) (am : middle ≠ some a) :
    (rightRewire h x y middle parent)[a]? = h[a]? := by
  cases middle with
  | none => simp [rightRewire, Ne.symm ax, Ne.symm ay]
  | some b =>
    have ab : b ≠ a := fun eq => am (congrArg some eq)
    simp [rightRewire, Ne.symm ax, Ne.symm ay, ab]

/-- Rotation creates no records. -/
@[simp] theorem length_rightRewire (h : List (Record M (layout extra regs))) (x y : ℕ)
    (middle parent : Pointer) : (rightRewire h x y middle parent).length = h.length := by
  cases middle <;> simp [rightRewire]


/-- For distinct pivots and a middle root distinct from both, the promoted node
points right to the old root and inherits its parent; the old root points left to
the middle subtree and has the promoted node as parent. Scalar fields are preserved. -/
private theorem rightRewire_pivots (h : List (Record M (layout extra regs))) (x y : ℕ)
    (rx ry : Record M (layout extra regs)) (hx : h[x]? = some rx)
    (hy : h[y]? = some ry) (different : x ≠ y)
    (mx : rx.ptr 1 ≠ some x) (my : rx.ptr 1 ≠ some y) :
    let h' := rightRewire h x y (rx.ptr 1) (ry.ptr 2)
    h'[x]? = some { rx with ptr := (Function.update
      (Function.update rx.ptr 1 (some y)) 2 (ry.ptr 2)) } ∧
    h'[y]? = some { ry with ptr := (Function.update
      (Function.update ry.ptr 0 (rx.ptr 1)) 2 (some x)) } := by
  cases mid : rx.ptr 1 with
  | none => simp [rightRewire, different, Ne.symm different, hx, hy]
  | some b =>
    have bx : b ≠ x := fun eq => mx (mid.trans (congrArg some eq))
    have by' : b ≠ y := fun eq => my (mid.trans (congrArg some eq))
    simp [rightRewire, different, Ne.symm different, bx, by', hx, hy]

/-- The middle subtree changes only its root's parent link. -/
private theorem rightRewire_middle (h : List (Record M (layout extra regs))) (x y b : ℕ)
    (rb : Record M (layout extra regs)) (hb : h[b]? = some rb)
    (bx : b ≠ x) (by' : b ≠ y) (parent : Pointer) :
    (rightRewire h x y (some b) parent)[b]? =
      some { rb with ptr := Function.update rb.ptr 2 (some y) } := by
  simp [rightRewire, Ne.symm bx, Ne.symm by', hb]


/-- Different positions in the represented tree have different heap addresses. -/
@[expose] def AddressesDistinct (t : BinaryTree (Label M extra)) : Prop :=
  ∀ p q u v, t.get p = some u → t.get q = some v → u.address = v.address → p = q

private def unrotatePath : PosNum → PosNum
  | .one => .bit0 .one
  | .bit0 p => .bit0 (.bit0 p)
  | .bit1 .one => .one
  | .bit1 (.bit0 p) => .bit0 (.bit1 p)
  | .bit1 (.bit1 p) => .bit1 p

private def rotatePath : PosNum → PosNum
  | .one => .bit1 .one
  | .bit0 .one => .one
  | .bit0 (.bit0 p) => .bit0 p
  | .bit0 (.bit1 p) => .bit1 (.bit0 p)
  | .bit1 p => .bit1 (.bit1 p)

private theorem unrotatePath_injective : Function.Injective unrotatePath := by
  apply Function.LeftInverse.injective (g := rotatePath)
  intro p
  cases p with
  | one => rfl
  | bit0 p => rfl
  | bit1 p => cases p <;> rfl

/-- Address separation survives rotation, so the result can be rotated again. -/
theorem AddressesDistinct.rotateRight {x y : Label M extra}
    {a b c : BinaryTree (Label M extra)}
    (h : AddressesDistinct (.node y (.node x a b) c)) :
    AddressesDistinct (.node x a (.node y b c)) := by
  have get (p : PosNum) :
      (.node y (.node x a b) c : BinaryTree (Label M extra)).get (unrotatePath p) =
      (.node x a (.node y b c) : BinaryTree (Label M extra)).get p := by
    cases p with
    | one => rfl
    | bit0 p => rfl
    | bit1 p => cases p <;> rfl
  intro p q u v hp hq eq
  apply unrotatePath_injective
  exact h _ _ u v ((get p).trans hp) ((get q).trans hq) eq

private theorem frame {h k : List (Record M (layout extra regs))}
    {t : BinaryTree (Label M extra)} {parent : Pointer} (rep : Represents h parent t)
    (agree : ∀ p a, t.get p = some a → k[a.address]? = h[a.address]?) :
    Represents k parent t := by
  induction t generalizing parent with
  | nil => trivial
  | node a l r il ir =>
    exact ⟨(agree .one a rfl).trans rep.1,
      il rep.2.1 (fun p b hp => agree (.bit0 p) b hp),
      ir rep.2.2 (fun p b hp => agree (.bit1 p) b hp)⟩

/-- A right rotation preserves the full recursive subtree representation, including
parent links, in ten actual instructions. The external parent's child link and cached
heights are the caller's responsibility. -/
theorem rotateRight_represents (s : State M (layout extra regs))
    (x y : Label M extra) (a b c : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents s.heap parent (.node y (.node x a b) c))
    (distinct : AddressesDistinct (.node y (.node x a b) c))
    (cursor : s.ptr 0 = some y.address) (pc : s.pc = 0) :
    ∃ t, Executes rotateRight s t 10 ∧
      Represents t.heap parent (.node x a (.node y b c)) ∧
      t.ptr 0 = some x.address ∧ t.data = s.data ∧ t.heap.length = s.heap.length := by
  rcases rep with ⟨hy, ⟨hx, ha, hb⟩, hc⟩
  have sep {p q : PosNum} {u v : Label M extra}
      (hp : (BinaryTree.node y (.node x a b) c).get p = some u)
      (hq : (BinaryTree.node y (.node x a b) c).get q = some v) (pq : p ≠ q) :
      u.address ≠ v.address := fun eq => pq (distinct p q u v hp hq eq)
  have xy : x.address ≠ y.address := sep (p := .bit0 .one) rfl (q := .one) rfl (by decide)
  have bx : root b ≠ some x.address := by
    cases b with
    | nil => simp [root]
    | node z l r =>
      exact fun h => sep (p := .bit0 (.bit1 .one)) rfl (q := .bit0 .one) rfl
        (by decide) (Option.some.inj h)
  have by' : root b ≠ some y.address := by
    cases b with
    | nil => simp [root]
    | node z l r =>
      exact fun h => sep (p := .bit0 (.bit1 .one)) rfl (q := .one) rfl
        (by decide) (Option.some.inj h)
  obtain ⟨t, exec, heap, cur, data, _⟩ := rotateRight_executes s x.address y.address
    (record (root a) (root b) (some y.address) x)
    (record (some x.address) (root c) parent y) pc cursor hy hx rfl
  have pivots := rightRewire_pivots s.heap x.address y.address
    (record (root a) (root b) (some y.address) x)
    (record (some x.address) (root c) parent y) hx hy xy bx by'
  change
    (rightRewire s.heap x.address y.address (root b) parent)[x.address]? = _ ∧
    (rightRewire s.heap x.address y.address (root b) parent)[y.address]? = _ at pivots
  refine ⟨t, exec, ?_, cur, data, ?_⟩
  · rw [heap]
    change Represents (rightRewire s.heap x.address y.address (root b) parent)
      parent (.node x a (.node y b c))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [pivots.1]
      simp only [record, Option.some.injEq, Record.mk.injEq]
      exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
    · apply frame ha
      intro p u hp
      apply rightRewire_frame
      · exact sep (p := .bit0 (.bit0 p)) hp (q := .bit0 .one) rfl (by simp)
      · exact sep (p := .bit0 (.bit0 p)) hp (q := .one) rfl (by simp)
      · cases b with
        | nil => simp [root]
        | node z l r =>
          exact fun h => sep (p := .bit0 (.bit1 .one)) rfl
            (q := .bit0 (.bit0 p)) hp (by simp) (Option.some.inj h)
    · rw [pivots.2]
      simp only [record, Option.some.injEq, Record.mk.injEq]
      exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
    · cases b with
      | nil => trivial
      | node z l r =>
        refine ⟨?_, ?_, ?_⟩
        · have hb := rightRewire_middle s.heap x.address y.address z.address
            (record (root l) (root r) (some x.address) z) hb.1
            (sep (p := .bit0 (.bit1 .one)) rfl (q := .bit0 .one) rfl (by decide))
            (sep (p := .bit0 (.bit1 .one)) rfl (q := .one) rfl (by decide)) parent
          simp only [root]
          rw [hb]
          simp only [record, Option.some.injEq, Record.mk.injEq]
          exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
        · apply frame hb.2.1
          intro p u hp
          apply rightRewire_frame
          · exact sep (p := .bit0 (.bit1 (.bit0 p))) hp (q := .bit0 .one) rfl (by simp)
          · exact sep (p := .bit0 (.bit1 (.bit0 p))) hp (q := .one) rfl (by simp)
          · exact fun h => sep (p := .bit0 (.bit1 .one)) rfl
              (q := .bit0 (.bit1 (.bit0 p))) hp (by simp) (Option.some.inj h)
        · apply frame hb.2.2
          intro p u hp
          apply rightRewire_frame
          · exact sep (p := .bit0 (.bit1 (.bit1 p))) hp (q := .bit0 .one) rfl (by simp)
          · exact sep (p := .bit0 (.bit1 (.bit1 p))) hp (q := .one) rfl (by simp)
          · exact fun h => sep (p := .bit0 (.bit1 .one)) rfl
              (q := .bit0 (.bit1 (.bit1 p))) hp (by simp) (Option.some.inj h)
    · apply frame hc
      intro p u hp
      apply rightRewire_frame
      · exact sep (p := .bit1 p) hp (q := .bit0 .one) rfl (by simp)
      · exact sep (p := .bit1 p) hp (q := .one) rfl (by simp)
      · cases b with
        | nil => simp [root]
        | node z l r =>
          exact fun h => sep (p := .bit0 (.bit1 .one)) rfl
            (q := .bit1 p) hp (by simp) (Option.some.inj h)
  · rw [heap]
    exact length_rightRewire _ _ _ _ _

end Cslib.DataStructure.SearchTree.PointerMachine
