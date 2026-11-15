/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Basic
public import CslibFrontier.DataStructure.SearchTree.Cost

/-!
# Linked representations of binary search trees

Adapted from `RotationBST.Models.RealWorld.Linked` in Stefan Langerman's
`lean-bst` at commit `ad5dcac07e8b842f7a629ab0d79c4b32a19be51e`: the
left/right/parent record layout and the recursive heap representation. Mathematical trees use
Frontier's existing `BinaryTree` rather than
introducing another tree type. Addresses are ghost labels, inaccessible to scalar instructions.
Extra data fields hold values and balancing metadata. Unrelated heap records are permitted.

`Represents` describes the contents of a subtree, independently of ordering and of a cursor.
Mutation routines must additionally establish separation of the records they modify.
The companion search module proves charged machine execution against `SearchTree.contains`.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine

open Cslib.PointerMachine

/-- Cursor, root, parent, grandparent, middle, null and comparison pointer registers;
query and temporary data registers followed by client registers. Records contain
left, right and parent links, then a key and client data fields. -/
abbrev layout (extra regs : ℕ) : Layout := ⟨7, regs + 2, 3, extra + 1⟩

/-- A ghost address and all scalar fields of a tree node. Only `data` is available
through scalar loads; `address` records its heap location for the proof. -/
structure Label (M : Model) (extra : ℕ) where
  /-- Heap location, used only in the representation proof. -/
  address : ℕ
  /-- Key in field zero, followed by client data. -/
  data : Fin (extra + 1) → M.Value

variable {M : Model} {extra regs : ℕ}

/-- Root address of a ghost-labelled tree; the empty tree has a null root. -/
@[expose] def root : BinaryTree (Label M extra) → Pointer
  | .nil => none
  | .node x _ _ => some x.address

/-- Concrete left/right/parent record for a ghost label. -/
@[expose] def record (l r p : Pointer) (x : Label M extra) : Record M (layout extra regs) :=
  ⟨fun i => if i = 0 then l else if i = 1 then r else p, x.data⟩

/-- Every node has its labelled address, scalar fields and prescribed child/parent links.
The first pointer is the external parent of the represented subtree. -/
@[expose] def Represents (heap : List (Record M (layout extra regs))) :
    Pointer → BinaryTree (Label M extra) → Prop
  | _, .nil => True
  | p, .node x l r => heap[x.address]? = some (record (root l) (root r) p x) ∧
      Represents heap (some x.address) l ∧ Represents heap (some x.address) r

/-- Appending fresh records preserves every existing linked-tree representation. -/
theorem Represents.append {heap : List (Record M (layout extra regs))}
    {parent : Pointer} {tree : BinaryTree (Label M extra)}
    (h : Represents heap parent tree) (suffix : List (Record M (layout extra regs))) :
    Represents (heap ++ suffix) parent tree := by
  induction tree generalizing parent with
  | nil => trivial
  | node label left right ihl ihr =>
    refine ⟨?_, ihl h.2.1, ihr h.2.2⟩
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp h.1
    rw [List.getElem?_append_left bound]
    exact h.1

/-- Forget addresses and metadata, retaining the keys in Frontier's existing tree type. -/
@[expose] def keys (t : BinaryTree (Label M extra)) : BinaryTree M.Value :=
  t.map fun x => x.data 0

end Cslib.DataStructure.SearchTree.PointerMachine
