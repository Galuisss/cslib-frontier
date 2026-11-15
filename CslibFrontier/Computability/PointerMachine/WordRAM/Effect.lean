/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.WordRAM.Allocation

/-!
# Correctness of compiled pointer-machine instructions

Each instruction's memory and register effect is implemented by its compiled word-RAM code.
Scalar implementations discharge only scalar operations; the pointer-access and allocation
proofs use the explicit memory representation.
-/

public section

namespace Cslib.PointerMachine.WordRAM

open Cslib.WordRAM (Code ExecWithin)

variable {M : Model} {L : Layout}

namespace Scalars

private theorem nop_spec {w : ℕ} (y : Cslib.WordRAM.Data (regCount L)) :
    ExecWithin w (.op (.copy (zeroReg L) (zeroReg L)) : Code .standard _) y y 1 := by
  simpa [Cslib.WordRAM.Data.set] using
    (ExecWithin.copy (B := .standard) (w := w) (x := y) (d := zeroReg L) (s := zeroReg L))

private theorem address_spec {e : M.Value ↪ ℕ} {w : ℕ} {x : State M L}
    {y : Cslib.WordRAM.Data (regCount L)} (h : Repr e x y) (hf : Fits e w x)
    (b : Fin L.ptrRegs) (a offset : ℕ) (hp : x.ptr b = some a)
    (ha : a < x.heap.length) (ho : offset < stride L) :
    ∃ z, ExecWithin w (address (ptrReg L b) offset) y z 2 ∧ Repr e x z ∧
      z.regs (addrReg L) = cellAddr L a offset := by
  have hba : ptrReg L b ≠ addrReg L := by
    intro he; have := congrArg Fin.val he; have := b.isLt
    simp only [ptrReg, addrReg] at *; omega
  have hoff : Cslib.WordRAM.Fits w offset := (hf.cellAddr ha ho).of_le (by
    simp [cellAddr])
  let y₁ := y.set (addrReg L) offset
  have hcalc : Cslib.WordRAM.BinOp.add.eval
      (y₁.regs (ptrReg L b)) (y₁.regs (addrReg L)) = cellAddr L a offset := by
    simp [y₁, Cslib.WordRAM.Data.set, hba, h.ptr, hp, ptrWord, cellAddr,
      Cslib.WordRAM.BinOp.eval]
  have hb := ExecWithin.bin (x := y₁) (d := addrReg L) (i := ptrReg L b)
    (j := addrReg L) (f := .add) (w := w) (by rw [hcalc]; exact hf.cellAddr ha ho)
  rw [hcalc] at hb
  refine ⟨y₁.set (addrReg L) (cellAddr L a offset),
    (ExecWithin.const hoff).seq hb, ?_, by simp [Cslib.WordRAM.Data.set]⟩
  exact (h.scratch (addrReg L) (by simp [addrReg]) offset).scratch
    (addrReg L) (by simp [addrReg]) _

private theorem access_spec {e : M.Value ↪ ℕ} {w : ℕ} {x target : State M L}
    {y : Cslib.WordRAM.Data (regCount L)} (h : Repr e x y) (hv : x.Valid)
    (hf : Fits e w x) (b : Fin L.ptrRegs) (offset : ℕ) (ho : offset < stride L)
    (body : Code .standard (regCount L))
    (hnull : x.ptr b = none → Repr e target y)
    (hbody : ∀ a n, x.ptr b = some a → x.heap[a]? = some n →
      ∀ z, Repr e x z → z.regs (addrReg L) = cellAddr L a offset →
        ∃ z', ExecWithin w body z z' 1 ∧ Repr e target z') :
    ∃ z, ExecWithin w (access (ptrReg L b) offset body) y z 5 ∧ Repr e target z := by
  cases hp : x.ptr b with
  | none =>
    refine ⟨y, (ExecWithin.branch_pos ?_ (nop_spec y)).mono (by omega), hnull hp⟩
    simp [Cslib.WordRAM.Cond.Holds, h.ptr, h.zero, hp, ptrWord]
  | some a =>
    have ha := hv.1 b a hp
    have hn : x.heap[a]? = some (x.heap[a]'ha) := List.getElem?_eq_getElem ha
    obtain ⟨z, he, hz, hadr⟩ := address_spec h hf b a offset hp ha ho
    obtain ⟨z', he', hz'⟩ := hbody a _ hp hn z hz hadr
    refine ⟨z', ExecWithin.branch_neg ?_ (he.seq he'), hz'⟩
    simp [Cslib.WordRAM.Cond.Holds, h.ptr, h.zero, hp, ptrWord, nodeAddr]

/-- The compiled effect performs the source instruction, within its explicit instruction bound.
For a scalar branch it also leaves the predicate result in the temporary value register. -/
theorem effect_correct (S : Scalars M L) (i : Instr M L) {w : ℕ} {x : State M L}
    {y : Cslib.WordRAM.Data (regCount L)} (hv : x.Valid) (h : Repr S.encode x y)
    (hf : Fits S.encode w x) (hf' : Fits S.encode w (i.effect x)) (hs : S.Safe w x i) :
    ∃ z, ExecWithin w (S.effect i) y z (S.effectTime i) ∧
      Repr S.encode (i.effect x) z ∧
      (match i with
      | .ifTest p a b _ => z.regs (valueReg L) = if M.evalTest p (x.data a) (x.data b) then 1 else 0
      | _ => True) := by
  cases i with
  | null r =>
    refine ⟨_, ?_, h.setPtr r none, trivial⟩
    simpa only [effect, effectTime, h.zero, ptrWord] using
      (ExecWithin.copy (B := .standard) (w := w) (x := y) (d := ptrReg L r) (s := zeroReg L))
  | movePtr r s =>
    refine ⟨_, ?_, h.setPtr r (x.ptr s), trivial⟩
    simpa only [effect, effectTime, h.ptr] using
      (ExecWithin.copy (B := .standard) (w := w) (x := y) (d := ptrReg L r) (s := ptrReg L s))
  | moveData r s =>
    refine ⟨_, ?_, h.setData r (x.data s), trivial⟩
    simpa only [effect, effectTime, h.data] using
      (ExecWithin.copy (B := .standard) (w := w) (x := y) (d := dataReg L r) (s := dataReg L s))
  | loadPtr r f b =>
    have ho : f.val < stride L := by have := f.isLt; unfold stride; omega
    obtain ⟨z, he, hz⟩ := access_spec h hv hf b f.val ho
      (.op (.load (ptrReg L r) (addrReg L)))
      (target := (Instr.loadPtr r f b).effect x) (by
        intro hp; simpa [Instr.effect, State.deref, hp] using h) (by
        intro a n hp hn z hz hadr
        have he := ExecWithin.load (B := .standard) (w := w) (x := z)
          (d := ptrReg L r) (a := addrReg L)
        rw [hadr, hz.heapPtr a n hn f] at he
        refine ⟨_, he, ?_⟩
        simpa [Instr.effect, State.deref, hp, hn] using hz.setPtr r (n.ptr f))
    exact ⟨z, he, hz, trivial⟩
  | loadData r f b =>
    have ho : L.ptrFields + f.val < stride L := by have := f.isLt; unfold stride; omega
    obtain ⟨z, he, hz⟩ := access_spec h hv hf b (L.ptrFields + f.val) ho
      (.op (.load (dataReg L r) (addrReg L)))
      (target := (Instr.loadData r f b).effect x) (by
        intro hp; simpa [Instr.effect, State.deref, hp] using h) (by
        intro a n hp hn z hz hadr
        have he := ExecWithin.load (B := .standard) (w := w) (x := z)
          (d := dataReg L r) (a := addrReg L)
        rw [hadr, hz.heapData a n hn f] at he
        refine ⟨_, he, ?_⟩
        simpa [Instr.effect, State.deref, hp, hn] using hz.setData r (n.data f))
    exact ⟨z, he, hz, trivial⟩
  | storePtr f b r =>
    have ho : f.val < stride L := by have := f.isLt; unfold stride; omega
    obtain ⟨z, he, hz⟩ := access_spec h hv hf b f.val ho
      (.op (.store (addrReg L) (ptrReg L r)))
      (target := (Instr.storePtr f b r).effect x) (by
        intro hp; simpa [Instr.effect, State.modify, hp] using h) (by
        intro a n hp hn z hz hadr
        have he := ExecWithin.store (B := .standard) (w := w) (x := z)
          (a := addrReg L) (s := ptrReg L r)
        rw [hadr, hz.ptr r] at he
        refine ⟨_, he, ?_⟩
        simpa [Instr.effect, State.modify, hp] using hz.writePtr a f (x.ptr r))
    exact ⟨z, he, hz, trivial⟩
  | storeData f b r =>
    have ho : L.ptrFields + f.val < stride L := by have := f.isLt; unfold stride; omega
    obtain ⟨z, he, hz⟩ := access_spec h hv hf b (L.ptrFields + f.val) ho
      (.op (.store (addrReg L) (dataReg L r)))
      (target := (Instr.storeData f b r).effect x) (by
        intro hp; simpa [Instr.effect, State.modify, hp] using h) (by
        intro a n hp hn z hz hadr
        have he := ExecWithin.store (B := .standard) (w := w) (x := z)
          (a := addrReg L) (s := dataReg L r)
        rw [hadr, hz.data r] at he
        refine ⟨_, he, ?_⟩
        simpa [Instr.effect, State.modify, hp] using hz.writeData a f (x.data r))
    exact ⟨z, he, hz, trivial⟩
  | op o d a b =>
    have hout : Cslib.WordRAM.Fits w (S.encode (M.evalOp o (x.data a) (x.data b))) := by
      simpa [Instr.effect, State.setData] using hf'.2.1 d
    obtain ⟨z, he, hz⟩ := S.op_spec w o (dataReg L d) (dataReg L a) (dataReg L b)
      y (x.data a) (x.data b) (h.data a) (h.data b) hs hout
    exact ⟨z, he, h.setData_of_frame d _ hz.result hz.frame hz.memory, trivial⟩
  | create r =>
    obtain ⟨z, he, hz⟩ := S.create_spec r h hf'
    exact ⟨z, he, hz, trivial⟩
  | ifTest p a b t =>
    have hone : 1 < 2 ^ w := lt_of_le_of_lt (by simp [nodeAddr]) hf.1
    obtain ⟨z, he, hz⟩ := S.test_spec w p (valueReg L) (dataReg L a) (dataReg L b)
      y (x.data a) (x.data b) (h.data a) (h.data b) hs hone
    refine ⟨z, he, h.of_frame (fun r hr => hz.frame r hr ?_) hz.memory, hz.result⟩
    intro he; have := congrArg Fin.val he; simp only [valueReg] at this; omega
  | goto t => exact ⟨y, nop_spec y, h, trivial⟩
  | ifPtrEq a b t => exact ⟨y, nop_spec y, h, trivial⟩
  | halt => exact ⟨y, nop_spec y, h, trivial⟩

end Scalars
end Cslib.PointerMachine.WordRAM
