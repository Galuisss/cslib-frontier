/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.RegisterCompiler
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Enum

/-!
# Correctness of the symmetric-door register compiler

An instruction's private return marker prevents a call from returning through another
instruction. The first register traversal checks its guard, and the return side fixes its
written value. Arbitrary extra cycles inside a register core preserve this contract.

## Main results

* `RegisterProgram.compile_reachability_iff`: the compiled network accepts exactly the
  executions of its register program.
-/

public section

namespace Cslib.Complexity.SelfClosingDoor.RegisterProgram

open Compiler

private inductive Place where
  | external (v : ℕ)
  | entry (j : ℕ)
  | input (r : ℕ) (b : Bool)
  | output (r : ℕ) (b : Bool)
  deriving DecidableEq

private def Place.code : Place → ℕ
  | .external v => Compiler.external v
  | .entry j => Compiler.entry j
  | .input r b => Compiler.input r b
  | .output r b => Compiler.output r b

private theorem Place.code_injective : Function.Injective Place.code := by
  intro x y h
  cases x <;> cases y <;>
    simp only [Place.code, Compiler.external, Compiler.entry, Compiler.input, Compiler.output] at h
  all_goals (try split_ifs at h) <;> simp_all <;> omega

private structure MachineState where
  location : Place
  registers : List Bool
  markers : List Bool

private def MachineState.toState (s : MachineState) : State :=
  ⟨s.location.code, s.registers ++ s.markers⟩

private def MachineState.Valid (p : Program) (s : MachineState) : Prop :=
  s.registers.length = p.initial.length ∧ s.markers.length = p.instructions.length

private inductive MachineStep (p : Program) : MachineState → MachineState → Prop
  | jump {registers markers : List Bool} {a : Tunnel} (ha : a ∈ p.jumps) :
      MachineStep p ⟨.external a.source, registers, markers⟩
        ⟨.external a.target, registers, markers⟩
  | enter {registers markers : List Bool} (j : Fin p.instructions.length) :
      MachineStep p ⟨.external p.instructions[j].source, registers, markers⟩
        ⟨.entry j.val, registers, markers⟩
  | approach {registers markers : List Bool} (j : Fin p.instructions.length) :
      MachineStep p ⟨.entry j.val, registers, markers⟩
        ⟨.input p.instructions[j].register p.instructions[j].guard, registers, markers⟩
  | connect {registers markers : List Bool} (r : Fin p.initial.length) (b : Bool) :
      MachineStep p ⟨.output r.val b, registers, markers⟩
        ⟨.input r.val (!b), registers, markers⟩
  | register {registers markers : List Bool} (r : Fin p.initial.length) (b : Bool)
      (hb : registers.getD r.val false = b) :
      MachineStep p ⟨.input r.val b, registers, markers⟩
        ⟨.output r.val b, registers.set r.val (!b), markers⟩
  | openMarker {registers markers : List Bool} (j : Fin p.instructions.length)
      (hb : markers.getD j.val false = false) :
      MachineStep p ⟨.entry j.val, registers, markers⟩
        ⟨.entry j.val, registers, markers.set j.val true⟩
  | returnMarker {registers markers : List Bool} (j : Fin p.instructions.length)
      (hb : markers.getD j.val false = true) :
      MachineStep p ⟨.output p.instructions[j].register (!p.instructions[j].write),
          registers, markers⟩
        ⟨.external p.instructions[j].target, registers, markers.set j.val false⟩

private theorem MachineStep.valid_target {p : Program} {s t : MachineState}
    (h : MachineStep p s t) (hs : s.Valid p) : t.Valid p := by
  cases h <;> simpa only [MachineState.Valid, List.length_set] using hs

private theorem registerDoors_length (p : Program) :
    (registerDoors p).length = p.initial.length := by
  simp [registerDoors]

private theorem markerDoors_length (p : Program) :
    (markerDoors p).length = p.instructions.length := by
  simp [markerDoors]

private theorem registerDoors_get (p : Program) (r : Fin p.initial.length) :
    (registerDoors p)[r.val]'(by simpa only [registerDoors_length] using r.isLt) =
      registerDoor r.val p.initial[r] := by
  simp [registerDoors, List.getElem_zipIdx, Fin.getElem_fin]

private theorem markerDoors_get (p : Program) (j : Fin p.instructions.length) :
    (markerDoors p)[j.val]'(by simpa only [markerDoors_length] using j.isLt) =
      markerDoor j.val p.instructions[j] := by
  simp [markerDoors, List.getElem_zipIdx, Fin.getElem_fin]

private theorem MachineState.actual_valid {p : Program} {s : MachineState} (hs : s.Valid p) :
    s.toState.Valid (principalDoors p) := by
  simp only [State.Valid, MachineState.toState, principalDoors, List.length_append,
    registerDoors_length, markerDoors_length]
  exact congrArg₂ (· + ·) hs.1 hs.2

private theorem register_tunnel (r : ℕ) (initial b : Bool) :
    (registerDoor r initial).tunnel b = ⟨input r b, output r b⟩ := by
  cases b <;> rfl

private theorem principal_register_get (p : Program) (r : Fin p.initial.length) :
    (principalDoors p)[r.val]'(by
      simp only [principalDoors, List.length_append, registerDoors_length, markerDoors_length]
      omega) = registerDoor r.val p.initial[r] := by
  change (registerDoors p ++ markerDoors p)[r.val]'(by
    simp only [List.length_append, registerDoors_length, markerDoors_length]; omega) = _
  rw [List.getElem_append_left (by simpa only [registerDoors_length] using r.isLt)]
  exact registerDoors_get p r

private theorem principal_marker_get (p : Program) (j : Fin p.instructions.length) :
    (principalDoors p)[p.initial.length + j.val]'(by
      simp only [principalDoors, List.length_append, registerDoors_length, markerDoors_length]
      omega) = markerDoor j.val p.instructions[j] := by
  change (registerDoors p ++ markerDoors p)[p.initial.length + j.val]'(by
    simp only [List.length_append, registerDoors_length, markerDoors_length]; omega) = _
  rw [List.getElem_append_right (by simp only [registerDoors_length]; omega)]
  simpa only [registerDoors_length, Nat.add_sub_cancel_left] using markerDoors_get p j

private theorem actual_register_step (p : Program) (registers markers : List Bool)
    (hr : registers.length = p.initial.length) (hm : markers.length = p.instructions.length)
    (r : Fin p.initial.length) (b : Bool) (hb : registers.getD r.val false = b) :
    SelfClosingDoor.Step (principalDoors p)
      ⟨input r.val b, registers ++ markers⟩
      ⟨output r.val b, registers.set r.val (!b) ++ markers⟩ := by
  have hi : r.val < registers.length := by omega
  have hd := principal_register_get p r
  have hbits : (registers ++ markers).getD r.val false = b :=
    (List.getD_append _ _ _ _ hi).trans hb
  refine ⟨?_, ⟨r.val, by
    simp only [principalDoors, List.length_append, registerDoors_length, markerDoors_length]
    omega⟩, ?_, ?_⟩
  · simp only [State.Valid, List.length_append, principalDoors, registerDoors_length,
      markerDoors_length, hr, hm]
  · simp only [Fin.getElem_fin, hd, hbits, register_tunnel]
  · simp only [Fin.getElem_fin, hd, hbits, register_tunnel, List.set_append_left _ _ hi]

private theorem actual_marker_step (p : Program) (registers markers : List Bool)
    (hr : registers.length = p.initial.length) (hm : markers.length = p.instructions.length)
    (j : Fin p.instructions.length) (b : Bool) (hb : markers.getD j.val false = b) :
    let d := markerDoor j.val p.instructions[j]
    SelfClosingDoor.Step (principalDoors p)
      ⟨(d.tunnel b).source, registers ++ markers⟩
      ⟨(d.tunnel b).target, registers ++ markers.set j.val (!b)⟩ := by
  have hd := principal_marker_get p j
  have hbits : (registers ++ markers).getD (p.initial.length + j.val) false = b := by
    rw [List.getD_append_right _ _ _ _ (by omega), hr, Nat.add_sub_cancel_left, hb]
  have hset : (registers ++ markers).set (p.initial.length + j.val) (!b) =
      registers ++ markers.set j.val (!b) := by
    rw [List.set_append_right _ _ (by omega), hr, Nat.add_sub_cancel_left]
  refine ⟨?_, ⟨p.initial.length + j.val, by
    simp only [principalDoors, List.length_append, registerDoors_length, markerDoors_length]
    omega⟩, ?_, ?_⟩
  · simp only [State.Valid, List.length_append, principalDoors, registerDoors_length,
      markerDoors_length, hr, hm]
  · simp only [Fin.getElem_fin, hd, hbits]
  · simp only [Fin.getElem_fin, hd, hbits, hset]

private theorem indexed_instruction_mem (p : Program) (j : Fin p.instructions.length) :
    (p.instructions[j], j.val) ∈ p.instructions.zipIdx := by
  simp [List.mk_mem_zipIdx_iff_getElem?, Fin.getElem_fin]

private theorem MachineStep.actual {p : Program} {s t : MachineState}
    (h : MachineStep p s t) (hs : s.Valid p) :
    Wiring.Step (principalDoors p) (wiring p) s.toState t.toState := by
  have hv := MachineState.actual_valid hs
  cases h with
  | @jump registers markers a ha =>
    right
    refine ⟨hv, ⟨external a.source, external a.target⟩, ?_, rfl, rfl⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, ha, rfl⟩))
  | enter j =>
    right
    refine ⟨hv, ⟨external p.instructions[j].source, entry j.val⟩, ?_, rfl, rfl⟩
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨(p.instructions[j], j.val), indexed_instruction_mem p j, by simp⟩
  | approach j =>
    right
    refine ⟨hv, ⟨entry j.val, input p.instructions[j].register p.instructions[j].guard⟩,
      ?_, rfl, rfl⟩
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨(p.instructions[j], j.val), indexed_instruction_mem p j, by simp⟩
  | connect r b =>
    right
    refine ⟨hv, ⟨output r.val b, input r.val (!b)⟩, ?_, rfl, rfl⟩
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨r.val, List.mem_range.mpr r.isLt, ?_⟩
    cases b <;> simp [Bool.not_false]
  | register r b hb =>
    exact Or.inl (actual_register_step p _ _ hs.1 hs.2 r b hb)
  | openMarker j hb =>
    exact Or.inl (actual_marker_step p _ _ hs.1 hs.2 j false hb)
  | returnMarker j hb =>
    exact Or.inl (actual_marker_step p _ _ hs.1 hs.2 j true hb)

private theorem actual_door_complete {p : Program} {s : MachineState} {t : State}
    (hs : s.Valid p) (h : SelfClosingDoor.Step (principalDoors p) s.toState t) :
    ∃ u, MachineStep p s u ∧ u.toState = t := by
  rcases s with ⟨location, registers, markers⟩
  obtain ⟨_, i, hp, rfl⟩ := h
  have hr : registers.length = p.initial.length := hs.1
  have hm : markers.length = p.instructions.length := hs.2
  by_cases hi : i.val < p.initial.length
  · let r : Fin p.initial.length := ⟨i.val, hi⟩
    let b := registers.getD i.val false
    have hd := principal_register_get p r
    dsimp only [r] at hd
    have hb : (registers ++ markers).getD i.val false = b :=
      List.getD_append _ _ _ _ (by omega)
    have hl : location = .input i.val b := by
      apply Place.code_injective
      simpa only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb,
        register_tunnel] using hp
    subst location
    refine ⟨⟨.output i.val b, registers.set i.val (!b), markers⟩,
      MachineStep.register r b rfl, ?_⟩
    simp only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb,
      register_tunnel, List.set_append_left _ _ (by omega : i.val < registers.length)]
  · have hj : i.val - p.initial.length < p.instructions.length := by
      have := i.isLt
      simp only [principalDoors, List.length_append, registerDoors_length,
        markerDoors_length] at this
      omega
    let j : Fin p.instructions.length := ⟨i.val - p.initial.length, hj⟩
    have hd : (principalDoors p)[i.val] = markerDoor j.val p.instructions[j] := by
      have hd := principal_marker_get p j
      simpa only [j, Nat.add_sub_of_le (by omega : p.initial.length ≤ i.val)] using hd
    have hb : (registers ++ markers).getD i.val false = markers.getD j.val false := by
      rw [List.getD_append_right _ _ _ _ (by omega), hr]
    have hset (b : Bool) : (registers ++ markers).set i.val b =
        registers ++ markers.set j.val b := by
      rw [List.set_append_right _ _ (by omega), hr]
    cases hmj : markers.getD j.val false with
    | false =>
      have hl : location = .entry j.val := by
        apply Place.code_injective
        simpa only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb, hmj,
          markerDoor, Door.tunnel, Bool.false_eq_true, ↓reduceIte] using hp
      subst location
      refine ⟨⟨.entry j.val, registers, markers.set j.val true⟩,
        MachineStep.openMarker j hmj, ?_⟩
      simp only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb, hmj,
        markerDoor, Door.tunnel, Bool.false_eq_true, ↓reduceIte, Bool.not_false, hset]
    | true =>
      have hl : location = .output p.instructions[j].register (!p.instructions[j].write) := by
        apply Place.code_injective
        simpa only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb, hmj,
          markerDoor, Door.tunnel, ↓reduceIte] using hp
      subst location
      refine ⟨⟨.external p.instructions[j].target, registers, markers.set j.val false⟩,
        MachineStep.returnMarker j hmj, ?_⟩
      simp only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb, hmj,
        markerDoor, Door.tunnel, ↓reduceIte, Bool.not_true, hset]

private theorem actual_step_complete {p : Program} {s : MachineState} {t : State}
    (hs : s.Valid p) (h : Wiring.Step (principalDoors p) (wiring p) s.toState t) :
    ∃ u, MachineStep p s u ∧ u.toState = t := by
  rcases h with h | ⟨_, a, ha, hp, rfl⟩
  · exact actual_door_complete hs h
  · rcases s with ⟨location, registers, markers⟩
    simp only [wiring, List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      have hl : location = .external b.source := Place.code_injective hp
      subst location
      exact ⟨⟨.external b.target, registers, markers⟩, MachineStep.jump hb, rfl⟩
    · obtain ⟨r, hr, ha⟩ := List.mem_flatMap.1 ha
      have hr := List.mem_range.1 hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · have hl : location = .output r false := Place.code_injective hp
        subst location
        exact ⟨⟨.input r true, registers, markers⟩,
          MachineStep.connect ⟨r, hr⟩ false, rfl⟩
      · have hl : location = .output r true := Place.code_injective hp
        subst location
        exact ⟨⟨.input r false, registers, markers⟩,
          MachineStep.connect ⟨r, hr⟩ true, rfl⟩
    · obtain ⟨⟨i, j⟩, hj, ha⟩ := List.mem_flatMap.1 ha
      obtain ⟨hbound, hi⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hj)
      change j < p.instructions.length at hbound
      change p.instructions[j] = i at hi
      subst i
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · have hl : location = .external p.instructions[j].source := Place.code_injective hp
        subst location
        exact ⟨⟨.entry j, registers, markers⟩, MachineStep.enter ⟨j, hbound⟩, rfl⟩
      · have hl : location = .entry j := Place.code_injective hp
        subst location
        exact ⟨⟨.input p.instructions[j].register p.instructions[j].guard, registers, markers⟩,
          MachineStep.approach ⟨j, hbound⟩, rfl⟩

private def closedMarkers (p : Program) : List Bool :=
  List.replicate p.instructions.length false

private def selectedMarkers (p : Program) (j : Fin p.instructions.length) (b : Bool) :
    List Bool := (closedMarkers p).set j.val b

private theorem selectedMarkers_false (p : Program) (j : Fin p.instructions.length) :
    selectedMarkers p j false = closedMarkers p := by
  simp [selectedMarkers, closedMarkers]

private theorem selectedMarkers_self (p : Program) (j : Fin p.instructions.length) (b : Bool) :
    (selectedMarkers p j b).getD j.val false = b := by
  simp [selectedMarkers, closedMarkers, List.getD_eq_getElem?_getD]

private theorem selectedMarkers_true {p : Program} {j k : Fin p.instructions.length} {b : Bool}
    (h : (selectedMarkers p j b).getD k.val false = true) : k = j ∧ b = true := by
  by_cases hkj : k.val = j.val
  · have he : k = j := Fin.ext hkj
    subst k
    exact ⟨rfl, (selectedMarkers_self p j b).symm.trans h⟩
  · simp [selectedMarkers, closedMarkers, List.getD_eq_getElem?_getD,
      List.getElem_set_ne (Ne.symm hkj)] at h

private inductive Certified (p : Program) : MachineState → Prop
  | boundary (s : State) (hr : p.Reachable p.initialState s) :
      Certified p ⟨.external s.location, s.bits, closedMarkers p⟩
  | entry (s : State) (hr : p.Reachable p.initialState s)
      (j : Fin p.instructions.length) (hp : s.location = p.instructions[j].source) (m : Bool) :
      Certified p ⟨.entry j.val, s.bits, selectedMarkers p j m⟩
  | ready (s : State) (hr : p.Reachable p.initialState s)
      (j : Fin p.instructions.length) (hp : s.location = p.instructions[j].source) (m : Bool) :
      Certified p ⟨.input p.instructions[j].register p.instructions[j].guard,
        s.bits, selectedMarkers p j m⟩
  | input (s : State) (hr : p.Reachable p.initialState s)
      (j : Fin p.instructions.length) (hp : s.location = p.instructions[j].source)
      (hg : s.bits.getD p.instructions[j].register false = p.instructions[j].guard)
      (hreg : p.instructions[j].register < s.bits.length) (m b : Bool) :
      Certified p ⟨.input p.instructions[j].register b,
        s.bits.set p.instructions[j].register b, selectedMarkers p j m⟩
  | output (s : State) (hr : p.Reachable p.initialState s)
      (j : Fin p.instructions.length) (hp : s.location = p.instructions[j].source)
      (hg : s.bits.getD p.instructions[j].register false = p.instructions[j].guard)
      (hreg : p.instructions[j].register < s.bits.length) (m b : Bool) :
      Certified p ⟨.output p.instructions[j].register b,
        s.bits.set p.instructions[j].register (!b), selectedMarkers p j m⟩

private theorem Certified.step {p : Program} {s t : MachineState}
    (hs : Certified p s) (hstep : MachineStep p s t) : Certified p t := by
  generalize hsource : s = u at hstep
  cases hs <;> cases hstep
  all_goals
    obtain ⟨hloc, hregs, hmarkers⟩ := MachineState.mk.inj hsource
    try cases hloc
  case boundary.jump source hr registers markers a ha =>
    subst registers
    subst markers
    apply Certified.boundary ⟨a.target, source.bits⟩
    apply hr.tail
    exact ⟨hr.length rfl, Or.inl ⟨a, ha, Place.external.inj hloc, rfl⟩⟩
  case boundary.enter source hr registers markers j =>
    subst registers
    subst markers
    rw [← selectedMarkers_false p j]
    exact Certified.entry source hr j (Place.external.inj hloc) false
  case entry.approach source hr j hp m registers markers k =>
    subst registers
    subst markers
    have he : j = k := Fin.ext (Place.entry.inj hloc)
    subst k
    exact Certified.ready source hr j hp m
  case entry.openMarker source hr j hp m registers markers k hb =>
    subst registers
    subst markers
    have he : j = k := Fin.ext (Place.entry.inj hloc)
    subst k
    simpa only [selectedMarkers, List.set_set] using Certified.entry source hr j hp true
  case ready.register source hr j hp m registers markers r b hb =>
    subst registers
    subst markers
    obtain ⟨hri, hbi⟩ := Place.input.inj hloc
    have hg : source.bits.getD p.instructions[j].register false = p.instructions[j].guard := by
      simpa only [hri, hbi] using hb
    have hreg : p.instructions[j].register < source.bits.length := by
      have hlen := hr.length rfl
      rw [hri, hlen]
      exact r.isLt
    simpa only [hri, hbi] using
      Certified.output source hr j hp hg hreg m p.instructions[j].guard
  case input.register source hr j hp hg hreg m b₀ registers markers r b hb =>
    subst registers
    subst markers
    obtain ⟨hri, hbi⟩ := Place.input.inj hloc
    simpa only [hri, hbi, List.set_set] using Certified.output source hr j hp hg hreg m b₀
  case output.connect source hr j hp hg hreg m b₀ registers markers r b =>
    subst registers
    subst markers
    obtain ⟨hri, hbi⟩ := Place.output.inj hloc
    simpa only [hri, hbi] using Certified.input source hr j hp hg hreg m (!b₀)
  case output.returnMarker source hr j hp hg hreg m b registers markers k hb =>
    subst registers
    subst markers
    obtain ⟨he, hm⟩ := selectedMarkers_true hb
    subst k
    subst m
    have hbit : b = !p.instructions[j].write := (Place.output.inj hloc).2
    let next : State := ⟨p.instructions[j].target, source.bits.set p.instructions[j].register
      p.instructions[j].write⟩
    have hnext : p.Step source next :=
      ⟨hr.length rfl, Or.inr ⟨p.instructions[j], List.getElem_mem j.isLt,
        hreg, hp, hg, rfl⟩⟩
    simpa only [next, hbit, Bool.not_not, selectedMarkers, List.set_set,
      closedMarkers, List.set_replicate_self] using Certified.boundary next (hr.tail hnext)

private def boundary (p : Program) (s : State) : MachineState :=
  ⟨.external s.location, s.bits, List.replicate p.instructions.length false⟩

private theorem machine_instruction_path (p : Program) (j : Fin p.instructions.length)
    (s t : State) (hs : s.bits.length = p.initial.length) (hi : p.instructions[j].Step s t) :
    Relation.ReflTransGen (MachineStep p) (boundary p s) (boundary p t) := by
  obtain ⟨hr, hsource, hguard, rfl⟩ := hi
  let r : Fin p.initial.length := ⟨p.instructions[j].register, by omega⟩
  let off := List.replicate p.instructions.length false
  let on := off.set j.val true
  have hoff : off.getD j.val false = false := by
    simp [off, List.getD_eq_getElem?_getD]
  have hon : on.getD j.val false = true := by
    rw [List.getD_eq_getElem _ _
      (by simpa only [on, off, List.length_set, List.length_replicate] using j.isLt)]
    exact List.getElem_set_self
      (by simpa only [on, off, List.length_set, List.length_replicate] using j.isLt)
  have hstart : MachineStep p (boundary p s) ⟨.entry j.val, s.bits, off⟩ := by
    simpa only [boundary, hsource] using
      (MachineStep.enter (registers := s.bits) (markers := off) j)
  have hprefix := ((Relation.ReflTransGen.single hstart).tail
    (MachineStep.openMarker j hoff)).tail (MachineStep.approach j)
  have hfirst := hprefix.tail (MachineStep.register r p.instructions[j].guard hguard)
  have hready : Relation.ReflTransGen (MachineStep p) (boundary p s)
      ⟨.output p.instructions[j].register (!p.instructions[j].write),
        s.bits.set p.instructions[j].register p.instructions[j].write, on⟩ := by
    by_cases hsame : p.instructions[j].guard = p.instructions[j].write
    · have hsecond : (s.bits.set r.val (!p.instructions[j].guard)).getD r.val false =
          !p.instructions[j].guard := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hr, Option.getD_some]
      have hcycle := (hfirst.tail (MachineStep.connect r p.instructions[j].guard)).tail
        (MachineStep.register r (!p.instructions[j].guard) hsecond)
      simpa only [r, hsame, Bool.not_not, List.set_set] using hcycle
    · have hother : p.instructions[j].guard = !p.instructions[j].write := by
        cases hg : p.instructions[j].guard <;> cases hw : p.instructions[j].write <;>
          simp_all
      simpa only [r, hother, Bool.not_not] using hfirst
  have hfinish := hready.tail (MachineStep.returnMarker j hon)
  simpa only [boundary, on, List.set_set, List.set_replicate_self, off] using hfinish

private theorem machine_program_path {p : Program} {s t : State}
    (hs : s.bits.length = p.initial.length) (hr : p.Reachable s t) :
    Relation.ReflTransGen (MachineStep p) (boundary p s) (boundary p t) := by
  induction hr with
  | refl => exact .refl
  | @tail u v hprefix hstep ih =>
    obtain ⟨_, h | ⟨i, hi, hist⟩⟩ := hstep
    · obtain ⟨a, ha, hsource, rfl⟩ := h
      exact ih.tail (by
        simpa only [boundary, hsource] using
          (MachineStep.jump (registers := u.bits)
            (markers := List.replicate p.instructions.length false) ha))
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hi
      exact ih.trans (machine_instruction_path p ⟨j, hj⟩ u v
        (Program.Reachable.length hprefix hs) hist)

private theorem machine_reachable_valid {p : Program} {s t : MachineState}
    (hs : s.Valid p) (hr : Relation.ReflTransGen (MachineStep p) s t) : t.Valid p := by
  induction hr with
  | refl => exact hs
  | tail _ hstep ih => exact hstep.valid_target ih

private theorem machine_reachable_actual {p : Program} {s t : MachineState}
    (hs : s.Valid p) (hr : Relation.ReflTransGen (MachineStep p) s t) :
    Wiring.Reachable (principalDoors p) (wiring p) s.toState t.toState := by
  induction hr with
  | refl => exact .refl
  | tail hprefix hstep ih =>
    exact ih.tail (hstep.actual (machine_reachable_valid hs hprefix))

private theorem actual_reachable_complete {p : Program} {s : MachineState} {t : State}
    (hs : s.Valid p) (hr : Wiring.Reachable (principalDoors p) (wiring p) s.toState t) :
    ∃ u, Relation.ReflTransGen (MachineStep p) s u ∧ u.toState = t := by
  induction hr with
  | refl => exact ⟨s, .refl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨u, hu, rfl⟩ := ih
    obtain ⟨v, hv, he⟩ := actual_step_complete (machine_reachable_valid hs hu) hstep
    exact ⟨v, hu.tail hv, he⟩

private theorem certified_reachable {p : Program} {s : MachineState}
    (hr : Relation.ReflTransGen (MachineStep p) (boundary p p.initialState) s) :
    Certified p s := by
  induction hr with
  | refl => exact Certified.boundary p.initialState .refl
  | tail _ hstep ih => exact ih.step hstep

private theorem Certified.accepts {p : Program} {s : MachineState}
    (hs : Certified p s) (hp : s.location = .external p.target) : p.Accepts := by
  cases hs with
  | boundary source hr => exact ⟨source, hr, Place.external.inj hp⟩
  | entry | ready | input | output => cases hp

private theorem principal_initial (p : Program) :
    (principalDoors p).map Door.initial = p.initial ++ closedMarkers p := by
  simp [principalDoors, registerDoors, markerDoors, registerDoor, markerDoor,
    List.zipIdx_map_fst, List.map_const', Function.comp_def, closedMarkers]

/-- The explicit symmetric-door network accepts precisely the executions of its register
program, including instructions with out-of-range register indices. -/
theorem compile_reachability_iff (p : Program) :
    compile p ∈ SelfClosingDoor.Reachability ↔ p.Accepts := by
  change Wiring.compile (principalDoors p) (wiring p) (external p.start) (external p.target) ∈
    SelfClosingDoor.Reachability ↔ p.Accepts
  rw [Wiring.compile_reachability_iff, principal_initial]
  have hs : (boundary p p.initialState).Valid p := ⟨rfl, List.length_replicate⟩
  constructor
  · rintro ⟨t, hr, hp⟩
    obtain ⟨u, hu, he⟩ := actual_reachable_complete hs hr
    apply (certified_reachable hu).accepts
    apply Place.code_injective
    exact (congrArg State.location he).trans hp
  · rintro ⟨t, hr, hp⟩
    refine ⟨(boundary p t).toState, ?_, ?_⟩
    · exact machine_reachable_actual hs (machine_program_path rfl hr)
    · simp only [boundary, MachineState.toState, Place.code, hp]


end Cslib.Complexity.SelfClosingDoor.RegisterProgram
