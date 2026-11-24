/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.RegisterCompiler
public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.RegisterEncoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured

/-!
# Polynomial-time compilation of Boolean register programs

The compiler traverses the explicit register, instruction and jump lists. Enumerated indices
are unary counters, converted to binary labels before the constant-size location arithmetic.
In particular, no enumeration depends on the magnitude of a binary control label.

## Main results

* `RegisterProgram.computableInPolyTime_compile`: the explicit door compiler runs in polynomial
  time on the standard structural encodings.
-/

public section

namespace Cslib.Complexity.SelfClosingDoor.RegisterProgram

open _root_.Turing.MultiTapeTM Compiler

private theorem external_polyTime :
    ComputableInPolyTime external encNat encNat := by
  unfold external
  fun_prop

private theorem entry_polyTime : ComputableInPolyTime entry encNat encNat := by
  unfold entry
  fun_prop

private theorem input_polyTime :
    ComputableInPolyTime (fun q : ℕ × Bool => input q.1 q.2)
      (encPair encNat encBool) encNat := by
  unfold input
  fun_prop

private theorem output_polyTime :
    ComputableInPolyTime (fun q : ℕ × Bool => output q.1 q.2)
      (encPair encNat encBool) encNat := by
  have hi := input_polyTime
  unfold output
  fun_prop

private theorem registerDoor_polyTime :
    ComputableInPolyTime (fun q : Bool × ℕ => registerDoor q.2 q.1)
      (encPair encBool encUnary) encDoor := by
  have hr : ComputableInPolyTime (fun q : Bool × ℕ => q.2)
      (encPair encBool encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hi := input_polyTime
  have ho := output_polyTime
  unfold registerDoor
  fun_prop

private theorem markerDoor_polyTime :
    ComputableInPolyTime (fun q : Instruction × ℕ => markerDoor q.2 q.1)
      (encPair encInstruction encUnary) encDoor := by
  have hj : ComputableInPolyTime (fun q : Instruction × ℕ => q.2)
      (encPair encInstruction encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have he := entry_polyTime
  have hx := external_polyTime
  have ho := output_polyTime
  unfold markerDoor
  fun_prop

private theorem diode_polyTime : ComputableInPolyTime Wiring.diode encTunnel encDoor := by
  unfold Wiring.diode
  fun_prop

private theorem registerDoors_polyTime :
    ComputableInPolyTime registerDoors encProgram (encList encDoor) := by
  have hi : ComputableInPolyTime Program.initial encProgram (encList encBool) :=
    ComputableInPolyTime.bitsToList.comp (by fun_prop)
  have hz := (ComputableInPolyTime.zipIdx encBool).comp hi
  have hm := registerDoor_polyTime
  unfold registerDoors
  fun_prop

private theorem markerDoors_polyTime :
    ComputableInPolyTime markerDoors encProgram (encList encDoor) := by
  have hz : ComputableInPolyTime (fun p : Program => p.instructions.zipIdx)
      encProgram (encList (encPair encInstruction encUnary)) := by fun_prop
  have hm := markerDoor_polyTime
  unfold markerDoors
  fun_prop

private theorem coreWiring_polyTime :
    ComputableInPolyTime coreWiring encProgram (encList encTunnel) := by
  have hi : ComputableInPolyTime Program.initial encProgram (encList encBool) :=
    ComputableInPolyTime.bitsToList.comp (by fun_prop)
  have hn : ComputableInPolyTime (fun p : Program => p.initial.length) encProgram encUnary :=
    (ComputableInPolyTime.length encBool).comp hi
  have hr : ComputableInPolyTime (fun r : ℕ => r) encUnary encNat :=
    ComputableInPolyTime.unary_to_binary
  have hb : ComputableInPolyTime
      (fun r => [Tunnel.mk (output r false) (input r true),
        Tunnel.mk (output r true) (input r false)]) encUnary (encList encTunnel) := by
    have hi := input_polyTime
    have ho := output_polyTime
    fun_prop
  have hindices : ComputableInPolyTime (fun p : Program => List.range p.initial.length)
      encProgram (encList encUnary) := by fun_prop
  unfold coreWiring
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (ComputableInPolyTime.flatten encTunnel).comp ((ComputableInPolyTime.map hb).comp hindices)

private theorem instructionWiring_polyTime :
    ComputableInPolyTime instructionWiring encProgram (encList encTunnel) := by
  have hz : ComputableInPolyTime (fun p : Program => p.instructions.zipIdx)
      encProgram (encList (encPair encInstruction encUnary)) := by fun_prop
  have hb : ComputableInPolyTime
      (fun q : Instruction × ℕ =>
        [Tunnel.mk (external q.1.source) (entry q.2),
          Tunnel.mk (entry q.2) (input q.1.register q.1.guard)])
      (encPair encInstruction encUnary) (encList encTunnel) := by
    have hj : ComputableInPolyTime (fun q : Instruction × ℕ => q.2)
        (encPair encInstruction encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    have hx := external_polyTime
    have he := entry_polyTime
    have hi := input_polyTime
    fun_prop
  unfold instructionWiring
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (ComputableInPolyTime.flatten encTunnel).comp ((ComputableInPolyTime.map hb).comp hz)

private theorem wiring_polyTime :
    ComputableInPolyTime wiring encProgram (encList encTunnel) := by
  have hcore := coreWiring_polyTime
  have hinstructions := instructionWiring_polyTime
  have hj : ComputableInPolyTime
      (fun a : Tunnel => Tunnel.mk (external a.source) (external a.target))
      encTunnel encTunnel := by
    have hx := external_polyTime
    fun_prop
  unfold wiring
  fun_prop

/-- The complete explicit door network of a finite register program is computable in
polynomial time, with binary labels and the explicitly listed register contents. -/
@[fun_prop] theorem computableInPolyTime_compile :
    ComputableInPolyTime compile encProgram encInstance := by
  have hr := registerDoors_polyTime
  have hm := markerDoors_polyTime
  have hw := wiring_polyTime
  have hd := diode_polyTime
  have hx := external_polyTime
  unfold compile Wiring.compile principalDoors
  fun_prop

end Cslib.Complexity.SelfClosingDoor.RegisterProgram
