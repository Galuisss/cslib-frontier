/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.RegisterProgram
public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Wiring

/-!
# Compiling Boolean register programs to symmetric self-closing doors

One door stores each register. Its two tunnels form a directed cycle with two wiring arcs.
Each instruction opens a private return marker, enters the register's guarded tunnel, and can
return only from the side representing its prescribed written value. Every wiring arc is a
symmetric door whose first tunnel is an opening self-loop and whose second tunnel traverses
the arc. This original construction implements the network model of
[AniBosboomDemaineEtAl2021, Section 2.1].

## Main definitions

* `RegisterProgram.compile`: the explicit symmetric self-closing door network of a program.
-/

@[expose] public section

namespace Cslib.Complexity.SelfClosingDoor.RegisterProgram

namespace Compiler

/-- External control labels occupy residue zero modulo six. -/
def external (v : ℕ) : ℕ := 6 * v

/-- A private instruction entry occupies residue one modulo six. -/
def entry (j : ℕ) : ℕ := 6 * j + 1

/-- The register tunnel enabled by `b` starts in residue two or four modulo six. -/
def input (r : ℕ) (b : Bool) : ℕ := 6 * r + if b then 4 else 2

/-- The corresponding tunnel exits in residue three or five modulo six. -/
def output (r : ℕ) (b : Bool) : ℕ := input r b + 1

/-- A register door flips its bit between the two halves of its directed core cycle. -/
def registerDoor (r : ℕ) (b : Bool) : Door :=
  ⟨⟨input r false, output r false⟩, ⟨input r true, output r true⟩, b⟩

/-- An instruction's return latch opens only at its private entry. -/
def markerDoor (j : ℕ) (i : Instruction) : Door :=
  ⟨⟨entry j, entry j⟩,
    ⟨output i.register (!i.write), external i.target⟩, false⟩

/-- Register doors, in the same order as the program's initial registers. -/
def registerDoors (p : Program) : List Door :=
  p.initial.zipIdx.map fun (b, r) => registerDoor r b

/-- Return markers, in the same order as the program's instructions. -/
def markerDoors (p : Program) : List Door :=
  p.instructions.zipIdx.map fun (i, j) => markerDoor j i

/-- The two directed connectors of each register's core cycle. -/
def coreWiring (p : Program) : List Tunnel :=
  (List.range p.initial.length).flatMap fun r =>
    [⟨output r false, input r true⟩, ⟨output r true, input r false⟩]

/-- Each instruction has a one-way entry and a one-way guarded approach to its register. -/
def instructionWiring (p : Program) : List Tunnel :=
  p.instructions.zipIdx.flatMap fun (i, j) =>
    [⟨external i.source, entry j⟩, ⟨entry j, input i.register i.guard⟩]

/-- Source jumps, register-core connectors and guarded instruction approaches. -/
def wiring (p : Program) : List Tunnel :=
  p.jumps.map (fun a => ⟨external a.source, external a.target⟩) ++
    coreWiring p ++ instructionWiring p

/-- The registers and return markers, before replacing directed wiring by diode doors. -/
def principalDoors (p : Program) : List Door := registerDoors p ++ markerDoors p

end Compiler

/-- Compile an arbitrary finite register program to an explicit door network. Out-of-range
register instructions enter a core with no register door and have no successful return. -/
def compile (p : Program) : Instance :=
  ⟨Compiler.principalDoors p ++ (Compiler.wiring p).map Wiring.diode,
    Compiler.external p.start, Compiler.external p.target⟩

end Cslib.Complexity.SelfClosingDoor.RegisterProgram
