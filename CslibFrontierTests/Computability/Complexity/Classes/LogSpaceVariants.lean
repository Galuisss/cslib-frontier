/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Function
import CslibFrontier.Computability.Complexity.Classes.LogSpace.NondeterministicOracle
import CslibFrontier.Computability.Complexity.Classes.NP.Logarithmic

open Cslib.Complexity Turing Turing.MultiTapeTM

-- For a zero-or-one branch count, the same witness is also a valid parity count.
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ UL enc) :
    A ∈ ParityL enc := by
  obtain ⟨f, hf, hle, hpos⟩ := hA
  refine ⟨f, hf, fun a => (hpos a).trans ?_⟩
  have h : f a = 0 ∨ f a = 1 := by have := hle a; omega
  obtain h | h := h <;> rw [h] <;> decide

-- The verifier can feed a tagged end marker to the NL bit-graph machine.
example (x : List Bool) (i : ℕ) :
    encFNLQuery encBits ⟨x, i, none⟩ = encPair encBits (encPair encNat (encOption encBool))
      (x, i, none) := rfl

-- Each ordered LOGNP field has its own binary frame, apart from the final rank.
example (x : List Bool) (s u v j : ℕ) :
    encLOGNPQuery encBits ⟨x, s, u, v, j⟩ =
      encPair encBits (encPair encNat (encPair encNat (encPair encNat encNat))) (x, s, u, v, j) :=
  rfl

-- Two nondeterministic choices on the same input write different oracle query bits.
example (A : Set (List Bool)) (x : List Bool) :
    let chooseQueryBit : MultiTapeMachine 0 Bool Unit Unit List :=
      { initial := ()
        tr := fun _ _ _ _ => [false, true].map fun bit =>
          .step ⟨0, Fin.elim0, none, none⟩ (fun _ => some bit) (fun _ => 0) }
    (∃ cfg : MultiTapeMachine.Config 0 Bool Unit Unit x,
      OracleReaches chooseQueryBit A [0] cfg ∧ (cfg.channels ()).queryBuffer = [false]) ∧
    (∃ cfg : MultiTapeMachine.Config 0 Bool Unit Unit x,
      OracleReaches chooseQueryBit A [1] cfg ∧ (cfg.channels ()).queryBuffer = [true]) :=
  ⟨⟨_, ⟨[0], rfl⟩, rfl⟩, ⟨_, ⟨[1], rfl⟩, rfl⟩⟩
