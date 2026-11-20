/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Logarithmically restricted NP

`LOGNPLocal` guesses a logarithmic-size subset of input indices. For every polynomially
bounded universal index there is a polynomially bounded response that works for
all chosen indices. The test sees the instance, the chosen element, the universal
index, the response and the position of that element in the chosen subset. This captures
the local bounded-index presentation with a polynomial-time matrix. The reduction-closed class in
the source requires a separate definition or equivalence proof.

## References

* [C. Papadimitriou and M. Yannakakis, *On Limited Nondeterminism and the Complexity of the V-C
  Dimension*](https://doi.org/10.1006/jcss.1996.0058)
* [Complexity Zoo, LOGNP](https://complexityzoo.net/Complexity_Zoo:L#lognp)
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- One evaluation of the local predicate of `LOGNPLocal`. -/
structure LOGNPQuery (α : Type) where
  /-- The input instance. -/
  instanceData : α
  /-- The selected input position. -/
  selected : ℕ
  /-- The universal challenge. -/
  challenge : ℕ
  /-- The existential response. -/
  response : ℕ
  /-- The rank of the selected position in the subset. -/
  rank : ℕ

/-- Frame the instance and the first three binary parameters, then append the binary rank. -/
enc_structure encLOGNPQuery (enc : α ↪ List Bool) : LOGNPQuery α where
  instanceData : enc,
  selected : encNat,
  challenge : encNat,
  response : encNat,
  rank : encNat

/-- The local bounded-index predicate with a polynomial-time matrix. The chosen indices are
enumerated in increasing order. The universal challenge and existential response each range
over polynomially many values, so either can be represented with logarithmically many bits.
The finitely many instances encoded by strings of length zero or one are unrestricted. -/
def LOGNPLocal (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p q : ℕ) (R : Set (LOGNPQuery α)), R ∈ P (encLOGNPQuery enc) ∧
    ∀ a, let n := (enc a).length
      2 ≤ n → (a ∈ A ↔ ∃ s : Fin (Nat.log2 n) → Fin n, StrictMono s ∧
        ∀ u : Fin ((n + 1) ^ p), ∃ v : Fin ((n + 1) ^ q),
          ∀ j : Fin (Nat.log2 n), ⟨a, (s j).val, u.val, v.val, j.val⟩ ∈ R)}

end Cslib.Complexity
