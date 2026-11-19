/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.PolyRounds

/-!
# Public-coin interactive proofs with polynomially many moves

`PPSPACE` uses public randomness during a polynomial number of interactions.

## References

* [Complexity Zoo, PPSPACE](https://complexityzoo.net/Complexity_Zoo:P#ppspace)
* [C. Papadimitriou, *Computational Complexity*, §19.2][Papadimitriou94]
-/

namespace Cslib.Complexity

/-- The public-coin interactive proof class with a polynomially computable game schedule
and polynomially many moves. -/
@[expose] public def PPSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ p : Polynomial ℕ, A ∈ AMPolyRounds enc p.eval}

end Cslib.Complexity
