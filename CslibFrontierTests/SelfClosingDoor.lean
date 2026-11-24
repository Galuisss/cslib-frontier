import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.PSPACE

open Cslib.Complexity.SelfClosingDoor

namespace SelfClosingDoorTests

private def loopNetwork : Instance :=
  ⟨[⟨⟨0, 0⟩, ⟨0, 1⟩, false⟩], 0, 1⟩

-- An identified entry and exit still flips the door before the second traversal.
example : loopNetwork ∈ Reachability := by
  have h₁ : Step loopNetwork.doors loopNetwork.initial ⟨0, [true]⟩ :=
    (checkStep_eq_true_iff _ _ _).1 (by decide +kernel)
  have h₂ : Step loopNetwork.doors ⟨0, [true]⟩ ⟨1, [false]⟩ :=
    (checkStep_eq_true_iff _ _ _).1 (by decide +kernel)
  exact ⟨⟨1, [false]⟩, (Relation.ReflTransGen.single h₁).tail h₂, rfl⟩

private def oneWay : Instance :=
  ⟨[⟨⟨0, 1⟩, ⟨2, 3⟩, false⟩], 0, 1⟩

-- The final bit may differ from its prescribed initial value.
example : oneWay ∈ Reachability := by
  have h : Step oneWay.doors oneWay.initial ⟨1, [true]⟩ :=
    (checkStep_eq_true_iff _ _ _).1 (by decide +kernel)
  exact ⟨⟨1, [true]⟩, Relation.ReflTransGen.single h, rfl⟩

private def parallel : List Door :=
  [⟨⟨0, 1⟩, ⟨1, 0⟩, false⟩, ⟨⟨0, 1⟩, ⟨1, 0⟩, false⟩]

-- Equal tunnel records remain independent list entries.
example : Step parallel ⟨0, [false, false]⟩ ⟨1, [false, true]⟩ :=
  (checkStep_eq_true_iff _ _ _).1 (by decide +kernel)

-- The enabled tunnel is directed; its destination does not serve as an entry.
example : ¬ Step oneWay.doors ⟨1, [false]⟩ ⟨0, [true]⟩ := by
  rw [← checkStep_eq_true_iff]
  decide +kernel

-- A short bit list cannot obtain an enabled tunnel through the lookup fallback.
example : ¬ Step oneWay.doors ⟨0, []⟩ ⟨1, []⟩ := by
  rw [← checkStep_eq_true_iff]
  decide +kernel

-- With no doors, an empty path accepts precisely when already at the target.
example : (⟨[], 5, 5⟩ : Instance) ∈ Reachability :=
  ⟨⟨5, []⟩, Relation.ReflTransGen.refl, rfl⟩

end SelfClosingDoorTests
