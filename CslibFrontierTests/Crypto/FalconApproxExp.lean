/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.Falcon.ApproxExp
import Mathlib.Tactic.NormNum

/-!
# Tests for Falcon v1.2 ApproxExp

These ordinary-import clients check the literal coefficient table, rounded-input endpoints, an
interior fixed-point evaluation, the source arithmetic invariant, the structurally linked
operation ledger, and occurrence-aware retained table size.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.FalconApproxExp

open Cslib.Crypto.Falcon

public section

private abbrev zeroExponent : ApproxExpExponentInput := ⟨0, by norm_num [approxExpScale]⟩
private abbrev halfExponent : ApproxExpExponentInput := ⟨2 ^ 62, by norm_num [approxExpScale]⟩
private abbrev zeroScaling : ApproxExpScalingInput := ⟨0, by norm_num [approxExpScale]⟩
private abbrev halfScaling : ApproxExpScalingInput := ⟨2 ^ 62, by norm_num [approxExpScale]⟩
private abbrev oneScaling : ApproxExpScalingInput := ⟨2 ^ 63, by norm_num [approxExpScale]⟩

#guard approxExpCoefficients.length == 13
#guard approxExpCoefficients.head? == some 0x00000004741183A3
#guard approxExpCoefficients.getLast? == some 0x8000000000000000

/-- At `x = 0`, the polynomial stage reaches `2^63`, so final scaling returns `ccs63`. -/
example : approxExpFixedPoint zeroExponent halfScaling = 2 ^ 62 := by
  simpa using approxExpFixedPoint_zero_x halfScaling

/-- The published `ccs = 1` endpoint returns `2^63` at `x = 0`. -/
#guard approxExpFixedPoint zeroExponent oneScaling == 0x8000000000000000

/-- Before the final shift, that endpoint's scaling product is exactly `2^126`; this is distinct
from the strict 126-bit bound for Horner products. -/
#guard oneScaling.val * approxExpHorner zeroExponent (approxExpCoefficients.headD 0)
    approxExpCoefficients.tail == 2 ^ 126

/-- A zero scaling factor returns zero independently of the Horner input. -/
example : approxExpFixedPoint halfExponent zeroScaling = 0 := by
  simpa using approxExpFixedPoint_zero_ccs halfExponent

/-- Independent integer evaluation at `x63 = ccs63 = 2^62`. -/
#guard approxExpFixedPoint halfExponent halfScaling == 2797128963144290736
#guard (approxExpRun halfExponent halfScaling).output == 2797128963144290736
#guard (approxExpRun halfExponent halfScaling).mulShiftCount == 13
#guard (approxExpRun halfExponent halfScaling).subtractionCount == 12

example : ApproxExpHornerSafe halfExponent (approxExpCoefficients.headD 0)
    approxExpCoefficients.tail :=
  approxExp_horner_safe halfExponent

example : approxExpFixedPoint halfExponent halfScaling ≤ approxExpScale :=
  approxExpFixedPoint_le_scale halfExponent halfScaling

example : (approxExpRun halfExponent halfScaling).mulShiftCount = 13 ∧
    (approxExpRun halfExponent halfScaling).subtractionCount = 12 :=
  approxExpRun_ledger halfExponent halfScaling

example : oneScaling.val * approxExpScale ≤ 2 ^ 126 :=
  approxExp_scalingProduct_le_twoPow126 oneScaling le_rfl

#guard approxExpHornerRounds == 12
#guard approxExpMulShiftCount == 13
#guard approxExpSubtractionCount == 12
#guard approxExpTablePayloadBits == 832
#guard approxExpRetainedBits 100 0 == 100
#guard approxExpRetainedBits 100 1 == 932
#guard approxExpRetainedBits 100 2 == 1764

end

end CslibFrontierTests.Crypto.FalconApproxExp
