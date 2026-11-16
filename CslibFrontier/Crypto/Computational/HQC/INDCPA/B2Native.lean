/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.ClassicalQuery.Semantics
public import CslibFrontier.Crypto.Computational.HQC.INDCPA.B2Service

/-!
# Native query-free controller for the HQC B2 reduction

The B2 reduction receives the complete `3 * n + codeLen` truncated-syndrome word.  Its first
native stage sees exactly the two `n`-bit public blocks, the reversible service receives the full
word together with the two-message request and hidden bit, and the second stage sees exactly the
`n + codeLen` ciphertext plus the complete saved first-stage register.

`b2ClassicalQueryLayout` instantiates the shared query-free controller with those exact component
descriptions.  Its compatibility theorem derives the service shape and validity from the actual
`b2ServiceDescription`; callers provide only the two adversary stages' admitted input/output
shapes and the elementary bound placing the two-message output inside the first stage's classical
prefix.

This module still uses fixed ideal parameters `P` and one installed Boolean encoder.  It does not
supply the concrete NIST concatenated encoder, a growing parameter/encoder-family generator, the
full native success-law equality, or a QPT security theorem.

## Main definitions

* `Cslib.Crypto.HQC.b2ClassicalQueryLayout`: the exact component/register layout of the native
  query-free B2 controller.

## Main results

* `Cslib.Crypto.HQC.compatible_b2ClassicalQueryLayout`: the actual HQC service and admitted native
  stage shapes satisfy every shared controller compatibility condition.

## References

This retained controller is original formalization infrastructure for [HQC2026], Theorem 6.3,
pp. 61--64.
-/

public section

namespace Cslib.Crypto.HQC

open Cslib.Quantum
open Circuits Circuits.Boolean

/-- Exact shared-controller layout of the fixed-parameter native B2 reduction.  The first stage
receives the two public syndrome blocks; the second receives the remaining first-value and
masked-second-value ciphertext blocks. -/
@[expose] def b2ClassicalQueryLayout (P : PKEParams)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (first second : UniformOracleCircuitFamily) (securityParameter : ℕ) :
    ClassicalQueryLayout :=
  { input := ⟨securityParameter, 3 * P.n + P.codeLen⟩
    publicKeyWidth := 2 * P.n
    first := first.description securityParameter (2 * P.n)
    service := b2ServiceDescription P securityParameter encoder
    second := second.description securityParameter (P.n + P.codeLen) }

/-- The actual fixed-parameter B2 service and two admitted native stages satisfy the complete
shared-controller shape contract.  In particular, the choose stage receives only the public-key
projection, the guess stage receives all saved first-stage qubits but not the protected hidden
bit, and the service emits exactly one HQC ciphertext. -/
theorem compatible_b2ClassicalQueryLayout (P : PKEParams)
    (encoder : Circuits.Circuit Boolean.signature P.k P.codeLen)
    (first second : UniformOracleCircuitFamily) (securityParameter : ℕ)
    (hfirstInput :
      (first.description securityParameter (2 * P.n)).quantumInputWidth = 0)
    (hfirstOutput :
      (first.description securityParameter (2 * P.n)).outputWidth = 2 * P.k)
    (hmessagesFit : 2 * P.k ≤ 2 * securityParameter + 1 + 2 * P.n)
    (hsecondInput :
      (second.description securityParameter (P.n + P.codeLen)).quantumInputWidth =
        (first.description securityParameter (2 * P.n)).width)
    (hsecondOutput :
      1 ≤ (second.description securityParameter (P.n + P.codeLen)).outputWidth) :
    (b2ClassicalQueryLayout P encoder first second securityParameter).Compatible := by
  let layout := b2ClassicalQueryLayout P encoder first second securityParameter
  have hciphertext : layout.ciphertextWidth = P.n + P.codeLen := by
    simp only [layout, b2ClassicalQueryLayout, ClassicalQueryLayout.ciphertextWidth]
    omega
  refine
    { publicKey_le := by
        simp only [b2ClassicalQueryLayout]
        omega
      first_wellFormed := first.wellFormed securityParameter (2 * P.n)
      service_wellFormed := wellFormed_b2ServiceDescription P securityParameter encoder
      second_wellFormed := by
        change layout.second.WellFormed
          ⟨layout.input.securityParameter, layout.ciphertextWidth⟩
        rw [hciphertext]
        exact second.wellFormed securityParameter (P.n + P.codeLen)
      first_quantumInputWidth := hfirstInput
      first_output_le := by
        simp only [b2ClassicalQueryLayout, ClassicalQueryLayout.firstInputWidth,
          hfirstOutput]
        exact hmessagesFit
      service_quantumInputWidth := by
        simp only [b2ClassicalQueryLayout,
          b2ServiceDescription_quantumInputWidth, hfirstOutput]
      service_outputWidth := by
        change (b2ServiceDescription P securityParameter encoder).outputWidth =
          layout.ciphertextWidth
        rw [b2ServiceDescription_outputWidth]
        exact hciphertext.symm
      second_quantumInputWidth := hsecondInput
      second_outputWidth := hsecondOutput }

end Cslib.Crypto.HQC
