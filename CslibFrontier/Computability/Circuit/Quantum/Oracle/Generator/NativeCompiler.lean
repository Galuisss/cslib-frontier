/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Generator
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Retained native generators of uniform quantum oracle circuits

This module turns an actual `NativeCompiler` for a uniform circuit description into a
`UniformOracleCircuitFamily.GeneratorCertificate`. The caller supplies polynomial schedules that
dominate the compiler's input-indexed time and workspace maps because generator certificates are
indexed only by encoded input length: distinct pairs of security parameter and auxiliary-input
length can have the same encoded length.

The resulting certificate uses the compiler's constructive literal description, not a newly
selected existential machine. Consequently its static charge is exactly
`NativeCompiler.staticBits`, while its emitted-program charge is exactly the encoded
`OracleCircuitDescription` produced by that compiler. Installed-artifact inventories remain the
responsibility of the scheme or game that stores and uses those words.

## Main definitions

* `Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate.ofNativeCompiler`: derive a
  generator certificate from a retained deterministic compiler and polynomial resource schedules.

## Main results

The construction derives output correctness and the visited-workspace bound from the retained
compiler's computation certificate; it does not ask the caller for a second semantic witness.

## References

This adapter is an original bridge between the library's native compiler and uniform quantum
oracle-circuit APIs.
-/

public section

namespace Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate

open Turing MultiTapeTM

private theorem headAt_nativeDescription {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (compiler : Internal.NativeCompiler f encIn encOut) (x : List Bool) (j : ℕ)
    (i : Fin compiler.tapeCount) :
    Universal.headAt compiler.description (x.map Universal.eBit) j i =
      (compiler.table.toTM.runFrom (compiler.table.toTM.initCfg x) j).workTapePos i := by
  have hcfg := (Universal.toCfg_iterate_of_holds compiler.stateEncoding Universal.eBit
    compiler.table.toTM compiler.description compiler.description_header.1
      compiler.description_header.2 compiler.description_holds x j).1
  have hhead := congrArg (·.workTapePos i) hcfg
  simpa [Universal.SCfg.toCfg, Cfg.map, Universal.headAt, Universal.run] using hhead.symm

private theorem simSpace_nativeDescription {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (compiler : Internal.NativeCompiler f encIn encOut) (x : List Bool) (j : ℕ) :
    Universal.simSpace compiler.description (x.map Universal.eBit) j =
      (MultiTapeNTM.RunPath.ofDeterministic compiler.table.toTM
        (compiler.table.toTM.initCfg x) j).space := by
  rw [MultiTapeNTM.RunPath.space]
  simp only [Universal.simSpace, MultiTapeNTM.RunPath.spaceUsedByTape]
  rw [compiler.description_header.1, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card (Finset.ext fun z => ?_)
  rw [MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic]
  simp only [Universal.visited, Finset.mem_image, Finset.mem_range,
    headAt_nativeDescription]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by omega, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by omega, rfl⟩

/-- Derive an encoded uniform-circuit generator certificate from an actual retained deterministic
compiler. The two schedules are length-indexed upper bounds for the compiler's exact-form,
semantic-input-indexed resource maps; no machine or computation proof is selected existentially.

The static program occurs once as `compiler.description`, and the emitted circuit description
occurs once as the compiler output. Components inlined into `compiler.table` are therefore not
separate generator programs. -/
@[expose] def ofNativeCompiler {F : UniformOracleCircuitFamily}
    (compiler : Internal.NativeCompiler
      (fun input : OracleInputSize =>
        F.description input.securityParameter input.classicalInputLength)
      encOracleInputSize encOracleCircuitDescription)
    (time workspace : ℕ → ℕ)
    (time_polynomiallyBounded : PolynomiallyBounded time)
    (workspace_polynomiallyBounded : PolynomiallyBounded workspace)
    (time_le : ∀ input, compiler.time input ≤ time (encOracleInputSize input).length)
    (workspace_le : ∀ input,
      compiler.workspace input ≤ workspace (encOracleInputSize input).length) :
    F.GeneratorCertificate where
  code := compiler.description
  time := time
  workspace := workspace
  time_polynomiallyBounded := time_polynomiallyBounded
  workspace_polynomiallyBounded := workspace_polynomiallyBounded
  computes input := by
    have hrun := MultiTapeTM.ComputesInTimeAndSpace.runFrom_of_le
      (compiler.computes input).computesInTimeAndSpace (time_le input)
    rw [Universal.simulate_of_holds compiler.stateEncoding Universal.eBit compiler.table.toTM
      compiler.description compiler.description_header.1 compiler.description_header.2
      compiler.description_holds, hrun.2]
    have hhalt : (compiler.table.toTM.runFrom
        (compiler.table.toTM.initCfg (encOracleInputSize input))
        (time (encOracleInputSize input).length)).state = none := hrun.1
    exact Prod.ext rfl (by rw [hhalt]; rfl)
  workspace_le input := by
    rw [simSpace_nativeDescription]
    exact (space_le_of_runsInSpace
      (compiler.computes input).computesInTimeAndSpace.2.2 _).trans (workspace_le input)

end Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate
