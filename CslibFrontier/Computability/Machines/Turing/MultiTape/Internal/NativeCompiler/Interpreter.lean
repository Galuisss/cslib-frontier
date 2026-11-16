/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Replicate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Output

/-!
# Concrete retained bounded interpretation

This concrete-only component installs an actual deterministic interpreter for a fixed description
and a unary clock. It streams emitted symbols instead of retaining and repeatedly copying the
output prefix. The clock controls simulated steps; the returned compiler charges the interpreter's
own native execution and workspace separately. Its complete installed description includes the
interpreted program.

Polynomial majorants for this exact interpreter, and its use with the adversary certificate's
dominating polynomial clock, remain part of the open certificate bridge in issue #5281.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.simulateOutputCompiler`: retained bounded simulation
  with exact output semantics and construction-derived time and workspace maps.
* `Turing.MultiTapeTM.Internal.NativeCompiler.simulateBitOutputCompiler`: bit input and output
  adapters retained in the installed interpreter.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM.Universal

private noncomputable def contextStepCompiler :
    NativeCompiler (fun c : Ctx => Universal.step c.desc c.input c.cfg)
      eCtx (encPair eCfg eSym) := by
  let original := first (encPair eDesc (encList encUnary)) eCfg
  let description := (first eDesc (encList encUnary)).comp original
  let word := (second eDesc (encList encUnary)).comp original
  let cfg := second (encPair eDesc (encList encUnary)) eCfg
  exact stepCompiler.comp (description.pair (word.pair cfg))

private def interpreterNext (input : Ctx × Bool) : Ctx :=
  (input.1.1, (Universal.step input.1.desc input.1.input input.1.cfg).1)

private def interpreterEmit (input : Ctx × Bool) : List Bool :=
  encList encUnary (Universal.step input.1.desc input.1.input input.1.cfg).2.toList

private noncomputable def interpreterNextCompiler :
    NativeCompiler interpreterNext (encPair eCtx encBool) eCtx := by
  let ctx := first eCtx encBool
  let fixed := (first (encPair eDesc (encList encUnary)) eCfg).comp ctx
  let advanced := (first eCfg eSym).comp (contextStepCompiler.comp ctx)
  exact (fixed.pair advanced).ofOutputEq fun _ => rfl

private noncomputable def interpreterEmitCompiler :
    NativeCompiler interpreterEmit (encPair eCtx encBool) encBits := by
  let ctx := first eCtx encBool
  let emitted := (second eCfg eSym).comp (contextStepCompiler.comp ctx)
  exact ((optionToListCompiler encUnary).comp emitted).ofOutputEq fun _ => rfl

private theorem interpreterEmit_eq (ctx : Ctx) (tokens : List Bool) :
    streamEmit interpreterNext interpreterEmit ctx tokens =
      encList encUnary ((stepOut ctx.desc ctx.input)^[tokens.length] (ctx.cfg, [])).2 := by
  induction tokens generalizing ctx with
  | nil => rfl
  | cons bit tokens ih =>
      rw [streamEmit, ih, List.length_cons, Function.iterate_succ_apply]
      simp only [interpreterNext, interpreterEmit, Ctx.desc, Ctx.input, Ctx.cfg, stepOut,
        List.nil_append]
      rw [stepOut_iterate_append ctx.desc ctx.input tokens.length
        (Universal.step ctx.desc ctx.input ctx.cfg).1
        (Universal.step ctx.desc ctx.input ctx.cfg).2.toList, encList_append]

private noncomputable def interpreterStreamCompiler :
    NativeCompiler
      (fun input : Ctx × List Bool =>
        ((stepOut input.1.desc input.1.input)^[input.2.length] (input.1.cfg, [])).2)
      (encPair eCtx (encList encBool)) (encList encUnary) :=
  listFoldEmitCompiler eCtx encBool (encList encUnary)
    interpreterNextCompiler interpreterEmitCompiler fun input =>
      (interpreterEmit_eq input.1 input.2).symm

/-- Install a fixed deterministic description and execute the supplied number of simulated steps.
The compiler's time and workspace fields charge its actual finite transition table, independently
of the simulated clock. The output is valid even if the simulated program has not yet halted. -/
noncomputable def simulateOutputCompiler (description : Desc) :
    NativeCompiler (fun input : List ℕ × ℕ => (simulate description input.1 input.2).1)
      (encPair (encList encUnary) encUnary) (encList encUnary) := by
  let encInput := encPair (encList encUnary) encUnary
  let word := first (encList encUnary) encUnary
  let ticks := unaryTrueListCompiler.comp (second (encList encUnary) encUnary)
  let fixed := (const encInput eDesc description).pair word
  let ctx := fixed.pair (const encInput eCfg (Universal.init description))
  exact (interpreterStreamCompiler.comp (ctx.pair ticks)).ofOutputEq fun input => by
    simp only [simulate, List.length_replicate, Function.const_apply,
      Ctx.desc, Ctx.input, Ctx.cfg]

private def inputSymbolsCompiler :
    NativeCompiler (List.map Universal.eBit) encBits (encList encUnary) := by
  let doubled : NativeCompiler (id : List Bool → List Bool) encBits encTrueDoubled :=
    ofTransducer trueDoubleT unitStateEncoding fun word => trueDoubleT_run word
  let symbols : NativeCompiler (List.map Universal.eBit) encTrueDoubled (encList encUnary) :=
    ofTransducer symbolsT Universal.eBit fun word => symbolsT_run word
  exact symbols.comp doubled

private def outputBitCompiler :
    NativeCompiler (fun symbol : ℕ => decide (symbol = 1)) encUnary encBool :=
  ((wordEqBool encUnary).comp
    ((identity encUnary).pair (const encUnary encUnary 1))).ofOutputEq fun symbol => by
      simp only [encUnary.injective.eq_iff, id_eq, Function.const_apply]

private def outputBitsCompiler :
    NativeCompiler (List.map fun symbol : ℕ => decide (symbol = 1))
      (encList encUnary) encBits := by
  let encInput := encPair encUnit encUnary
  let emit : NativeCompiler
      (fun input : Unit × ℕ => [decide (input.2 = 1)]) encInput encBits :=
    (outputBitCompiler.comp (second encUnit encUnary)).ofOutputEq fun _ => rfl
  let stream := listFoldEmitCompiler encUnit encUnary encBits
    (first encUnit encUnary) emit
    (result := fun input : Unit × List ℕ => input.2.map fun symbol => decide (symbol = 1))
    (fun input => by
      induction input.2 with
      | nil => rfl
      | cons symbol rest ih => simpa [streamEmit, encBits_apply] using ih)
  exact (stream.comp
    ((const (encList encUnary) encUnit ()).pair (identity (encList encUnary)))).ofOutputEq
      fun _ => rfl

/-- Bounded interpretation with literal bit-symbol adapters. A simulated output symbol is read
as `true` exactly when it is `1`; callers claiming bit-output semantics must establish that the
simulated output is the image of a bit word under `Universal.eBit`. -/
noncomputable def simulateBitOutputCompiler (description : Desc) :
    NativeCompiler
      (fun input : List Bool × ℕ =>
        ((simulate description (input.1.map Universal.eBit) input.2).1).map
          fun symbol => decide (symbol = 1))
      (encPair encBits encUnary) encBits := by
  let word := inputSymbolsCompiler.comp (first encBits encUnary)
  let clock := second encBits encUnary
  exact outputBitsCompiler.comp ((simulateOutputCompiler description).comp (word.pair clock))

end Turing.MultiTapeTM.Internal.NativeCompiler
