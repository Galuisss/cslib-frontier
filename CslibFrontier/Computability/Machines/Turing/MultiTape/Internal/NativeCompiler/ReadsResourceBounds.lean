/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Universal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamResourceBounds

/-!
# Resource bounds for retained work-tape reads

This module bounds the actual time and workspace maps of `reads`. The bounds apply the retained
list-stream construction to the concrete `tapeRead` callback and keep installed program size as a
separate static coordinate.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.reads_time_le`: a concrete quadratic time majorant.
* `Turing.MultiTapeTM.Internal.NativeCompiler.reads_workspace_le`: an independent concrete
  quadratic workspace majorant.

The construction and bounds are original formalization infrastructure.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM.Universal

/-- The actual retained work-head map has quadratic time in the complete encoded tape list. -/
theorem reads_time_le (tapes : List Tape) :
    reads.time tapes ≤ 1000000 * ((encList eTape tapes).length + 1) ^ 2 := by
  let L := (encList eTape tapes).length
  let encInput := encPair encUnit eTape
  let nextCompiler : NativeCompiler (fun input : Unit × Tape => input.1)
      encInput encUnit := first encUnit eTape
  let callback : NativeCompiler (fun input : Unit × Tape => input.2.read)
      encInput eSym := tapeRead.comp (second encUnit eTape)
  let emitCompiler : NativeCompiler (fun input : Unit × Tape => frame (eSym input.2.read))
      encInput encBits :=
    ((framedValue eSym).comp callback).ofOutputEq fun _ => rfl
  let finishCompiler : NativeCompiler (Function.const Unit ([] : List Bool))
      encUnit encBits := const encUnit encBits []
  let marshal : NativeCompiler (fun input : List Tape => ((), input))
      (encList eTape) (encPair encUnit (encList eTape)) :=
    (const (encList eTape) encUnit ()).pair (identity (encList eTape))
  have hstate : ∀ j, j ≤ tapes.length →
      (encUnit (streamState () (fun input : Unit × Tape => input.1) tapes j)).length ≤ L + 4 := by
    intro j hj
    simp [encUnit_apply]
  have helem : ∀ j (hj : j < tapes.length), (eTape tapes[j]).length ≤ L + 4 := by
    intro j hj
    exact (length_le_encList_of_mem eTape (List.getElem_mem hj)).trans (by omega)
  have hnext : ∀ j (hj : j < tapes.length),
      nextCompiler.time
        (streamState () (fun input : Unit × Tape => input.1) tapes j, tapes[j]) ≤
        100 * (L + 4) := by
    intro j hj
    have h := helem j hj
    simp only [eTape_apply, length_encPair] at h
    simp [nextCompiler, first, ofTransducer, L, encInput] at h ⊢
    omega
  have hemit : ∀ j (hj : j < tapes.length),
      emitCompiler.time
        (streamState () (fun input : Unit × Tape => input.1) tapes j, tapes[j]) ≤
        50000 * (L + 4) := by
    intro j hj
    let pair := (streamState () (fun input : Unit × Tape => input.1) tapes j, tapes[j])
    have hsecond := time_comp_le tapeRead (second encUnit eTape) pair
    change (tapeRead.comp (second encUnit eTape)).time pair ≤
      5 * (second encUnit eTape).time pair + tapeRead.time tapes[j] + 9 at hsecond
    have hsecondTime : (second encUnit eTape).time pair ≤ 100 * (L + 4) := by
      have h := helem j hj
      simp only [eTape_apply, length_encPair] at h
      simp [second, ofTransducer, pair] at h ⊢
      omega
    have htape : tapeRead.time tapes[j] ≤ 2000 * (L + 4) := by
      have h := tapeRead_time_le tapes[j]
      have he := helem j hj
      omega
    have hcallback : callback.time pair ≤ 6000 * (L + 4) := by
      simp only [callback]
      exact hsecond.trans (by omega)
    have hframed := time_comp_le (framedValue eSym) callback pair
    change ((framedValue eSym).comp callback).time pair ≤
      5 * callback.time pair + (4 * (eSym pair.2.read).length + 8) + 9 at hframed
    have hread : (eSym pair.2.read).length ≤ L + 4 := by
      have h := Universal.length_eSym_read_le tapes[j]
      have he := helem j hj
      simpa only [pair, Prod.snd] using h.trans he
    change emitCompiler.time pair ≤ 50000 * (L + 4)
    simp only [emitCompiler, ofOutputEq]
    exact hframed.trans (by omega)
  have hfinish : finishCompiler.time
      (streamState () (fun input : Unit × Tape => input.1) tapes tapes.length) ≤ 1 := by
    simp [finishCompiler, const]
  have hstream := streamFoldPairTime_le nextCompiler emitCompiler finishCompiler
    ((), tapes) (50000 * (L + 4)) (100 * (L + 4)) 1 (L + 4)
    (by simp [L]) hstate helem hemit hnext hfinish
  have hstream' :
      (listMapWithStateCompiler encUnit eTape eSym callback).time ((), tapes) ≤
        tapes.length * (50000 * (L + 4) + 100 * (L + 4) + 46 * (L + 4) + 60) +
          1 + 24 * (L + 4) + 40 := by
    change streamFoldPairTime nextCompiler emitCompiler finishCompiler ((), tapes) ≤ _
    exact hstream
  have hcount : tapes.length ≤ L := length_le_length_encList eTape tapes
  have hround :
      50000 * (L + 4) + 100 * (L + 4) + 46 * (L + 4) + 60 ≤
        50200 * (L + 4) := by omega
  have hmul := Nat.mul_le_mul hcount hround
  have hquad : L * (50200 * (L + 4)) ≤ 300000 * (L + 1) ^ 2 := by
    nlinarith
  have hrounds := hmul.trans hquad
  have hlinear : L + 4 ≤ 4 * (L + 1) ^ 2 := by
    nlinarith
  have hstreamBound :
      (listMapWithStateCompiler encUnit eTape eSym callback).time ((), tapes) ≤
        400000 * (L + 1) ^ 2 := by
    omega
  have hmarshalRaw := time_pair_le (const (encList eTape) encUnit ())
    (identity (encList eTape)) tapes
  have hmarshal : marshal.time tapes ≤ 100 * (L + 1) := by
    change ((const (encList eTape) encUnit ()).pair
      (identity (encList eTape))).time tapes ≤ 100 * (L + 1)
    exact hmarshalRaw.trans (by simp [const, identity]; omega)
  have hcomp := time_comp_le (listMapWithStateCompiler encUnit eTape eSym callback)
    marshal tapes
  change ((listMapWithStateCompiler encUnit eTape eSym callback).comp marshal).time tapes ≤
    1000000 * (L + 1) ^ 2
  simp only [marshal] at hmarshal hcomp ⊢
  omega

/-- The actual retained work-head map has quadratic workspace in the complete encoded tape list,
independently of its time coordinate. -/
theorem reads_workspace_le (tapes : List Tape) :
    reads.workspace tapes ≤ 10000000000 * ((encList eTape tapes).length + 1) ^ 2 := by
  let L := (encList eTape tapes).length
  let encInput := encPair encUnit eTape
  let nextCompiler : NativeCompiler (fun input : Unit × Tape => input.1)
      encInput encUnit := first encUnit eTape
  let callback : NativeCompiler (fun input : Unit × Tape => input.2.read)
      encInput eSym := tapeRead.comp (second encUnit eTape)
  let emitCompiler : NativeCompiler (fun input : Unit × Tape => frame (eSym input.2.read))
      encInput encBits :=
    ((framedValue eSym).comp callback).ofOutputEq fun _ => rfl
  let marshal : NativeCompiler (fun input : List Tape => ((), input))
      (encList eTape) (encPair encUnit (encList eTape)) :=
    (const (encList eTape) encUnit ()).pair (identity (encList eTape))
  have hstate : ∀ j, j ≤ tapes.length →
      (encUnit (streamState () (fun input : Unit × Tape => input.1) tapes j)).length ≤ L + 4 := by
    intro j hj
    simp [encUnit_apply]
  have helem : ∀ j (hj : j < tapes.length), (eTape tapes[j]).length ≤ L + 4 := by
    intro j hj
    exact (length_le_encList_of_mem eTape (List.getElem_mem hj)).trans (by omega)
  have hnext : ∀ j (hj : j < tapes.length),
      nextCompiler.workspace
        (streamState () (fun input : Unit × Tape => input.1) tapes j, tapes[j]) ≤
          100 * (L + 4) := by
    intro j hj
    have h := helem j hj
    simp only [eTape_apply, length_encPair] at h
    simp [nextCompiler, first, ofTransducer, L, encInput] at h ⊢
  have hemit : ∀ j (hj : j < tapes.length),
      emitCompiler.workspace
        (streamState () (fun input : Unit × Tape => input.1) tapes j, tapes[j]) ≤
          100000 * (L + 4) := by
    intro j hj
    let pair := (streamState () (fun input : Unit × Tape => input.1) tapes j, tapes[j])
    have hsecondTime : (second encUnit eTape).time pair ≤ 100 * (L + 4) := by
      have h := helem j hj
      simp only [eTape_apply, length_encPair] at h
      simp [second, ofTransducer, pair] at h ⊢
      omega
    have hsecondSpace : (second encUnit eTape).workspace pair ≤ 100 * (L + 4) := by
      have h := helem j hj
      simp only [eTape_apply, length_encPair] at h
      simp [second, ofTransducer, pair] at h ⊢
    have htapeTime : tapeRead.time tapes[j] ≤ 2000 * (L + 4) := by
      have h := tapeRead_time_le tapes[j]
      have he := helem j hj
      omega
    have htapeSpace : tapeRead.workspace tapes[j] ≤ 2000 * (L + 4) := by
      have h := tapeRead_workspace_le tapes[j]
      have he := helem j hj
      omega
    have hcomponentTapes :
        max (second encUnit eTape).tapeCount tapeRead.tapeCount ≤ 100 := by
      have hread := tapeRead_tapeCount_le
      simp [second, ofTransducer]
      omega
    have hcallbackTimeRaw := time_comp_le tapeRead (second encUnit eTape) pair
    simp only [pair] at hsecondTime hsecondSpace hcallbackTimeRaw
    have hcallbackTime : callback.time pair ≤ 6000 * (L + 4) := by
      simp only [callback]
      exact hcallbackTimeRaw.trans (by omega)
    have hcallbackSpaceRaw := workspace_comp_le tapeRead (second encUnit eTape) pair
    simp only [pair] at hcallbackSpaceRaw
    have hcallbackSpace : callback.workspace pair ≤ 10000 * (L + 4) := by
      simp only [callback]
      exact hcallbackSpaceRaw.trans (by nlinarith)
    have hcallbackTapes : callback.tapeCount ≤ 102 := by
      simp only [callback, comp]
      omega
    have hframedSpace : (framedValue eSym).workspace pair.2.read = 0 := rfl
    have hframedTape : (framedValue eSym).tapeCount = 0 := rfl
    have hframedTapes : max callback.tapeCount (framedValue eSym).tapeCount ≤ 102 := by
      rw [hframedTape, Nat.max_zero]
      exact hcallbackTapes
    have hframed := workspace_comp_le (framedValue eSym) callback pair
    rw [hframedSpace] at hframed
    change emitCompiler.workspace pair ≤ 100000 * (L + 4)
    simp only [emitCompiler, ofOutputEq]
    exact hframed.trans (by nlinarith)
  have hresult : ∀ input : Unit × List Tape,
      encList eSym (input.2.map fun tape => tape.read) =
        streamEmit (fun pair : Unit × Tape => pair.1)
          (fun pair => frame (eSym pair.2.read)) input.1 input.2 := by
    intro input
    induction input.2 with
    | nil => rfl
    | cons tape tapes ih => simpa [streamEmit, encList_cons] using ih
  have hstreamRaw := listFoldEmitCompiler_workspace_le nextCompiler emitCompiler hresult
    ((), tapes) (100000 * (L + 4)) (100 * (L + 4)) (L + 4)
    hstate helem hemit hnext
  let K := streamFoldPairTapeCount nextCompiler emitCompiler (const encUnit encBits [])
  have hK : K ≤ 1000 := by
    have hread := tapeRead_tapeCount_le
    simp [K, streamFoldPairTapeCount, streamFramedNext, streamUnframedFinish,
      nextCompiler, emitCompiler, callback, first, second, framedValue, ofTransducer,
      comp, const, encodeFrame, unframeValue, ofOutputEq]
    omega
  have hstream :
      (listMapWithStateCompiler encUnit eTape eSym callback).workspace ((), tapes) ≤
        1000000000 * (L + 1) ^ 2 := by
    change (listFoldEmitCompiler encUnit eTape (encList eSym) nextCompiler emitCompiler
      hresult).workspace ((), tapes) ≤ _
    change (listFoldEmitCompiler encUnit eTape (encList eSym) nextCompiler emitCompiler
      hresult).workspace ((), tapes) ≤
        2 * K * (100000 * (L + 4) + 100 * (L + 4) + 48 * (L + 4) +
          20 * K + 90) + 13 * (L + 4) + 5 * K + 43 at hstreamRaw
    have hB : L + 4 ≤ 4 * (L + 1) := by omega
    exact hstreamRaw.trans (by nlinarith)
  have hmarshalTimeRaw := time_pair_le (const (encList eTape) encUnit ())
    (identity (encList eTape)) tapes
  have hmarshalTime : marshal.time tapes ≤ 100 * (L + 1) := by
    change ((const (encList eTape) encUnit ()).pair
      (identity (encList eTape))).time tapes ≤ 100 * (L + 1)
    exact hmarshalTimeRaw.trans (by simp [const, identity]; omega)
  have hmarshalSpaceRaw := workspace_pair_le (const (encList eTape) encUnit ())
    (identity (encList eTape)) tapes
  have hmarshalSpace : marshal.workspace tapes ≤ 100 * (L + 1) := by
    change ((const (encList eTape) encUnit ()).pair
      (identity (encList eTape))).workspace tapes ≤ 100 * (L + 1)
    exact hmarshalSpaceRaw.trans (by simp [const, identity]; omega)
  have hmarshalTapes : marshal.tapeCount ≤ 100 := by
    simp [marshal, const, identity, pair, comp, encodeFrame]
  have hstreamTapes :
      (listMapWithStateCompiler encUnit eTape eSym callback).tapeCount ≤ 1000 := by
    change streamFoldPairTapeCount nextCompiler emitCompiler (const encUnit encBits []) ≤ 1000
    simpa only [K] using hK
  have hmax : max marshal.tapeCount
      (listMapWithStateCompiler encUnit eTape eSym callback).tapeCount ≤ 1000 :=
    max_le (hmarshalTapes.trans (by omega)) hstreamTapes
  have hcomp := workspace_comp_le (listMapWithStateCompiler encUnit eTape eSym callback)
    marshal tapes
  change ((listMapWithStateCompiler encUnit eTape eSym callback).comp marshal).workspace tapes ≤
    10000000000 * (L + 1) ^ 2
  exact hcomp.trans (by nlinarith)

end Turing.MultiTapeTM.Internal.NativeCompiler
