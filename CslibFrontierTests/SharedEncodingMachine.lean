/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (shared encoding machine regression tests)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
import CslibFrontier.Foundations.Data.BitString.List.PrefixFree

/-! Ordinary-import clients of shared encodings and native machine certificates. -/

namespace CslibFrontierTests.SharedEncodingMachine

open Turing.MultiTapeTM

/-- Mixed fields exercise framing, empty options and list payloads. -/
structure Packet where
  /-- A one-bit tag. -/
  tag : Bool
  /-- Optional unframed payload. -/
  payload : Option (List Bool)

enc_structure encPacket : Packet where tag : encBool, payload : (encOption encBits)

-- The generated encoding retains the former field-tuple word, through the shared product.
example (p : Packet) : encPacket p =
    Cslib.Encoding.encProd Cslib.Encoding.encBool
      (Cslib.Encoding.encOption Cslib.Encoding.encBits) (p.tag, p.payload) := rfl

example : encPacket ⟨false, some []⟩ = [true, false, false, true] := rfl

example (p : Packet) : (encBool p.tag).length ≤ (encPacket p).length :=
  encPacket_tag_length_le p

-- Shared encodings accept the machine rules without transports or changed resource bounds.
example : ComputableInTimeAndSpace (· + 1) Cslib.Encoding.encNat Cslib.Encoding.encNat
    (fun n => 2 * (Cslib.Encoding.encNat n).length + 3) (fun _ => 0) :=
  computableInTimeAndSpace_succ

example (n : ℕ) : encNat n = n.bits := encNat_apply n

-- The fixed-width client keeps its previous literal range/testBit layout.
example (K : ℕ) (i : Fin K) : Cslib.BitString.finIdxBits K i =
    (List.range (Nat.clog 2 K)).map i.val.testBit := rfl

end CslibFrontierTests.SharedEncodingMachine
