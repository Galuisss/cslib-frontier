/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SLHDSA.XMSS.PublicKeyFromSignature

/-!
# Checked clients for FIPS 205 XMSS public-key reconstruction

These ordinary clients cover Algorithm 11's even and odd block orders, mutable address evolution,
all six standardized XMSS heights, executable composition with WOTS+ Algorithm 8, and the exact
operation/query/static source ledgers. They do not claim generated-signature correctness,
verification, security or compiled resource bounds.
-/

public section

namespace SLHDSAXMSSPublicKeyTests

open Cslib.Crypto Cslib.Crypto.SLHDSA Cslib.Crypto.SLHDSA.XMSS

private def zeroBytes (p : SecurityBytes) : NBytes p := fun _ => 0
private def oneBytes (p : SecurityBytes) : NBytes p := fun _ => 1
private def twoBytes (p : SecurityBytes) : NBytes p := fun _ => 2
private def zeroMessage (p : SecurityBytes) : WOTS.Message p := fun _ => 0
private def zeroWOTSSignature (p : SecurityBytes) : WOTS.Signature p := fun _ _ => 0

private def zeroSignature (p : SecurityBytes) (shape : ParameterShape) : Signature p shape :=
  { wots := zeroWOTSSignature p
    authentication := fun _ _ => 0 }

private def zeroIndex (p : SecurityBytes) (shape : ParameterShape) : LeafIndex p shape :=
  ⟨0, by cases p <;> cases shape <;> decide⟩

private def baseAddress : Address :=
  Address.tree 3 0x0102030405060708 0 0

/-! ### Exact signature and parameter shapes -/

example : ParameterShape.xmssHeight .bytes16 .small = 9 := rfl
example : ParameterShape.xmssHeight .bytes16 .fast = 3 := rfl
example : ParameterShape.xmssHeight .bytes24 .small = 9 := rfl
example : ParameterShape.xmssHeight .bytes24 .fast = 3 := rfl
example : ParameterShape.xmssHeight .bytes32 .small = 8 := rfl
example : ParameterShape.xmssHeight .bytes32 .fast = 4 := rfl

example : signatureBlocks .bytes16 .small = 44 := rfl
example : signatureBytes .bytes16 .small = 704 := rfl
example : signatureBlocks .bytes32 .fast = 71 := rfl
example : signatureBytes .bytes32 .fast = 2272 := rfl

/-! ### Branch order and mutable address evolution -/

private def indexZero : LeafIndex .bytes16 .fast := ⟨0, by decide⟩
private def indexOne : LeafIndex .bytes16 .fast := ⟨1, by decide⟩
private def indexFive : LeafIndex .bytes16 .fast := ⟨5, by decide⟩
private def levelZero : Fin (ParameterShape.xmssHeight .bytes16 .fast) := ⟨0, by decide⟩
private def levelOne : Fin (ParameterShape.xmssHeight .bytes16 .fast) := ⟨1, by decide⟩

example : nodeIsLeft indexZero.val levelZero.val = true := rfl
example : nodeIsLeft indexOne.val levelZero.val = false := rfl

example (node authenticationNode : NBytes .bytes16) :
    authenticationInput indexZero levelZero node authenticationNode =
      FixedBytes.pairBlocks node authenticationNode :=
  authenticationInput_of_left indexZero levelZero node authenticationNode rfl

example (node authenticationNode : NBytes .bytes16) :
    authenticationInput indexOne levelZero node authenticationNode =
      FixedBytes.pairBlocks authenticationNode node :=
  authenticationInput_of_right indexOne levelZero node authenticationNode rfl

private def initialFive : Address := initialTreeAddress baseAddress indexFive
private def afterLevelZero : Address :=
  authenticationStepAddress initialFive levelZero (nodeIsLeft indexFive.val levelZero.val)
private def afterLevelOne : Address :=
  authenticationStepAddress afterLevelZero levelOne (nodeIsLeft indexFive.val levelOne.val)

example : initialFive.word7.val = 5 := rfl
example : afterLevelZero.word6.val = 1 ∧ afterLevelZero.word7.val = 2 := ⟨rfl, rfl⟩
example : afterLevelOne.word6.val = 2 ∧ afterLevelOne.word7.val = 1 := ⟨rfl, rfl⟩

-- Exercise the two block-order branches through the actual recursive evaluator, rather than only
-- through the detached input helper.
example (family : HashFamily) :
    (authenticationRootWithCalls family indexZero (fun _ => twoBytes .bytes16)
      (zeroBytes .bytes16) baseAddress (oneBytes .bytes16) 1 (by decide)).output =
      h family (zeroBytes .bytes16)
        (authenticationStepAddress (initialTreeAddress baseAddress indexZero) levelZero true)
        (FixedBytes.pairBlocks (oneBytes .bytes16) (twoBytes .bytes16)) := by
  rw [authenticationRootWithCalls_succ_output]
  rw [authenticationRootWithCalls_zero]
  rfl

example (family : HashFamily) :
    (authenticationRootWithCalls family indexOne (fun _ => twoBytes .bytes16)
      (zeroBytes .bytes16) baseAddress (oneBytes .bytes16) 1 (by decide)).output =
      h family (zeroBytes .bytes16)
        (authenticationStepAddress (initialTreeAddress baseAddress indexOne) levelZero false)
        (FixedBytes.pairBlocks (twoBytes .bytes16) (oneBytes .bytes16)) := by
  rw [authenticationRootWithCalls_succ_output]
  rw [authenticationRootWithCalls_zero]
  rfl

example (family : HashFamily) :
    AddressAtLevel baseAddress indexFive 2
      (authenticationRootWithCalls family indexFive (fun _ => zeroBytes .bytes16)
        (zeroBytes .bytes16) baseAddress (zeroBytes .bytes16) 2 (by decide)).address :=
  authenticationRootWithCalls_addressAtLevel family indexFive (fun _ => zeroBytes .bytes16)
    (zeroBytes .bytes16) baseAddress (zeroBytes .bytes16) 2 (by decide)

/-! ### Complete executable clients -/

example : NBytes .bytes16 :=
  xmssPkFromSig .shake (zeroIndex .bytes16 .small) (zeroSignature .bytes16 .small)
    (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress
example : NBytes .bytes16 :=
  xmssPkFromSig .sha2 (zeroIndex .bytes16 .fast) (zeroSignature .bytes16 .fast)
    (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress
example : NBytes .bytes24 :=
  xmssPkFromSig .shake (zeroIndex .bytes24 .small) (zeroSignature .bytes24 .small)
    (zeroMessage .bytes24) (zeroBytes .bytes24) baseAddress
example : NBytes .bytes24 :=
  xmssPkFromSig .sha2 (zeroIndex .bytes24 .fast) (zeroSignature .bytes24 .fast)
    (zeroMessage .bytes24) (zeroBytes .bytes24) baseAddress
example : NBytes .bytes32 :=
  xmssPkFromSig .shake (zeroIndex .bytes32 .small) (zeroSignature .bytes32 .small)
    (zeroMessage .bytes32) (zeroBytes .bytes32) baseAddress
example : NBytes .bytes32 :=
  xmssPkFromSig .sha2 (zeroIndex .bytes32 .fast) (zeroSignature .bytes32 .fast)
    (zeroMessage .bytes32) (zeroBytes .bytes32) baseAddress

example (family : HashFamily) :
    (xmssPkFromSigWithLedger family indexFive (zeroSignature .bytes16 .fast)
      (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress).output =
      xmssPkFromSig family indexFive (zeroSignature .bytes16 .fast) (zeroMessage .bytes16)
        (zeroBytes .bytes16) baseAddress :=
  xmssPkFromSigWithLedger_output family indexFive (zeroSignature .bytes16 .fast)
    (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress

example (family : HashFamily) :
    (xmssPkFromSigWithLedger family indexFive (zeroSignature .bytes16 .fast)
      (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress).ledger =
      sourceLedger (zeroMessage .bytes16) indexFive :=
  xmssPkFromSigWithLedger_ledger family indexFive (zeroSignature .bytes16 .fast)
    (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress

/-! ### Exact source ledgers -/

example : (authenticationCalls 5 3).hCalls = 3 := rfl
example : (authenticationCalls 5 3).nodeFirstBranches = 1 := rfl
example : (authenticationCalls 5 3).authenticationFirstBranches = 2 := rfl
example : (operationLedger (zeroMessage .bytes16) indexFive).treeIndexWrites = 4 := rfl
example : (operationLedger (zeroMessage .bytes16) indexFive).authentication.hCalls = 3 := rfl
example : queryLedger.externalOracleQueries = 0 := rfl
example : queryLedger.externalOracleHandlers = 0 := rfl
example :
    (staticDescriptionLedger .bytes16 .fast).compiledDescriptionBytes = none := rfl
example : (staticDescriptionLedger .bytes16 .fast).hInputBytes = 32 := rfl
example : (staticDescriptionLedger .bytes16 .fast).outputBytes = 16 := rfl

end SLHDSAXMSSPublicKeyTests
