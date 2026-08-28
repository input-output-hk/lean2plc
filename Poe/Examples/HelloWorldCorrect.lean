import Poe.Examples.HelloWorld

/-! Correctness of `validatorB`, over the business logic only. -/

namespace Poe.Examples.HelloWorld

open Poe.PlutusData (Data)
open Poe.Lib.DataDecoding (elemBytes_iff ByteArray.beq_iff_eq)

def mkCtxData (txInfo : Data) (messageBytes owner : ByteArray) : Data :=
  .constr 0
    [ txInfo
    , .constr 0 [.b messageBytes]
    , .constr 1 [.b (ByteArray.mk #[]), .constr 0 [.constr 0 [.b owner]]] ]

theorem validatorB_correct
    (txInfo : Data) (signatories : List ByteArray) (h : TxInfoOk txInfo)
    (hsig : decodeSignatories txInfo h = signatories)
    (messageBytes owner : ByteArray) :
    validatorB (mkCtxData txInfo messageBytes owner) ⟨h, trivial, trivial⟩ = true ↔
      messageBytes = "Hello, World!".toUTF8 ∧ owner ∈ signatories := by
  unfold validatorB
  simp only [mkCtxData, decodeMessage, decodeOwner, hsig]
  simp [elemBytes_iff, ByteArray.beq_iff_eq, and_comm]

end Poe.Examples.HelloWorld
