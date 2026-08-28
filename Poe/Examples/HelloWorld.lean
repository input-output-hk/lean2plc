import Poe.Lint
import Poe.Prelude
import Poe.PlutusData
import Poe.Lib.DataDecoding

namespace Poe.Examples.HelloWorld

open Poe.PlutusData (Data decodeByteStringList IsByteStringList)
open Poe.Lib.DataDecoding (elemBytes)

/-- `redeemer` really is `Constr _ [msg]` with `msg` a bytestring —
    pattern-matched all the way to `.b`, so there's nothing left to
    assert once the shape matches. -/
def RedeemerOk (redeemer : Data) : Prop :=
  match redeemer with
  | .constr _ [.b _] => True
  | _ => False

/-- The redeemer's message, given a proof its shape is honest. -/
def decodeMessage : ∀ redeemer, RedeemerOk redeemer → ByteArray
  | .constr _ [.b msgBytes], _ => msgBytes

/-- `txInfo` really has 8 filler fields, then the signatories list, then
    whatever real `TxInfo`'s other 7 fields are — pattern-matched down
    to `sigListData` directly, `IsByteStringList` on it because a
    variable-length list can't be pattern-matched any further (no finite
    pattern says "however many elements, every one a bytestring"). -/
def TxInfoOk (txInfo : Data) : Prop :=
  match txInfo with
  | .constr _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: sigListData :: _) =>
      IsByteStringList sigListData
  | _ => False

/-- `txInfo`'s signatories, given a proof its shape is honest. -/
def decodeSignatories : ∀ txInfo, TxInfoOk txInfo → List ByteArray
  | .constr _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: sigListData :: _), h =>
      decodeByteStringList sigListData h

/-- `scriptInfo` really is `Constr _ [_, Constr _ [Constr _ [.b owner]]]`
    — walking down through the `Just`-wrapped, `Datum`-wrapped owner
    bytes, all the way to `.b`, same reasoning as `RedeemerOk`. -/
def ScriptInfoOk (scriptInfo : Data) : Prop :=
  match scriptInfo with
  | .constr _ [_, .constr _ [.constr _ [.b _]]] => True
  | _ => False

/-- `scriptInfo`'s datum owner, given a proof its shape is honest. -/
def decodeOwner : ∀ scriptInfo, ScriptInfoOk scriptInfo → ByteArray
  | .constr _ [_, .constr _ [.constr _ [.b ownerBytes]]], _ => ownerBytes

/-- `ctx` really has the honest `ScriptContext` shape: `Constr 0
    [txInfo, redeemer, scriptInfo]`, with each of the three sub-trees
    honest per its own predicate above. -/
def WellFormed (ctx : Data) : Prop :=
  match ctx with
  | .constr 0 [txInfo, redeemer, scriptInfo] =>
      TxInfoOk txInfo ∧ RedeemerOk redeemer ∧ ScriptInfoOk scriptInfo
  | _ => False

/-- Aiken's `hello_world`, the main validator: the message must be
    exactly `"Hello, World!"`, and the datum's `owner` must be among the
    transaction's `signatories`. -/
def validatorB (ctx : Data) (wf : WellFormed ctx) : Bool :=
  match ctx, wf with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    let message := decodeMessage redeemer wfRedeemer
    let signatories := decodeSignatories txInfo wfTxInfo
    let owner := decodeOwner scriptInfo wfScriptInfo
    message == "Hello, World!".toUTF8 && elemBytes owner signatories

/-- The deployable artifact: turns `validatorB`'s `Bool` into
    the `()`-or-abort shape a real script needs. All the logic lives
    above; this is deliberately a one-line wrapper. -/
def validatorE (ctx : Data) (wf : WellFormed ctx) : Unit :=
  Poe.Prelude.check (validatorB ctx wf)

end Poe.Examples.HelloWorld
