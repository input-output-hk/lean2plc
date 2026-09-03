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

/-- `scriptInfo` really is `Constr 1 [_, Constr 0 [Constr 0 [.b owner]]]` —
    tag `1` because real `ScriptInfo`'s `SpendingScript` constructor is
    index 1 (`MintingScript=0, SpendingScript=1, ...`, confirmed directly
    against `PlutusLedgerApi.V3.Contexts`'s own `makeIsDataSchemaIndexed`
    call), not a wildcard: `CertifyingScript`/`ProposingScript` also have
    exactly two fields, so an unchecked tag here would accept a
    certifying- or proposing-purpose `ScriptContext` as if it were a
    spending one, silently decoding the wrong bytes as `owner` — exactly
    the "accept decision depends on the wrong subset of context" bug
    class (double satisfaction/script-purpose confusion), not a
    hypothetical one, until this was checked against the real ledger-api
    source. The inner tag `0` is `Just` (also confirmed against the real
    ledger: PlutusTx's `Maybe` is indexed `[('Just, 0), ('Nothing, 1)]`,
    not declaration order), then `0` again for `Datum`'s own
    single-constructor record. -/
def ScriptInfoOk (scriptInfo : Data) : Prop :=
  match scriptInfo with
  | .constr 1 [_, .constr 0 [.constr 0 [.b _]]] => True
  | _ => False

/-- `scriptInfo`'s datum owner, given a proof its shape is honest. -/
def decodeOwner : ∀ scriptInfo, ScriptInfoOk scriptInfo → ByteArray
  | .constr 1 [_, .constr 0 [.constr 0 [.b ownerBytes]]], _ => ownerBytes

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
