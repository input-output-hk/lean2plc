import Poe.Lint
import Poe.Oracle
import Poe.Prelude
import Poe.PlutusData
import Poe.Examples.DataDecoding

/-!
# One `Data` argument, real `ScriptContext`-shaped

`Poe.Examples.AikenHelloWorld.validateHelloWorld` still takes three
already-decoded `Data` arguments. A real Plutus V3 validator gets exactly
one — the whole `ScriptContext` — and has to navigate down into it by
hand. Verified against `plutus-ledger-api` source
(`PlutusLedgerApi.V3.Contexts`), not assumed:

  ScriptContext          = Constr 0 [txInfo, redeemer, scriptInfo]
  TxInfo                 = Constr 0 [16 fields; txInfoSignatories is field 8]
  ScriptInfo/SpendingScript = Constr 1 [txOutRef, Maybe Datum]   -- tag 1, confirmed
  Maybe                   = Just: Constr 0 [x]; Nothing: Constr 1 []  -- NOT 0/1 the "obvious" way round
  Datum, Redeemer (ours)  = Constr 0 [payload]                  -- the newtypes wrapping them are
                                                                  transparent (`newtype Datum =
                                                                  Datum BuiltinData`), no extra layer

`TxInfo` here is trimmed to just the one field used (`txInfoSignatories`
at its real index 8) with `I 0` placeholders elsewhere — the point is the
*navigation*, not reproducing all 16 fields.
-/

namespace Poe.Examples.ScriptContext

open Poe.PlutusData (Data unBData decodeByteStringList constrTag field0 field1 field2 field8)
open Poe.Examples.DataDecoding (elemBytes)

/-- Aiken's `hello_world`, but from one real `ScriptContext`-shaped `Data`
    argument instead of three pre-decoded ones: reject unless this is a
    `SpendingScript` invocation, reject unless it actually has a datum,
    then the same message + signer checks as before. -/
def validateScriptContext (ctx : Data) : Unit :=
  let txInfo := field0 ctx
  let redeemer := field1 ctx
  let scriptInfo := field2 ctx
  let message := unBData (field0 redeemer)
  let signatories := decodeByteStringList (field8 txInfo)
  if constrTag scriptInfo == 1 then
    let maybeDatum := field1 scriptInfo
    if constrTag maybeDatum == 0 then
      let owner := unBData (field0 (field0 maybeDatum))
      Poe.Prelude.check
        (message == "Hello, World!".toUTF8 && elemBytes owner signatories)
    else
      Poe.Prelude.abort ()
  else
    Poe.Prelude.abort ()

#eval Poe.Lint.check ``validateScriptContext

/-! ## Building test `ScriptContext` blobs -/

def dataStr (s : String) : Poe.Uplc.DataValue := .b s.toUTF8

def mkTxInfo (signatories : List String) : Poe.Uplc.DataValue :=
  let filler := List.replicate 8 (Poe.Uplc.DataValue.b (ByteArray.mk #[]))
  .constr 0 (filler.take 8 ++ [.list (signatories.map dataStr)] ++ filler.take 7)

/-- `scriptInfo` for an honest `Spending` invocation with an inline datum
    whose owner is `owner`. -/
def mkSpendingScriptInfo (owner : String) : Poe.Uplc.DataValue :=
  .constr 1
    [ .constr 0 [.b (ByteArray.mk #[])]           -- dummy TxOutRef
    , .constr 0 [.constr 0 [dataStr owner]] ]     -- Just (Datum { owner })

/-- `scriptInfo` for a `Spending` invocation with *no* datum (`None`). -/
def mkSpendingScriptInfoNoDatum : Poe.Uplc.DataValue :=
  .constr 1 [.constr 0 [.b (ByteArray.mk #[])], .constr 1 []]

/-- `scriptInfo` for a non-`Spending` purpose (any tag other than 1). -/
def mkMintingScriptInfo : Poe.Uplc.DataValue :=
  .constr 0 [.b (ByteArray.mk #[])]

def mkScriptContext (message : String) (signatories : List String)
    (scriptInfo : Poe.Uplc.DataValue) : Poe.Uplc.Term :=
  .const (.data (.constr 0
    [ mkTxInfo signatories
    , .constr 0 [dataStr message]   -- Redeemer { msg }
    , scriptInfo ]))

/- Honest: Spending, has a datum, owner signed, right message.
   Dishonest: not a Spending script; Spending but no datum; right
   shape but owner isn't a signatory; wrong message. -/
#eval show Lean.CoreM Unit from do
  let signers := ["bob", "alice", "carol"]
  Poe.Oracle.runSuite ``validateScriptContext
    [([mkScriptContext "Hello, World!" signers (mkSpendingScriptInfo "alice")], .unit)]
  Poe.Oracle.runSuiteAborts ``validateScriptContext
    [ [mkScriptContext "Hello, World!" signers mkMintingScriptInfo]
    , [mkScriptContext "Hello, World!" signers mkSpendingScriptInfoNoDatum]
    , [mkScriptContext "Hello, World!" signers (mkSpendingScriptInfo "mallory")]
    , [mkScriptContext "wrong message" signers (mkSpendingScriptInfo "alice")]
    ]

end Poe.Examples.ScriptContext
