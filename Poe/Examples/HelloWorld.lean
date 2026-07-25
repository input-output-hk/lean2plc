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

namespace Poe.Examples.HelloWorld

open Poe.PlutusData (Data unBData decodeByteStringList constrTag field0 field1 field2 field8)
open Poe.Examples.DataDecoding (elemBytes elemBytes_iff ByteArray.beq_iff_eq)

/-- Aiken's `hello_world`, but from one real `ScriptContext`-shaped `Data`
    argument instead of three pre-decoded ones: `false` unless this is a
    `SpendingScript` invocation, `false` unless it actually has a datum,
    then the same message + signer checks as before. Split out from
    `validateScriptContext` (a plain `Bool`, not `Unit`) so there's
    something a correctness theorem can actually say something about —
    `Unit` has exactly one inhabitant, so any theorem of the shape
    `validateScriptContext ctx = ()` would be vacuously true regardless of
    what the function does (same reason `Poe.Examples.HelloWorldString`
    proves things about `validate`, never `validateChecked`). -/
def isHonestScriptContext (ctx : Data) : Bool :=
  let txInfo := field0 ctx
  let redeemer := field1 ctx
  let scriptInfo := field2 ctx
  let message := unBData (field0 redeemer)
  let signatories := decodeByteStringList (field8 txInfo)
  if constrTag scriptInfo == 1 then
    let maybeDatum := field1 scriptInfo
    if constrTag maybeDatum == 0 then
      let owner := unBData (field0 (field0 maybeDatum))
      message == "Hello, World!".toUTF8 && elemBytes owner signatories
    else
      false
  else
    false

def validateScriptContext (ctx : Data) : Unit :=
  Poe.Prelude.check (isHonestScriptContext ctx)

#eval Poe.Lint.check ``isHonestScriptContext
#eval Poe.Lint.check ``validateScriptContext

/-! ## (a) An ordinary Lean correctness theorem about the source function

Conditional on the `_spec` axioms in `Poe.PlutusData` (the honest trust
boundary documented there: what `Translate` emits is *claimed*, not
proven here, to implement these primitives) — this is the same kind of
theorem `Poe.Examples.HelloWorldString.validate_correct` proves, just
over real `ScriptContext`-shaped `Data` navigation instead of `String`
arguments already handed to the validator pre-decoded. -/

open Poe.PlutusData (unBData_spec decodeByteStringList_spec constrTag_spec
  field0_spec field1_spec field2_spec field8_spec)

/-- Builds the `Data` shape `isHonestScriptContext` expects, at the
    `Poe.PlutusData.Data` level — same shape `mkScriptContext`/
    `mkSpendingScriptInfo` (below) build at the `Poe.Uplc.DataValue`
    level for the oracle, just so the theorem can be stated over concrete
    inputs instead of an abstract shape hypothesis for everything.
    `txInfo` stays abstract (see `isHonestScriptContext_correct`) rather
    than a fully-built 16-field record — reconstructing that real shape
    just to re-derive `field8`/`decodeByteStringList` on it would be
    reproving `Poe.PlutusData`'s own axioms, not saying anything new about
    `isHonestScriptContext`'s actual navigation logic. -/
def mkCtxData (txInfo : Data) (messageBytes : ByteArray) (owner : ByteArray) : Data :=
  .constr 0
    [ txInfo
    , .constr 0 [.b messageBytes]
    , .constr 1 [.b (ByteArray.mk #[]), .constr 0 [.constr 0 [.b owner]]] ]

/-- Correctness of the honest-`Spending`-with-a-datum path: accepts
    exactly when the message is right and the owner signed — the same
    statement `validate_correct` makes, over the real navigation.
    `signatories` is given via a `field8 txInfo` hypothesis rather than by
    constructing a full, real 16-field `TxInfo` and re-deriving that
    `field8`/`decodeByteStringList` extract it correctly — that's already
    exactly what the `_spec` axioms assert, and what the oracle's
    `mkTxInfo`-based tests below exercise on the *real* compiled program;
    reconstructing it here would just restate those, not say anything new
    about `isHonestScriptContext`'s own logic (the scriptInfo/maybeDatum/
    message/owner navigation) that this theorem is actually about. The
    dishonest-shape cases (wrong purpose, no datum) aren't `Data`-shape
    hypotheses here either — they're a separate, simpler fact:
    `isHonestScriptContext` is `false` outright whenever `constrTag` of
    `field2`/`field1 (field2 ·)` isn't `1`/`0`, visible directly from the
    `if`s in its own definition, with no need to unfold the accessor
    axioms at all. -/
theorem isHonestScriptContext_correct
    (txInfo : Data) (signatories : List ByteArray)
    (hsig : decodeByteStringList (field8 txInfo) = signatories)
    (messageBytes : ByteArray) (owner : ByteArray) :
    isHonestScriptContext (mkCtxData txInfo messageBytes owner) = true ↔
      messageBytes = "Hello, World!".toUTF8 ∧ owner ∈ signatories := by
  simp only [isHonestScriptContext, mkCtxData,
    field0_spec, field1_spec, field2_spec, constrTag_spec, unBData_spec, hsig]
  simp [elemBytes_iff, ByteArray.beq_iff_eq, and_comm]

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

end Poe.Examples.HelloWorld
