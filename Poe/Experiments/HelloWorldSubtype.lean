import Poe.Examples.HelloWorld
import Poe.Translate
import Poe.TranslateTplc
import Poe.Oracle
import Poe.TplcOracle

/-!
Scratch: a `Subtype`-bundled variant of `Poe.Examples.HelloWorld.validatorB`
— `(v : {ctx : Data // WellFormed ctx})` instead of the flagship's curried
`(ctx : Data) (wf : WellFormed ctx)`. Same body, same `WellFormed`/decoder
helpers, only the packaging differs. Not a replacement for the flagship
(that curried style was a deliberate earlier choice, not an oversight) —
just checking, by direct analogy to `vHead`, whether today's `Subtype`
fix in `Poe.TranslateTplc` really does carry over to this shape too.
-/

namespace Poe.Experiments.HelloWorldSubtype

open Poe.PlutusData (Data)
open Poe.Examples.HelloWorld (WellFormed decodeMessage decodeSignatories decodeOwner)
open Poe.Lib.DataDecoding (elemBytes)

def validatorBSubtype (v : {ctx : Data // WellFormed ctx}) : Bool :=
  match v.1, v.2 with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    let message := decodeMessage redeemer wfRedeemer
    let signatories := decodeSignatories txInfo wfTxInfo
    let owner := decodeOwner scriptInfo wfScriptInfo
    message == "Hello, World!".toUTF8 && elemBytes owner signatories

end Poe.Experiments.HelloWorldSubtype

open Poe.Uplc

def mkCtxSubtype (msg owner : String) (signatories : List String) : Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 0 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .const (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtype
    [ ([mkCtxSubtype "Hello, World!" "alice" ["alice", "bob"]], .bool true)
    , ([mkCtxSubtype "wrong message" "alice" ["alice", "bob"]], .bool false)
    , ([mkCtxSubtype "Hello, World!" "mallory" ["alice", "bob"]], .bool false)
    ]

def mkCtxSubtypeTplc (msg owner : String) (signatories : List String) : Poe.Tplc.Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 0 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .constant (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtype
    [ ([mkCtxSubtypeTplc "Hello, World!" "alice" ["alice", "bob"]], .bool true)
    , ([mkCtxSubtypeTplc "wrong message" "alice" ["alice", "bob"]], .bool false)
    , ([mkCtxSubtypeTplc "Hello, World!" "mallory" ["alice", "bob"]], .bool false)
    ]
