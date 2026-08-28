import Poe.Examples.HelloWorld
import Poe.TplcOracle

/-!
`validatorB`/`validatorE`'s D2 oracle suite for the *typed* backend
(`Poe.TranslateTplc`) — same cases as `Poe.Examples.HelloWorldOracle`,
run through `plc typecheck`/`plc evaluate` instead of `uplc`.
-/

namespace Poe.Examples.HelloWorld

open Poe.Uplc

def mkCtxTplc (msg owner : String) (signatories : List String) : Poe.Tplc.Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 0 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .constant (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``validatorB
    [ ([mkCtxTplc "Hello, World!" "alice" ["alice", "bob"]], .bool true)
    , ([mkCtxTplc "wrong message" "alice" ["alice", "bob"]], .bool false)
    , ([mkCtxTplc "Hello, World!" "mallory" ["alice", "bob"]], .bool false)
    ]

#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``validatorE
    [([mkCtxTplc "Hello, World!" "alice" ["alice", "bob"]], .unit)]
  Poe.TplcOracle.runSuiteAborts ``validatorE
    [ [mkCtxTplc "wrong message" "alice" ["alice", "bob"]]
    , [mkCtxTplc "Hello, World!" "mallory" ["alice", "bob"]]
    ]

end Poe.Examples.HelloWorld
