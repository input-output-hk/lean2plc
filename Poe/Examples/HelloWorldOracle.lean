import Poe.Examples.HelloWorld
import Poe.Oracle

/-!
`validatorB`/`validatorE`'s D2 oracle suite: real `ScriptContext` `Data`
values, run through the actual `uplc` binary. Kept separate from
`HelloWorld.lean` itself (that file is the flagship example, meant to
read as clean business logic, not test scaffolding).
-/

namespace Poe.Examples.HelloWorld

open Poe.Uplc

/-- A `ScriptContext`-shaped `Data` value honest enough for `WellFormed`:
    `txInfo` has 8 filler fields then the signatories list at index 8;
    `redeemer` is `Constr _ [msg]`; `scriptInfo` is `Constr _ [_, Constr _
    [Constr _ [owner]]]`. -/
def mkCtx (msg owner : String) (signatories : List String) : Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 0 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .const (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``validatorB
    [ ([mkCtx "Hello, World!" "alice" ["alice", "bob"]], .bool true)
    , ([mkCtx "wrong message" "alice" ["alice", "bob"]], .bool false)
    , ([mkCtx "Hello, World!" "mallory" ["alice", "bob"]], .bool false)
    ]

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``validatorE
    [([mkCtx "Hello, World!" "alice" ["alice", "bob"]], .unit)]
  Poe.Oracle.runSuiteAborts ``validatorE
    [ [mkCtx "wrong message" "alice" ["alice", "bob"]]
    , [mkCtx "Hello, World!" "mallory" ["alice", "bob"]]
    ]

end Poe.Examples.HelloWorld
