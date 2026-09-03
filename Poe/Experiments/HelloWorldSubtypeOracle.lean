import Poe.Experiments.HelloWorldSubtype
import Poe.Oracle
import Poe.TplcOracle

/-!
Oracle tests for `Poe.Experiments.HelloWorldSubtype`, kept separate from
the definitions themselves (same split as `Poe.Examples.HelloWorldOracle`/
`HelloWorldOracleTplc` and `Poe.Experiments.ValidatorDecidableOracle`).
-/

open Poe.Uplc

def mkCtxSubtype (msg owner : String) (signatories : List String) : Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 1 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .const (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtype
    [ ([mkCtxSubtype "Hello, World!" "alice" ["alice", "bob"]], .bool true)
    , ([mkCtxSubtype "wrong message" "alice" ["alice", "bob"]], .bool false)
    , ([mkCtxSubtype "Hello, World!" "mallory" ["alice", "bob"]], .bool false)
    ]

/- `validatorBSubtypePost`'s compiled shape is identical to
   `validatorBSubtype`'s (the postcondition, like the precondition, is
   `Prop`-erased) — same oracle cases, same expected results, checked
   independently rather than assumed from `validatorBSubtype`'s own
   passing suite. Needed one further typed-backend fix beyond `vHead`'s
   own `Subtype`/`.val` work: constructing `⟨val, proof⟩` itself
   (`Subtype.mk`), not just consuming an existing one. -/
#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtypePost
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
  let scriptInfo := DataValue.constr 1 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .constant (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtype
    [ ([mkCtxSubtypeTplc "Hello, World!" "alice" ["alice", "bob"]], .bool true)
    , ([mkCtxSubtypeTplc "wrong message" "alice" ["alice", "bob"]], .bool false)
    , ([mkCtxSubtypeTplc "Hello, World!" "mallory" ["alice", "bob"]], .bool false)
    ]

#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtypePost
    [ ([mkCtxSubtypeTplc "Hello, World!" "alice" ["alice", "bob"]], .bool true)
    , ([mkCtxSubtypeTplc "wrong message" "alice" ["alice", "bob"]], .bool false)
    , ([mkCtxSubtypeTplc "Hello, World!" "mallory" ["alice", "bob"]], .bool false)
    ]
