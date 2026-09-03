import Poe.Experiments.ValidatorDecidable
import Poe.Oracle
import Poe.TplcOracle

/-!
Oracle tests for `Poe.Experiments.ValidatorDecidable`, kept separate from
the definitions themselves (same split as `Poe.Examples.HelloWorldOracle`/
`HelloWorldOracleTplc` from `Poe.Examples.HelloWorld`).
-/

open Poe.Uplc

def mkCtxDecidable (msg owner : String) (signatories : List String) : Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 1 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .const (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

/- Confirms the untyped backend's `Decidable`-erasure genuinely produces
   the correct boolean behavior, membership included (`hmem`, built from
   `elemBytes_iff` the exact same way `heq` is built from
   `ByteArray.beq_iff_eq`) — not just that it translates without error. -/
#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``Poe.Experiments.ValidatorDecidable.validatorEDecidable
    [([mkCtxDecidable "Hello, World!" "alice" ["alice", "bob"]], .unit)]
  Poe.Oracle.runSuiteAborts ``Poe.Experiments.ValidatorDecidable.validatorEDecidable
    [ [mkCtxDecidable "wrong message" "alice" ["alice", "bob"]]
    , [mkCtxDecidable "Hello, World!" "mallory" ["alice", "bob"]]
    ]

def mkCtxDecidableTplc (msg owner : String) (signatories : List String) : Poe.Tplc.Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 1 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .constant (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

/- Same check on the typed backend — needed two real fixes to reach at
   all: join-point support in `Poe.TranslateTplc.translateCode` (the base
   LCNF `And.decidable` generates for its shared `isTrue`/`isFalse`
   continuation, confirmed directly by dumping `validatorBDecidable`'s own
   base LCNF), and a constructor case for `Decidable.isFalse`/`isTrue`
   (both fields already `Prop`-erased, same collapse-to-`Bool` `Decidable`
   cases already got on the consuming side). -/
#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``Poe.Experiments.ValidatorDecidable.validatorEDecidable
    [([mkCtxDecidableTplc "Hello, World!" "alice" ["alice", "bob"]], .unit)]
  Poe.TplcOracle.runSuiteAborts ``Poe.Experiments.ValidatorDecidable.validatorEDecidable
    [ [mkCtxDecidableTplc "wrong message" "alice" ["alice", "bob"]]
    , [mkCtxDecidableTplc "Hello, World!" "mallory" ["alice", "bob"]]
    ]
