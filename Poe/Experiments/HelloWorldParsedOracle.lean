import Poe.Experiments.HelloWorldParsed
import Poe.Oracle

/-!
Oracle suite for `HelloWorldParsed.validatorE` — the parsed-boundary
style where `WellFormed` is decided explicitly at the entry point.

Three well-formed cases (accept / wrong message / wrong owner) match every
other oracle suite in the project. A fourth case — ill-formed input — is
specific to this style: `validatorE_bad` proves the else branch is real
Lean code, and this oracle confirms the compiled UPLC actually errors on
inputs that don't match `WellFormed`, not just theoretically.
-/

namespace Poe.Experiments.HelloWorldParsed

open Poe.Uplc

def mkCtx (msg owner : String) (signatories : List String) : Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer  := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 0
    [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .const (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

-- An input that fails WellFormed: ctx is a Constr with zero fields.
def illFormedCtx : Term := .const (.data (.constr 0 []))

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``validatorE
    [([mkCtx "Hello, World!" "alice" ["alice", "bob"]], .unit)]
  Poe.Oracle.runSuiteAborts ``validatorE
    [ [mkCtx "wrong message" "alice" ["alice", "bob"]]
    , [mkCtx "Hello, World!" "mallory" ["alice", "bob"]]
    -- ill-formed: WellFormed fails, else branch fires, UPLC errors
    , [illFormedCtx]
    ]

end Poe.Experiments.HelloWorldParsed
