import Poe.Experiments.ValidatorStyles
import Poe.Experiments.HelloWorldParsed
import Poe.Oracle
import Poe.TplcOracle

/-!
Oracle tests for every *runnable* style in `ValidatorStyles.lean`, all
built from the same three `ScriptContext`-shaped inputs, run through both
backends, side by side — real evidence all four actually compile to
UPLC/TPLC and evaluate correctly, not just that they translate without
error (same discipline as every other oracle suite in this project).

Style 2 (`validatorB_correct`) isn't here: it's a theorem, not a runtime
artifact, so there's nothing to compile or execute. Style 6 (`vecHead`)
isn't here either: it takes a `List Int`, not a `ScriptContext`, so it
doesn't share this file's inputs — see its own oracle test directly in
`VecScratch.lean`.
-/

namespace Poe.Experiments.ValidatorStyles

open Poe.Uplc

/-- Same `ScriptContext` shape every other oracle suite in this project
    uses (`Poe.Examples.HelloWorldOracle.mkCtx` and friends) — repeated
    here rather than imported so this file's three cases are visibly
    shared across every style below. -/
def mkCtx (msg owner : String) (signatories : List String) : Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 0 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .const (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

def mkCtxTplc (msg owner : String) (signatories : List String) : Poe.Tplc.Term :=
  let txInfo := DataValue.constr 0
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer := DataValue.constr 0 [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 0 [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .constant (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

-- The three cases every style below is checked against: accept, wrong
-- message, wrong owner.
def okCtx := mkCtx "Hello, World!" "alice" ["alice", "bob"]
def wrongMsgCtx := mkCtx "wrong message" "alice" ["alice", "bob"]
def wrongOwnerCtx := mkCtx "Hello, World!" "mallory" ["alice", "bob"]

def okCtxTplc := mkCtxTplc "Hello, World!" "alice" ["alice", "bob"]
def wrongMsgCtxTplc := mkCtxTplc "wrong message" "alice" ["alice", "bob"]
def wrongOwnerCtxTplc := mkCtxTplc "Hello, World!" "mallory" ["alice", "bob"]

/-! ## Style 1: `validatorB` -/

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``Poe.Examples.HelloWorld.validatorB
    [([okCtx], .bool true), ([wrongMsgCtx], .bool false), ([wrongOwnerCtx], .bool false)]

#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``Poe.Examples.HelloWorld.validatorB
    [([okCtxTplc], .bool true), ([wrongMsgCtxTplc], .bool false), ([wrongOwnerCtxTplc], .bool false)]

/-! ## Style 3: `validatorEDecidable`

`Decidable`'s own runtime shape is "accept or abort" (via `checkDecidable`),
not a `Bool` you compare — checked like `validatorE`, matching
`ValidatorDecidableOracle.lean`'s own convention, not like `validatorB`. -/

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``Poe.Experiments.ValidatorDecidable.validatorEDecidable [([okCtx], .unit)]
  Poe.Oracle.runSuiteAborts ``Poe.Experiments.ValidatorDecidable.validatorEDecidable
    [[wrongMsgCtx], [wrongOwnerCtx]]

#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``Poe.Experiments.ValidatorDecidable.validatorEDecidable [([okCtxTplc], .unit)]
  Poe.TplcOracle.runSuiteAborts ``Poe.Experiments.ValidatorDecidable.validatorEDecidable
    [[wrongMsgCtxTplc], [wrongOwnerCtxTplc]]

/-! ## Style 4: `validatorBSubtype`

Erases to exactly the same one-argument shape as `validatorB` (`Subtype`'s
`Prop`-sorted `property` field carries no runtime content) — called the
same way, single bundled `ctx` argument. -/

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtype
    [([okCtx], .bool true), ([wrongMsgCtx], .bool false), ([wrongOwnerCtx], .bool false)]

#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtype
    [([okCtxTplc], .bool true), ([wrongMsgCtxTplc], .bool false), ([wrongOwnerCtxTplc], .bool false)]

/-! ## Style 5: `validatorBSubtypePost`

Same compiled shape again — the postcondition, like the precondition, is
`Prop`-erased, so this collapses to exactly the same runtime function as
styles 1 and 4. -/

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtypePost
    [([okCtx], .bool true), ([wrongMsgCtx], .bool false), ([wrongOwnerCtx], .bool false)]

#eval show Lean.CoreM Unit from do
  Poe.TplcOracle.runSuite ``Poe.Experiments.HelloWorldSubtype.validatorBSubtypePost
    [([okCtxTplc], .bool true), ([wrongMsgCtxTplc], .bool false), ([wrongOwnerCtxTplc], .bool false)]

/-! ## Flat-encoded sizes

`uplc convert --of hex` gives hex output; `length / 2` = bytes.
Aiken's reference (285 bytes) is from the official `hello_world` example.
-/

private def flatSize (declName : Lean.Name) : Lean.CoreM Nat := do
  let term ← Poe.Translate.translate declName
  let progText := Poe.Emit.emit term
  let hex ← IO.Process.run
    { cmd := "uplc", args := #["convert", "--if", "textual", "--of", "hex"] }
    (some progText)
  return hex.trim.length / 2

/-! `HelloWorldParsed.validatorE` (style 2E) decides `WellFormed` at the
entry point via `wellFormedB`, which pattern-matches on `Data` with two
reachable arms — that goes through the translator's `chooseData` multi-branch
path plus the native→SoP list conversion at the `unListData` boundary (see
`Poe.Translate.nativeListToSoPTerm`). It's the largest of the group because it
runs the full wellformedness check *and* re-decodes the fields, but it is in
the fragment and evaluates correctly (see `HelloWorldParsedOracle.lean`). -/

#eval show Lean.CoreM Unit from do
  let s1E ← flatSize ``Poe.Examples.HelloWorld.validatorE
  let s2E ← flatSize ``Poe.Experiments.HelloWorldParsed.validatorE
  let s3E ← flatSize ``Poe.Experiments.ValidatorDecidable.validatorEDecidable
  let s4E ← flatSize ``Poe.Experiments.HelloWorldSubtype.validatorBSubtype
  IO.println "Flat-encoded sizes (bytes):"
  IO.println s!"  Aiken hello_world (reference):  285"
  IO.println s!"  style4E / style5E (Subtype):     {s4E}"
  IO.println s!"  style1E (Bool, ghost wf):        {s1E}"
  IO.println s!"  style2E (Parsed, decided wf):     {s2E}"
  IO.println s!"  style3E (Decidable):             {s3E}"

end Poe.Experiments.ValidatorStyles
