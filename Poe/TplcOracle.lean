import Lean
import Poe.Uplc
import Poe.Emit
import Poe.Tplc
import Poe.EmitTplc
import Poe.TranslateTplc

/-!
# D2 (typed backend): emitter + oracle harness

`Poe.Oracle`'s own role, for the typed backend: translates a declaration,
applies it to encoded argument terms, emits the result, and runs it
through the real `plc` CLI. Unlike `Poe.Oracle`, every check runs `plc
typecheck` *first*, as a hard gate before ever evaluating — both real bugs
found while building `Poe.TranslateTplc` this session (`Bool`/`Unit`
construction, `Decidable.decide`'s `Prop`-sorted parameter) surfaced as
type errors, not evaluation mismatches, and would otherwise have gone
uncaught by an evaluate-only check that happened to still produce the
right *value* via some other route.
-/

namespace Poe.TplcOracle

open Lean Poe.EmitTplc

/-- Shell out to `plc typecheck`, piping the program in on stdin. Throws
    (with `plc`'s own type error message) if the emitted term is ill-typed
    — the harness's first line of defense, run before every evaluation. -/
def runPlcTypecheck (program : String) : IO String := do
  let out ← IO.Process.run { cmd := "plc", args := #["typecheck"] } (some program)
  return out.trim

/-- Shell out to `plc evaluate`, piping the program in on stdin. Throws if
    `plc` exits non-zero (e.g. the program genuinely aborts) or isn't on
    `PATH`. -/
def runPlcEvaluate (program : String) : IO String := do
  let out ← IO.Process.run { cmd := "plc", args := #["evaluate"] } (some program)
  return out.trim

def encodeInt (i : Int) : Tplc.Term := .constant (.integer i)
def encodeString (s : String) : Tplc.Term := .constant (.string s)
def encodeByteArray (b : ByteArray) : Tplc.Term := .constant (.bytestring b)

/-- Encode a `List α` as the `iwrap`/`constr` chain `Poe.TranslateTplc`'s
    own `List.nil`/`List.cons` translation builds — same `listPatFunctor`/
    `listUnrolledSop` helpers, so the encoder and the translator can't
    silently disagree about the recursive-type encoding (nil = index 0,
    cons = index 1, matching `Poe.PlutusData.Data`'s own declaration
    order, same convention `Poe.Oracle.encodeList`'s `ctorNames`-based
    lookup uses for the untyped side). -/
def encodeList (elemTy : Tplc.Ty) (elemEncode : α → Tplc.Term) (xs : List α) : Tplc.Term :=
  let nilTerm := Tplc.Term.iwrap TranslateTplc.listPatFunctor elemTy
    (.constr (TranslateTplc.listUnrolledSop elemTy) 0 [])
  xs.foldr (init := nilTerm) fun x acc =>
    .iwrap TranslateTplc.listPatFunctor elemTy
      (.constr (TranslateTplc.listUnrolledSop elemTy) 1 [elemEncode x, acc])

def encodeIntList (xs : List Int) : Tplc.Term := encodeList (.builtin .integer) encodeInt xs
def encodeByteArrayList (xs : List ByteArray) : Tplc.Term := encodeList (.builtin .bytestring) encodeByteArray xs

/-- Translate `declName`, apply it to `args`, emit, typecheck (thrown away —
    a hard gate, not a return value), then evaluate; returns the raw result
    term text (e.g. `"(con integer 42)"`). -/
def evalDecl (declName : Name) (args : List Tplc.Term) : CoreM String := do
  let f ← TranslateTplc.translate declName
  let program := emit (args.foldl .apply f)
  let _ ← runPlcTypecheck program
  runPlcEvaluate program

/-- One test case: the oracle's answer for `declName` applied to `args`,
    checked against `expected` (computed by the caller from the *actual*
    Lean function, not re-specified by hand) — same convention
    `Poe.Oracle.check` uses, reusing `Poe.Emit.emitConst` directly since
    `Tplc.Term.constant` wraps the very same `Poe.Uplc.Const`. -/
def check (declName : Name) (args : List Tplc.Term) (expected : Poe.Uplc.Const) : CoreM (Except String Unit) := do
  let actual ← evalDecl declName args
  let expectedText := Poe.Emit.emitConst expected
  if actual == expectedText then
    return .ok ()
  else
    return .error s!"{declName} {args.map (emitTerm 0 0)}: oracle says {actual}, expected {expectedText}"

/-- Run a batch of test cases for one declaration; prints a pass count and
    every failure (a translator bug, if any, shows up here). -/
def runSuite (declName : Name) (cases : List (List Tplc.Term × Poe.Uplc.Const)) : CoreM Unit := do
  let mut failures := 0
  for (args, expected) in cases do
    match ← check declName args expected with
    | .ok () => pure ()
    | .error msg =>
      failures := failures + 1
      IO.println s!"FAIL: {msg}"
  IO.println s!"{declName}: {cases.length - failures}/{cases.length} passed"

/-- Like `evalDecl`, but for a program expected to *abort* — typechecks
    first (still a hard gate: an aborting program must still be
    *well-typed*, or the abort is for the wrong reason), then evaluates
    allowing a non-zero exit, which is the success signal here. -/
def evalDeclAllowingError (declName : Name) (args : List Tplc.Term) : CoreM (UInt32 × String) := do
  let f ← TranslateTplc.translate declName
  let program := emit (args.foldl .apply f)
  let _ ← runPlcTypecheck program
  let out ← IO.Process.output { cmd := "plc", args := #["evaluate"] } (some program)
  return (out.exitCode, out.stdout.trim)

def checkAborts (declName : Name) (args : List Tplc.Term) : CoreM (Except String Unit) := do
  let (exitCode, actual) ← evalDeclAllowingError declName args
  if exitCode != 0 then
    return .ok ()
  else
    return .error s!"{declName} {args.map (emitTerm 0 0)}: expected to abort, oracle returned {actual}"

/-- `runSuite`'s counterpart for cases that should abort. -/
def runSuiteAborts (declName : Name) (casesArgs : List (List Tplc.Term)) : CoreM Unit := do
  let mut failures := 0
  for args in casesArgs do
    match ← checkAborts declName args with
    | .ok () => pure ()
    | .error msg =>
      failures := failures + 1
      IO.println s!"FAIL: {msg}"
  IO.println s!"{declName}: {casesArgs.length - failures}/{casesArgs.length} aborted as expected"

end Poe.TplcOracle
