import Lean
import Poe.Uplc
import Poe.Emit
import Poe.Translate

/-!
# D2: emitter + oracle harness

Translates a declaration, applies it to encoded argument terms, emits the
result, and runs it through the real `uplc` CLI — the execution oracle
(see PLAN.md). The oracle's answer is compared against the *actual* Lean
value (not a hand-copied formula), so a shim bug shows up as a mismatch
here rather than being assumed away.
-/

namespace Poe.Oracle

open Lean Poe.Emit

/-- Shell out to `uplc evaluate`, piping the program in on stdin (the CLI
    supports this directly — no temp file needed). Throws if `uplc` exits
    non-zero (e.g. the emitted term is malformed) or isn't on `PATH`. -/
def runUplc (program : String) : IO String := do
  let out ← IO.Process.run { cmd := "uplc", args := #["evaluate"] } (some program)
  return out.trim

def encodeInt (i : Int) : Uplc.Term :=
  .const (.integer i)

/-- Encode a `List Int` as the `constr` chain `Translate`'s `cases` handling
    expects. Constructor indices come from the same environment lookup
    `Translate.ctorNames` uses for translation, so the encoder and the
    translator can't silently disagree about which index means
    `nil`/`cons`. -/
def encodeIntList (xs : List Int) : CoreM Uplc.Term := do
  let ctors ← Translate.ctorNames ``List
  let some nilIdx := ctors.findIdx? (· == ``List.nil)
    | throwError "translator env: no List.nil constructor found"
  let some consIdx := ctors.findIdx? (· == ``List.cons)
    | throwError "translator env: no List.cons constructor found"
  return xs.foldr (init := .constr nilIdx []) fun x acc => .constr consIdx [encodeInt x, acc]

/-- Translate `declName`, apply it to `args`, emit, and run through the
    oracle; returns the raw result term text (e.g. `"(con integer 42)"`). -/
def evalDecl (declName : Name) (args : List Uplc.Term) : CoreM String := do
  let f ← Translate.translate declName
  runUplc (emit (args.foldl .app f))

/-- One test case: the oracle's answer for `declName` applied to `args`,
    checked against `expected` (computed by the caller from the *actual*
    Lean function, not re-specified by hand). -/
def check (declName : Name) (args : List Uplc.Term) (expected : Int) : CoreM (Except String Unit) := do
  let actual ← evalDecl declName args
  let expectedText := emitConst (.integer expected)
  if actual == expectedText then
    return .ok ()
  else
    return .error s!"{declName} {args.map (emitTerm 0)}: oracle says {actual}, expected {expectedText}"

/-- Run a batch of test cases for one declaration; prints a pass count and
    every failure (a shim bug, if any, shows up here). -/
def runSuite (declName : Name) (cases : List (List Uplc.Term × Int)) : CoreM Unit := do
  let mut failures := 0
  for (args, expected) in cases do
    match ← check declName args expected with
    | .ok () => pure ()
    | .error msg =>
      failures := failures + 1
      IO.println s!"FAIL: {msg}"
  IO.println s!"{declName}: {cases.length - failures}/{cases.length} passed"

end Poe.Oracle
