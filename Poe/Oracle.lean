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

/-- The real, on-chain-relevant size metric for `program` (already-emitted
    textual UPLC): flat-encoded byte count, via the actual `uplc convert`
    tool — not hand-measured, not reimplemented. Goes via temp files
    rather than piping through `IO.Process.run`'s `String`-typed stdout,
    since flat encoding is raw binary and a `String` capture risks
    mangling non-UTF8 byte sequences (`convert` does support
    `--stdin`/`--stdout`, but only `evaluate`'s text-in/text-out shape is
    safe to pipe that way). -/
def flatSize (program : String) : IO Nat := do
  let tmpIn := "/tmp/poe_oracle_flatSize_in.uplc"
  let tmpOut := "/tmp/poe_oracle_flatSize_out.flat"
  IO.FS.writeFile tmpIn program
  let out ← IO.Process.output
    { cmd := "uplc", args := #["convert", "--if", "textual", "--of", "flat", "-i", tmpIn, "-o", tmpOut] }
  if out.exitCode != 0 then
    throw (IO.userError s!"uplc convert failed: {out.stderr}")
  let bytes ← IO.FS.readBinFile tmpOut
  return bytes.size

/-- `flatSize`'s own input is `declName` applied to no arguments — for a
    validator whose translated shape doesn't depend on which argument
    values it's later applied to (true of every `Poe.Translate` output:
    application only ever adds `.app` nodes around the same translated
    function term), this is the size that matters. -/
def sizeOf (declName : Name) : CoreM Nat := do
  let f ← Translate.translate declName
  flatSize (emit f)

def encodeInt (i : Int) : Uplc.Term :=
  .const (.integer i)

def encodeString (s : String) : Uplc.Term :=
  .const (.string s)

/-- Encode a `List α` as the `constr` chain `Translate`'s `cases` handling
    expects. Constructor indices come from the same environment lookup
    `Translate.ctorNames` uses for translation, so the encoder and the
    translator can't silently disagree about which index means
    `nil`/`cons`. -/
def encodeList (elemEncode : α → Uplc.Term) (xs : List α) : CoreM Uplc.Term := do
  let ctors ← Translate.ctorNames ``List
  let some nilIdx := ctors.findIdx? (· == ``List.nil)
    | throwError "translator env: no List.nil constructor found"
  let some consIdx := ctors.findIdx? (· == ``List.cons)
    | throwError "translator env: no List.cons constructor found"
  return xs.foldr (init := .constr nilIdx []) fun x acc => .constr consIdx [elemEncode x, acc]

def encodeIntList (xs : List Int) : CoreM Uplc.Term := encodeList encodeInt xs
def encodeStringList (xs : List String) : CoreM Uplc.Term := encodeList encodeString xs

/-- Translate `declName`, apply it to `args`, emit, and run through the
    oracle; returns the raw result term text (e.g. `"(con integer 42)"`). -/
def evalDecl (declName : Name) (args : List Uplc.Term) : CoreM String := do
  let f ← Translate.translate declName
  runUplc (emit (args.foldl .app f))

/-- One test case: the oracle's answer for `declName` applied to `args`,
    checked against `expected` (computed by the caller from the *actual*
    Lean function, not re-specified by hand). -/
def check (declName : Name) (args : List Uplc.Term) (expected : Uplc.Const) : CoreM (Except String Unit) := do
  let actual ← evalDecl declName args
  let expectedText := emitConst expected
  if actual == expectedText then
    return .ok ()
  else
    return .error s!"{declName} {args.map (emitTerm 0)}: oracle says {actual}, expected {expectedText}"

/-- Run a batch of test cases for one declaration; prints a pass count and
    every failure (a shim bug, if any, shows up here). -/
def runSuite (declName : Name) (cases : List (List Uplc.Term × Uplc.Const)) : CoreM Unit := do
  let mut failures := 0
  for (args, expected) in cases do
    match ← check declName args expected with
    | .ok () => pure ()
    | .error msg =>
      failures := failures + 1
      IO.println s!"FAIL: {msg}"
  IO.println s!"{declName}: {cases.length - failures}/{cases.length} passed"

/-- Like `evalDecl`, but for a program expected to *abort* (a `check`-wrapped
    validator on dishonest input): the CLI's own non-zero exit is the
    success signal here, so this doesn't throw on it the way `evalDecl`
    does. -/
def evalDeclAllowingError (declName : Name) (args : List Uplc.Term) : CoreM (UInt32 × String) := do
  let f ← Translate.translate declName
  let out ← IO.Process.output { cmd := "uplc", args := #["evaluate"] } (some (emit (args.foldl .app f)))
  return (out.exitCode, out.stdout.trim)

def checkAborts (declName : Name) (args : List Uplc.Term) : CoreM (Except String Unit) := do
  let (exitCode, actual) ← evalDeclAllowingError declName args
  if exitCode != 0 then
    return .ok ()
  else
    return .error s!"{declName} {args.map (emitTerm 0)}: expected to abort, oracle returned {actual}"

/-- `runSuite`'s counterpart for cases that should abort (UPLC `error`),
    e.g. a `check`-wrapped validator on dishonest input. -/
def runSuiteAborts (declName : Name) (casesArgs : List (List Uplc.Term)) : CoreM Unit := do
  let mut failures := 0
  for args in casesArgs do
    match ← checkAborts declName args with
    | .ok () => pure ()
    | .error msg =>
      failures := failures + 1
      IO.println s!"FAIL: {msg}"
  IO.println s!"{declName}: {casesArgs.length - failures}/{casesArgs.length} aborted as expected"

end Poe.Oracle
