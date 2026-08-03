import Poe.Tplc
import Poe.EmitTplc

/-!
# First light, typed backend

`Poe.Examples.First`'s section 1 (hand-built term + emitted text, checked
against the real oracle before any translator exists) for the *typed*
Plutus Core backend. These three terms were hand-verified directly
against the real, production `plc` executable
(`nix build github:input-output-hk/plutus#plc`, now a permanent part of
this repo's own devshell alongside `uplc`, see `flake.nix`):

* `plc typecheck` on all three returns exactly the expected type
  (`(fun (con integer) (con integer))`, `(all t0-2 (type) (fun t0-2 t0-2))`,
  `(con integer)` respectively).
* `plc evaluate` on `appliedPoly` returns `(con integer 42)`.
* `plc erase` on `appliedPoly` returns
  `(program 1.1.0 [ (force (delay (lam x0-1 x0-1))) (con integer 42) ])`
  — exactly the `TyAbs → Delay`/`TyInst → Force` recipe read directly out
  of the real `PlutusCore/Compiler/Erase.hs`.

Paste any of the three `#eval`ed strings below into `plc typecheck`/
`plc evaluate`/`plc erase` (piped on stdin, same convention `Poe.Oracle`
already uses for `uplc`) to reproduce this directly.
-/

namespace Poe.Examples

open Poe.Tplc

/-- `\(x : integer) -> x`. -/
def tplcIdentity : Term :=
  .lamAbs (.builtin .integer) (.var 0)

#eval Poe.EmitTplc.emit tplcIdentity

/-- `/\t. \(x : t) -> x`, the polymorphic identity — the whole reason a
    *typed* backend exists at all: this term has no untyped-UPLC
    counterpart of its own (it erases to `force (delay (lam x x))`,
    already representable, but only *after* erasure). -/
def tplcPolyIdentity : Term :=
  .tyAbs .type (.lamAbs (.var 0) (.var 0))

#eval Poe.EmitTplc.emit tplcPolyIdentity

/-- `polyIdentity {integer} 42`, i.e. the polymorphic identity
    instantiated at `integer` and applied to `42`. -/
def tplcAppliedPoly : Term :=
  .apply (.tyInst tplcPolyIdentity (.builtin .integer)) (.constant (.integer 42))

#eval Poe.EmitTplc.emit tplcAppliedPoly

end Poe.Examples
