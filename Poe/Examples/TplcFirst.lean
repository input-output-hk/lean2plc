import Poe.Tplc
import Poe.EmitTplc
import Poe.TranslateTplc
import Poe.TplcOracle
import Poe.Examples.First

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

/-! ## D1 (typed): first translator targets

`Poe.TranslateTplc.translate`, the real base-LCNF → `Tplc.Term`
translator (not hand-built), exercised on two functions and checked
directly against `plc` (not just eyeballed):

* `double` (from `Poe.Examples.First`, monomorphic — no genuine
  polymorphism involved) translates to a term that `plc typecheck`s as
  `(fun (con integer) (con integer))` and `plc evaluate`s applied to `5`
  as `(con integer 10)`.
* `genericId` (genuinely polymorphic — the reason this whole second
  backend exists) translates to *exactly* `tplcPolyIdentity` above,
  `Term.tyAbs .type (Term.lamAbs (Ty.var 0) (Term.var 0))` — a real,
  non-hand-built reproduction of the same term already `plc`-verified
  above, this time produced by reading `α`'s `Param` (a type-former,
  hence wrapped in `tyAbs`) and its call-site `Arg.type` instantiations
  straight out of base LCNF instead of being written down by hand. -/

/-- Genuinely polymorphic (unlike everything in `Poe.Examples.First`
    so far): `α`'s own `Param.type` is a type former (`Type`), so
    `Poe.TranslateTplc.translateDecl` wraps it in `Term.tyAbs` rather
    than a value-level `Term.lamAbs` — the first fragment function this
    translator can't even represent in the untyped backend without first
    monomorphizing it away. -/
def genericId {α : Type} (x : α) : α := x

-- `genericId` is genuinely polymorphic, so testing it through
-- `Poe.TplcOracle` would need to apply a `TyInst` before any value
-- argument — `evalDecl` only supports ordinary value application so
-- far (no other fragment target needs polymorphic application yet).
-- Its correctness is already pinned down structurally instead: it
-- translates to *exactly* `tplcPolyIdentity` above, which *is*
-- `plc`-verified.
#eval show Lean.CoreM Unit from do
  IO.println (Poe.EmitTplc.emit (← Poe.TranslateTplc.translate ``genericId))

#eval show Lean.CoreM Unit from do
  IO.println (Poe.EmitTplc.emit (← Poe.TranslateTplc.translate ``Poe.Examples.double))
#eval show Lean.CoreM Unit from
  Poe.TplcOracle.runSuite ``Poe.Examples.double
    ((List.range 5).map fun n =>
      ([Poe.TplcOracle.encodeInt (Int.ofNat n)], .integer (Poe.Examples.double (Int.ofNat n))))

/-! `absInt` (also from `Poe.Examples.First`) is the first `Bool`-branching
    target: base LCNF's `if x < 0 then ...` turns out to be `cases` on
    `Decidable.isFalse`/`Decidable.isTrue`, not plain `Bool` — mono-phase
    LCNF has already collapsed that down to `Bool.false`/`Bool.true` by
    the time `Poe.Translate` looks (confirmed directly by comparing
    `dumpMonoLCNF`/`Poe.TranslateTplc.dumpBaseLCNF` side by side), so this
    is a genuinely new case the untyped translator never had to handle.
    `Poe.TplcOracle.runSuite` below (not a hand-copied `plc` transcript
    — the real oracle, checked against `absInt`'s own Lean value) covers
    both signs, confirming the `ifThenElse` thunk encoding (see
    `Poe.TranslateTplc`'s doc comment) picks the *correct* branch in both
    directions, not just that *a* branch evaluates without error. -/
#eval show Lean.CoreM Unit from do
  IO.println (Poe.EmitTplc.emit (← Poe.TranslateTplc.translate ``Poe.Examples.absInt))
#eval show Lean.CoreM Unit from
  Poe.TplcOracle.runSuite ``Poe.Examples.absInt
    ([(-3 : Int), -1, 0, 1, 3].map fun n =>
      ([Poe.TplcOracle.encodeInt n], .integer (Poe.Examples.absInt n)))

/-! `divide` (also from `Poe.Examples.First`) exercises two more things at
    once: its `hy : y ≠ 0` proof parameter is dropped entirely (LCNF's
    `lcErased` type on that `Param`, filtered the same way
    `Poe.Translate.translateDecl` already had to), and its `poeError`
    branch (`Code.unreach`) becomes `Term.error`, both inside a
    `Decidable`-branching `ifThenElse`. The oracle suite includes a
    negative-divisor case (`7 / (-2) = -4`, floor division — the same
    `divideInteger`/`Int.fdiv` correspondence `Poe.Translate` already
    relies on) and a `runSuiteAborts` case confirming `divide 7 0`
    genuinely aborts, not just "some branch happens to evaluate". -/
#eval show Lean.CoreM Unit from do
  IO.println (Poe.EmitTplc.emit (← Poe.TranslateTplc.translate ``Poe.Examples.divide))
#eval show Lean.CoreM Unit from
  Poe.TplcOracle.runSuite ``Poe.Examples.divide
    [ ([Poe.TplcOracle.encodeInt 7, Poe.TplcOracle.encodeInt (-2)],
        .integer (Poe.Examples.divide 7 (-2) (by decide)))
    , ([Poe.TplcOracle.encodeInt (-41), Poe.TplcOracle.encodeInt 5],
        .integer (Poe.Examples.divide (-41) 5 (by decide)))
    ]
#eval show Lean.CoreM Unit from
  Poe.TplcOracle.runSuiteAborts ``Poe.Examples.divide
    [[Poe.TplcOracle.encodeInt 7, Poe.TplcOracle.encodeInt 0]]

/-! `head` (also from `Poe.Examples.First`) is the first target needing
    `List`'s `cases`/`constr` support (`Poe.TranslateTplc.listPatFunctor`/
    `listTy`/`listUnrolledSop`, the isorecursive pattern-functor encoding
    — see that file's doc comment). `Poe.TplcOracle.encodeIntList` builds
    the input list through the *same* `iwrap`/`constr` encoding the
    translator itself uses, so this is testing the real translator's
    `List` handling on both the producer and consumer side, not a
    hand-built shortcut. -/
#eval show Lean.CoreM Unit from do
  IO.println (Poe.EmitTplc.emit (← Poe.TranslateTplc.translate ``Poe.Examples.head))
#eval show Lean.CoreM Unit from
  Poe.TplcOracle.runSuite ``Poe.Examples.head
    [ ([Poe.TplcOracle.encodeIntList [3, 99]], .integer (Poe.Examples.head [3, 99] (by decide)))
    , ([Poe.TplcOracle.encodeIntList [7]], .integer (Poe.Examples.head [7] (by decide)))
    ]
#eval show Lean.CoreM Unit from
  Poe.TplcOracle.runSuiteAborts ``Poe.Examples.head [[Poe.TplcOracle.encodeIntList []]]

/-! `sumList` (also from `Poe.Examples.First`) is the first genuinely
    *recursive* target — `Poe.TranslateTplc.typedFix`/`fixPat`/`fixArg`/
    `selfTy`, the isorecursive self-application fixpoint combinator (see
    that file's doc comment for the CBV-vs-call-by-name bug this design
    caught along the way). The empty-list case is the one that actually
    confirms the recursion *terminates* rather than merely not crashing
    on the first call. -/
#eval show Lean.CoreM Unit from do
  IO.println (Poe.EmitTplc.emit (← Poe.TranslateTplc.translate ``Poe.Examples.sumList))
#eval show Lean.CoreM Unit from
  Poe.TplcOracle.runSuite ``Poe.Examples.sumList
    [ ([Poe.TplcOracle.encodeIntList [3, 99]], .integer (Poe.Examples.sumList [3, 99]))
    , ([Poe.TplcOracle.encodeIntList []], .integer (Poe.Examples.sumList []))
    ]

end Poe.Examples
