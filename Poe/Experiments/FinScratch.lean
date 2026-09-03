import Poe.Translate
import Poe.TranslateTplc
import Poe.TplcOracle
import Poe.PlutusData

/-!
# `Fin`, as a first step toward a witnessed (not just decidable) membership check

Item 4 from the 2026-08-31 "what's next" thread: `Fin`-witness membership
— replacing `HelloWorld.lean`'s `Bool`/`Decidable`-valued
`elemBytes`/`List.Mem` check with something that returns *where* `owner`
was found (a real index), not just *whether* it was. `Fin n` is the
natural carrier: `structure Fin (n : Nat) where val : Nat; isLt : val < n`
— one live field, one `Prop`-sorted field that erases away, exactly the
same shape as `Subtype` (see `Poe.TranslateTplc`'s own `Subtype`
handling) — so `Fin n` should collapse to plain `Nat`/`.integer`, the same
way `Subtype α p` collapses to `α`.

Confirmed empirically, not assumed:
- The untyped backend already handled this for free (`Fin`'s erasure is
  exactly the kind of thing its generic fallback already covers).
- The typed backend needed two small, direct additions to
  `Poe.TranslateTplc` — a `Fin n → .builtin .integer` case in `translateTy`
  (alongside `Subtype`'s), and `.proj Fin 0`/`Fin.mk` handling in
  `translateLetValue`/`translateConstCall` (alongside `Subtype.mk`'s) —
  plus `Nat.add` in both backends' `builtinTable` (needed for `i.val + 1`
  arithmetic on a witness index; safe unconditionally, unlike `Nat.sub`'s
  own narrower literal-pattern-matching-only safety caveat, since `Nat`
  addition has no truncation edge case to get wrong).
-/

namespace Poe.Experiments.FinScratch

/-- `Fin`'s `val` field, projected back out — the identity once erased. -/
def finToNat {n : Nat} (i : Fin n) : Nat := i.val

#eval show Lean.CoreM Unit from do
  let f ← Poe.TranslateTplc.translate ``finToNat
  let applied := Poe.Tplc.Term.apply (Poe.Tplc.Term.apply f (.constant (.integer 5))) (.constant (.integer 2))
  let program := Poe.EmitTplc.emit applied
  let _ ← Poe.TplcOracle.runPlcTypecheck program
  IO.println s!"finToNat 5 2 (typed): {← Poe.TplcOracle.runPlcEvaluate program}"

/-- Constructing a genuine, live `Fin` value (not the dead-index case
    `dupIgnoringFin` in `VecScratch.lean` already covered) — the
    construction-side counterpart to `finToNat`. -/
def mkFin1 (h : (0 : Nat) < 3) : Fin 3 := ⟨0, h⟩

#eval show Lean.CoreM Unit from do
  let f ← Poe.TranslateTplc.translate ``mkFin1
  let program := Poe.EmitTplc.emit f
  let _ ← Poe.TplcOracle.runPlcTypecheck program
  IO.println s!"mkFin1 (typed): {← Poe.TplcOracle.runPlcEvaluate program}"

/-- `Option`'s construction (`some`/`none`) and consumption (`cases`),
    checked both ways — `wrapSome 7` unwrapped with a `-1` default should
    give `7`; `wrapNone` unwrapped the same way should give the default
    `-1` back. -/
def wrapSome (n : Int) : Option Int := some n
def wrapNone : Option Int := none
def unwrapOr (d : Int) : Option Int → Int
  | none => d
  | some x => x

#eval show Lean.CoreM Unit from do
  let some' ← Poe.TranslateTplc.translate ``wrapSome
  let none' ← Poe.TranslateTplc.translate ``wrapNone
  let unwrap ← Poe.TranslateTplc.translate ``unwrapOr
  let someProgram := Poe.EmitTplc.emit
    (.apply (.apply unwrap (.constant (.integer (-1)))) (.apply some' (.constant (.integer 7))))
  let noneProgram := Poe.EmitTplc.emit (.apply (.apply unwrap (.constant (.integer (-1)))) none')
  let _ ← Poe.TplcOracle.runPlcTypecheck someProgram
  let _ ← Poe.TplcOracle.runPlcTypecheck noneProgram
  IO.println s!"unwrapOr (-1) (wrapSome 7) (typed): {← Poe.TplcOracle.runPlcEvaluate someProgram}"
  IO.println s!"unwrapOr (-1) wrapNone (typed): {← Poe.TplcOracle.runPlcEvaluate noneProgram}"

/-!
## `Option`, added — genuinely non-recursive, so no `ifix`/`iwrap`/`unwrap`
anywhere (`optionSop`), unlike `List`/`Vec`

`Poe.TranslateTplc` now has full `Option` support: `translateTy`'s
`Option X` case, `Option.none`/`Option.some` construction, and a
`cases`-on-`Option` branch — confirmed with `wrapSome`/`wrapNone`/
`unwrapOr` directly against real `plc`, both the `none` and `some` paths.

## The actual witnessed-membership search — still not translatable, but
for a different, separate reason now

`findIndex` genuinely elaborates and type-checks in Lean (a certified
linear search: either the list is empty (`none`), or the head matches
(`some` at index `0`), or a recursive search on the tail succeeds and its
index gets shifted up by one, with `i.isLt`/`omega` proving the shifted
index still respects the longer list's own length). This is the actual
"fuller dependently typed" artifact — a real position, not just a
yes/no answer.

It still doesn't translate — but `Option` isn't the reason anymore.
`Fin l.length`'s own index computation calls `List.length`
(`List.lengthTR`/`List.lengthTRAux` in its actual compiled form), which
is *generic* (polymorphic in the list's element type) *and* recursive —
exactly the combination `Poe.TranslateTplc`'s own `typedFix` machinery
already documents as unsupported (`translateDecl`'s own error: "generic
recursive decl — not yet supported (`fixArg` would need to embed `T`
under a fresh binder with reshifting)"), a pre-existing, already-known
restriction, not a new gap discovered here. Note that `Fin.mk`'s own
translation only ever uses its *second* argument (`val`) — the index `n`
itself is completely unused by the translation — but `List.lengthTR`'s
call to *compute* `n` still has to translate on its own right, as an
ordinary `let`-binding, before that discarding ever happens; there's no
dead-let elimination to skip it. Generalizing `typedFix` to generic
recursive declarations would be its own substantial undertaking, not a
quick follow-on to `Option` support. -/

def findIndex (owner : ByteArray) : (l : List ByteArray) → Option (Fin l.length)
  | [] => none
  | x :: xs =>
    if x == owner then some ⟨0, by simp⟩
    else (findIndex owner xs).map (fun i => ⟨i.val + 1, by have := i.isLt; simp only [List.length_cons]; omega⟩)

end Poe.Experiments.FinScratch
