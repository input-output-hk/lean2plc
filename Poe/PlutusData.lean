/-!
# Minimal on-chain `Data` slice

Real Plutus Core `Data = Constr Integer [Data] | Map [(Data,Data)] | List
[Data] | I Integer | B ByteString` (verified against
`plutus-core/src/PlutusCore/Data.hs`) is how Datum/Redeemer/ScriptContext
actually arrive on-chain — not as `String`/`List String` the way
`Poe.Examples.HelloWorld` models them. Full `Data`/serialization support is
a stated PLAN.md non-goal for increment 1; this is deliberately just
`unBData` and `decodeByteStringList` (a byte-string-list decoder — see
below), the primitives `Poe.Examples.DataDecoding` actually uses.

`Data` is never pattern-matched on the Lean side, only ever passed to
these primitives, which `Translate` recognizes by name. `unBData`'s Lean
body is a placeholder never inspected by the translator (it maps straight
to the real UPLC builtin of the same name) — but unlike `abort`
(`Poe.Prelude`), a
plain `axiom` doesn't work here: Lean's code generator refuses to compile
*any* reference to an axiom ("not supported by code generator"), which
would make every caller uncompilable. `opaque` is the fix — it has a real
(hidden, irrelevant) witness so callers still compile, while still being
irreducible enough that a call site survives to mono LCNF instead of
being unfolded away (checked directly: a `def`-based placeholder here
would risk the same silent-collapse bug `abort` had).

`Data` the *type* can't be `opaque` too, though (found by D0 rejecting
every function that mentions it): mono-phase type erasure
(`toLCNFType`/`Types.lean`) only recognizes a type as concrete if it
resolves to a real `inductive`; an `opaque` type isn't one, so it
collapses straight to `lcAny` regardless of whether anything is actually
dependent — a false positive indistinguishable, at the erased-type level,
from a genuine ghost-dependent violation. A real (if trivially
single-constructor) `inductive` avoids that entirely.

`unListData` alone doesn't work the way `unBData` does, though: checked
directly against `uplc` and found it returns UPLC's *native* builtin list
(`(con (list data) ...)`), not our SoP `constr`/`case` encoding of Lean's
`List` — `case` errors ("Attempted to apply a non-function") trying to
scrutinize it. `List`-typed LCNF looks structurally identical regardless
of which representation the *values* flowing through it actually use, so
the translator can't tell "this `List Data`-shaped `cases` should walk a
native list" from "this is an ordinary Lean `List`" generically. Rather
than build that (real, separate work), `decodeByteStringList` is a single
bespoke intrinsic, special-cased by name exactly like `abort`: `Translate`
recognizes this exact declaration and emits a hand-built loop over
`headList`/`tailList`/`nullList` (verified standalone against `uplc`
first) that builds an ordinary SoP `List ByteArray` as it goes, so
everything *downstream* of this one primitive is back in the regular
fragment. -/

namespace Poe.PlutusData

inductive Data where
  | mk

opaque unBData (_ : Data) : ByteArray := ByteArray.mk #[]

/-- Decodes a `Data`-encoded list of byte strings (`unListData` then
    `unBData` on each element) into an ordinary `List ByteArray`. See the
    module doc: `Translate` special-cases this exact name to a hand-built
    native-list loop, since `unListData`'s own output isn't something the
    generic `cases` translation can walk.

    `partial`/self-recursive, not `opaque := []`: found by dumping
    `_redArg` (the compiler's own argument-reduction pass, separate from
    `abort`'s inlining issue) and seeing the call site replaced outright
    with the literal `[]` — `opaque` blocks *definitional* unfolding, but
    apparently not this optimization, which can still see that the hidden
    witness always reduces to the same known constructor (`List.nil`)
    regardless of the argument, and drops the argument as irrelevant.
    `unBData` above doesn't trigger it (its result type isn't a small
    sum type the same way), confirmed by `validateOwnerData` actually
    distinguishing its two inputs. A genuinely divergent, self-recursive
    body has no knowable constructor to find, for the same reason `abort`
    needed one. -/
partial def decodeByteStringList (d : Data) : List ByteArray := decodeByteStringList d

end Poe.PlutusData
