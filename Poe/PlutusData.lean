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
`List`. `List`-typed LCNF looks structurally identical regardless of which
representation the *values* flowing through it actually use, so the
translator can't tell "this `List Data`-shaped `cases` should walk a
native list" from "this is an ordinary Lean `List`" generically. Rather
than build that (real, separate work), `decodeByteStringList` is a single
bespoke intrinsic, special-cased by name exactly like `abort`: `Translate`
recognizes this exact declaration and emits a hand-built loop using
UPLC's `case` directly on the native list (verified standalone against
`uplc`: a native-list scrutinee takes a 2-argument cons lambda first, a
0-argument nil term second — no `headList`/`tailList`/`nullList` needed)
that builds an ordinary SoP `List ByteArray` as it goes, so everything
*downstream* of this one primitive is back in the regular fragment. -/

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

/-!
## Generic `Data`-record accessors

Real records (`ScriptContext`, `TxInfo`, a user's own `Datum`/`Redeemer`)
are all just `Constr tag [field0, field1, ...]` at the `Data` level —
verified against `plutus-ledger-api` (`makeIsDataSchemaIndexed` always
tags single-constructor records 0; `Maybe`'s `Just`/`Nothing` are
specifically 0/1, the opposite of the "obvious" guess). These accessors
are purely positional, so the same `field0` works on any of them; `field8`
exists only because `TxInfo.txInfoSignatories` sits at index 8 of the
real 16-field record. `Translate` special-cases all five names directly
to `unConstrData`/`fstPair`/`sndPair`/`headList`/`tailList` chains
(verified standalone against `uplc` first, including a nested `Constr`).
A `case`-based version (mirroring `decodeByteStringList`'s loop) was
tried too, but measured *larger* for these: unlike that loop, which
reuses one body via the fixpoint combinator, these accessors unroll a
fresh `case` per field index walked, and each one's extra `(lam h (lam t
...)) (error)` wrapper costs more than the plain builtin chain it would
replace — see `Poe.Translate`'s doc comment on `fieldAtTerm` for the
measurement.

All return `Data`, a single-constructor type — same "the compiler can
still find a knowable constructor" risk `decodeByteStringList` hit, so
all five need the same self-recursive treatment, not `opaque`. -/

partial def constrTag (d : Data) : Int := constrTag d
partial def field0 (d : Data) : Data := field0 d
partial def field1 (d : Data) : Data := field1 d
partial def field2 (d : Data) : Data := field2 d
partial def field8 (d : Data) : Data := field8 d

end Poe.PlutusData
