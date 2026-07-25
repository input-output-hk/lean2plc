/-!
# Minimal on-chain `Data` slice

Real Plutus Core `Data = Constr Integer [Data] | Map [(Data,Data)] | List
[Data] | I Integer | B ByteString` (verified against
`plutus-core/src/PlutusCore/Data.hs`) is how Datum/Redeemer/ScriptContext
actually arrive on-chain — not as `String`/`List String` the way
`Poe.Examples.HelloWorldString` models them. `Map` is dropped (not needed
by any Poe example); the rest is a real inductive, not the earlier
single-constructor placeholder, specifically so proofs can pattern-match
on shape (see below).

`unBData`/`decodeByteStringList`/`constrTag`/`field0`/`field1`/`field2`/
`field8` all stay exactly as before — self-recursive placeholders,
special-cased *by name* in `Translate`, which maps each straight to the
real UPLC builtin/hand-built loop rather than compiling whatever's
written here (see each one's own comment). That's deliberately
*unchanged*: their compiled behaviour is already proven safe (D2's oracle
suites), and nothing about proofs requires touching it.

What changes is that these placeholders are no longer *totally* opaque:
the `_spec` axioms below say what each one actually computes when handed
a value built from `Data`'s real constructors, which is the missing
ingredient for saying anything about a validator that calls them —
without this, e.g. `field0 d` only satisfies the tautology `field0 d =
field0 d`, and no proof can relate it to what `d` actually contains. The
axioms are the honest trust boundary: `Translate` emits UPLC that is
*claimed* to match this semantics (and D2's oracle empirically exercises
that claim against the real `uplc` binary), but proving the translator
itself correct is out of scope (PLAN.md non-goal) — proofs built on these
axioms are conditional on that claim, same as any verified-source-level
reasoning about a trusted compiler backend. -/

namespace Poe.PlutusData

inductive Data where
  | constr : Nat → List Data → Data
  | list   : List Data → Data
  | b      : ByteArray → Data
  | i      : Int → Data

/-- Maps straight to the real UPLC builtin of the same name (see module
    doc: `opaque`, not `axiom`, so callers still compile). -/
opaque unBData (_ : Data) : ByteArray := ByteArray.mk #[]

axiom unBData_spec (bs : ByteArray) : unBData (.b bs) = bs

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

axiom decodeByteStringList_spec (bss : List ByteArray) :
    decodeByteStringList (.list (bss.map .b)) = bss

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

All still self-recursive, not `opaque`/ordinary `def`: same "the compiler
can find a knowable constructor, or just inline a small definition
outright" risk `decodeByteStringList` hit — an ordinary `def` pattern-
matching on `Data`'s real constructors is exactly the kind of small
function Lean's compiler tends to inline at call sites, which would make
the named call disappear from a caller's mono LCNF before `Translate`
ever gets to special-case it. The `_spec` axioms below carry the real
semantics instead, entirely separately from what's actually compiled. -/

partial def constrTag (d : Data) : Int := constrTag d
partial def field0 (d : Data) : Data := field0 d
partial def field1 (d : Data) : Data := field1 d
partial def field2 (d : Data) : Data := field2 d
partial def field8 (d : Data) : Data := field8 d

axiom constrTag_spec (tag : Nat) (fields : List Data) :
    constrTag (.constr tag fields) = Int.ofNat tag

axiom field0_spec (tag : Nat) (f0 : Data) (rest : List Data) :
    field0 (.constr tag (f0 :: rest)) = f0

axiom field1_spec (tag : Nat) (f0 f1 : Data) (rest : List Data) :
    field1 (.constr tag (f0 :: f1 :: rest)) = f1

axiom field2_spec (tag : Nat) (f0 f1 f2 : Data) (rest : List Data) :
    field2 (.constr tag (f0 :: f1 :: f2 :: rest)) = f2

axiom field8_spec (tag : Nat) (f0 f1 f2 f3 f4 f5 f6 f7 f8 : Data) (rest : List Data) :
    field8 (.constr tag (f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: rest)) = f8

end Poe.PlutusData
