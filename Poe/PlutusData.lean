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
`field8` all stay self-recursive placeholders, special-cased *by name* in
`Translate`, which maps each straight to the real UPLC builtin/hand-built
loop rather than compiling whatever's written here (see each one's own
comment). That's deliberately *unchanged*: their compiled behaviour is
already proven safe (D2's oracle suites), and nothing about proofs
requires touching it.

Real Plutus `un*` builtins (`unConstrData`, `unBData`, `unListData`, ...)
are *total as CEK steps but partial on their intended domain* — applying
`unConstrData` to a `Data` value that isn't actually a `Constr` doesn't
type-error (there's no such thing; `data` is one universal type), it
raises a fatal, uncatchable evaluation failure. Every accessor below
takes an explicit ghost precondition asserting the shape it needs,
exactly the way `Poe.Examples.First.divide` already takes `hy : y ≠ 0`
for division by zero: the precondition is `Prop`-sorted, so it's erased
by the *already-existing* Kreisel/proof-irrelevance machinery — nothing
new needs to compile, `Translate`'s name-based special-casing of the
underlying builtin is untouched, and a caller either has the proof (an
earlier `Decidable`-checked shape test, or literal knowledge of how the
value was built) or must fall through to `Poe.Prelude.abort`/`poeError`
instead of calling the accessor at all. That's the honest trust boundary
this file is about: `_spec` axioms below say what each accessor computes
*given* its precondition — proofs built on them are conditional on
`Translate` actually implementing this semantics (D2's oracle empirically
exercises that claim against the real `uplc` binary; proving the
translator itself correct is out of scope, a PLAN.md non-goal). -/

namespace Poe.PlutusData

inductive Data where
  | constr : Nat → List Data → Data
  | list   : List Data → Data
  | b      : ByteArray → Data
  | i      : Int → Data

/-- Ghost-only (never computed on-chain, never appears in compiled code):
    `d` really is a `Constr` application, of any arity. -/
def IsConstr (d : Data) : Prop := ∃ tag fields, d = .constr tag fields

/-- Ghost-only: `d` really is a `Constr` application with a field at
    index `n`. -/
def HasFieldAt (d : Data) (n : Nat) : Prop :=
  ∃ tag fields, d = .constr tag fields ∧ n < fields.length

/-- Ghost-only: `d` really is a `B` (bytestring) value. -/
def IsB (d : Data) : Prop := ∃ b, d = .b b

/-- Ghost-only: `d` really is a `List` of `B` values throughout — exactly
    what `decodeByteStringList` needs to decode every element. -/
def IsByteStringList (d : Data) : Prop := ∃ bss : List ByteArray, d = .list (bss.map .b)

/-- Maps straight to the real UPLC builtin of the same name (see module
    doc: `opaque`, not `axiom`, so callers still compile). -/
opaque unBData (d : Data) (_ : IsB d) : ByteArray := ByteArray.mk #[]

axiom unBData_spec (b : ByteArray) (h : IsB (.b b)) : unBData (.b b) h = b

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
partial def decodeByteStringList (d : Data) (h : IsByteStringList d) : List ByteArray :=
  decodeByteStringList d h

axiom decodeByteStringList_spec (bss : List ByteArray) (h : IsByteStringList (.list (bss.map .b))) :
    decodeByteStringList (.list (bss.map .b)) h = bss

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

partial def constrTag (d : Data) (h : IsConstr d) : Int := constrTag d h
partial def field0 (d : Data) (h : HasFieldAt d 0) : Data := field0 d h
partial def field1 (d : Data) (h : HasFieldAt d 1) : Data := field1 d h
partial def field2 (d : Data) (h : HasFieldAt d 2) : Data := field2 d h
partial def field8 (d : Data) (h : HasFieldAt d 8) : Data := field8 d h

axiom constrTag_spec (tag : Nat) (fields : List Data) (h : IsConstr (.constr tag fields)) :
    constrTag (.constr tag fields) h = Int.ofNat tag

axiom field0_spec (tag : Nat) (f0 : Data) (rest : List Data)
    (h : HasFieldAt (.constr tag (f0 :: rest)) 0) :
    field0 (.constr tag (f0 :: rest)) h = f0

axiom field1_spec (tag : Nat) (f0 f1 : Data) (rest : List Data)
    (h : HasFieldAt (.constr tag (f0 :: f1 :: rest)) 1) :
    field1 (.constr tag (f0 :: f1 :: rest)) h = f1

axiom field2_spec (tag : Nat) (f0 f1 f2 : Data) (rest : List Data)
    (h : HasFieldAt (.constr tag (f0 :: f1 :: f2 :: rest)) 2) :
    field2 (.constr tag (f0 :: f1 :: f2 :: rest)) h = f2

axiom field8_spec (tag : Nat) (f0 f1 f2 f3 f4 f5 f6 f7 f8 : Data) (rest : List Data)
    (h : HasFieldAt (.constr tag (f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: rest)) 8) :
    field8 (.constr tag (f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: rest)) h = f8

/-- `HasFieldAt` at any index already witnesses the weaker `IsConstr` —
    lets a caller pass one `HasFieldAt d n` hypothesis and get both
    `field n d` and `constrTag d`'s preconditions from it, instead of
    needing two separate ones for the same value. -/
theorem HasFieldAt.isConstr {d : Data} {n : Nat} (h : HasFieldAt d n) : IsConstr d :=
  let ⟨tag, fields, heq, _⟩ := h
  ⟨tag, fields, heq⟩

end Poe.PlutusData
