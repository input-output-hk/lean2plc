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

/-!
## Shape-guarded accessors

The `_spec` axioms above only ever fire when a proof already knows `d`'s
*exact literal* shape (`isHonestScriptContext_correct` gets this for free
because it universally quantifies over `mkCtxData`'s own construction).
They say nothing at all — not "returns some field", not "the compiled
program aborts" — about `field0 d` for a `d` whose shape isn't already
pinned down that way, which is exactly the case a validator is actually
in when navigating a nested, attacker-supplied `Redeemer`/`Datum`
(`isHonestScriptContext`'s own `field1 redeemer`/`field0 (field0
maybeDatum)` calls have no such proof available at all right now).

`HasFieldAt` names the missing ghost precondition; `field0Safe` is
*total*, given a proof of it — nothing new compiles, the proof argument
erases and the emitted UPLC is the exact same `field0`/`unConstrData`
chain as before (`Translate` still special-cases the name `field0`
itself, reached through the wrapper's transparent body). What's gained is
purely proof-side: one reusable precondition per accessor instead of a
fresh literal-shape hypothesis manufactured at every call site, so a
validator can be proved correct about a `d` whose shape is only known
indirectly (derived from an earlier check), not just one built by a
`mk...Data`-style test helper.

The real payoff this sets up, not yet done: on real chain data nobody
*has* a `HasFieldAt d n` proof for free — a caller either derives one
from an earlier `Decidable`-checked shape test (and then knows
`field0Safe` matches its spec), or has no such proof and must fall
through to `Poe.Prelude.abort`/`poeError` instead of calling any
accessor at all. That's the shape a validator's dishonest-input path
*should* have, and currently doesn't for `isHonestScriptContext`'s nested
fields — see its own module for the gap this closes. -/

/-- Ghost-only (never computed on-chain, never appears in compiled code):
    `d` really is a `Constr` application with a field at index `n`. -/
def HasFieldAt (d : Data) (n : Nat) : Prop :=
  ∃ tag fields, d = .constr tag fields ∧ n < fields.length

def field0Safe (d : Data) (_ : HasFieldAt d 0) : Data := field0 d

theorem field0Safe_spec {d : Data} {tag : Nat} {fields : List Data}
    (heq : d = .constr tag fields) (hlt : 0 < fields.length) :
    field0Safe d ⟨tag, fields, heq, hlt⟩ = fields[0] := by
  subst heq
  cases fields with
  | nil => simp at hlt
  | cons f0 rest => exact field0_spec tag f0 rest

end Poe.PlutusData
