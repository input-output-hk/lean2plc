/-!
# Minimal on-chain `Data` slice

Real Plutus Core `Data = Constr Integer [Data] | Map [(Data,Data)] | List
[Data] | I Integer | B ByteString` (verified against
`plutus-core/src/PlutusCore/Data.hs`) is how Datum/Redeemer/ScriptContext
actually arrive on-chain — not as `String`/`List String` the way
`Poe.Examples.HelloWorld` models them. Full `Data`/serialization support is
a stated PLAN.md non-goal for increment 1; this is deliberately just
`unBData`, the one primitive `Poe.Examples.DataDecoding` actually uses.

`Data` is never pattern-matched on the Lean side, only ever passed to
`unBData`, which `Translate`'s builtin table maps straight to the real
UPLC builtin of the same name. `unBData`'s Lean body is a placeholder
never inspected by the translator — but unlike `abort` (`Poe.Prelude`), a
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

No `unListData` here (`Poe.Uplc.Builtin` still has it, for whoever
extends this): checked directly against `uplc` and found it returns
UPLC's *native* builtin list (`(con (list data) ...)`), not our SoP
`constr`/`case` encoding of Lean's `List` — `case` errors
("Attempted to apply a non-function") trying to scrutinize it. Decoding a
`Data` list for real needs `headList`/`tailList`/`nullList` and a
translator that recognizes this specific representation instead of the
generic constructor-cases path; that's real, separate work, not part of
this minimal slice. -/

namespace Poe.PlutusData

inductive Data where
  | mk

opaque unBData (_ : Data) : ByteArray := ByteArray.mk #[]

end Poe.PlutusData
