import Poe.PlutusData
import Poe.Prelude
import Poe.Examples.DataDecoding
import Poe.Examples.HelloWorld

/-!
# The "ideal validator": reasoning about a genuinely partial function

`Poe.Examples.HelloWorld.validateScriptContext` is, informally, a partial
function on `Data` — it's only supposed to "succeed" on the honest
subset, exactly the way `Poe.Examples.First.head : List Int → Int` is
only supposed to succeed on nonempty lists. That parallel is real, not
decorative: both are total-given-a-proof, partial-in-practice, and the
resolution is identical in shape.

The one thing that does *not* carry over: which artifact gets deployed.
`head`'s proof-carrying form is directly useful because real Lean callers
inside the same closed program can supply `xs ≠ []` for values they
already have (literals, or facts an earlier check established). Nothing
can supply an equivalent honesty proof to a *deployed* validator, because
its argument is a real, adversarial transaction nobody has submitted yet
— discovering whether it's honest is the validator's whole job, not
something knowable in advance. So the deployed artifact stays exactly
`validateScriptContext` (compute the `Bool`, `check`/`abort` on it) —
unchanged, still the only thing this file's proofs ever get checked
against.

This file's `idealValidator` is a pure reasoning device: never lint-
checked, never translated, never runs anywhere. It exists to make the
"partial function, total given a proof" parallel with `head` completely
literal — including invoking it on a concrete, known-honest value with
a real proof, the exact same move as `head [3, 99] (by decide)`. -/

namespace Poe.Examples.IdealValidator

open Poe.PlutusData (Data unBData decodeByteStringList constrTag field0 field1 field2 field8)
open Poe.PlutusData (unBData_spec decodeByteStringList_spec constrTag_spec
  field0_spec field1_spec field2_spec field8_spec)
open Poe.Examples.DataDecoding (elemBytes elemBytes_iff ByteArray.beq_iff_eq)
open Poe.Examples.HelloWorld (isHonestScriptContext isHonestScriptContext_correct mkCtxData)

/-- The same hypotheses `isHonestScriptContext_correct` already needs to
    characterize acceptance — named here as what `idealValidator` requires,
    not reimplemented. `txInfo`/`messageBytes`/`owner` stay explicit
    parameters (matching `mkCtxData`) rather than an existential over
    `ctx`'s shape — asking "does some decomposition of `ctx` exist" is a
    much heavier proof obligation than "here are the pieces, `ctx` is
    built from them", for no benefit here. -/
def idealValidator
    (txInfo : Data) (signatories : List ByteArray)
    (_hsig : decodeByteStringList (field8 txInfo) = signatories)
    (messageBytes owner : ByteArray)
    (_hmsg : messageBytes = "Hello, World!".toUTF8)
    (_hsigned : owner ∈ signatories) :
    Unit :=
  ()

/-- The link back to reality: whenever `idealValidator`'s hypotheses hold,
    the *real*, compiled, deployed `isHonestScriptContext` — the thing
    that actually runs, computing everything against unknown data — also
    accepts. `idealValidator` isn't reasoning about a fiction; it's
    reasoning about exactly the case the deployed program accepts, just
    packaged so the acceptance condition can be handed around as a
    hypothesis instead of restated as a conjunction each time. -/
theorem idealValidator_reflects_real
    (txInfo : Data) (signatories : List ByteArray)
    (hsig : decodeByteStringList (field8 txInfo) = signatories)
    (messageBytes owner : ByteArray)
    (hmsg : messageBytes = "Hello, World!".toUTF8)
    (hsigned : owner ∈ signatories) :
    isHonestScriptContext (mkCtxData txInfo messageBytes owner) = true := by
  rw [isHonestScriptContext_correct txInfo signatories hsig messageBytes owner]
  exact ⟨hmsg, hsigned⟩

/-! ## Invoking it on a concrete, known-honest value

Exactly `head [3, 99] (by decide)`'s move: a specific, fully-known value,
with a real proof for that specific value, not a general claim about
arbitrary ones. The one thing worth noticing here that `head` didn't
have to contend with: `field8`/`decodeByteStringList` are opaque, so
`by decide`/`by native_decide` can't touch `_hsig` at all — it isn't a
computation that happens to be provable, it's a fact only the `_spec`
axioms can establish, for a `txInfo` shaped to match their exact
pattern. -/

private def literalSignatories : List ByteArray := ["bob".toUTF8, "alice".toUTF8]

/-- Nine `Data.b`/`Data.list` fields: the first eight are filler, the
    ninth (index 8) is the signatories list `field8_spec` needs to match
    on the `f0 :: f1 :: ... :: f8 :: rest` pattern exactly. -/
private def literalTxInfo : Data :=
  .constr 0
    [ .b (ByteArray.mk #[]), .b (ByteArray.mk #[]), .b (ByteArray.mk #[]), .b (ByteArray.mk #[])
    , .b (ByteArray.mk #[]), .b (ByteArray.mk #[]), .b (ByteArray.mk #[]), .b (ByteArray.mk #[])
    , .list (literalSignatories.map .b) ]

private theorem literalTxInfo_hsig :
    decodeByteStringList (field8 literalTxInfo) = literalSignatories := by
  simp only [literalTxInfo, field8_spec, decodeByteStringList_spec]

/-- The concrete invocation: a known, honest `ScriptContext` really does
    make `idealValidator`'s hypotheses satisfiable, and `isHonestScriptContext`
    — the real, compiled function — really does accept it. -/
theorem concreteHonestCase :
    isHonestScriptContext
      (mkCtxData literalTxInfo "Hello, World!".toUTF8 "alice".toUTF8) = true :=
  idealValidator_reflects_real literalTxInfo literalSignatories literalTxInfo_hsig
    "Hello, World!".toUTF8 "alice".toUTF8 rfl (by simp [literalSignatories])

end Poe.Examples.IdealValidator
