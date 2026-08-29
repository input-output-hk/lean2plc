import Poe.Examples.HelloWorld
import Poe.Translate
import Poe.TranslateTplc

/-!
Scratch: `validatorB`, `Decidable`-valued instead of `Bool`-valued. Not a
simplification of the business logic — the `Prop` being decided still has
to say exactly what `HelloWorldCorrect.validatorB_correct` says, so the
decision work is the same either way. What changes: today, `validatorB :
Bool` and `validatorB_correct : validatorB ... = true ↔ P` are two
separate artifacts that could in principle drift apart; here, returning
`isTrue`/`isFalse` at all is only possible by actually producing a proof
of `P`/`¬P`, so "the answer matches the spec" is enforced by the type
checker at the point of construction, not proved afterward as a separate
theorem. `Decidable`'s own erasure (already exercised earlier today,
for the tag check inside `validatorB`'s own `.constr 0 [...]` match) means
this should still compile to exactly the same boolean-shaped runtime
check either backend already does for `validatorB` itself.
-/

namespace Poe.Experiments.ValidatorDecidable

open Poe.PlutusData (Data)
open Poe.Examples.HelloWorld (WellFormed decodeMessage decodeSignatories decodeOwner)
open Poe.Lib.DataDecoding (elemBytes elemBytes_iff)

/-- Agda-style `_≟_`: a plain, named function lifting a boolean test to a
    `Decidable` answer, called directly at the use site — not a global
    typeclass instance found by search (no wider scope than the call
    site itself, unlike registering `DecidableEq ByteArray`). -/
def byteArrayDecEq (x y : ByteArray) : Decidable (x = y) :=
  decidable_of_iff (x == y) (Poe.Lib.DataDecoding.ByteArray.beq_iff_eq x y)

@[inherit_doc byteArrayDecEq] infix:50 " ≟ " => byteArrayDecEq

/-- Same idea, for list membership instead of equality. -/
def elemDecidable (a : ByteArray) (l : List ByteArray) : Decidable (a ∈ l) :=
  decidable_of_iff (elemBytes a l) (elemBytes_iff a l)

/-- Agda's `_×-dec_`: lift `∧` to `Decidable`, hand-written rather than
    borrowed from `instDecidableAnd`'s own typeclass machinery (even
    called explicitly via `@`, that's still routing through instance
    infrastructure for what's really just a 4-case match). -/
def decidableAnd {P Q : Prop} : Decidable P → Decidable Q → Decidable (P ∧ Q)
  | isTrue hp, isTrue hq => isTrue ⟨hp, hq⟩
  | isTrue _, isFalse hq => isFalse (hq ∘ And.right)
  | isFalse hp, _ => isFalse (hp ∘ And.left)

@[inherit_doc decidableAnd] infixr:35 " ×-dec " => decidableAnd

/-- Same role as `Poe.Prelude.check`, for a `Decidable`-valued answer
    instead of a `Bool` one: `isTrue` succeeds, `isFalse` aborts. -/
def checkDecidable {P : Prop} : Decidable P → Unit
  | isTrue _ => ()
  | isFalse _ => Poe.Prelude.abort ()

/-- The proposition `validatorB`'s `Bool` answer is only ever a stand-in
    for — same content as `HelloWorldCorrect.validatorB_correct`'s right
    side, just given a name here instead of stated as a theorem after
    the fact. -/
def Accepted (ctx : Data) (wf : WellFormed ctx) : Prop :=
  match ctx, wf with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    decodeMessage redeemer wfRedeemer = "Hello, World!".toUTF8 ∧
      decodeOwner scriptInfo wfScriptInfo ∈ decodeSignatories txInfo wfTxInfo

def validatorBDecidable (ctx : Data) (wf : WellFormed ctx) : Decidable (Accepted ctx wf) :=
  match ctx, wf with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    let message := decodeMessage redeemer wfRedeemer
    let signatories := decodeSignatories txInfo wfTxInfo
    let owner := decodeOwner scriptInfo wfScriptInfo
    (message ≟ "Hello, World!".toUTF8) ×-dec elemDecidable owner signatories

def validatorEDecidable (ctx : Data) (wf : WellFormed ctx) : Unit :=
  checkDecidable (validatorBDecidable ctx wf)

end Poe.Experiments.ValidatorDecidable
