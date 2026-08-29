import Poe.Examples.HelloWorld
import Poe.Translate
import Poe.TranslateTplc
import Poe.Oracle
import Poe.TplcOracle

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
    have heq : Decidable (message = "Hello, World!".toUTF8) :=
      decidable_of_iff (message == "Hello, World!".toUTF8) (Poe.Lib.DataDecoding.ByteArray.beq_iff_eq _ _)
    have hmem : Decidable (owner ∈ signatories) :=
      decidable_of_iff (elemBytes owner signatories) (elemBytes_iff _ _)
    show Decidable (message = "Hello, World!".toUTF8 ∧ owner ∈ signatories) from
      @instDecidableAnd _ _ heq hmem

def validatorEDecidable (ctx : Data) (wf : WellFormed ctx) : Unit :=
  match validatorBDecidable ctx wf with
  | isTrue _ => ()
  | isFalse _ => Poe.Prelude.abort ()

end Poe.Experiments.ValidatorDecidable
