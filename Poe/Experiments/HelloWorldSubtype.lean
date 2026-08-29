import Poe.Examples.HelloWorld
import Poe.Experiments.ValidatorDecidable
import Poe.Translate
import Poe.TranslateTplc

/-!
Scratch: a `Subtype`-bundled variant of `Poe.Examples.HelloWorld.validatorB`
— `(v : {ctx : Data // WellFormed ctx})` instead of the flagship's curried
`(ctx : Data) (wf : WellFormed ctx)`. Same body, same `WellFormed`/decoder
helpers, only the packaging differs. Not a replacement for the flagship
(that curried style was a deliberate earlier choice, not an oversight) —
just checking, by direct analogy to `vHead`, whether today's `Subtype`
fix in `Poe.TranslateTplc` really does carry over to this shape too.
-/

namespace Poe.Experiments.HelloWorldSubtype

open Poe.PlutusData (Data)
open Poe.Examples.HelloWorld (WellFormed decodeMessage decodeSignatories decodeOwner)
open Poe.Lib.DataDecoding (elemBytes elemBytes_iff ByteArray.beq_iff_eq)
open Poe.Experiments.ValidatorDecidable (Accepted)

def validatorBSubtype (v : {ctx : Data // WellFormed ctx}) : Bool :=
  match v.1, v.2 with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    let message := decodeMessage redeemer wfRedeemer
    let signatories := decodeSignatories txInfo wfTxInfo
    let owner := decodeOwner scriptInfo wfScriptInfo
    message == "Hello, World!".toUTF8 && elemBytes owner signatories

/-- Precondition bundled with the *input* (`WellFormed` inside `v`, same
    as `validatorBSubtype`), *and* the postcondition bundled with the
    *output* (`b = true ↔ Accepted v.1 v.2`, reusing `Accepted` rather
    than restating the same proposition again) — the full Hoare-triple
    packaging, both directions, instead of a separate correctness theorem
    proven afterward (`HelloWorldCorrect.validatorB_correct`). -/
def validatorBSubtypePost (v : {ctx : Data // WellFormed ctx}) :
    {b : Bool // b = true ↔ Accepted v.1 v.2} :=
  match v.1, v.2 with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    let message := decodeMessage redeemer wfRedeemer
    let signatories := decodeSignatories txInfo wfTxInfo
    let owner := decodeOwner scriptInfo wfScriptInfo
    ⟨message == "Hello, World!".toUTF8 && elemBytes owner signatories, by
      simp only [Accepted, message, signatories, owner]
      simp [ByteArray.beq_iff_eq, elemBytes_iff]⟩

end Poe.Experiments.HelloWorldSubtype
