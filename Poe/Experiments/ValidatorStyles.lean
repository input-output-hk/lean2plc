import Poe.PlutusData
import Poe.Lib.DataDecoding
import Poe.Prelude
import Poe.Examples.HelloWorld
import Poe.Examples.HelloWorldCorrect
import Poe.Experiments.ValidatorDecidable
import Poe.Experiments.HelloWorldSubtype

/-!
# The validator styles, side by side — same business logic, different packaging.

Self-contained: every definition needed to *read* this file is restated
here, not just imported. The imports of the canonical originals above are
kept only to support the `example ... := rfl` (or, for the one theorem,
direct-reuse) checks below each style, which guard against silent drift —
nothing in the styles themselves relies on opening those modules.

For reference, the original this whole file is modeled on — Aiken's own
`hello_world` example (`aiken-lang/aiken`, `examples/hello_world/validators/hello_world.ak`):

```
use aiken/collection/list
use aiken/crypto.{VerificationKeyHash}
use cardano/transaction.{OutputReference, Transaction}

pub type Datum {
  owner: VerificationKeyHash,
}

pub type Redeemer {
  msg: ByteArray,
}

validator hello_world {
  spend(
    datum: Option<Datum>,
    redeemer: Redeemer,
    _: OutputReference,
    transaction: Transaction,
  ) {
    let must_say_hello = redeemer.msg == "Hello, World!"

    expect Some(Datum { owner }) = datum

    let must_be_signed = list.has(transaction.extra_signatories, owner)

    must_say_hello && must_be_signed
  }

  else(_) {
    fail
  }
}
```
-/

namespace Poe.Experiments.ValidatorStyles

open Poe.PlutusData (Data decodeByteStringList IsByteStringList)
open Poe.Lib.DataDecoding (elemBytes elemBytes_iff ByteArray.beq_iff_eq)

-- Shared shape predicates and decoders every style below builds on.
def RedeemerOk (redeemer : Data) : Prop :=
  match redeemer with
  | .constr _ [.b _] => True
  | _ => False

def decodeMessage : ∀ redeemer, RedeemerOk redeemer → ByteArray
  | .constr _ [.b msgBytes], _ => msgBytes

def TxInfoOk (txInfo : Data) : Prop :=
  match txInfo with
  | .constr _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: sigListData :: _) => IsByteStringList sigListData
  | _ => False

def decodeSignatories : ∀ txInfo, TxInfoOk txInfo → List ByteArray
  | .constr _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: sigListData :: _), h => decodeByteStringList sigListData h

-- Tag `1` (not a wildcard): real ScriptInfo's SpendingScript is index 1
-- (MintingScript=0, SpendingScript=1, ...), and CertifyingScript/
-- ProposingScript also have exactly two fields — an unchecked tag here
-- would accept a certifying/proposing-purpose ScriptContext as a spending
-- one. Inner tag `0` is Just (PlutusTx's Maybe is indexed
-- [('Just, 0), ('Nothing, 1)], not declaration order), then `0` again for
-- Datum's own single-constructor record. All confirmed directly against
-- PlutusLedgerApi.V3.Contexts's own makeIsDataSchemaIndexed calls.
def ScriptInfoOk (scriptInfo : Data) : Prop :=
  match scriptInfo with
  | .constr 1 [_, .constr 0 [.constr 0 [.b _]]] => True
  | _ => False

def decodeOwner : ∀ scriptInfo, ScriptInfoOk scriptInfo → ByteArray
  | .constr 1 [_, .constr 0 [.constr 0 [.b ownerBytes]]], _ => ownerBytes

def WellFormed (ctx : Data) : Prop :=
  match ctx with
  | .constr 0 [txInfo, redeemer, scriptInfo] => TxInfoOk txInfo ∧ RedeemerOk redeemer ∧ ScriptInfoOk scriptInfo
  | _ => False

example : WellFormed = Poe.Examples.HelloWorld.WellFormed := rfl

-- 1. Plain `Bool`, precondition curried in as a separate argument.
def style1 (ctx : Data) (wf : WellFormed ctx) : Bool :=
  match ctx, wf with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    let message := decodeMessage redeemer wfRedeemer
    let signatories := decodeSignatories txInfo wfTxInfo
    let owner := decodeOwner scriptInfo wfScriptInfo
    message == "Hello, World!".toUTF8 && elemBytes owner signatories

example : style1 = Poe.Examples.HelloWorld.validatorB := rfl

-- The deployable shape every real validator actually needs: `()` on success, `error` otherwise
-- (a ledger never compares a script's result against `True` — it just needs the script to not
-- throw). `Poe.Prelude.check`/`abort` are genuine shared infrastructure (like `Data`/`ByteArray`
-- above), not "a style" of their own, so they stay a library import rather than being restated.
def style1E (ctx : Data) (wf : WellFormed ctx) : Unit := Poe.Prelude.check (style1 ctx wf)

example : style1E = Poe.Examples.HelloWorld.validatorE := rfl

-- 2. Plain `Bool`, correctness proven afterward as a separate theorem (two maintained artifacts).
def mkCtxData (txInfo : Data) (messageBytes owner : ByteArray) : Data :=
  .constr 0
    [ txInfo
    , .constr 0 [.b messageBytes]
    , .constr 1 [.b (ByteArray.mk #[]), .constr 0 [.constr 0 [.b owner]]] ]

-- Proved by direct reuse of the canonical theorem, not reproved from scratch — so if that
-- theorem's own proof ever breaks, this restatement fails to compile too, same drift guard as
-- every other style's `rfl` check.
theorem style1_correct
    (txInfo : Data) (signatories : List ByteArray) (h : TxInfoOk txInfo)
    (hsig : decodeSignatories txInfo h = signatories)
    (messageBytes owner : ByteArray) :
    style1 (mkCtxData txInfo messageBytes owner) ⟨h, trivial, trivial⟩ = true ↔
      messageBytes = "Hello, World!".toUTF8 ∧ owner ∈ signatories :=
  Poe.Examples.HelloWorld.validatorB_correct txInfo signatories h hsig messageBytes owner

-- 3. `Decidable`-valued — producing `isTrue`/`isFalse` forces a proof at construction time.
-- (Written as plain function application, not `≟`/`×-dec` infix notation — that notation is
-- already declared globally by `Poe.Experiments.ValidatorDecidable`, and redeclaring it here
-- for these local synonyms would just be ambiguous, not self-contained.)
def byteArrayDecEq (x y : ByteArray) : Decidable (x = y) :=
  decidable_of_iff (x == y) (ByteArray.beq_iff_eq x y)

def elemDecidable (a : ByteArray) (l : List ByteArray) : Decidable (a ∈ l) :=
  decidable_of_iff (elemBytes a l) (elemBytes_iff a l)

def decidableAnd {P Q : Prop} : Decidable P → Decidable Q → Decidable (P ∧ Q)
  | isTrue hp, isTrue hq => isTrue ⟨hp, hq⟩
  | isTrue _, isFalse hq => isFalse (hq ∘ And.right)
  | isFalse hp, _ => isFalse (hp ∘ And.left)

def Accepted (ctx : Data) (wf : WellFormed ctx) : Prop :=
  match ctx, wf with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    decodeMessage redeemer wfRedeemer = "Hello, World!".toUTF8 ∧
      decodeOwner scriptInfo wfScriptInfo ∈ decodeSignatories txInfo wfTxInfo

example : @Accepted = Poe.Experiments.ValidatorDecidable.Accepted := rfl

def style3 (ctx : Data) (wf : WellFormed ctx) : Decidable (Accepted ctx wf) :=
  match ctx, wf with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    let message := decodeMessage redeemer wfRedeemer
    let signatories := decodeSignatories txInfo wfTxInfo
    let owner := decodeOwner scriptInfo wfScriptInfo
    -- reads, with the notation this file doesn't redeclare, as:
    --   (message ≟ "Hello, World!".toUTF8) ×-dec elemDecidable owner signatories
    decidableAnd (byteArrayDecEq message "Hello, World!".toUTF8) (elemDecidable owner signatories)

example : style3 = Poe.Experiments.ValidatorDecidable.validatorBDecidable := rfl

def checkDecidable {P : Prop} : Decidable P → Unit
  | isTrue _ => ()
  | isFalse _ => Poe.Prelude.abort ()

def style3E (ctx : Data) (wf : WellFormed ctx) : Unit := checkDecidable (style3 ctx wf)

example : style3E = Poe.Experiments.ValidatorDecidable.validatorEDecidable := rfl

-- 4. `Subtype`-bundled precondition — `ctx`/`wf` packaged into one argument instead of curried.
def style4 (v : {ctx : Data // WellFormed ctx}) : Bool :=
  match v.1, v.2 with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    let message := decodeMessage redeemer wfRedeemer
    let signatories := decodeSignatories txInfo wfTxInfo
    let owner := decodeOwner scriptInfo wfScriptInfo
    message == "Hello, World!".toUTF8 && elemBytes owner signatories

example : style4 = Poe.Experiments.HelloWorldSubtype.validatorBSubtype := rfl

-- No canonical original exists for this one to check against — `HelloWorldSubtype.lean` never
-- wrote a check-wrapped version of `validatorBSubtype`, so this is new, not a restatement.
def style4E (v : {ctx : Data // WellFormed ctx}) : Unit := Poe.Prelude.check (style4 v)

-- 5. `Subtype`-bundled pre *and* post condition — the full Hoare-triple packaging.
def style5 (v : {ctx : Data // WellFormed ctx}) : {b : Bool // b = true ↔ Accepted v.1 v.2} :=
  match v.1, v.2 with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨wfTxInfo, wfRedeemer, wfScriptInfo⟩ =>
    let message := decodeMessage redeemer wfRedeemer
    let signatories := decodeSignatories txInfo wfTxInfo
    let owner := decodeOwner scriptInfo wfScriptInfo
    ⟨message == "Hello, World!".toUTF8 && elemBytes owner signatories, by
      simp only [Accepted, message, signatories, owner]
      simp [ByteArray.beq_iff_eq, elemBytes_iff]⟩

example : style5 = Poe.Experiments.HelloWorldSubtype.validatorBSubtypePost := rfl

-- Same as `style4E`: new, not a restatement of an existing artifact — takes `.val` since
-- `style5`'s postcondition proof is exactly as `Prop`-erased as `Accepted` itself.
def style5E (v : {ctx : Data // WellFormed ctx}) : Unit := Poe.Prelude.check (style5 v).val

end Poe.Experiments.ValidatorStyles
