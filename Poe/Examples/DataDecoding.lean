import Poe.Lint
import Poe.Oracle
import Poe.Prelude
import Poe.PlutusData

/-!
# `Data`-decoding, building up to a real `hello_world`

`validateOwnerData`/`validateSignerData` are the incremental steps that
got `unBData`/`decodeByteStringList` (see `Poe.PlutusData`) working —
kept around since they isolate the two primitives from each other (if a
future regression breaks list-decoding specifically, `validateOwnerData`
still passing says the fault isn't in `unBData` itself). Neither compares
against a literal `ByteArray`: that would need
`String.toUTF8`/`encodeUtf8`, which turned out to translate just fine
(a plain 1-arg builtin call, checked directly) — so `validateHelloWorld`,
below, is the real thing: Aiken's own `hello_world` template's shape
(redeemer message check + datum-owner-signed check), with real `Data`
throughout rather than `Poe.Examples.HelloWorld`'s `String` stand-ins.
-/

namespace Poe.Examples.DataDecoding

open Poe.PlutusData (Data unBData decodeByteStringList)

/-- Does the `Data`-encoded `owner` equal the `Data`-encoded
    `expectedOwner`? -/
def validateOwnerData (owner expectedOwner : Data) : Unit :=
  Poe.Prelude.check (unBData owner == unBData expectedOwner)

def elemBytes (x : ByteArray) : List ByteArray → Bool
  | []      => false
  | y :: ys => x == y || elemBytes x ys

/-- Does the `Data`-encoded `owner` appear in the `Data`-encoded
    `signatories`? -/
def validateSignerData (owner signatories : Data) : Unit :=
  Poe.Prelude.check (elemBytes (unBData owner) (decodeByteStringList signatories))

/-- Aiken's `hello_world` template, real `Data` throughout: the redeemer
    `message` must be exactly `"Hello, World!"`, and the datum's `owner`
    must be among the transaction's `signatories`. -/
def validateHelloWorld (owner message signatories : Data) : Unit :=
  Poe.Prelude.check
    (unBData message == "Hello, World!".toUTF8 &&
     elemBytes (unBData owner) (decodeByteStringList signatories))

#eval Poe.Lint.check ``validateOwnerData
#eval Poe.Lint.check ``elemBytes
#eval Poe.Lint.check ``validateSignerData
#eval Poe.Lint.check ``validateHelloWorld

def encodeBytes (s : String) : Poe.Uplc.Term := .const (.data (.b s.toUTF8))
def encodeByteList (ss : List String) : Poe.Uplc.Term :=
  .const (.data (.list (ss.map (fun s => .b s.toUTF8))))

/- Honest: same bytes. Dishonest: different bytes. -/
#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``validateOwnerData
    [([encodeBytes "alice", encodeBytes "alice"], .unit)]
  Poe.Oracle.runSuiteAborts ``validateOwnerData
    [[encodeBytes "alice", encodeBytes "mallory"]]

/- Honest: owner is among the signatories. Dishonest: owner is not. -/
#eval show Lean.CoreM Unit from do
  let signers := encodeByteList ["bob", "alice", "carol"]
  Poe.Oracle.runSuite ``validateSignerData
    [([encodeBytes "alice", signers], .unit)]
  Poe.Oracle.runSuiteAborts ``validateSignerData
    [[encodeBytes "mallory", signers]]

/- Honest: right message, owner signed. Dishonest: wrong message; right
   message but owner isn't a signatory. -/
#eval show Lean.CoreM Unit from do
  let signers := encodeByteList ["bob", "alice", "carol"]
  Poe.Oracle.runSuite ``validateHelloWorld
    [([encodeBytes "alice", encodeBytes "Hello, World!", signers], .unit)]
  Poe.Oracle.runSuiteAborts ``validateHelloWorld
    [ [encodeBytes "alice", encodeBytes "wrong message", signers]
    , [encodeBytes "mallory", encodeBytes "Hello, World!", signers]
    ]

end Poe.Examples.DataDecoding
