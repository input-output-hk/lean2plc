import Poe.Lint
import Poe.Oracle
import Poe.Prelude
import Poe.PlutusData

/-!
# Minimal `Data`-decoding example

The on-chain-shaped counterpart of `Poe.Examples.HelloWorld`'s `elem`:
`unBData` and `decodeByteStringList` (see `Poe.PlutusData`) translating
end to end, real `Data` values in, not `Poe.Oracle`'s plain
`ByteArray`/`List` terms. Never constructs a `ByteArray` literal in
translated source (e.g. for a hard-coded expected value): that would need
`String.toUTF8`/array-literal machinery this PoC doesn't support
translating, so every comparison is between two `Data`-decoded inputs
rather than one being a source-level constant.
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

#eval Poe.Lint.check ``validateOwnerData
#eval Poe.Lint.check ``elemBytes
#eval Poe.Lint.check ``validateSignerData

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

end Poe.Examples.DataDecoding
