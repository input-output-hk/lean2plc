import Poe.Lint
import Poe.Oracle
import Poe.Prelude
import Poe.PlutusData

/-!
# Minimal `Data`-decoding example

Demonstrates `unBData` translating end to end — not a redo of
`Poe.Examples.HelloWorld`'s logic, kept deliberately separate and
simpler: two `Data`-encoded `ByteArray`s in, compared for equality. No
list decoding here (see `Poe.PlutusData`'s module doc for why
`unListData` isn't wired up yet — its output is UPLC's native builtin
list, incompatible with our `case`/`constr` encoding of Lean's `List`).
Also never constructs a `ByteArray` literal in translated source: that
would need `String.toUTF8`/array-literal machinery this PoC doesn't
support translating, so both sides of the comparison are `Data`-decoded
inputs rather than one being a source-level constant.
-/

namespace Poe.Examples.DataDecoding

open Poe.PlutusData (Data unBData)

/-- Does the `Data`-encoded `owner` equal the `Data`-encoded
    `expectedOwner`? -/
def validateOwnerData (owner expectedOwner : Data) : Unit :=
  Poe.Prelude.check (unBData owner == unBData expectedOwner)

#eval Poe.Lint.check ``validateOwnerData

/- Honest: same bytes. Dishonest: different bytes. Encodes real Data
   literals ((con data (B ...))) as the arguments, not the plain
   ByteArray terms Poe.Oracle uses elsewhere. -/
#eval show Lean.CoreM Unit from do
  let encodeBytes (s : String) : Poe.Uplc.Term := .const (.data (.b s.toUTF8))
  Poe.Oracle.runSuite ``validateOwnerData
    [([encodeBytes "alice", encodeBytes "alice"], .unit)]
  Poe.Oracle.runSuiteAborts ``validateOwnerData
    [[encodeBytes "alice", encodeBytes "mallory"]]

end Poe.Examples.DataDecoding
