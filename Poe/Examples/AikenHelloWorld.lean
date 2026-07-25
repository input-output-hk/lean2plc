import Poe.Lint
import Poe.Oracle
import Poe.Prelude
import Poe.PlutusData
import Poe.Examples.DataDecoding

/-!
# Aiken's `hello_world`, with real `Data`

The Aiken `hello_world` template's shape (redeemer message check +
datum-owner-signed check), real `Data` throughout rather than
`Poe.Examples.HelloWorld`'s `String` stand-ins. Reuses
`elemBytes`/`encodeBytes`/`encodeByteList` from
`Poe.Examples.DataDecoding`, where `unBData`/`decodeByteStringList` were
built up and tested in isolation.
-/

namespace Poe.Examples.AikenHelloWorld

open Poe.PlutusData (Data unBData decodeByteStringList)
open Poe.Examples.DataDecoding (elemBytes encodeBytes encodeByteList)

/-- The redeemer `message` must be exactly `"Hello, World!"`, and the
    datum's `owner` must be among the transaction's `signatories`. -/
def validateHelloWorld (owner message signatories : Data) : Unit :=
  Poe.Prelude.check
    (unBData message == "Hello, World!".toUTF8 &&
     elemBytes (unBData owner) (decodeByteStringList signatories))

#eval Poe.Lint.check ``validateHelloWorld

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

end Poe.Examples.AikenHelloWorld
