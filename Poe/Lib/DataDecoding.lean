import Poe.Lint
import Poe.Oracle
import Poe.Prelude
import Poe.PlutusData

/-!
# `Data`-decoding test utilities

`validateOwnerData`/`validateSignerData` are the incremental steps that
got `unBData`/`decodeByteStringList` (see `Poe.PlutusData`) working —
kept around since they isolate the two primitives from each other (if a
future regression breaks list-decoding specifically, `validateOwnerData`
still passing says the fault isn't in `unBData` itself). `elemBytes`/
`elemBytes_iff`/`ByteArray.beq_iff_eq` are genuinely shared library code,
not example-specific — used by `Poe.Examples.HelloWorld`'s own
correctness reasoning, which is why this file lives under `Poe.Lib`
rather than `Poe.Examples`.
-/

namespace Poe.Lib.DataDecoding

open Poe.PlutusData (Data unBData decodeByteStringList IsB IsByteStringList)

/-- Does the `Data`-encoded `owner` equal the `Data`-encoded
    `expectedOwner`? `ho`/`he` are the ghost preconditions `unBData` now
    requires, exactly like `Poe.Examples.First.divide`'s `hy : y ≠ 0` —
    the caller has to already know the shape, same as before, just made
    explicit instead of assumed. -/
def validateOwnerData (owner expectedOwner : Data) (ho : IsB owner) (he : IsB expectedOwner) :
    Unit :=
  Poe.Prelude.check (unBData owner ho == unBData expectedOwner he)

def elemBytes (x : ByteArray) : List ByteArray → Bool
  | []      => false
  | y :: ys => x == y || elemBytes x ys

/-- `ByteArray` has no `LawfulBEq` instance in this toolchain (checked
    directly — `inferInstance : LawfulBEq ByteArray` fails to synthesize),
    unlike `String`, so `elemBytes_iff` below can't just `simp` through
    `==` the way `Poe.Examples.HelloWorldString.elem_iff` does; bridging
    through the underlying `Array UInt8`'s own (real) `LawfulBEq` instance
    first. -/
theorem ByteArray.beq_iff_eq (x y : ByteArray) : (x == y) = true ↔ x = y := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  show (a.isEqv b fun u v => decide (u = v)) = true ↔ ByteArray.mk a = ByteArray.mk b
  rw [show (a.isEqv b fun u v => decide (u = v)) = (a == b) from rfl, _root_.beq_iff_eq]
  simp

/-- Same shape as `Poe.Examples.HelloWorldString.elem_iff` — used by
    `Poe.Examples.HelloWorld`'s correctness proof, since that validator's
    signer check bottoms out in this function instead. -/
theorem elemBytes_iff (x : ByteArray) : ∀ ys, elemBytes x ys = true ↔ x ∈ ys
  | [] => by simp [elemBytes]
  | y :: ys => by simp [elemBytes, elemBytes_iff x ys, ByteArray.beq_iff_eq]

/-- Does the `Data`-encoded `owner` appear in the `Data`-encoded
    `signatories`? Same ghost-precondition treatment as
    `validateOwnerData`. -/
def validateSignerData (owner signatories : Data) (ho : IsB owner)
    (hs : IsByteStringList signatories) : Unit :=
  Poe.Prelude.check (elemBytes (unBData owner ho) (decodeByteStringList signatories hs))

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

end Poe.Lib.DataDecoding
