/-!
# Minimal UPLC AST

`Term`/`Builtin`/`Program` are deliberately isomorphic, constructor for
constructor, to PlutusCoreBlaster's real `PlutusCore.UPLC.Term`/`BuiltinFun`/
`Program` (de Bruijn indices, display-only names on `Lam`) — confirmed
directly against Blaster's own source, not assumed, so that the increment-2
bridge (`Poe.Bridge`) is a mechanical injection for these three.

`Const`/`DataValue` are *not* full isomorphisms, despite earlier claims to
that effect here (caught by an independent review of `Poe.Bridge`, not
found by the author) — they're a deliberate embedding of only the sub-fragment
Poe needs. Real `Const` has several more cases (BLS12-381 curve points, a
general `Pair`, list/pair-of-`Data` optimizations) Poe's fragment never
produces. -/

namespace Poe.Uplc

instance : Repr ByteArray where
  reprPrec b n := reprPrec b.data n

/-- Real Plutus Core `Data` has two more cases than this — `Map` *and* `I`
    (integer-as-`Data`, common on-chain for quantities/`POSIXTime`/indices) —
    corrected here after an independent review found this comment previously
    undercounted the gap (claimed only `Map` was missing). Neither is needed
    by any current Poe example (see `Poe.PlutusData`), but this means
    `DataValue` cannot represent a real `Data` value built from an integer
    literal at all yet, independent of the `ByteArray`/`ByteString` gap
    `Poe.Bridge` already documents. `constr`'s `Nat` is the constructor tag
    (e.g. `ScriptContext`/`TxInfo` are always tag 0 — single-constructor
    records; `Maybe`'s `Just`/`Nothing` are tags 0/1 respectively — both
    verified against `plutus-ledger-api` source, not assumed). -/
inductive DataValue
  | b      : ByteArray → DataValue
  | list   : List DataValue → DataValue
  | constr : Nat → List DataValue → DataValue
deriving Repr, BEq

/-- A deliberate embedding of the sub-fragment of Blaster's real (larger)
    `Const` Poe needs — not a full isomorphism (see file doc comment). -/
inductive Const
  | integer    : Int → Const
  | bytestring : ByteArray → Const
  | string     : String → Const
  | bool       : Bool → Const
  | unit       : Const
  | data       : DataValue → Const
deriving Repr, BEq

inductive Builtin
  | addInteger
  | subtractInteger
  | multiplyInteger
  | divideInteger
  | modInteger
  | equalsInteger
  | lessThanInteger
  | lessThanEqualsInteger
  | equalsByteString
  | appendByteString
  | lengthOfByteString
  | equalsString
  | appendString
  | ifThenElse
  | trace
  | unBData
  | unListData
  | headList
  | tailList
  | nullList
  | encodeUtf8
  | unConstrData
  | fstPair
  | sndPair
deriving Repr, BEq

/-- `Var i` is a de Bruijn index: 0 = innermost enclosing `lam`.
    The `String` on `lam` is display-only metadata. -/
inductive Term
  | var     : Nat → Term
  | const   : Const → Term
  | builtin : Builtin → Term
  | lam     : String → Term → Term
  | app     : Term → Term → Term
  | delay   : Term → Term
  | force   : Term → Term
  | constr  : Nat → List Term → Term
  | case    : Term → List Term → Term
  | error   : Term
deriving Repr, BEq

inductive Program
  | program : Nat × Nat × Nat → Term → Program

end Poe.Uplc
