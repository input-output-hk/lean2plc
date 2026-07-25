/-!
# Minimal UPLC AST

Deliberately isomorphic, constructor for constructor, to PlutusCoreBlaster's
`PlutusCore.UPLC.Term` (de Bruijn indices, display-only names on `Lam`), so
that the increment-2 bridge is a mechanical injection. Constants and builtins
cover only what the Poe fragment needs; both enums grow with the shim table.
-/

namespace Poe.Uplc

instance : Repr ByteArray where
  reprPrec b n := reprPrec b.data n

/-- Real Plutus Core `Data` has one more case (`Map`) — not needed by any
    Poe example (see `Poe.PlutusData`). `constr`'s `Nat` is the constructor
    tag (e.g. `ScriptContext`/`TxInfo` are always tag 0 — single-constructor
    records; `Maybe`'s `Just`/`Nothing` are tags 0/1 respectively — both
    verified against `plutus-ledger-api` source, not assumed). -/
inductive DataValue
  | b      : ByteArray → DataValue
  | list   : List DataValue → DataValue
  | constr : Nat → List DataValue → DataValue
deriving Repr, BEq

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
