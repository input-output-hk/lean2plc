import Poe.Uplc

/-!
# Textual UPLC emitter

Pretty-prints `Poe.Uplc.Term` in the classic concrete syntax that the
`uplc` CLI and other Plutus tooling parse:

  (program 1.1.0 (lam x0 [(builtin addInteger) x0 (con integer 1)]))

De Bruijn indices are rendered as names `x<depth>` generated at the binder.
No layout/indentation — the oracle doesn't care.
-/

namespace Poe.Emit

open Poe.Uplc

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (n.toNat + '0'.toNat)
  else Char.ofNat (n.toNat - 10 + 'a'.toNat)

def toHex (b : ByteArray) : String :=
  b.foldl (init := "") fun s byte =>
    s.push (hexDigit (byte / 16)) |>.push (hexDigit (byte % 16))

/-- Matches `uplc`'s own concrete syntax for `Data` literals exactly,
    verified directly (e.g. `(con data (List [B #61, B #62]))`,
    `(con data (Constr 0 [Constr 1 [B #61], I 2]))`) — real `Data` also has
    `Map`, not modeled here (see `Poe.PlutusData`). -/
partial def emitDataValue : DataValue → String
  | .b bytes => s!"B #{toHex bytes}"
  | .list xs => s!"List [{String.intercalate ", " (xs.map emitDataValue)}]"
  | .constr tag xs => s!"Constr {tag} [{String.intercalate ", " (xs.map emitDataValue)}]"

def emitConst : Const → String
  | .integer i    => s!"(con integer {i})"
  | .bytestring b => s!"(con bytestring #{toHex b})"
  | .string s     => s!"(con string {repr s})"
  | .bool b       => s!"(con bool {if b then "True" else "False"})"
  | .unit         => "(con unit ())"
  -- `emitDataValue` itself is unwrapped (matches nested-list-element
  -- syntax); the top-level `Data` needs one more paren layer around it
  -- (`(con data (B #..))`, not `(con data B #..)` — checked directly).
  | .data d       => s!"(con data ({emitDataValue d}))"

def builtinName : Builtin → String
  | .addInteger           => "addInteger"
  | .subtractInteger      => "subtractInteger"
  | .multiplyInteger      => "multiplyInteger"
  | .divideInteger        => "divideInteger"
  | .modInteger           => "modInteger"
  | .equalsInteger        => "equalsInteger"
  | .lessThanInteger      => "lessThanInteger"
  | .lessThanEqualsInteger => "lessThanEqualsInteger"
  | .equalsByteString     => "equalsByteString"
  | .appendByteString     => "appendByteString"
  | .lengthOfByteString   => "lengthOfByteString"
  | .equalsString         => "equalsString"
  | .appendString         => "appendString"
  | .ifThenElse           => "ifThenElse"
  | .trace                => "trace"
  | .unBData              => "unBData"
  | .unListData           => "unListData"
  | .headList             => "headList"
  | .tailList             => "tailList"
  | .nullList             => "nullList"
  | .encodeUtf8           => "encodeUtf8"
  | .unConstrData         => "unConstrData"
  | .fstPair              => "fstPair"
  | .sndPair              => "sndPair"

/-- `depth` = number of enclosing binders; `var i` names the binder
    introduced at depth `depth - 1 - i`. -/
partial def emitTerm (depth : Nat) : Term → String
  | .var i        => s!"x{depth - 1 - i}"
  | .const c      => emitConst c
  | .builtin b    => s!"(builtin {builtinName b})"
  | .lam _ t      => s!"(lam x{depth} {emitTerm (depth + 1) t})"
  | .app f a      => s!"[{emitTerm depth f} {emitTerm depth a}]"
  | .delay t      => s!"(delay {emitTerm depth t})"
  | .force t      => s!"(force {emitTerm depth t})"
  | .constr i ts  => s!"(constr {i}{String.join (ts.map (fun t => " " ++ emitTerm depth t))})"
  | .case s bs    => s!"(case {emitTerm depth s}{String.join (bs.map (fun t => " " ++ emitTerm depth t))})"
  | .error        => "(error)"

def emitProgram : Program → String
  | .program (a, b, c) t => s!"(program {a}.{b}.{c} {emitTerm 0 t})"

/-- Default wrapper: Plutus Core 1.1.0 (SoP-capable). -/
def emit (t : Term) : String :=
  emitProgram (.program (1, 1, 0) t)

end Poe.Emit
