import PlutusCore.UPLC.Term
import PlutusCore.UPLC.CekMachine
import Poe.Uplc
import Poe.Examples.First

/-!
# D5 (stretch): the increment-2 bridge to PlutusCoreBlaster

`Poe.Uplc.Term`/`Const`/`Builtin`/`Program` were deliberately built
isomorphic, constructor for constructor, to Blaster's own
`PlutusCore.UPLC.Term.Term`/`Const`/`BuiltinFun`/`Program` — confirmed
directly by reading Blaster's source, not assumed. This file is exactly
the "mechanical injection" `Poe.Uplc`'s own doc comment already promised:
a total, structural embedding, no partiality or cleverness needed for
`Term`/`BuiltinFun` at all.

**One real gap, found by actually trying this rather than assuming it
away**: Blaster's `ByteString` is backed by a Lean `String`
(`structure ByteString where data : String`), not a `ByteArray` like
`Poe.Uplc`'s own `Const.bytestring`. These are *not* interchangeable —
an arbitrary byte sequence is not valid UTF-8, so there is no honest,
total `ByteArray → Blaster.ByteString` embedding via simple
reinterpretation. `toBlasterConst`/`toBlasterData` below are left
unimplemented (`sorry`) for `bytestring`/`data`, flagged explicitly
rather than silently doing something wrong — resolving this (probably:
Blaster gaining a real byte-sequence representation, or Poe restricting
this specific certificate direction to the ByteArray-free part of the
fragment) is follow-up scoping work, not something to paper over here.
-/

namespace Poe.Bridge

open PlutusCore.UPLC

/-- Total: every `Poe.Uplc.Builtin` case names a real `BuiltinFun`
    constructor, confirmed directly against `Term/Basic.lean`'s full
    enum (Blaster's is a strict superset — BLS crypto, more batches —
    Poe's fragment just never produces any of the extra ones). -/
def toBlasterBuiltin : Poe.Uplc.Builtin → Term.BuiltinFun
  | .addInteger => .AddInteger
  | .subtractInteger => .SubtractInteger
  | .multiplyInteger => .MultiplyInteger
  | .divideInteger => .DivideInteger
  | .modInteger => .ModInteger
  | .equalsInteger => .EqualsInteger
  | .lessThanInteger => .LessThanInteger
  | .lessThanEqualsInteger => .LessThanEqualsInteger
  | .equalsByteString => .EqualsByteString
  | .appendByteString => .AppendByteString
  | .lengthOfByteString => .LengthOfByteString
  | .equalsString => .EqualsString
  | .appendString => .AppendString
  | .ifThenElse => .IfThenElse
  | .trace => .Trace
  | .unBData => .UnBData
  | .unListData => .UnListData
  | .headList => .HeadList
  | .tailList => .TailList
  | .nullList => .NullList
  | .encodeUtf8 => .EncodeUtf8
  | .unConstrData => .UnConstrData
  | .fstPair => .FstPair
  | .sndPair => .SndPair

/-- See the file doc comment: `bytestring`/`data` are the one real gap,
    `ByteArray` has no honest total embedding into Blaster's
    `String`-backed `ByteString` yet. -/
def toBlasterData : Poe.Uplc.DataValue → PlutusCore.Data.Data
  | .constr tag fields => .Constr (Int.ofNat tag) (fields.map toBlasterData)
  | .list xs => .List (xs.map toBlasterData)
  | .b _ => sorry -- ByteArray -> Blaster's String-backed ByteString: no honest total embedding yet

def toBlasterConst : Poe.Uplc.Const → Term.Const
  | .integer i => .Integer i
  | .bytestring _ => sorry -- see toBlasterData
  | .string s => .String s
  | .bool b => .Bool b
  | .unit => .Unit
  | .data d => .Data (toBlasterData d)

/-- Total, structural, one case per constructor — the "mechanical
    injection" by construction. -/
def toBlasterTerm : Poe.Uplc.Term → Term.Term
  | .var i => .Var i
  | .const c => .Const (toBlasterConst c)
  | .builtin b => .Builtin (toBlasterBuiltin b)
  | .lam n t => .Lam n (toBlasterTerm t)
  | .app f a => .Apply (toBlasterTerm f) (toBlasterTerm a)
  | .delay t => .Delay (toBlasterTerm t)
  | .force t => .Force (toBlasterTerm t)
  | .constr i ts => .Constr i (ts.map toBlasterTerm)
  | .case scrut branches => .Case (toBlasterTerm scrut) (branches.map toBlasterTerm)
  | .error => .Error

def toBlasterProgram : Poe.Uplc.Program → Term.Program
  | .program (a, b, c) t => .Program (.Version a b c) (toBlasterTerm t)

/-!
## D5 (stretch): certificate theorem shape, stated for `double`

`PlutusCore.UPLC.CekMachine.cekExecuteProgram : Program → List Term → Nat
→ State` is fuel-limited (`Nat` steps), returning `Eval`/`Return` if fuel
runs out, `Halt value` on success, `Error` on a genuine crash — so the
natural certificate shape is existential over fuel: for every input,
*some* amount of stepping reaches the halted state matching the source
function's real Lean value.

`doubleUplcTerm` is `double`'s already-`plc`/oracle-verified compiled
shape (see `Poe.Examples.First`), transcribed by hand rather than
threaded through `Poe.Translate.translate` (a `CoreM` metaprogramming
action, not plain data a `theorem` statement can reference directly) —
matching the same "hand-built term, checked to match the real
translator's output" methodology `Poe.Examples.First`'s own opening
section already uses. Stated, not proved (`sorry`), per D5's own
"state, don't necessarily prove" — the point of this exercise is to see
how much encoding pain the statement itself involves, not to discharge
it. -/

def doubleUplcTerm : Poe.Uplc.Term :=
  .lam "x" (.app (.app (.builtin .addInteger) (.var 0)) (.var 0))

def doubleProgram : Poe.Uplc.Program :=
  .program (1, 1, 0) doubleUplcTerm

theorem double_certificate :
    ∀ (x : Int), ∃ (n : Nat),
      PlutusCore.UPLC.CekMachine.cekExecuteProgram
        (toBlasterProgram doubleProgram)
        [Term.Term.Const (.Integer x)]
        n
      = PlutusCore.UPLC.CekMachine.State.Halt
          (PlutusCore.UPLC.CekValue.CekValue.VCon (.Integer (Poe.Examples.double x))) := by
  sorry

end Poe.Bridge
