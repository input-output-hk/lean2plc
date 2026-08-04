import Poe.Tplc
import Poe.Emit

/-!
# Textual TPLC emitter

Pretty-prints `Poe.Tplc.Term` in the real "classic" concrete syntax
(checked directly against
`plutus-core/plutus-core/src/PlutusCore/Core/Instance/Pretty/Classic.hs`,
the same rigor `Poe.Emit` was built against for `uplc`'s own textual
form): `Apply`/`TyApp` use `[...]` (matching `Poe.Emit`'s own `app`
exactly), `TyInst` uses `{...}` — the one bracket shape untyped UPLC has
no need for at all, since instantiation doesn't exist post-erasure —
and everything else is `(keyword arg1 arg2 ...)`.

Two separate de Bruijn scopes, tracked as two separate depths throughout
— `Term.var`'s (term-level binders: `LamAbs`) and `Ty.var`'s (type-level
binders: `Ty.forall_`/`Ty.lam`, *and* `Term.tyAbs`, which is a term
constructor that introduces a type-level binder any `Ty` annotation
inside its body can reference). Getting this conflated would silently
mis-render a real, well-typed term as one that doesn't parse or type-checks
differently — worth being as careful here as `Poe.Emit`'s own single
depth counter already is. -/

namespace Poe.EmitTplc

open Poe.Tplc

def emitKind : Kind → String
  | .type        => "(type)"
  | .arrow k1 k2 => s!"(fun {emitKind k1} {emitKind k2})"

def emitTyBuiltin : TyBuiltin → String
  | .integer    => "integer"
  | .bytestring => "bytestring"
  | .string     => "string"
  | .bool       => "bool"
  | .unit       => "unit"
  | .data       => "data"
  | .list       => "list"
  | .pair       => "pair"

/-- `depth` = number of enclosing *type*-level binders (`Ty.forall_`,
    `Ty.lam`, or an enclosing `Term.tyAbs`) — a completely separate
    counter from `emitTerm`'s term-level one, even though both render as
    `x<depth>`-style names; `t<depth>` here to keep them visually
    distinct in the emitted text too. -/
partial def emitTy (depth : Nat) : Ty → String
  | .var i         => s!"t{depth - 1 - i}"
  | .fn a b        => s!"(fun {emitTy depth a} {emitTy depth b})"
  | .ifix pat arg  => s!"(ifix {emitTy depth pat} {emitTy depth arg})"
  | .forall_ k b   => s!"(all t{depth} {emitKind k} {emitTy (depth + 1) b})"
  | .builtin b     => s!"(con {emitTyBuiltin b})"
  | .lam k b       => s!"(lam t{depth} {emitKind k} {emitTy (depth + 1) b})"
  | .app a b       => s!"[{emitTy depth a} {emitTy depth b}]"
  | .sop tyls      =>
    s!"(sop{String.join (tyls.map (fun tyl => " [" ++ String.intercalate " " (tyl.map (emitTy depth)) ++ "]"))})"

/-- `termDepth`/`tyDepth`: the term- and type-level de Bruijn depths,
    threaded independently. `Term.constant`/`Term.builtin` reuse
    `Poe.Emit`'s own, already-`uplc`-verified renderers directly —
    `eraseTerm` passes these two constructors through completely
    unchanged, so there's nothing TPLC-specific left to get right for
    them at all. -/
partial def emitTerm (termDepth tyDepth : Nat) : Term → String
  | .var i           => s!"x{termDepth - 1 - i}"
  | .lamAbs ty t     =>
    s!"(lam x{termDepth} {emitTy tyDepth ty} {emitTerm (termDepth + 1) tyDepth t})"
  | .apply f a       => s!"[{emitTerm termDepth tyDepth f} {emitTerm termDepth tyDepth a}]"
  | .tyAbs k t       =>
    s!"(abs t{tyDepth} {emitKind k} {emitTerm termDepth (tyDepth + 1) t})"
  | .tyInst t ty     => s!"{"{"}{emitTerm termDepth tyDepth t} {emitTy tyDepth ty}{"}"}"
  | .iwrap ty1 ty2 t =>
    s!"(iwrap {emitTy tyDepth ty1} {emitTy tyDepth ty2} {emitTerm termDepth tyDepth t})"
  | .unwrap t        => s!"(unwrap {emitTerm termDepth tyDepth t})"
  | .constr ty i ts  =>
    s!"(constr {emitTy tyDepth ty} {i}{String.join (ts.map (fun t => " " ++ emitTerm termDepth tyDepth t))})"
  | .case ty scrut bs =>
    s!"(case {emitTy tyDepth ty} {emitTerm termDepth tyDepth scrut}{String.join (bs.map (fun t => " " ++ emitTerm termDepth tyDepth t))})"
  | .constant c      => Poe.Emit.emitConst c
  | .builtin b       => s!"(builtin {Poe.Emit.builtinName b})"
  | .error ty        => s!"(error {emitTy tyDepth ty})"

def emitProgram : Program → String
  | .program (a, b, c) t => s!"(program {a}.{b}.{c} {emitTerm 0 0 t})"

/-- Default wrapper: Plutus Core 1.1.0, matching `Poe.Emit.emit`'s own
    default exactly. -/
def emit (t : Term) : String :=
  emitProgram (.program (1, 1, 0) t)

end Poe.EmitTplc
