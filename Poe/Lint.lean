import Lean
import Poe.Translate

/-!
# D0: fragment linter

Per PLAN.md, half of the "ghost discipline" is already enforced before we
ever see a declaration: Lean's own Prop-elimination restriction means
computation cannot depend on proofs. The other half — computational types
staying in the translatable universe, no Type-level dependency doing
runtime work — is what this linter checks (open question 4).

It turns out that half is *fully* decidable purely at mono LCNF, with no
pre-erasure `Expr` pass needed. Mono-phase type erasure (`toLCNFType`,
`Lean.Compiler.LCNF.Types`) already collapses any value-dependent type
index it can't reduce to a concrete inductive down to one sentinel,
`lcAny` (`Expr.isAny`) — verified empirically: a genuinely value-indexed
type like `Vec α n` (`n : Nat` a free index, not a proof) prints, at mono
LCNF, as `Vec lcAny lcAny`, with the whole declaration's exported type
`{α} → {n} → Vec lcAny lcAny → lcAny`. Ordinary parametric polymorphism
(the type parameter `α` itself) erases to `lcErased` instead, which is
exactly the *expected*, harmless erasure — `lcAny` is the one signal that
actually means "reject". So D0 reduces to: scan every type occurring in
the declaration for an `lcAny` subterm.
-/

namespace Poe.Lint

open Lean Compiler.LCNF

/-- Does `e` contain the LCNF "couldn't reduce this dependency" marker
    anywhere as a subterm? -/
partial def hasAny (e : Expr) : Bool :=
  if e.isAny then true
  else match e with
    | .app f a => hasAny f || hasAny a
    | .forallE _ d b _ => hasAny d || hasAny b
    | .lam _ d b _ => hasAny d || hasAny b
    | .letE _ t v b _ => hasAny t || hasAny v || hasAny b
    | .mdata _ e => hasAny e
    | .proj _ _ e => hasAny e
    | _ => false

def checkType (label : String) (type : Expr) : List String :=
  if hasAny type then
    [s!"{label}: value-dependent type escaped erasure (lcAny) — out of the ghost-dependent fragment"]
  else []

mutual

partial def lintCode : Code → List String
  | .let decl k => checkType s!"let {decl.binderName}" decl.type ++ lintCode k
  | .fun decl k => lintFunDecl decl ++ lintCode k
  | .jp decl k => lintFunDecl decl ++ lintCode k
  | .cases cases =>
    checkType "cases result" cases.resultType ++ cases.alts.toList.flatMap lintAlt
  | .jmp .. | .return _ | .unreach _ => []

partial def lintAlt : Alt → List String
  | .alt _ params code =>
    params.toList.flatMap (fun p => checkType s!"param {p.binderName}" p.type) ++ lintCode code
  | .default code => lintCode code

partial def lintFunDecl (decl : FunDecl) : List String :=
  checkType s!"fun {decl.binderName}" decl.type ++
  decl.params.toList.flatMap (fun p => checkType s!"param {p.binderName}" p.type) ++
  lintCode decl.value

end

def lintDecl (decl : Decl) : List String :=
  let violations :=
    decl.params.toList.flatMap (fun p => checkType s!"param {p.binderName}" p.type) ++
    checkType "result" decl.type
  match decl.value with
  | .extern _ => violations ++ ["extern declarations are not in the fragment"]
  | .code code => violations ++ lintCode code

/-- D0: accept (`[]`) or reject (reasons) a declaration's mono LCNF. -/
def lint (declName : Name) : CoreM (List String) := do
  let some decl ← getMonoDecl? declName
    | return [s!"no mono LCNF for {declName} (not compiled — Prop/noncomputable?)"]
  return lintDecl decl

/-- Convenience for examples/tests: print accept/reject with reasons. -/
def check (declName : Name) : CoreM Unit := do
  match ← lint declName with
  | [] => IO.println s!"{declName}: accepted"
  | violations =>
    IO.println s!"{declName}: rejected"
    for v in violations do
      IO.println s!"  - {v}"

end Poe.Lint
