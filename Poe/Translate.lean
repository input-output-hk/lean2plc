import Lean
import Poe.Uplc

/-!
# D1: LCNF → UPLC translator (stub)

The tap point is mono-phase LCNF (`Lean.Compiler.LCNF`): strict,
let-normalized, types/proofs already erased. Mapping (see PLAN.md):

  let x := e; body        ~>  [(lam x body) e]
  fun / application       ~>  lam / app        (CEK does closures)
  constructor application ~>  (constr i ...)
  cases                   ~>  (case ...)
  projection              ~>  single-branch case
  join points             ~>  let-bound lams (nullary: delay/force)
  recursive def           ~>  fix via self-application
  Int/Bool/... primitives ~>  builtin shim table

Open questions 1-2 in PLAN.md (LCNF API surface at 4.24.0; what structural
recursion looks like post-compilation) get answered here first, by inspecting
`Lean.Compiler.LCNF.getMonoDecl?` output for the example functions before
any translation code is written.
-/

namespace Poe.Translate

open Lean Compiler.LCNF

/-- Debug entry point: print a declaration's mono-phase LCNF so we can see
    what we're translating before writing the translator. -/
def dumpMonoLCNF (declName : Name) : CoreM Unit := do
  let some decl ← getMonoDecl? declName
    | throwError "no mono LCNF for {declName}"
  IO.println (← ppDecl' decl)

/-!
## Translation context

LCNF binds variables by `FVarId`; UPLC's `Term.var` is a de Bruijn index.
`Ctx` records, for each `FVarId` currently in scope, the binder *depth* at
which it was introduced (0 = outermost), plus the current depth. At a use
site the index is `depth - 1 - bindingDepth` (0 = innermost enclosing
binder), matching `Poe.Emit`'s convention.
-/

structure Ctx where
  depth : Nat := 0
  vars  : List (FVarId × Nat) := []

def Ctx.bind (ctx : Ctx) (fvarId : FVarId) : Ctx :=
  { depth := ctx.depth + 1, vars := (fvarId, ctx.depth) :: ctx.vars }

def Ctx.lookup (ctx : Ctx) (fvarId : FVarId) : CoreM Nat := do
  let some (_, bindingDepth) := ctx.vars.find? (·.1 == fvarId)
    | throwError "translator: unbound variable {Expr.fvar fvarId}"
  return ctx.depth - 1 - bindingDepth

/-- D1's builtin shim table (see PLAN.md): global names that translate
    directly to a builtin applied to the (translated) LCNF args, in order.
    Grows with the fragment. -/
def builtinTable : List (Name × Uplc.Builtin) :=
  [(``Int.add, .addInteger), (``Int.decLt, .lessThanInteger)]

def applyArgs (f : Uplc.Term) (args : List Uplc.Term) : Uplc.Term :=
  args.foldl .app f

def translateArg (ctx : Ctx) : Arg → CoreM Uplc.Term
  | .fvar fvarId => return .var (← ctx.lookup fvarId)
  | .erased | .type _ =>
    throwError "translator: erased/type argument reached D1 (out of fragment)"

/-- Calls that don't fit the flat builtin-table shape: `Int.ofNat` is the
    identity at the value level (Nat/Int share the UPLC integer constant),
    and `Int.neg` has no builtin of its own (synthesized as `0 - x`). -/
def translateConstCall (ctx : Ctx) (declName : Name) (args : Array Arg) : CoreM Uplc.Term := do
  match declName, args with
  | ``Int.ofNat, #[a] => translateArg ctx a
  | ``Int.neg, #[a] =>
    return .app (.app (.builtin .subtractInteger) (.const (.integer 0))) (← translateArg ctx a)
  | _, _ =>
    let some b := builtinTable.lookup declName
      | throwError "translator: no builtin shim for {declName} (out of fragment for D1)"
    applyArgs (.builtin b) <$> args.toList.mapM (translateArg ctx)

/-- Other `LetValue` shapes (projections, local/self application) aren't
    needed until `sumList`. -/
def translateLetValue (ctx : Ctx) : LetValue → CoreM Uplc.Term
  | .const declName _us args => translateConstCall ctx declName args
  | .lit (.nat n) => return .const (.integer (Int.ofNat n))
  | .lit .. => throwError "translator: only Nat literals are handled so far"
  | .fvar .. => throwError "translator: local/self application not yet handled"
  | .proj .. => throwError "translator: projections not yet handled"
  | .erased => throwError "translator: erased let-value reached D1 (out of fragment)"

/-- `let`/`return`, and `cases` on `Bool` (open question 3 in PLAN.md: cased
    on the *builtin* bool via `ifThenElse`, not an SoP `constr`/`case` pair —
    matches the census idiom of forced-builtin bindings). `cases` on any
    other inductive isn't needed until `sumList`. -/
partial def translateCode (ctx : Ctx) : Code → CoreM Uplc.Term
  | .let decl k => do
    let v ← translateLetValue ctx decl.value
    let body ← translateCode (ctx.bind decl.fvarId) k
    return .app (.lam decl.binderName.toString body) v
  | .return fvarId => return .var (← ctx.lookup fvarId)
  | .cases cases => do
    unless cases.typeName == ``Bool do
      throwError "translator: cases on {cases.typeName} not yet handled (only Bool so far)"
    let some trueAlt := cases.alts.find? (fun | .alt n .. => n == ``Bool.true | .default _ => false)
      | throwError "translator: Bool cases missing a Bool.true alternative"
    let some falseAlt := cases.alts.find? (fun | .alt n .. => n == ``Bool.false | .default _ => false)
      | throwError "translator: Bool cases missing a Bool.false alternative"
    let discr := Uplc.Term.var (← ctx.lookup cases.discr)
    let thenBranch ← translateCode ctx trueAlt.getCode
    let elseBranch ← translateCode ctx falseAlt.getCode
    -- `ifThenElse` is polymorphic even in UPLC: one `force` to strip that
    -- before applying the (strict) value args, one more to force whichever
    -- delayed branch it returns.
    return .force (.app (.app (.app (.force (.builtin .ifThenElse)) discr) (.delay thenBranch)) (.delay elseBranch))
  | _ => throwError "translator: unsupported Code constructor (not yet handled)"

def translateDecl (decl : Decl) : CoreM Uplc.Term := do
  let .code code := decl.value
    | throwError "translator: extern declarations are not in the fragment"
  let ctx := decl.params.foldl (init := {}) (·.bind ·.fvarId)
  let body ← translateCode ctx code
  return decl.params.foldr (init := body) fun p acc => .lam p.binderName.toString acc

def translate (declName : Name) : CoreM Uplc.Term := do
  let some decl ← getMonoDecl? declName
    | throwError "no mono LCNF for {declName}"
  translateDecl decl

end Poe.Translate
