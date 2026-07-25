import Lean
import Poe.Uplc
import Poe.Prelude
import Poe.PlutusData

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
  /-- `some (declName, bindingDepth)` while translating a self-recursive
      decl: calls to `declName` inside its own body go through the
      self-application fixpoint's "self" binder instead of the builtin
      table (see `zFix` below). -/
  self  : Option (Name × Nat) := none

def Ctx.bind (ctx : Ctx) (fvarId : FVarId) : Ctx :=
  { ctx with depth := ctx.depth + 1, vars := (fvarId, ctx.depth) :: ctx.vars }

def Ctx.lookup (ctx : Ctx) (fvarId : FVarId) : CoreM Nat := do
  let some (_, bindingDepth) := ctx.vars.find? (·.1 == fvarId)
    | throwError "translator: unbound variable {Expr.fvar fvarId}"
  return ctx.depth - 1 - bindingDepth

/-!
## Recursion: fix via self-application

UPLC has no named top-level recursive bindings, so a self-recursive `Decl`
(`sumList` calling `sumList` by name in its own LCNF body) gets wrapped in
the standard call-by-value fixpoint combinator (the "Z combinator", safe
under CBV unlike the naive Y combinator since the self-application is
guarded behind a lambda):

  fix f = (λx. f (λv. x x v)) (λx. f (λv. x x v))

so that `fix (λself. body[self])` reduces, on each call to `self`, back to
`body[fix (λself. body[self])]` — tying the knot without a named binding.
Verified standalone against the uplc oracle before wiring in (a countdown
function via this exact combinator, 5 steps, evaluates to 5).
-/

/-- `λx. f (λv. (x x) v)`, referencing `f` as the (as yet unbound) variable
    at de Bruijn index 1 — correct once nested directly under the `lam "f"`
    in `zCombinator`. -/
private def selfApp : Uplc.Term :=
  .lam "x" (.app (.var 1) (.lam "v" (.app (.app (.var 1) (.var 1)) (.var 0))))

private def zCombinator : Uplc.Term :=
  .lam "f" (.app selfApp selfApp)

def zFix (f : Uplc.Term) : Uplc.Term :=
  .app zCombinator f

/-!
## `decodeByteStringList`: a bespoke native-list-decode intrinsic

`Poe.PlutusData.decodeByteStringList` is special-cased by name (in
`translateConstCall`) to this hand-built loop instead of being translated
from its Lean body — `unListData`'s own output is UPLC's *native* builtin
list, which the ordinary `case` translation (built for our SoP `constr`
encoding of Lean's `List`) can't walk (checked directly: `case` errors,
"Attempted to apply a non-function"). Uses the same fixpoint combinator
as ordinary recursive decls, walking the native list via
`headList`/`tailList`/`nullList` (each needs exactly one `force` — a
single-`forall` builtin, unlike the two-`forall` `ifThenElse`) and
building an ordinary SoP `constr`-encoded `List ByteArray` as it goes, so
everything downstream of this one primitive is back in the regular
fragment. Verified standalone against `uplc` (both a non-empty and an
empty native list) before wiring in.
-/

/-- Body of `λself. λlst. ...`, at depth 2 throughout (`self` = index 1,
    `lst` = index 0 — `force`/`delay`/`constr` don't introduce binders). -/
private def dataListLoopBody : Uplc.Term :=
  let lst : Uplc.Term := .var 0
  let self : Uplc.Term := .var 1
  let cond := .app (.force (.builtin .nullList)) lst
  let nilBranch := Uplc.Term.constr 0 []
  let head := .app (.builtin .unBData) (.app (.force (.builtin .headList)) lst)
  let tailRec := .app self (.app (.force (.builtin .tailList)) lst)
  let consBranch := Uplc.Term.constr 1 [head, tailRec]
  .force (.app (.app (.app (.force (.builtin .ifThenElse)) cond) (.delay nilBranch)) (.delay consBranch))

/-- `λd. (fix loop) (unListData d)`. -/
def decodeByteStringListTerm : Uplc.Term :=
  .lam "d" (.app (zFix (.lam "self" (.lam "lst" dataListLoopBody)))
                 (.app (.builtin .unListData) (.var 0)))

/-!
## Generic `Data`-record accessors: `constrTag`/`field0`/`field1`/`field2`/`field8`

Real records like `ScriptContext`/`TxInfo` are just `Constr tag [field0,
field1, ...]` (verified against `plutus-ledger-api` source:
`makeIsDataSchemaIndexed` always assigns single-constructor records tag 0,
sum-type variants their declared index — e.g. `Maybe`'s `Just`/`Nothing`
are 0/1). These accessors are purely *positional* — the same `field0`
works on `ScriptContext` (→ `TxInfo`), `ScriptInfo`'s `SpendingScript`
payload (→ its `TxOutRef`), `Maybe`'s `Just` payload, or a user's own
single-field `Datum` record — since `unConstrData`+`sndPair` gives back
the field list regardless of what the record "means". `field8` exists
only because `TxInfo.txInfoSignatories` happens to sit at index 8 in the
real 16-field record. Same reasoning as `decodeByteStringList`: the field
list is UPLC's *native* list, not our SoP encoding, so this is a bespoke
intrinsic, not something a generic `cases` translation could produce. -/

/-- `unConstrData blob`'s fields, as UPLC's native `list(data)` (not our
    SoP `List`). -/
private def fieldsOfTerm (blob : Uplc.Term) : Uplc.Term :=
  .app (.force (.force (.builtin .sndPair))) (.app (.builtin .unConstrData) blob)

private def applyTailListN : Nat → Uplc.Term → Uplc.Term
  | 0, t => t
  | n + 1, t => applyTailListN n (.app (.force (.builtin .tailList)) t)

private def fieldAtTerm (n : Nat) (blob : Uplc.Term) : Uplc.Term :=
  .app (.force (.builtin .headList)) (applyTailListN n (fieldsOfTerm blob))

private def constrTagTerm (blob : Uplc.Term) : Uplc.Term :=
  .app (.force (.force (.builtin .fstPair))) (.app (.builtin .unConstrData) blob)

/-- D1's builtin shim table (see PLAN.md): global names that translate
    directly to a builtin applied to the (translated) LCNF args, in order.
    Grows with the fragment. -/
def builtinTable : List (Name × Uplc.Builtin) :=
  [ (``Int.add, .addInteger), (``Int.decLt, .lessThanInteger), (``String.decEq, .equalsString)
  , (``ByteArray.instBEq.beq, .equalsByteString), (``String.toUTF8, .encodeUtf8)
  , (``Int.decEq, .equalsInteger)
  , (``Poe.PlutusData.unBData, .unBData)
  ]

def applyArgs (f : Uplc.Term) (args : List Uplc.Term) : Uplc.Term :=
  args.foldl .app f

def translateArg (ctx : Ctx) : Arg → CoreM Uplc.Term
  | .fvar fvarId => return .var (← ctx.lookup fvarId)
  | .erased | .type _ =>
    throwError "translator: erased/type argument reached D1 (out of fragment)"

/-- The constructors of an inductive type, in declaration order — which is
    also the `constr`/`case` index convention this translator uses both for
    building `case` branches here and for encoding sample inputs in tests. -/
def ctorNames (typeName : Name) : CoreM (Array Name) := do
  let some (.inductInfo info) := (← getEnv).find? typeName
    | throwError "translator: {typeName} is not an inductive type"
  return info.ctors.toArray

/-- `Code.let`/`LetValue.const` self-references detect recursion; no attempt
    to detect *mutual* recursion (non-goal, see PLAN.md). -/
partial def codeMentionsSelf (name : Name) : Code → Bool
  | .let decl k =>
    (match decl.value with
      | .const n .. => n == name
      | _ => false) || codeMentionsSelf name k
  | .cases cases => cases.alts.any fun alt => codeMentionsSelf name alt.getCode
  | .fun decl k | .jp decl k => codeMentionsSelf name decl.value || codeMentionsSelf name k
  | .return _ | .jmp .. | .unreach _ => false

/- `translateConstCall`, `translateLetValue`, `translateCode`, `translateDecl`
   and `translate` are mutually recursive: a call to another top-level decl
   (`validate` calling the separately-defined `elem`, say — not a self-call)
   translates that decl too and applies the result, so the translator
   covers a call *graph*, not just one declaration at a time. No cycle
   detection — mutually-recursive *decls* (as opposed to a decl calling
   itself) are a stated non-goal and would just not terminate here. -/
mutual

/-- Calls that don't fit the flat builtin-table shape: a self-recursive call
    goes through the fixpoint's `self` binder; `Int.ofNat` is the identity
    at the value level (Nat/Int share the UPLC integer constant); `Int.neg`
    has no builtin of its own (synthesized as `0 - x`); anything else falls
    back to translating (and applying) that other declaration. -/
partial def translateConstCall (ctx : Ctx) (declName : Name) (args : Array Arg) : CoreM Uplc.Term := do
  if let some (selfName, selfDepth) := ctx.self then
    if declName == selfName then
      return applyArgs (.var (ctx.depth - 1 - selfDepth)) (← args.toList.mapM (translateArg ctx))
  match declName, args with
  | ``Int.ofNat, #[a] => translateArg ctx a
  | ``Int.neg, #[a] =>
    return .app (.app (.builtin .subtractInteger) (.const (.integer 0))) (← translateArg ctx a)
  -- Bool is represented as the *builtin* bool everywhere (matches the
  -- `cases`-on-Bool handling below), not as an SoP `constr` value like
  -- other inductives — constructing `Bool.false`/`Bool.true` as a plain
  -- value has to agree with that or a downstream `ifThenElse`/`equalsBool`
  -- consumer would choke on a `constr` where it expects `(con bool _)`.
  | ``Bool.false, #[] => return .const (.bool false)
  | ``Bool.true, #[] => return .const (.bool true)
  -- Same reasoning for `Unit`: the builtin unit constant, not a 0-field
  -- SoP `constr`, so it matches real UPLC's own convention for it.
  | ``PUnit.unit, #[] => return .const .unit
  -- `Poe.Prelude.abort`'s Lean body is a placeholder never translated —
  -- the name itself means UPLC's `error` term, full stop (whatever
  -- dummy argument it was given to make it a real, non-inlinable
  -- `partial def` is irrelevant and ignored).
  | ``Poe.Prelude.abort, _ => return .error
  | ``Poe.PlutusData.decodeByteStringList, #[a] =>
    return .app decodeByteStringListTerm (← translateArg ctx a)
  | ``Poe.PlutusData.constrTag, #[a] => return constrTagTerm (← translateArg ctx a)
  | ``Poe.PlutusData.field0, #[a] => return fieldAtTerm 0 (← translateArg ctx a)
  | ``Poe.PlutusData.field1, #[a] => return fieldAtTerm 1 (← translateArg ctx a)
  | ``Poe.PlutusData.field2, #[a] => return fieldAtTerm 2 (← translateArg ctx a)
  | ``Poe.PlutusData.field8, #[a] => return fieldAtTerm 8 (← translateArg ctx a)
  | _, _ =>
    -- Constructor application (`List.cons`, ...): erased/type args are the
    -- inductive's own type parameters, not real fields, so they're dropped
    -- rather than run through the stricter `translateArg`.
    if let some (.ctorInfo info) := (← getEnv).find? declName then
      let fieldArgs := args.toList.filterMap fun | .fvar fvarId => some fvarId | _ => none
      Uplc.Term.constr info.cidx <$> fieldArgs.mapM fun fvarId => return .var (← ctx.lookup fvarId)
    else
      match builtinTable.lookup declName with
      | some b => applyArgs (.builtin b) <$> args.toList.mapM (translateArg ctx)
      | none => do
        let callee ← translate declName
        applyArgs callee <$> args.toList.mapM (translateArg ctx)

/-- Other `LetValue` shapes (projections) aren't needed by the examples so
    far. -/
partial def translateLetValue (ctx : Ctx) : LetValue → CoreM Uplc.Term
  | .const declName _us args => translateConstCall ctx declName args
  | .lit (.nat n) => return .const (.integer (Int.ofNat n))
  | .lit (.str s) => return .const (.string s)
  | .lit .. => throwError "translator: only Nat/String literals are handled so far"
  | .fvar .. => throwError "translator: local (non-self) application not yet handled"
  | .proj .. => throwError "translator: projections not yet handled"
  | .erased => throwError "translator: erased let-value reached D1 (out of fragment)"

/-- `let`/`return`; `cases` on `Bool` goes through builtin `ifThenElse`
    (open question 3 in PLAN.md: matches the census's forced-builtin idiom,
    not an SoP `constr`/`case` pair); `cases` on any other inductive becomes
    a UPLC `case` over one branch per constructor, in declaration order,
    each wrapped in a lambda per constructor field (0 fields ⇒ no wrapping,
    per the `case` semantics of applying the branch to the fields).
    Every constructor needs an explicit alternative — `default` alts
    (unneeded by `sumList`) aren't handled yet. -/
partial def translateCode (ctx : Ctx) : Code → CoreM Uplc.Term
  | .let decl k => do
    let v ← translateLetValue ctx decl.value
    let body ← translateCode (ctx.bind decl.fvarId) k
    return .app (.lam decl.binderName.toString body) v
  | .return fvarId => return .var (← ctx.lookup fvarId)
  | .cases cases => do
    let discr := Uplc.Term.var (← ctx.lookup cases.discr)
    if cases.typeName == ``Bool then
      let some trueAlt := cases.alts.find? (fun | .alt n .. => n == ``Bool.true | .default _ => false)
        | throwError "translator: Bool cases missing a Bool.true alternative"
      let some falseAlt := cases.alts.find? (fun | .alt n .. => n == ``Bool.false | .default _ => false)
        | throwError "translator: Bool cases missing a Bool.false alternative"
      let thenBranch ← translateCode ctx trueAlt.getCode
      let elseBranch ← translateCode ctx falseAlt.getCode
      -- `ifThenElse` is polymorphic even in UPLC: one `force` to strip that
      -- before applying the (strict) value args, one more to force
      -- whichever delayed branch it returns.
      return .force (.app (.app (.app (.force (.builtin .ifThenElse)) discr) (.delay thenBranch)) (.delay elseBranch))
    else
      let branches ← (← ctorNames cases.typeName).toList.mapM fun ctorName => do
        let some (.alt _ params code) := cases.alts.find? (fun | .alt n .. => n == ctorName | .default _ => false)
          | throwError "translator: cases on {cases.typeName} missing an alternative for {ctorName} (default alts not yet handled)"
        let branchBody ← translateCode (params.foldl (init := ctx) (·.bind ·.fvarId)) code
        return params.foldr (init := branchBody) fun p acc => .lam p.binderName.toString acc
      return .case discr branches
  | _ => throwError "translator: unsupported Code constructor (not yet handled)"

partial def translateDecl (decl : Decl) : CoreM Uplc.Term := do
  let .code code := decl.value
    | throwError "translator: extern declarations are not in the fragment"
  let recursive := codeMentionsSelf decl.name code
  let ctx0 : Ctx := if recursive then { depth := 1, self := some (decl.name, 0) } else {}
  let ctx := decl.params.foldl (init := ctx0) (·.bind ·.fvarId)
  let body ← translateCode ctx code
  let paramsBody := decl.params.foldr (init := body) fun p acc => .lam p.binderName.toString acc
  return if recursive then zFix (.lam "self" paramsBody) else paramsBody

partial def translate (declName : Name) : CoreM Uplc.Term := do
  let some decl ← getMonoDecl? declName
    | throwError "no mono LCNF for {declName}"
  translateDecl decl

end

end Poe.Translate
