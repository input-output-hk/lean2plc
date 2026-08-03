import Lean
import Lean.Compiler.LCNF.CompilerM
import Poe.Tplc
import Poe.Prelude
import Poe.PlutusData

/-!
# D1 (typed backend): base-LCNF → `Tplc.Term` translator (stub)

The tap point is *base*-phase LCNF (`Lean.Compiler.LCNF.getDecl?` via
`CompilerM.run`, default `Phase.base`), not the mono-phase `getMonoDecl?`
`Poe.Translate` uses — confirmed directly (see `Poe.Tplc`'s doc comment)
that base LCNF still carries genuine `TyAbs`/`TyInst`-shaped polymorphism:
a `Param` whose own type is a type former (`α : Type`) survives as a real
binder, and a call site instantiating it (`@myLength _ tail`) survives as
a real `Arg.type e` argument, rather than having already been
monomorphized away.

Deliberate fragment restrictions for this first increment (grow along
with `Poe.Translate`'s own incremental history):

* **Non-recursive only.** A self-recursive decl is rejected outright.
  `Poe.Translate`'s own recursion strategy (the Z-combinator's
  self-application `x x`) is ill-typed under TPLC without a supporting
  recursive type — real TPLC's own recursion story goes through
  `TyIFix`/`IWrap`/`Unwrap` (isorecursive types), a genuinely separate,
  substantial piece of design work, not attempted here yet.
* **`cases` on `Bool`/`Decidable` only** — no user inductives yet (would
  need `Ty.sop`/`Term.constr`/`Term.case`, a separate piece of work).
  `Decidable` shows up because base LCNF still has it (`if x < 0 then...`
  is `cases` on `Decidable.isFalse`/`Decidable.isTrue`, each carrying an
  erased proof field) — `Poe.Translate`'s own mono-phase translator only
  ever sees `Bool` because monomorphization has already collapsed
  `Decidable` down to a plain runtime bool by the time it looks; base
  phase hasn't done that collapse yet, confirmed directly by comparing
  `Poe.Translate.dumpMonoLCNF`/`dumpBaseLCNF` on the same declaration.
  Bool/Decidable branching itself *is* handled (see `translateCode`'s
  `.cases` case): real
  `ifThenElse : all a. bool -> a -> a -> a` (confirmed directly against
  `PlutusCore/Default/Builtins.hs`), instantiated via `TyInst` at a
  *thunk* type `all t. a` rather than at `a` directly, with each branch
  wrapped in a matching `TyAbs .type` — TPLC has no `Force`/`Delay` term
  formers at all (unlike `Poe.Uplc.Term`), so the untyped translator's own
  delay/force idiom for keeping `ifThenElse`'s eager builtin call lazy per
  branch has to be *reconstructed* from the very mechanism `eraseTerm`
  maps down to it (`TyAbs → Delay`, `TyInst → Force`) — i.e. a thunk is a
  term abstracted over an unused type variable, forced by instantiating
  that dummy variable at any (irrelevant) closed type. Confirmed directly
  against `plc`: typechecks, evaluates the selected branch correctly, and
  — critically — genuinely never evaluates the *other* branch (an
  `error` planted in the unselected branch does not fire).
* **Type-former params must precede all value params** in a decl's
  parameter list (matches idiomatic Lean style, `{α β : Type} (x : α) ...`)
  — lets a single left-to-right pass over `decl.params` double as the
  scope every later value param's own `Ty` translation needs, since by
  this restriction no type param can appear after the value param whose
  annotation is being translated.
-/

namespace Poe.TranslateTplc

open Lean Compiler.LCNF

/-- Debug entry point, base-LCNF analogue of `Poe.Translate.dumpMonoLCNF`. -/
def dumpBaseLCNF (declName : Name) : CoreM Unit := do
  let some decl ← CompilerM.run (getDecl? declName)
    | throwError "no base LCNF for {declName}"
  IO.println (← ppDecl' decl)

/-!
## Translation context

Two independent de Bruijn scopes, mirroring `Poe.EmitTplc`'s own
`termDepth`/`tyDepth` split: `termVars` for ordinary `Param`/`LetDecl`
`FVarId`s (bound by `Term.lamAbs`), `tyVars` for type-former `Param`
`FVarId`s (bound by `Term.tyAbs`).
-/

structure Ctx where
  termDepth : Nat := 0
  termVars  : List (FVarId × Nat) := []
  tyDepth   : Nat := 0
  tyVars    : List (FVarId × Nat) := []

def Ctx.bindTerm (ctx : Ctx) (fvarId : FVarId) : Ctx :=
  { ctx with termDepth := ctx.termDepth + 1, termVars := (fvarId, ctx.termDepth) :: ctx.termVars }

def Ctx.bindTy (ctx : Ctx) (fvarId : FVarId) : Ctx :=
  { ctx with tyDepth := ctx.tyDepth + 1, tyVars := (fvarId, ctx.tyDepth) :: ctx.tyVars }

/-- Bump `tyDepth` for a synthetic (translation-introduced, not a real
    LCNF `Param`) type binder — the dummy `TyAbs .type` a thunk wraps a
    branch body in. Nothing can ever look this binder up by `FVarId`
    (there isn't one), but any *real* `Ty.var` reference already inside
    the branch body still needs its index shifted by the new enclosing
    binder, exactly as `Poe.EmitTplc.emitTerm`'s own `tyDepth + 1` does
    for `Term.tyAbs`. -/
def Ctx.bindTyAnon (ctx : Ctx) : Ctx :=
  { ctx with tyDepth := ctx.tyDepth + 1 }

def Ctx.lookupTerm (ctx : Ctx) (fvarId : FVarId) : CoreM Nat := do
  let some (_, bindingDepth) := ctx.termVars.find? (·.1 == fvarId)
    | throwError "translateTplc: unbound term variable {Expr.fvar fvarId}"
  return ctx.termDepth - 1 - bindingDepth

def Ctx.lookupTy (ctx : Ctx) (fvarId : FVarId) : CoreM Nat := do
  let some (_, bindingDepth) := ctx.tyVars.find? (·.1 == fvarId)
    | throwError "translateTplc: unbound type variable {Expr.fvar fvarId}"
  return ctx.tyDepth - 1 - bindingDepth

/-- The handful of base (non-generic) types the fragment needs, matching
    `Poe.Uplc.Const`'s own cases one for one. Grows with the fragment,
    same as `Poe.Translate.builtinTable`. -/
def builtinTyTable : List (Name × Tplc.TyBuiltin) :=
  [ (``Int, .integer), (``Nat, .integer), (``Bool, .bool), (``String, .string)
  , (``ByteArray, .bytestring), (``Poe.PlutusData.Data, .data)
  , (``PUnit, .unit), (``Unit, .unit)
  ]

/-- A type-former `Param`'s own type is bound directly (`Ty.var`, via
    `Ctx.lookupTy`); anything else must be a concrete base type from
    `builtinTyTable` — no user-defined inductives/type applications yet
    (out of fragment, same incremental spirit as `Poe.Translate`'s own
    `translateArg`). `Decidable ◾` (a `let`-bound `Int.decLt`/`Int.decEq`/
    ...'s own LCNF type, its `Prop` argument already erased) is a runtime
    bool by Lean's own convention regardless of *which* proposition it
    decides — same reasoning as `translateCode`'s `.cases` handling
    collapsing `Decidable.isFalse`/`isTrue` into the `Bool` case. -/
def translateTy (ctx : Ctx) : Expr → CoreM Tplc.Ty
  | .fvar fvarId => return .var (← ctx.lookupTy fvarId)
  | .const declName _ =>
    match builtinTyTable.lookup declName with
    | some b => return .builtin b
    | none => throwError "translateTplc: unsupported type {declName} (out of fragment)"
  | e =>
    if e.isAppOf ``Decidable then
      return .builtin .bool
    else
      throwError "translateTplc: unsupported type expression {e} (out of fragment)"

/-- D1's builtin shim table, same declName → `Poe.Uplc.Builtin` mapping
    `Poe.Translate.builtinTable` uses — `Poe.Tplc.Term.builtin` wraps the
    very same `Poe.Uplc.Builtin` enum, so no separate table is needed. -/
def builtinTable : List (Name × Poe.Uplc.Builtin) :=
  [ (``Int.add, .addInteger), (``Int.decLt, .lessThanInteger), (``String.decEq, .equalsString)
  , (``ByteArray.instBEq.beq, .equalsByteString), (``String.toUTF8, .encodeUtf8)
  , (``Int.decEq, .equalsInteger)
  , (``Poe.PlutusData.unBData, .unBData)
  , (``Int.fdiv, .divideInteger)
  ]

/-- Apply `f` to `args` in order: a `.fvar` arg is an ordinary `Term.apply`,
    a `.type` arg is a `Term.tyInst` (the whole reason this translator
    exists separately from `Poe.Translate`'s own `applyArgs`/`translateArgs`
    combo, which only ever *drops* `.type`/`.erased` args), and `.erased`
    (a dropped `Prop`-typed proof) contributes nothing, matching
    `Poe.Translate.translateArgs`'s own erasure. -/
def applyArgsTplc (ctx : Ctx) (f : Tplc.Term) (args : Array Arg) : CoreM Tplc.Term :=
  args.foldlM (init := f) fun acc arg =>
    match arg with
    | .erased => return acc
    | .fvar fvarId => return .apply acc (.var (← ctx.lookupTerm fvarId))
    | .type e => return .tyInst acc (← translateTy ctx e)

/-- `Code.let`/`LetValue.const` self-references detect recursion, same
    definition as `Poe.Translate.codeMentionsSelf` (duplicated rather than
    shared since the two translators are expected to diverge further as
    each grows its own fragment). -/
partial def codeMentionsSelf (name : Name) : Code → Bool
  | .let decl k =>
    (match decl.value with
      | .const n .. => n == name
      | _ => false) || codeMentionsSelf name k
  | .cases cases => cases.alts.any fun alt => codeMentionsSelf name alt.getCode
  | .fun decl k | .jp decl k => codeMentionsSelf name decl.value || codeMentionsSelf name k
  | .return _ | .jmp .. | .unreach _ => false

mutual

/-- Calls that don't fit the flat builtin-table shape: `Int.ofNat`/`Int.neg`
    as in `Poe.Translate`; anything else is another top-level decl,
    translated (and applied/instantiated) in turn. No self-recursive case
    at all — `translateDecl` rejects recursive decls before this is ever
    reached. -/
partial def translateConstCall (ctx : Ctx) (declName : Name) (args : Array Arg) : CoreM Tplc.Term := do
  match declName, args with
  | ``Int.ofNat, #[a] =>
    match a with
    | .fvar fvarId => return .var (← ctx.lookupTerm fvarId)
    | _ => throwError "translateTplc: Int.ofNat applied to a non-value argument"
  | ``Int.neg, #[a] =>
    match a with
    | .fvar fvarId =>
      return .apply (.apply (.builtin .subtractInteger) (.constant (.integer 0))) (.var (← ctx.lookupTerm fvarId))
    | _ => throwError "translateTplc: Int.neg applied to a non-value argument"
  | ``Poe.Prelude.abort, _ =>
    throwError "translateTplc: Poe.Prelude.abort needs a result Ty annotation, not yet handled"
  | _, _ =>
    match builtinTable.lookup declName with
    | some b => applyArgsTplc ctx (.builtin b) args
    | none => do
      let callee ← translate declName
      applyArgsTplc ctx callee args

/-- Other `LetValue` shapes (projections, non-self local application)
    aren't needed by the examples so far, same restriction as
    `Poe.Translate.translateLetValue`. -/
partial def translateLetValue (ctx : Ctx) : LetValue → CoreM Tplc.Term
  | .const declName _us args => translateConstCall ctx declName args
  | .lit (.nat n) => return .constant (.integer (Int.ofNat n))
  | .lit (.str s) => return .constant (.string s)
  | .lit .. => throwError "translateTplc: only Nat/String literals are handled so far"
  | .fvar .. => throwError "translateTplc: local (non-self) application not yet handled"
  | .proj .. => throwError "translateTplc: projections not yet handled"
  | .erased => throwError "translateTplc: erased let-value reached D1 (out of fragment)"

/-- `let`/`return`/`unreach`, plus `cases` on `Bool` (see file doc comment
    for the thunk-via-`TyAbs`/`TyInst` encoding `ifThenElse` needs — no
    other inductive's `cases` is handled yet). -/
partial def translateCode (ctx : Ctx) : Code → CoreM Tplc.Term
  | .let decl k => do
    let v ← translateLetValue ctx decl.value
    let body ← translateCode (ctx.bindTerm decl.fvarId) k
    -- The `let`-bound value's own `Ty` for the wrapping `lamAbs`: LCNF's
    -- `LetDecl.type` is the very `Expr` `Poe.Translate` never needed
    -- (untyped UPLC's `lam` carries no type annotation at all).
    return .apply (.lamAbs (← translateTy ctx decl.type) body) v
  | .return fvarId => return .var (← ctx.lookupTerm fvarId)
  -- `Code.unreach` already carries its own result `Ty` (LCNF needs this
  -- to keep the surrounding code type-correct even though the branch is
  -- dead) — exactly the annotation `Tplc.Term.error` itself requires,
  -- so no extra bookkeeping is needed beyond `translateTy`.
  | .unreach ty => return .error (← translateTy ctx ty)
  | .cases cases => do
    -- `if`/`decide`-style branching on an `Int`/`String`/... comparison
    -- goes through `Decidable`, not `Bool`, directly: confirmed directly
    -- (`absInt`'s base LCNF dump shows `cases _x.3 : Int | Decidable.isFalse
    -- x.4 | Decidable.isTrue x.5`, each alt carrying one `Prop`-erased
    -- proof field) — `Poe.Translate`'s own mono-phase translator never
    -- sees this, since monomorphization has already collapsed `Decidable`
    -- down to a plain runtime `Bool` by the time it looks. Both cases are
    -- otherwise identical: the discriminant is a real runtime bool either
    -- way, and any ctor field (`Decidable`'s erased proof; `Bool` has
    -- none) is dropped rather than bound.
    let trueName  := if cases.typeName == ``Decidable then ``Decidable.isTrue else ``Bool.true
    let falseName := if cases.typeName == ``Decidable then ``Decidable.isFalse else ``Bool.false
    if cases.typeName == ``Bool || cases.typeName == ``Decidable then
      let some trueAlt := cases.alts.find? (fun | .alt n .. => n == trueName | .default _ => false)
        | throwError "translateTplc: {cases.typeName} cases missing a {trueName} alternative"
      let some falseAlt := cases.alts.find? (fun | .alt n .. => n == falseName | .default _ => false)
        | throwError "translateTplc: {cases.typeName} cases missing a {falseName} alternative"
      let discr := Tplc.Term.var (← ctx.lookupTerm cases.discr)
      -- Each branch sits under one synthetic type binder (the thunk's
      -- `TyAbs .type`), so any real `Ty.var` it references needs shifting
      -- — `Ctx.bindTyAnon`, not `ctx` itself.
      let thenBranch ← translateCode ctx.bindTyAnon trueAlt.getCode
      let elseBranch ← translateCode ctx.bindTyAnon falseAlt.getCode
      let resultTy ← translateTy ctx cases.resultType
      -- `all t. resultTy` — the thunk type `ifThenElse`'s own type
      -- parameter gets instantiated to, confirmed directly against `plc`
      -- (both branch selection *and* the unselected branch's genuine
      -- non-evaluation).
      let thunkTy := Tplc.Ty.forall_ .type resultTy
      let scrutinee :=
        Tplc.Term.apply
          (Tplc.Term.apply
            (Tplc.Term.apply (.tyInst (.builtin .ifThenElse) thunkTy) discr)
            (.tyAbs .type thenBranch))
          (.tyAbs .type elseBranch)
      -- Force the thunked result: any closed type instantiates the dummy
      -- variable equally well (it's unused in the body), so `resultTy`
      -- itself is as good a choice as any.
      return .tyInst scrutinee resultTy
    else
      throwError "translateTplc: cases on {cases.typeName} not yet handled (out of fragment)"
  | _ => throwError "translateTplc: unsupported Code constructor (not yet handled)"

/-- Fragment restrictions: non-recursive; type-former params precede all
    value params (see file doc comment) — a single left-to-right ctx-build
    pass then doubles as the scope every value param's own `Ty`
    translation needs, since by that restriction no type param can follow
    the value param whose annotation is being translated. -/
partial def translateDecl (decl : Decl) : CoreM Tplc.Term := do
  let .code code := decl.value
    | throwError "translateTplc: extern declarations are not in the fragment"
  if codeMentionsSelf decl.name code then
    throwError "translateTplc: {decl.name} is recursive — not yet supported (would need isorecursive TyIFix/IWrap/Unwrap, not Poe.Translate's untyped self-application trick, which is ill-typed here)"
  let ctx := decl.params.foldl (init := ({} : Ctx)) fun ctx p =>
    if Compiler.LCNF.isTypeFormerType p.type then ctx.bindTy p.fvarId else ctx.bindTerm p.fvarId
  let body ← translateCode ctx code
  decl.params.foldrM (init := body) fun p acc =>
    if Compiler.LCNF.isTypeFormerType p.type then
      return .tyAbs .type acc
    else
      return .lamAbs (← translateTy ctx p.type) acc

partial def translate (declName : Name) : CoreM Tplc.Term := do
  let some decl ← CompilerM.run (getDecl? declName)
    | throwError "no base LCNF for {declName}"
  translateDecl decl

end

end Poe.TranslateTplc
