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

* **Recursive decls must be non-generic** (no type-former params at all).
  `Poe.Translate`'s own recursion strategy (the Z-combinator's
  self-application `x x`) is ill-typed under TPLC without a supporting
  recursive type; `typedFix`/`fixPat`/`fixArg`/`selfTy` below implement
  the classic isorecursive-self-application fixpoint (TAPL ch. 20),
  generalized from a standalone countdown-function test verified
  directly against `plc` — first attempt used the *unguarded* textbook
  construction, which only terminates under call-by-name and looped
  forever under UPLC/TPLC's actual call-by-value semantics (genuinely
  OOM-killed the `plc` process at 57GB resident before the same
  CBV-safe eta-guard `Poe.Translate.zCombinator` already uses got ported
  in). Restricting to non-generic decls sidesteps a real complication:
  the fixpoint's own machinery embeds the decl's function type `T` under
  a fresh type binder it introduces (`fixArg`), so `T` needs to be a
  *closed* `Ty` (no free `Ty.var`s) to embed safely without reshifting —
  guaranteed automatically when there are no type-former params to
  create a free type variable in the first place.
* **`cases`/`constr` on `Bool`/`Decidable`/`List` only** — no other user
  inductives yet. `List` needed the most new machinery: it's a genuinely
  *recursive* type (`Cons` holds another `List`), and `Ty.sop` alone can't
  express that (a sum-of-products is a closed, finite shape — nothing
  lets one of its fields refer back to "this same type"). Real Plutus
  Core's own compiler needs `TyIFix`/`IWrap`/`Unwrap` for exactly this
  reason even when using the modern SOP encoding (confirmed by reading
  `PlutusIR/Compiler/Datatype.hs` and `PlutusCore/StdLib/Type.hs`
  directly: `mkDatatypeType List <pattern functor body>
  = fix (\(List :: * -> *) (a :: *) -> sop [] [a, List a])` — the `sop`
  supplies the *shape*, `ifix` is what lets `List` appear *inside* it).
  `listPatFunctor`/`listTy`/`listUnrolledSop` below implement exactly
  that recipe (`makeRecursiveType1`'s single-type-parameter case),
  verified by hand against `plc` before being wired in: a hand-built
  `List Int` (`nil`, `cons 1 (cons 2 nil)`) type-checked, and a
  `case`-based `head` function correctly returned `1` for the non-empty
  list and genuinely aborted on `nil`.
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
  /-- `some (declName, bindingDepth)` while translating a self-recursive
      decl — same role as `Poe.Translate.Ctx.self`: calls to `declName`
      inside its own body go through the fixpoint's "self" binder
      (`typedFix`) instead of the ordinary callee/builtin lookup. -/
  self : Option (Name × Nat) := none
  /-- Fvars bound to a *native* builtin `list` (e.g. the field list
      `unConstrData`/`unListData` hand back) rather than the ordinary
      `IWrap`-encoded `listTy` a Lean `List α` otherwise translates to —
      same role as `Poe.Translate.Ctx.nativeListVars`, needed here because
      TPLC is fully type-checked: the two representations are genuinely
      different `Ty`s (`nativeListOfDataTy` vs `listTy (.builtin .data)`),
      and using the wrong one at a binder makes `plc` reject the term. -/
  nativeListVars : List FVarId := []

def Ctx.bindTerm (ctx : Ctx) (fvarId : FVarId) : Ctx :=
  { ctx with termDepth := ctx.termDepth + 1, termVars := (fvarId, ctx.termDepth) :: ctx.termVars }

def Ctx.markNative (ctx : Ctx) (fvarId : FVarId) : Ctx :=
  { ctx with nativeListVars := fvarId :: ctx.nativeListVars }

def Ctx.isNative (ctx : Ctx) (fvarId : FVarId) : Bool :=
  ctx.nativeListVars.contains fvarId

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

/-- `List`'s pattern functor (see `Poe.TranslateTplc`'s recursion doc
    comment below, and the real recipe in `PlutusCore/StdLib/Type.hs`'s
    `makeRecursiveType1`, confirmed directly against `plc`):
    `\(List :: * -> *) (a :: *) -> sop [] [a, [List a]]`. Fixed and
    reusable across every element type — only the `ifix`'s second
    argument (the element `Ty`) varies per instantiation. -/
def listPatFunctor : Tplc.Ty :=
  .lam (.arrow .type .type) (.lam .type (.sop [[], [.var 0, .app (.var 1) (.var 0)]]))

/-- `List elemTy`, i.e. `ifix listPatFunctor elemTy` — confirmed directly
    against `plc typecheck`. -/
def listTy (elemTy : Tplc.Ty) : Tplc.Ty :=
  .ifix listPatFunctor elemTy

/-- The concrete (self-reference already unrolled to `listTy elemTy`) SOP
    shape a `List elemTy` value's `Constr`/`Case` need as their own `Ty`
    annotation — *not* the abstract pattern-functor body, which still has
    a `List`-shaped hole in it. Matches PIR's own `mkConstructor`/`Case`
    recipe: "the pattern functor with the hole filled in with the
    datatype type". -/
def listUnrolledSop (elemTy : Tplc.Ty) : Tplc.Ty :=
  .sop [[], [elemTy, listTy elemTy]]

/-!
## `Data`-record accessors: `constrTag`/`field0`–`field8`

Real Plutus Core's *native* `pair`/`list` builtin types (a completely
different representation from `listTy`'s user-level SOP encoding, see
`Poe.Tplc.TyBuiltin`'s doc comment) — `unConstrData : data -> pair
integer (list data)` (monomorphic, confirmed directly against both
`PlutusCore/Default/Builtins.hs`'s Haskell signature and `plc
typecheck`), `fstPair`/`sndPair : all a b. pair a b -> a`/`-> b`,
`headList`/`tailList : all a. list a -> a`/`-> list a` (both genuinely
polymorphic, each instantiation confirmed directly against `plc`).
Mirrors `Poe.Translate`'s own `fstPair`/`sndPair`/`headList`/`tailList`
chains exactly, just with the extra `TyInst`s real typed builtins need
that untyped UPLC's `force` doesn't distinguish.
-/

def dataFieldsTy : Tplc.Ty := .app (.builtin .list) (.builtin .data)

def constrTagTerm (blob : Tplc.Term) : Tplc.Term :=
  .apply (.tyInst (.tyInst (.builtin .fstPair) (.builtin .integer)) dataFieldsTy)
    (.apply (.builtin .unConstrData) blob)

def fieldsOfTerm (blob : Tplc.Term) : Tplc.Term :=
  .apply (.tyInst (.tyInst (.builtin .sndPair) (.builtin .integer)) dataFieldsTy)
    (.apply (.builtin .unConstrData) blob)

def applyTailListN : Nat → Tplc.Term → Tplc.Term
  | 0, t => t
  | n + 1, t => applyTailListN n (.apply (.tyInst (.builtin .tailList) (.builtin .data)) t)

def fieldAtTerm (n : Nat) (blob : Tplc.Term) : Tplc.Term :=
  .apply (.tyInst (.builtin .headList) (.builtin .data)) (applyTailListN n (fieldsOfTerm blob))

/-!
## Recursion: the typed isorecursive fixpoint combinator

`Poe.Translate`'s untyped self-application `x x` (the Z-combinator) is
ill-typed here — `x`'s type would need to structurally contain its own
function type. The classic fix (TAPL ch. 20, "Recursive Types"): a
one-constructor recursive type `SelfTy` whose *unwrapping* gives back
`SelfTy -> T`, so `(unwrap x) x` type-checks as a genuine value of type
`T` despite `T` itself having nothing to do with `SelfTy`.

`fixPat`/`fixArg`/`selfTy` implement `PlutusCore/StdLib/Type.hs`'s own
`makeRecursiveType0` recipe (a *0-ary* pattern functor — `T` itself is
the "index", not a further type parameter). `typedFix`'s self-application
is *guarded* (delayed behind one extra lambda over the function's own
first argument) for the same reason `Poe.Translate.zCombinator`'s own
`λv. (x x) v` is: verified directly against `plc` that the *unguarded*
textbook version loops forever under call-by-value (it OOM-killed the
`plc` process at 57GB resident before this guard was added), while the
guarded version both type-checks as `(T -> T) -> T` and terminates
correctly on a standalone countdown-function test.
-/

/-- The fixed 0-ary pattern functor `\(rec :: (*->*) -> *) (f :: *->*) ->
    f (rec f)` — the same regardless of `T`; only `fixArg` varies. -/
def fixPat : Tplc.Ty :=
  .lam (.arrow (.arrow .type .type) .type)
    (.lam (.arrow .type .type) (.app (.var 0) (.app (.var 1) (.var 0))))

/-- `\(dataName :: *) -> dataName -> t` — `t` must be a *closed* `Ty` (no
    free `Ty.var`s): it gets embedded under this fresh binder with no
    reshifting, which `translateDecl` guarantees by only calling this for
    non-generic recursive decls (see file doc comment). -/
def fixArg (t : Tplc.Ty) : Tplc.Ty :=
  .lam .type (.fn (.var 0) t)

/-- `ifix fixPat (fixArg t)` — unwrapping a value of this type gives back
    `selfTy t -> t` (confirmed directly against `plc`), letting
    `(unwrap x) x` type-check as a genuine value of type `t`. -/
def selfTy (t : Tplc.Ty) : Tplc.Ty :=
  .ifix fixPat (fixArg t)

/-- The typed fixpoint combinator: `(t -> t) -> t`. `argTy` is `t`'s
    *first* argument type (`t` may itself be a multi-argument curried
    function) — the guard only needs to delay behind *one* lambda,
    regardless of `t`'s arity, since that alone already stops the
    self-application from forcing itself before `f` is ever called
    (matching `Poe.Translate.zCombinator`'s own single-argument guard). -/
def typedFix (t argTy : Tplc.Ty) : Tplc.Term :=
  -- de Bruijn bookkeeping (term-level depth only; no type-level binders
  -- here): `f` is bound one level out (index 1 inside `x`'s lambda, sole
  -- reference site is right before `v`'s lambda, hence index 1 there
  -- too); `x` (bound by `selfApp`'s own lambda) is referenced twice
  -- inside `v`'s lambda body, both at index 1 (one level further in);
  -- `v` itself is index 0.
  let selfApp : Tplc.Term :=
    .lamAbs (selfTy t)
      (.apply (.var 1)
        (.lamAbs argTy
          (.apply (.apply (.unwrap (.var 1)) (.var 1)) (.var 0))))
  .lamAbs (.fn t t) (.apply selfApp (.iwrap fixPat (fixArg t) selfApp))

/-!
## `decodeByteStringList`: a bespoke native-list-decode intrinsic

Same role as `Poe.Translate.decodeByteStringListTerm` (both are
special-cased by name in `translateConstCall`, not translated from
`Poe.PlutusData.decodeByteStringList`'s own placeholder Lean body) — but
here `Term.case`'s native support for scrutinizing a *builtin* `list`
directly (confirmed against the real type-checker's own
`annotateCaseBuiltin`/`caseBuiltin` instances in
`PlutusCore/Default/Universe.hs`, and independently against `plc`) means
no `headList`/`tailList`/`nullList` loop is needed at all — just a
`Case` with branches in `[cons, nil]` order (cons a 2-argument lambda,
nil a bare term), the exact same convention `Poe.Translate`'s own
native-list `case` already uses. -/

def nativeListOfDataTy : Tplc.Ty := .app (.builtin .list) (.builtin .data)

/-- Body of `λself. λlst. case lst [consBranch, nilBranch]`, building an
    ordinary SoP-`constr`/`IWrap`-encoded `List elemTy` as it goes (so
    everything downstream of this one primitive is back in the regular
    fragment) — `self`/`lst` at depth 2 (self index 1, lst index 0);
    inside the cons branch, two more binders shift everything already
    bound by 2 (h index 1, t index 0, self now index 3). -/
def dataListLoopBody (elemTy : Tplc.Ty) : Tplc.Term :=
  let consBranch :=
    Tplc.Term.lamAbs (.builtin .data) (.lamAbs nativeListOfDataTy
      (.iwrap listPatFunctor elemTy
        (.constr (listUnrolledSop elemTy) 1
          [.apply (.builtin .unBData) (.var 1), .apply (.var 3) (.var 0)])))
  let nilBranch := Tplc.Term.iwrap listPatFunctor elemTy (.constr (listUnrolledSop elemTy) 0 [])
  .case (listTy elemTy) (.var 0) [consBranch, nilBranch]

/-- `λd. (fix loop) (unListData d)`. -/
def decodeByteStringListTerm : Tplc.Term :=
  let bsTy := Tplc.Ty.builtin .bytestring
  let t := Tplc.Ty.fn nativeListOfDataTy (listTy bsTy)
  let loopF := Tplc.Term.lamAbs t (.lamAbs nativeListOfDataTy (dataListLoopBody bsTy))
  .lamAbs (.builtin .data)
    (.apply (.apply (typedFix t nativeListOfDataTy) loopF) (.apply (.builtin .unListData) (.var 0)))

/-- A type-former `Param`'s own type is bound directly (`Ty.var`, via
    `Ctx.lookupTy`); a concrete base type comes from `builtinTyTable`;
    `List α` recurses into `listTy` — no other user-defined
    inductives/type applications yet (out of fragment, same incremental
    spirit as `Poe.Translate`'s own `translateArg`). `Decidable ◾` (a
    `let`-bound `Int.decLt`/`Int.decEq`/...'s own LCNF type, its `Prop`
    argument already erased) is a runtime bool by Lean's own convention
    regardless of *which* proposition it decides — same reasoning as
    `translateCode`'s `.cases` handling collapsing
    `Decidable.isFalse`/`isTrue` into the `Bool` case. -/
partial def translateTy (ctx : Ctx) : Expr → CoreM Tplc.Ty
  | .fvar fvarId => return .var (← ctx.lookupTy fvarId)
  | .const declName _ =>
    match builtinTyTable.lookup declName with
    | some b => return .builtin b
    | none => throwError "translateTplc: unsupported type {declName} (out of fragment)"
  -- A non-dependent arrow (LCNF's own erased types never depend on the
  -- bound value, so `cod` never actually mentions it) — needed to
  -- translate a whole recursive decl's own `Decl.type` (its full curried
  -- function type, confirmed directly to include every param: dumping
  -- `sumList2 : List Int -> Int`'s base LCNF `decl.type` gives back
  -- exactly `List Int -> Int`, not just the result `Int`) in one call.
  | .forallE _ dom cod _ => return .fn (← translateTy ctx dom) (← translateTy ctx cod)
  | e =>
    if e.isAppOf ``Decidable then
      return .builtin .bool
    else if e.isAppOfArity ``List 1 then
      return listTy (← translateTy ctx e.appArg!)
    -- `{x : α // p x}` erases to exactly `α`'s own representation — `p`'s
    -- own argument is already `lcErased` by base phase (confirmed
    -- directly: `vlength`'s `v : Subtype (List X) lcErased`), matching
    -- `Subtype.mk`'s runtime shape once its `Prop`-sorted `property`
    -- field is dropped: there's no wrapper left at all, just the
    -- carrier value.
    else if e.isAppOfArity ``Subtype 2 then
      translateTy ctx e.getAppArgs[0]!
    -- `Vec X n`'s index `n` carries no runtime content (never referenced
    -- by any real computation over a `Vec` — the same "forcing" situation
    -- as `Subtype`'s own erased proof, just a real `Nat` instead of a
    -- `Prop`), so it's dropped entirely and `Vec X n` compiles to exactly
    -- `listTy X` — reusing `List`'s own ifix/iwrap machinery rather than a
    -- fresh, indexed pattern functor.
    else if e.isAppOfArity `Poe.Experiments.VecScratch.Vec 2 then
      return listTy (← translateTy ctx e.getAppArgs[0]!)
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

/-- A single value argument, `Poe.Translate.translateArg`'s typed
    counterpart — used by the `Data`-accessor special cases below, which
    (unlike `applyArgsTplc`) build a bespoke term around their one
    argument rather than a plain `Term.apply` chain. -/
def translateArgTplc (ctx : Ctx) : Arg → CoreM Tplc.Term
  | .fvar fvarId => return .var (← ctx.lookupTerm fvarId)
  | .erased | .type _ =>
    throwError "translateTplc: erased/type argument reached a Data accessor (out of fragment)"

/-- Same definition as `Poe.Translate.singleRealAlt` (duplicated, same
    reason `codeMentionsSelf` below is): a joint match against an erased
    shape proof rules out every `Data`/native-list constructor but one,
    compiling the rest to `Code.unreach`. Real TPLC `Case` can't dispatch
    on a builtin `data` value either (same `annotateCaseBuiltin` rules the
    untyped fragment's finding rests on), so this backend's `Data` cases
    handling below trusts the single live branch the same way. -/
def singleRealAlt (cases : Cases) : CoreM (Name × Array Param × Code) := do
  let isUnreach : Alt → Bool
    | .alt _ _ (.unreach _) => true
    | .default (.unreach _) => true
    | _ => false
  match cases.alts.filter (!isUnreach ·) with
  | #[.alt ctorName params code] => return (ctorName, params, code)
  | alts => throwError "translateTplc: cases on {cases.typeName} has {alts.size} reachable alternatives, need exactly 1 (out of fragment)"

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

/-- Calls that don't fit the flat builtin-table shape: a self-recursive
    call goes through the fixpoint's `self` binder (matching
    `Poe.Translate.translateConstCall`'s own check); `Int.ofNat`/`Int.neg`
    as in `Poe.Translate`; anything else is another top-level decl,
    translated (and applied/instantiated) in turn. -/
partial def translateConstCall (ctx : Ctx) (declName : Name) (args : Array Arg) : CoreM Tplc.Term := do
  if let some (selfName, selfDepth) := ctx.self then
    if declName == selfName then
      return ← applyArgsTplc ctx (.var (ctx.termDepth - 1 - selfDepth)) args
  -- Ghost (`Prop`-typed) arguments — e.g. `Poe.PlutusData.field0`'s new
  -- `HasFieldAt d 0` precondition — must be dropped before the
  -- arity-based match below, matching `applyArgsTplc`'s own erasure;
  -- unlike `.type` (never relevant to these monomorphic accessors), an
  -- unfiltered `.erased` here silently breaks the `#[a]` arity match.
  let args := args.filter fun | .erased => false | _ => true
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
  -- `abort`'s Lean type is the concrete `Unit → Unit`, never instantiated
  -- at any other type, so its own result `Ty` needs no lookup at all.
  | ``Poe.Prelude.abort, _ => return .error (.builtin .unit)
  -- `Bool`/`Unit` are the *builtin* constants everywhere (matching
  -- `translateTy`'s own `Decidable`-collapses-to-`bool` reasoning and
  -- `.cases`'s Bool/Decidable handling), not SOP `constr` values like
  -- `List` — same special-casing `Poe.Translate.translateConstCall`
  -- already needs for exactly the same reason (a `true`/`false`/`()`
  -- literal reaches here as an ordinary 0-arg constructor application,
  -- not through `.cases` at all).
  | ``Bool.false, #[] => return .constant (.bool false)
  | ``Bool.true, #[] => return .constant (.bool true)
  -- `Decidable.isFalse`/`Decidable.isTrue` each carry exactly one
  -- `Prop`-sorted field (`¬p`/`p`), already dropped by the `args` filter
  -- above — so, same as `Bool`'s own constructors, there's nothing left
  -- to build once erased. Matches `translateCode`'s existing `.cases`
  -- handling, which already treats `Decidable` cases identically to
  -- `Bool` on the consuming side; this is the same collapse on the
  -- constructing side.
  | ``Decidable.isFalse, #[] => return .constant (.bool false)
  | ``Decidable.isTrue, #[] => return .constant (.bool true)
  | ``PUnit.unit, #[] => return .constant .unit
  -- `Poe.PlutusData`'s accessors are opaque/self-recursive placeholder
  -- bodies (e.g. `field0 d := field0 d`) never meant to be translated
  -- literally — special-cased by name exactly like
  -- `Poe.Translate.translateConstCall` already has to, or the typed
  -- translator would (now that recursion is wired in) happily compile
  -- the placeholder body into a well-typed term that loops forever.
  | ``Poe.PlutusData.constrTag, #[a] => return constrTagTerm (← translateArgTplc ctx a)
  | ``Poe.PlutusData.field0, #[a] => return fieldAtTerm 0 (← translateArgTplc ctx a)
  | ``Poe.PlutusData.field1, #[a] => return fieldAtTerm 1 (← translateArgTplc ctx a)
  | ``Poe.PlutusData.field2, #[a] => return fieldAtTerm 2 (← translateArgTplc ctx a)
  | ``Poe.PlutusData.field8, #[a] => return fieldAtTerm 8 (← translateArgTplc ctx a)
  | ``Poe.PlutusData.decodeByteStringList, #[a] =>
    return .apply decodeByteStringListTerm (← translateArgTplc ctx a)
  | _, _ =>
    if let some (.ctorInfo info) := (← getEnv).find? declName then
      -- Only `List`'s two constructors, for now (see file doc comment) —
      -- any other inductive's constructor is out of fragment. Unlike
      -- `Poe.Translate`'s untyped `constr` (a bare tag + fields, no type
      -- needed at all), a *typed* `Constr` needs the concrete, unrolled
      -- SOP `Ty` — which needs the element type, recovered from the
      -- constructor's own `Arg.type` (e.g. `@List.cons Int head tail`) —
      -- and the whole thing wrapped in `IWrap` to actually produce a
      -- `List elemTy`-typed value, confirmed directly against `plc`.
      if info.induct == ``List then
        let some elemTyExpr := args.toList.findSome? fun | .type e => some e | _ => none
          | throwError "translateTplc: {declName} missing its element-type argument"
        let elemTy ← translateTy ctx elemTyExpr
        let fields ← (args.toList.filterMap fun | .fvar fvarId => some fvarId | _ => none).mapM
          fun fvarId => return Tplc.Term.var (← ctx.lookupTerm fvarId)
        return .iwrap listPatFunctor elemTy (.constr (listUnrolledSop elemTy) info.cidx fields)
      -- `Vec X n` compiles to exactly `listTy X` (see `translateTy`'s own
      -- `Vec` case) — `Vec.cons`'s own signature is `{n : Nat} → X → Vec X
      -- n → Vec X (n+1)`, so its *first* fvar field is always the index,
      -- dropped for the same reason `translateTy` drops it: no runtime
      -- content, never referenced by any real computation over a `Vec`.
      else if info.induct == `Poe.Experiments.VecScratch.Vec then
        let some elemTyExpr := args.toList.findSome? fun | .type e => some e | _ => none
          | throwError "translateTplc: {declName} missing its element-type argument"
        let elemTy ← translateTy ctx elemTyExpr
        let allFields ← (args.toList.filterMap fun | .fvar fvarId => some fvarId | _ => none).mapM
          fun fvarId => return Tplc.Term.var (← ctx.lookupTerm fvarId)
        let fields := if declName == `Poe.Experiments.VecScratch.Vec.cons then allFields.drop 1 else allFields
        return .iwrap listPatFunctor elemTy (.constr (listUnrolledSop elemTy) info.cidx fields)
      else
        throwError "translateTplc: constructors of {info.induct} not yet handled (only List/Vec, out of fragment)"
    else
      match builtinTable.lookup declName with
      | some b => applyArgsTplc ctx (.builtin b) args
      | none => do
        let callee ← translate declName
        applyArgsTplc ctx callee args

/-- Other `LetValue` shapes (non-self local application) aren't needed by
    the examples so far, same restriction as `Poe.Translate.translateLetValue`.
    `.proj Subtype 0 struct` (`.val`) is the one projection that *is*
    needed — `Subtype.mk`'s `Prop`-sorted `property` field (index 1)
    already carries no runtime content, so the whole structure erases to
    exactly its `val`, and projecting it back out is the identity on
    whatever `struct` already compiled to (matching `translateTy`'s own
    `Subtype` case, which drops the wrapper the same way). A `.proj` on
    `property` itself would mean a `Prop` value reached a computation
    position, which shouldn't happen in valid fragment code — no example
    needs it, so it's left as a clear error rather than guessed at. -/
partial def translateLetValue (ctx : Ctx) : LetValue → CoreM Tplc.Term
  | .const declName _us args => translateConstCall ctx declName args
  | .lit (.nat n) => return .constant (.integer (Int.ofNat n))
  | .lit (.str s) => return .constant (.string s)
  | .lit .. => throwError "translateTplc: only Nat/String literals are handled so far"
  | .fvar .. => throwError "translateTplc: local (non-self) application not yet handled"
  | .proj ``Subtype 0 struct => return .var (← ctx.lookupTerm struct)
  | .proj typeName idx _ =>
    throwError "translateTplc: projection {idx} of {typeName} not yet handled (out of fragment)"
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
  -- A join point is just a local (non-recursive, here — no example needs
  -- a self-referencing one yet) function shared by multiple call sites —
  -- `Decidable.rec`/`And.decidable`-shaped control flow generates these
  -- for the common `isTrue`/`isFalse` continuation multiple branches jump
  -- to, confirmed directly by dumping `validatorBDecidable`'s base LCNF.
  -- Translated exactly like `.let` (`.apply (.lamAbs ty body) value`),
  -- just with the bound value being a lambda instead of a computed term;
  -- `.jmp` is then an ordinary application to it, via the same
  -- `applyArgsTplc` every other call site uses.
  | .jp decl k => do
    let jpParams := decl.params.filter fun p => !p.type.isErased
    let jpCtx := jpParams.foldl (init := ctx) (·.bindTerm ·.fvarId)
    let jpBody ← translateCode jpCtx decl.value
    let jpLam ← jpParams.foldrM (init := jpBody) fun p acc =>
      return Tplc.Term.lamAbs (← translateTy ctx p.type) acc
    -- `decl.type` is already the join point's own full curried function
    -- type (`param → ... → result`), confirmed directly by dumping it —
    -- not just the result type the way it first looked from the pretty
    -- printer eliding params from the `: TYPE` annotation.
    let jpTy ← translateTy ctx decl.type
    let body ← translateCode (ctx.bindTerm decl.fvarId) k
    return .apply (.lamAbs jpTy body) jpLam
  | .jmp fvarId args => do applyArgsTplc ctx (.var (← ctx.lookupTerm fvarId)) args
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
    else if cases.typeName == ``Nat then
      -- A literal-tag match (`.constr 0 [...]`) compiles, at base phase,
      -- to a genuine `cases` on `Nat` itself (`Nat.zero`/`Nat.succ`) — the
      -- mono-phase-only `Nat.decEq`+`Bool` collapse hasn't happened yet
      -- (confirmed directly: dumping `validatorB`'s base LCNF shows `cases
      -- a.1 : Bool | Nat.zero => ... | Nat.succ n => ⊥`). `Nat` is a
      -- builtin `integer` at runtime, not an SoP value, so real `Case`
      -- can't dispatch on it either — same trust-the-single-live-branch
      -- strategy as `Data` below, not a runtime `equalsInteger` check.
      let (ctorName, allParams, code) ← singleRealAlt cases
      let params := allParams.filter fun p => !p.type.isErased
      let discrTerm := Tplc.Term.var (← ctx.lookupTerm cases.discr)
      match ctorName, params with
      | ``Nat.zero, #[] => translateCode ctx code
      | ``Nat.succ, #[predParam] =>
        let body ← translateCode (ctx.bindTerm predParam.fvarId) code
        return .apply (.lamAbs (.builtin .integer) body)
          (.apply (.apply (.builtin .subtractInteger) discrTerm) (.constant (.integer 1)))
      | _, _ => throwError "translateTplc: unexpected Nat constructor {ctorName}"
    else if cases.typeName == ``Poe.PlutusData.Data then
      -- Same reasoning as `Poe.Translate.translateCode`'s `Data` case:
      -- every real use is guarded by an erased shape proof (exactly one
      -- live branch, the rest `Code.unreach`), and real `Case` can't
      -- dispatch on a builtin `data` value at all — so trust the one
      -- live branch and apply the matching `un*Data` accessor directly.
      -- `constr`'s field list is `nativeListOfDataTy`, *not* whatever
      -- `translateTy` would derive from the Lean `List Data` type (that's
      -- the different, `IWrap`-encoded `listTy`) — marked native so a
      -- further destructure below picks the matching `case` convention.
      let (ctorName, allParams, code) ← singleRealAlt cases
      let params := allParams.filter fun p => !p.type.isErased
      let discrTerm := Tplc.Term.var (← ctx.lookupTerm cases.discr)
      match ctorName, params with
      | ``Poe.PlutusData.Data.constr, #[tagParam, fieldsParam] =>
        let ctx' := ((ctx.bindTerm tagParam.fvarId).bindTerm fieldsParam.fvarId).markNative fieldsParam.fvarId
        let body ← translateCode ctx' code
        let curried := Tplc.Term.lamAbs (.builtin .integer) (.lamAbs nativeListOfDataTy body)
        -- Both values apply as siblings of the lambdas they fill (not
        -- nested inside an inner lambda's body), matching
        -- `Poe.Translate`'s own fix for the same de Bruijn hazard.
        return #[constrTagTerm discrTerm, fieldsOfTerm discrTerm].foldl .apply curried
      | ``Poe.PlutusData.Data.b, #[byteParam] =>
        let body ← translateCode (ctx.bindTerm byteParam.fvarId) code
        return .apply (.lamAbs (.builtin .bytestring) body) (.apply (.builtin .unBData) discrTerm)
      | ``Poe.PlutusData.Data.list, #[listParam] =>
        let body ← translateCode ((ctx.bindTerm listParam.fvarId).markNative listParam.fvarId) code
        return .apply (.lamAbs nativeListOfDataTy body) (.apply (.builtin .unListData) discrTerm)
      | ``Poe.PlutusData.Data.i, _ =>
        throwError "translateTplc: Data.i (integer-as-Data) not yet handled (out of fragment)"
      | _, _ => throwError "translateTplc: unexpected Data constructor {ctorName}"
    else if cases.typeName == ``List && ctx.isNative cases.discr then
      -- Native builtin list (see `Ctx.nativeListVars`): unlike the
      -- `IWrap`-encoded `List` handled below, this needs no `unwrap` (it's
      -- not a recursive-type value at all, just `list data`), and the
      -- element/tail binders need the native `Ty`s, not whatever
      -- `translateTy` would derive from the Lean types.
      let some (.alt _ consParams consCode) :=
          cases.alts.find? (fun | .alt n .. => n == ``List.cons | .default _ => false)
        | throwError "translateTplc: native List cases missing a List.cons alternative"
      let some nilAlt :=
          cases.alts.find? (fun | .alt n .. => n == ``List.nil | .default _ => false)
            <|> cases.alts.find? (fun | .default _ => true | _ => false)
        | throwError "translateTplc: native List cases missing a List.nil alternative (no default either)"
      let #[headParam, tailParam] := consParams.filter fun p => !p.type.isErased
        | throwError "translateTplc: native List.cons alt has unexpected (erased-mixed) param shape"
      let nilBranch ← translateCode ctx nilAlt.getCode
      let consCtx := ((ctx.bindTerm headParam.fvarId).bindTerm tailParam.fvarId).markNative tailParam.fvarId
      let consBody ← translateCode consCtx consCode
      let consBranch := Tplc.Term.lamAbs (.builtin .data) (.lamAbs nativeListOfDataTy consBody)
      let resultTy ← translateTy ctx cases.resultType
      let scrutinee := Tplc.Term.var (← ctx.lookupTerm cases.discr)
      return .case resultTy scrutinee [consBranch, nilBranch]
    else if cases.typeName == ``List then
      let some nilAlt := cases.alts.find? (fun | .alt n .. => n == ``List.nil | .default _ => false)
        | throwError "translateTplc: List cases missing a List.nil alternative"
      let some (.alt _ consParams consCode) :=
          cases.alts.find? (fun | .alt n .. => n == ``List.cons | .default _ => false)
        | throwError "translateTplc: List cases missing a List.cons alternative"
      let #[headParam, tailParam] := consParams
        | throwError "translateTplc: List.cons alternative has the wrong number of fields"
      -- 0-field `nil` branch is a bare term (no wrapping), matching real
      -- `Case`'s own calling convention — same rule `Poe.Translate`'s own
      -- SOP `case` handling already relies on for 0-field constructors.
      let nilBranch ← translateCode ctx nilAlt.getCode
      let consCtx := (ctx.bindTerm headParam.fvarId).bindTerm tailParam.fvarId
      let consBody ← translateCode consCtx consCode
      let headTy ← translateTy ctx headParam.type
      let tailTy ← translateTy ctx tailParam.type
      let consBranch := Tplc.Term.lamAbs headTy (.lamAbs tailTy consBody)
      let resultTy ← translateTy ctx cases.resultType
      let scrutinee := Tplc.Term.unwrap (.var (← ctx.lookupTerm cases.discr))
      -- Branch order = declaration order (`nil` = 0, `cons` = 1), same
      -- convention `Poe.Translate`'s own `ctorNames`-ordered `case` uses.
      return .case resultTy scrutinee [nilBranch, consBranch]
    -- Same shape as `List`'s own case just above — `Vec X n` compiles to
    -- `listTy X`, so `case` works on it directly the same way, no
    -- builtin-type limitation the way `Data`/`Nat` have. Only difference:
    -- `Vec.cons`'s own params are `[index, head, tail]` (see
    -- `translateConstCall`'s matching `Vec.cons` handling), so the index
    -- is dropped here too rather than bound.
    else if cases.typeName == `Poe.Experiments.VecScratch.Vec then
      let some nilAlt :=
          cases.alts.find? (fun | .alt n .. => n == `Poe.Experiments.VecScratch.Vec.nil | .default _ => false)
        | throwError "translateTplc: Vec cases missing a Vec.nil alternative"
      let some (.alt _ consParams consCode) :=
          cases.alts.find? (fun | .alt n .. => n == `Poe.Experiments.VecScratch.Vec.cons | .default _ => false)
        | throwError "translateTplc: Vec cases missing a Vec.cons alternative"
      let #[_indexParam, headParam, tailParam] := consParams
        | throwError "translateTplc: Vec.cons alternative has the wrong number of fields"
      let nilBranch ← translateCode ctx nilAlt.getCode
      let consCtx := (ctx.bindTerm headParam.fvarId).bindTerm tailParam.fvarId
      let consBody ← translateCode consCtx consCode
      let headTy ← translateTy ctx headParam.type
      let tailTy ← translateTy ctx tailParam.type
      let consBranch := Tplc.Term.lamAbs headTy (.lamAbs tailTy consBody)
      let resultTy ← translateTy ctx cases.resultType
      let scrutinee := Tplc.Term.unwrap (.var (← ctx.lookupTerm cases.discr))
      return .case resultTy scrutinee [nilBranch, consBranch]
    else
      throwError "translateTplc: cases on {cases.typeName} not yet handled (out of fragment)"
  | _ => throwError "translateTplc: unsupported Code constructor (not yet handled)"

/-- Fragment restrictions: type-former params precede all value params
    (see file doc comment) — a single left-to-right ctx-build pass then
    doubles as the scope every value param's own `Ty` translation needs,
    since by that restriction no type param can follow the value param
    whose annotation is being translated; recursive decls must be
    non-generic (no type-former params at all). -/
partial def translateDecl (decl : Decl) : CoreM Tplc.Term := do
  let .code code := decl.value
    | throwError "translateTplc: extern declarations are not in the fragment"
  -- Ghost (`Prop`-typed, hence `lcErased`) params — e.g. a `y ≠ 0` proof —
  -- get no binder at all, matching `applyArgsTplc`'s `.erased` case at
  -- every call site (same necessity `Poe.Translate.translateDecl`'s own
  -- identical filter documents: without it, a param whose type is
  -- `lcErased` itself would reach `translateTy` and fail outright, since
  -- `lcErased` isn't a real `Ty`). *Also* drop params whose type is
  -- itself `Prop`/`A → Prop` (`isPropFormerTypeQuick`) — a genuinely new
  -- case base phase needs that mono phase never surfaces: confirmed
  -- directly by dumping `Decidable.decide (p : Prop) [h : Decidable p]`,
  -- where `p`'s own type *is* `Sort 0`, so `isTypeFormerType` alone
  -- would (wrongly) treat it as a real `tyAbs` binder — but call sites
  -- pass `p` as `Arg.erased`, not `Arg.type` (Props carry no runtime
  -- content, unlike a genuine `Type`-sorted argument), so an unfiltered
  -- `p` produces a decl/call-site arity mismatch (an extra leading
  -- `tyAbs` no caller ever instantiates).
  let params := decl.params.filter fun p =>
    !p.type.isErased && !Compiler.LCNF.isPropFormerTypeQuick p.type
  if codeMentionsSelf decl.name code then
    if params.any fun p => Compiler.LCNF.isTypeFormerType p.type then
      throwError "translateTplc: {decl.name} is a generic recursive decl — not yet supported (fixArg would need to embed T under a fresh binder with reshifting; see file doc comment)"
    let some firstParam := params[0]?
      | throwError "translateTplc: {decl.name} is recursive but takes no parameters"
    -- `Decl.type` is the whole curried function type (confirmed
    -- directly: `sumList2 : List Int -> Int`'s base LCNF `decl.type` is
    -- exactly `List Int -> Int`, not just the result `Int`), so one
    -- `translateTy` call gives `T` directly.
    let t ← translateTy {} decl.type
    let argTy ← translateTy {} firstParam.type
    -- `self` is bound *before* the real params (matching
    -- `Poe.Translate.translateDecl`'s own `ctx0 := { depth := 1, self :=
    -- some (decl.name, 0) }`), so a self-call resolves to the fixpoint's
    -- own outer binder rather than the builtin/callee lookup.
    let ctx0 : Ctx := { termDepth := 1, self := some (decl.name, 0) }
    let ctx := params.foldl (init := ctx0) (·.bindTerm ·.fvarId)
    let body ← translateCode ctx code
    let paramsBody ← params.foldrM (init := body) fun p acc =>
      return Tplc.Term.lamAbs (← translateTy ctx p.type) acc
    return .apply (typedFix t argTy) (.lamAbs t paramsBody)
  else
    let ctx := params.foldl (init := ({} : Ctx)) fun ctx p =>
      if Compiler.LCNF.isTypeFormerType p.type then ctx.bindTy p.fvarId else ctx.bindTerm p.fvarId
    let body ← translateCode ctx code
    params.foldrM (init := body) fun p acc =>
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
