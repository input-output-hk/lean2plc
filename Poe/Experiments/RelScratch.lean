import Poe.Tplc
import Poe.TranslateTplc
import Poe.Bridge
import Poe.Examples.VecScratch
import Poe.Examples.First
import Poe.Examples.TplcFirst

#eval show Lean.CoreM Unit from do
  let t ← Poe.TranslateTplc.translate ``Poe.Examples.genericId
  IO.println (repr t)

def idList {α : Type} (xs : List α) : List α := xs

#eval show Lean.CoreM Unit from do
  let t ← Poe.TranslateTplc.translate ``idList
  IO.println (repr t)

/-!
Scratch: a Fig.-4-style logical relation over `Poe.Tplc.Ty`, restricted
to the arrow/forall core (`ifix` deferred — see the earlier discussion).
First check: does it even typecheck (yes, confirmed already). Next:
attempt it for `double`, self-related at its own (monomorphic) type —
this won't exercise `forall_` at all, since `double : Int → Int` isn't
polymorphic, but it's the right first check that the relation's
"apply and compare" plumbing is real, not a stand-in.
-/

namespace Poe.Examples.RelScratch

open Poe.Bridge Poe.Examples.VecScratch
open PlutusCore.UPLC PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue

abbrev RelEnv := List (CekValue → CekValue → Prop)

/-- `f` applied to `v`, as a CEK state: push the one frame that consumes
    a function value against an already-computed argument value (the
    same `RightApplicationOfValue` rule `head_certificate`'s own proof
    already exercised), then let it run. Reaching `Halt` here means
    exactly what reaching `Halt` from `cekExecuteProgram` means, just
    starting from two already-evaluated values instead of a program. -/
def applyValue (f v : CekValue) : State := State.Return [Frame.RightApplicationOfValue f] v

/-- `f` forced, as a CEK state — the real counterpart of `applyValue` for
    the `forall_` clause, needed because real Plutus erases `TyAbs` to
    `Delay` (confirmed directly against `plutus-metatheory`'s own erasure
    map), so a genuinely polymorphic value's erased form is a *delayed*
    computation that must be forced before it does anything. -/
def forceValue (f : CekValue) : State := State.Return [Frame.ForceFrame] f

/-- Only the two clauses that map directly onto Fig. 4 (`fn`, `forall_`);
    every other `Ty` constructor is a placeholder for now. `ifix`
    (isorecursive types) is the genuinely hard, deliberately-deferred
    case — recursing into `F[ifix F X/X]` isn't structurally smaller, so
    it needs step-indexing, not plain structural recursion. -/
def R : Poe.Tplc.Ty → RelEnv → CekValue → CekValue → Prop
  | .var i, ρ, v, w => (ρ.get? i).getD (fun _ _ => False) v w
  | .fn A B, ρ, f, g =>
      ∀ v w, R A ρ v w →
        ∃ (n m : Nat) (f' g' : CekValue),
          iterate default (applyValue f v) n = State.Halt f' ∧
          iterate default (applyValue g w) m = State.Halt g' ∧
          R B ρ f' g'
  | .forall_ _k B, ρ, f, g =>
      ∀ (R' : CekValue → CekValue → Prop),
        ∃ (n m : Nat) (f' g' : CekValue),
          iterate default (forceValue f) n = State.Halt f' ∧
          iterate default (forceValue g) m = State.Halt g' ∧
          R B (R' :: ρ) f' g'
  | .ifix _ _, _, _, _ => True
  | .builtin .integer, _, v, w => ∃ i, v = .VCon (.Integer i) ∧ w = .VCon (.Integer i)
  | .builtin _, _, v, w => v = w
  | .lam _ _, _, _, _ => True
  | .app _ _, _, _, _ => True
  | .sop _, _, _, _ => True

/-- `double`'s own compiled closure, evaluated once (no argument yet) —
    the value `toBlasterProgram doubleProgram`'s term reduces to. -/
def doubleFuncValue : CekValue :=
  .VLam "x0"
    (Term.Term.Apply (Term.Term.Lam "x1" (Term.Term.Var 0))
      (Term.Term.Apply (Term.Term.Apply (Term.Term.Builtin Term.BuiltinFun.AddInteger)
        (Term.Term.Var 0)) (Term.Term.Var 0)))
    []

/-- `double` is self-related at its own type — the intended first check.
    Reduces almost entirely to `double_certificate` plus the fact that
    evaluation is a plain Lean function (hence automatically
    deterministic) — no real `forall_` content yet, since `double` isn't
    polymorphic; that's the honest limit of this example. -/
theorem applyValue_double :
    iterate default (applyValue doubleFuncValue (.VCon (.Integer i))) 20
      = State.Halt (.VCon (.Integer (Poe.Examples.double i))) := by
  simp [iterate, step, applyValue, doubleFuncValue, Poe.Examples.double,
    PlutusCore.UPLC.Builtins.expectedArgs, PlutusCore.UPLC.CekMachine.evalBuiltin,
    PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    PlutusCore.UPLC.BuiltinFunctions.Integer.addInteger, PlutusCore.Integer.addInteger]

theorem double_self_related :
    R (.fn (.builtin .integer) (.builtin .integer)) [] doubleFuncValue doubleFuncValue := by
  intro v w hvw
  simp only [R] at hvw
  obtain ⟨i, hv, hw⟩ := hvw
  subst hv; subst hw
  refine ⟨20, 20, .VCon (.Integer (Poe.Examples.double i)), .VCon (.Integer (Poe.Examples.double i)),
    applyValue_double, applyValue_double, ?_⟩
  simp [R]

#print axioms double_self_related

/-!
## `genericId` — the real `forall_` content, finally exercised

`genericId`'s real TPLC term (confirmed directly, not guessed, via
`Poe.TranslateTplc.translate`): `tyAbs Kind.type (lamAbs (Ty.var 0)
(Term.var 0))`. Erasing per the real Plutus rule (`TyAbs t ↦ delay
(erase t)`, confirmed earlier against `plutus-metatheory`) gives `Delay
(Lam "x" (Var 0))` — a delayed identity closure, hand-transcribed the
same way every other certificate's term has been all session. -/

def genericIdValue : CekValue :=
  .VDelay (Term.Term.Lam "x" (Term.Term.Var 0)) []

theorem force_genericId :
    iterate default (forceValue genericIdValue) 3 = State.Halt (.VLam "x" (Term.Term.Var 0) []) := by
  simp [iterate, step, forceValue, genericIdValue]

theorem applyValue_id (v : CekValue) :
    iterate default (applyValue (.VLam "x" (Term.Term.Var 0) []) v) 3 = State.Halt v := by
  simp [iterate, step, applyValue]

/-- The actual free theorem: `genericId` is self-related at `∀X. X→X`,
    for *every* choice of relation `R'` — not just checked for one type,
    the full quantifier is real. Given any `R'`-related `v`/`w`, forcing
    `genericId` twice gives the same identity closure both times, and
    applying it to `v`/`w` just returns them unchanged — so the
    conclusion `R' v w` is exactly the hypothesis handed back, which is
    the free theorem "the identity preserves any relation" made literal
    and kernel-checked rather than just quoted from the paper. -/
theorem genericId_self_related :
    R (.forall_ .type (.fn (.var 0) (.var 0))) [] genericIdValue genericIdValue := by
  intro R'
  refine ⟨3, 3, .VLam "x" (Term.Term.Var 0) [], .VLam "x" (Term.Term.Var 0) [],
    force_genericId, force_genericId, ?_⟩
  intro v w hvw
  simp only [R, List.get?] at hvw ⊢
  exact ⟨3, 3, v, w, applyValue_id v, applyValue_id w, hvw⟩

#print axioms genericId_self_related

/-!
## The genuinely binary case — two *different* closures

Everything above only ever related a value to *itself*. Real doubling
(Fig. 5) is about relating two different implementations. `genericIdValue2`
below is the "let-wrapped" identity, `λx. (λy.y) x` — exactly the extra
identity-continuation wrapper `Poe.Translate.translateCode`'s `.let` case
always emits (the same wrapper shape whose omission was the real bug
`double_certificate` had to be fixed for, earlier this session).
Syntactically a different term from plain `λx.x`; behaviorally identical.
This is the first proof this file needed that isn't a disguised
self-relation. -/

def genericIdValue2 : CekValue :=
  .VDelay (Term.Term.Lam "x"
    (Term.Term.Apply (Term.Term.Lam "y" (Term.Term.Var 0)) (Term.Term.Var 0))) []

theorem force_genericId2 :
    iterate default (forceValue genericIdValue2) 3
      = State.Halt (.VLam "x" (Term.Term.Apply (Term.Term.Lam "y" (Term.Term.Var 0))
          (Term.Term.Var 0)) []) := by
  simp [iterate, step, forceValue, genericIdValue2]

theorem applyValue_id2 (v : CekValue) :
    iterate default
        (applyValue (.VLam "x" (Term.Term.Apply (Term.Term.Lam "y" (Term.Term.Var 0))
          (Term.Term.Var 0)) []) v) 10
      = State.Halt v := by
  simp [iterate, step, applyValue]

/-- The real binary content: the plain identity and the let-wrapped
    identity — two genuinely different compiled terms — are related at
    `∀X. X→X`, for every choice of relation. This is what "doubling"
    (Fig. 5) is actually for: not checking a term against itself, but
    checking that two different implementations agree, up to the
    relation, at every instantiation. -/
theorem genericId_binary_related :
    R (.forall_ .type (.fn (.var 0) (.var 0))) [] genericIdValue genericIdValue2 := by
  intro R'
  refine ⟨3, 3, .VLam "x" (Term.Term.Var 0) [],
    .VLam "x" (Term.Term.Apply (Term.Term.Lam "y" (Term.Term.Var 0)) (Term.Term.Var 0)) [],
    force_genericId, force_genericId2, ?_⟩
  intro v w hvw
  simp only [R, List.get?] at hvw ⊢
  exact ⟨3, 10, v, w, applyValue_id v, applyValue_id2 w, hvw⟩

#print axioms genericId_binary_related

/-!
## The `ifix` case, specialized to `List`

Unfolding `μX.F` one level gives `F` with itself substituted back in —
not structurally smaller than the original `ifix F A`, so plain
recursion on `Ty` (what `R` above does) can't reach this case at all.
The standard fix is *step-indexing*: recurse on a separately-decreasing
`Nat` fuel count instead. Rather than handling arbitrary `F` (which would
need a general type-level substitution/beta-reducer Poe doesn't have),
this specializes directly to `List`'s own real pattern functor
(`listPatFunctor` in `Poe.TranslateTplc`) — the concrete case that
actually matters, the same scoping discipline used all session.
`wrap`/`unwrap` erase to nothing at all (confirmed earlier against real
Plutus's own erasure map), so no CEK step is needed to "enter" a list
value — it's already just a plain `constr`-tagged value once erased. -/

def Rk : Nat → Poe.Tplc.Ty → RelEnv → CekValue → CekValue → Prop
  | 0, _, _, _, _ => True
  | k + 1, .var i, ρ, v, w => (ρ.get? i).getD (fun _ _ => False) v w
  | k + 1, .fn A B, ρ, f, g =>
      ∀ v w, Rk k A ρ v w →
        ∃ (n m : Nat) (f' g' : CekValue),
          iterate default (applyValue f v) n = State.Halt f' ∧
          iterate default (applyValue g w) m = State.Halt g' ∧
          Rk k B ρ f' g'
  | k + 1, .forall_ _kd B, ρ, f, g =>
      ∀ (R' : CekValue → CekValue → Prop),
        ∃ (n m : Nat) (f' g' : CekValue),
          iterate default (forceValue f) n = State.Halt f' ∧
          iterate default (forceValue g) m = State.Halt g' ∧
          Rk k B (R' :: ρ) f' g'
  | k + 1, .ifix F A, ρ, v, w =>
      if F == Poe.TranslateTplc.listPatFunctor then
        (v = .VConstr 0 [] ∧ w = .VConstr 0 []) ∨
        (∃ v1 vt w1 wt, v = .VConstr 1 [v1, vt] ∧ w = .VConstr 1 [w1, wt] ∧
          Rk k A ρ v1 w1 ∧ Rk k (.ifix F A) ρ vt wt)
      else True
  | k + 1, .builtin .integer, _, v, w => ∃ i, v = .VCon (.Integer i) ∧ w = .VCon (.Integer i)
  | k + 1, .builtin _, _, v, w => v = w
  | k + 1, .lam _ _, _, _, _ => True
  | k + 1, .app _ _, _, _, _ => True
  | k + 1, .sop _, _, _, _ => True

#check @Rk

/-- `idList`'s real TPLC term is `tyAbs Kind.type (lamAbs (ifix
    listPatFunctor (var 0)) (Term.var 0))` — confirmed directly via
    `Poe.TranslateTplc.translate` (see the `#eval` dump above): the same
    body as `genericId`, only the argument's *type annotation* differs,
    which erasure never looks at. So `idList` erases to the exact same
    closure, `genericIdValue` — no new term needed, only a harder type
    to check it against. -/
theorem idList_self_related :
    Rk 2 (.forall_ .type (.fn (Poe.TranslateTplc.listTy (.var 0))
      (Poe.TranslateTplc.listTy (.var 0)))) [] genericIdValue genericIdValue := by
  intro R'
  refine ⟨3, 3, .VLam "x" (Term.Term.Var 0) [], .VLam "x" (Term.Term.Var 0) [],
    force_genericId, force_genericId, ?_⟩
  intro v w hvw
  exact ⟨3, 3, v, w, applyValue_id v, applyValue_id w, hvw⟩

#print axioms idList_self_related

end Poe.Examples.RelScratch
