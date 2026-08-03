import Poe.Uplc

/-!
# Typed Plutus Core (TPLC): a second backend target

Deliberately isomorphic, constructor for constructor, to the real
`PlutusCore.Core.Type`'s `Kind`/`Type`/`Term` (checked directly against
`plutus-core/plutus-core/src/PlutusCore/Core/Type.hs`), the same
methodology `Poe.Uplc` already uses for untyped UPLC. Two backend
targets, not one: `Poe.Uplc.Term` (what `Poe.Translate` emits today,
tapping mono-phase LCNF after monomorphization has already erased
type-level polymorphism) and this one (targeting *base*-phase LCNF,
confirmed directly to still carry genuine `TyAbs`/`TyInst`-shaped
polymorphism — `@myLength _ tail` survives as a real type instantiation
in base LCNF, but has already collapsed to a single monomorphic
`myLength._redArg` by the time mono-phase is reached).

The real `eraseTerm` (`PlutusCore/Compiler/Erase.hs`) maps this typed
language down to the untyped one Poe already targets — `TyAbs`/`TyInst`
to `Delay`/`Force`, `IWrap`/`Unwrap` to nothing at all, everything else
(`Var`/`LamAbs`/`Apply`/`Constant`/`Builtin`/`Constr`/`Case`/`Error`)
across unchanged. That correspondence is why this file's `Term`
constructors are named and shaped to line up with `Poe.Uplc.Term`
one-for-one wherever the real eraser doesn't touch them, rather than
inventing a different vocabulary. -/

namespace Poe.Tplc

/-- `Type ann` in the real source (the `Type ()` constructor specifically,
    for the base/no-annotation case) vs `KindArrow`. -/
inductive Kind
  | type
  | arrow : Kind → Kind → Kind
deriving Repr, BEq

/-- The builtin *types* a `Type` can name via `TyBuiltin` — the
    real source parameterizes this over a whole builtin-type universe
    (`SomeTypeIn uni`); Poe only ever needs the handful `Poe.Uplc.Const`
    already covers, so this mirrors that enum directly rather than the
    full universe machinery. -/
inductive TyBuiltin
  | integer
  | bytestring
  | string
  | bool
  | unit
  | data
deriving Repr, BEq

/-- `TyVar i` is a de Bruijn index into the *type-level* binder stack —
    a separate scope from `Term.var`'s index into the term-level stack,
    the same two-level-scoping convention real TPLC has via distinct
    `tyname`/`name` parameters. `TySOP` (sum-of-products) is the newer
    real-PLC alternative to `TyIFix`-based recursive encodings — included
    since it's the natural type-level counterpart of `Poe.Uplc.Term`'s
    own `constr`/`case`, which is already SoP-shaped. -/
inductive Ty
  | var     : Nat → Ty
  | fn      : Ty → Ty → Ty
  | ifix    : Ty → Ty → Ty
  | forall_ : Kind → Ty → Ty
  | builtin : TyBuiltin → Ty
  | lam     : Kind → Ty → Ty
  | app     : Ty → Ty → Ty
  | sop     : List (List Ty) → Ty
deriving Repr, BEq

/-- `Var`/`LamAbs`/`Apply`/`Constant`/`Builtin`/`Constr`/`Case`/`Error`
    match `Poe.Uplc.Term`'s shape exactly (same constructors, now each
    carrying the extra `Ty` annotations the real source has, e.g.
    `LamAbs`'s parameter type, `Constr`/`Case`/`Error`'s own `Ty`) —
    exactly the ones `eraseTerm` passes through unchanged. `TyAbs`/`TyInst`
    are the new arrivals with no untyped counterpart at all (they erase
    to `Delay`/`Force`), and `IWrap`/`Unwrap` erase to nothing (pure
    type-level bookkeeping, zero runtime trace either side). -/
inductive Term
  | var     : Nat → Term
  | lamAbs  : Ty → Term → Term
  | apply   : Term → Term → Term
  | tyAbs   : Kind → Term → Term
  | tyInst  : Term → Ty → Term
  | iwrap   : Ty → Ty → Term → Term
  | unwrap  : Term → Term
  | constr  : Ty → Nat → List Term → Term
  | case    : Ty → Term → List Term → Term
  | constant : Poe.Uplc.Const → Term
  | builtin : Poe.Uplc.Builtin → Term
  | error   : Ty → Term
deriving Repr, BEq

inductive Program
  | program : Nat × Nat × Nat → Term → Program

end Poe.Tplc
