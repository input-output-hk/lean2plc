import Poe.Translate
import Poe.Emit
import Poe.Examples.First
import Poe.Bridge

/-!
Scratch, not a permanent example: exploring what a "Girard-erasure of a
dependent index" would look like for Poe, for the Wadler-workshop talk.
Not wired into any translator, not a claim about what Poe supports today.
-/

namespace Poe.Examples.VecScratch

open Poe.Bridge
open PlutusCore.UPLC

/-- `n : Nat` genuinely appears in `v`'s *type* (an individual-quantified,
    Girard-style dependent index) but is never touched by the body —
    confirmed at mono LCNF (below) to survive as a real, un-erased
    parameter, since it isn't `Prop`-sorted and nothing in Poe erases it
    today. -/
def vHead {α : Type} {n : Nat} (v : {l : List α // l.length = n + 1}) : α :=
  match v.1, v.2 with
  | x :: _, _ => x

#eval Poe.Translate.dumpMonoLCNF ``vHead
#eval Poe.Translate.dumpMonoLCNF ``Poe.Examples.head

#eval show Lean.CoreM Unit from do
  let t ← Poe.Translate.translate ``Poe.Examples.head
  IO.println (Poe.Emit.emit t)

/-!
## A provable, minimal instance of the same phenomenon

`vHead`/`head` above need real `List`/`Constr` Blaster proof engineering
(no certificate for `head` exists yet) — too much surface area for a
first worked example. This one reuses `double_certificate` outright: the
dependent index here is `Fin n` (a genuinely dependent type — `Fin n`'s
own type mentions the individual `n`), the body ignores it completely,
and is chosen to be *literally* `double`'s body, so erasing the index
doesn't just "happen to be sound" — the erased program is syntactically
the exact same already-certified compiled term `double_certificate`
already covers. Zero new CEK-level proof needed; the point is the shape
of the erasure-soundness argument, not new machinery. -/

def dupIgnoringFin {n : Nat} (_ : Fin n) (x : Int) : Int := x + x

theorem dupIgnoringFin_eq_double {n : Nat} (i : Fin n) (x : Int) :
    dupIgnoringFin i x = Poe.Examples.double x := rfl

/-- Erasure certificate: for *every* dependent index `n` and every witness
    `i : Fin n`, the erased program — `double`'s own compiled term, not a
    new one — still computes `dupIgnoringFin i x`. This is the miniature
    version of what a real Reynolds-embedding-style soundness argument
    for index erasure needs: source function with a real dependent index,
    target program with the index gone, and a theorem relating them for
    every choice of the erased data (`n`, `i`), not just one. -/
theorem dupIgnoringFin_certificate {n : Nat} (i : Fin n) (x : Int) :
    ∃ (steps : Nat),
      PlutusCore.UPLC.CekMachine.cekExecuteProgram
        (toBlasterProgram doubleProgram)
        [Term.Term.Const (.Integer x)]
        steps
      = PlutusCore.UPLC.CekMachine.State.Halt
          (PlutusCore.UPLC.CekValue.CekValue.VCon (.Integer (dupIgnoringFin i x))) := by
  rw [dupIgnoringFin_eq_double]
  exact double_certificate x

#print axioms dupIgnoringFin_certificate

/-!
## The richer version: `head` itself

Real `List`/`Constr` proof engineering, attempted for real rather than
assumed tractable. `headUplcTerm` below is `Poe.Examples.head`'s own
already-oracle-verified compiled shape (confirmed by the `#eval` dumps
above: `(program 1.1.0 (lam x0 (case x0 (error) (lam x1 (lam x2 x1)))))`),
hand-transcribed the same way `Poe.Bridge`'s existing terms are.

Real Blaster `Constr`/`Case` semantics (`CekMachine.lean`, confirmed
directly, not assumed): a `Term.Constr i Ts` evaluates *every* field in
`Ts` to a value before becoming `VConstr i Vs` (via
`Frame.ConstructorArgument`) — so passing a `List Int` argument as an
unevaluated `Constr`-encoded term forces evaluating the *entire* list
structure, not just the head, before `head`'s own body even runs. That
means the step count genuinely depends on the tail's length — unlike
`double`/`absInt`, a single fixed fuel bound doesn't work for an
arbitrary-length list. Proving it for *every* `xs` needs induction on
`xs` (real, separate future work — see PLAN.md's own "recursion needs
induction, not a fixed fuel count" note). This certificate is
deliberately scoped to a fixed, minimal instance (the singleton list
`[x]`) instead, to see whether the technique from `double`/`absInt`
carries over at all before attempting the general (harder) case. -/

def headUplcTerm : Poe.Uplc.Term :=
  .lam "x0" (.case (.var 0) [.error, .lam "x1" (.lam "x2" (.var 1))])

def headProgram : Poe.Uplc.Program := .program (1, 1, 0) headUplcTerm

def encodeIntListTerm : List Int → Term.Term
  | [] => .Constr 0 []
  | x :: xs => .Constr 1 [.Const (.Integer x), encodeIntListTerm xs]

theorem head_singleton_certificate (x : Int) :
    ∃ (steps : Nat),
      PlutusCore.UPLC.CekMachine.cekExecuteProgram
        (toBlasterProgram headProgram)
        [encodeIntListTerm [x]]
        steps
      = PlutusCore.UPLC.CekMachine.State.Halt
          (PlutusCore.UPLC.CekValue.CekValue.VCon (.Integer x)) := by
  refine ⟨20, ?_⟩
  simp only [toBlasterProgram, toBlasterTerm, headProgram, headUplcTerm,
    encodeIntListTerm, List.map]
  rfl

#print axioms head_singleton_certificate

/-- Ties it back to `vHead` itself, not just its erasure target: for the
    one concrete shape this file's proof toolkit can reach (a length-1
    vector), erasing `vHead`'s index `n` and running the resulting
    `head`-shaped program really does compute what `vHead` computes. -/
theorem vHead_singleton_certificate (x : Int) (v : {l : List Int // l.length = 0 + 1})
    (hv : v.1 = [x]) :
    ∃ (steps : Nat),
      PlutusCore.UPLC.CekMachine.cekExecuteProgram
        (toBlasterProgram headProgram)
        [encodeIntListTerm v.1]
        steps
      = PlutusCore.UPLC.CekMachine.State.Halt
          (PlutusCore.UPLC.CekValue.CekValue.VCon (.Integer (vHead v))) := by
  have hval : vHead v = x := by
    rcases v with ⟨l, hl⟩
    simp only at hv
    subst hv
    rfl
  rw [hv, hval]
  exact head_singleton_certificate x

#print axioms vHead_singleton_certificate

/-!
## Attempting the general case (arbitrary-length tail)

Needs real induction, per the step-counting explanation above. First a
generic "fuel is additive" fact about `runSteps` (splitting `a+b` steps
into `a` steps then `b` more) — true because `step` is a pure function
and `runSteps` just iterates it, checked directly against its actual
recursive definition (fuel exhaustion aside: `Halt`/`Error` states are
absorbing, confirmed directly in `runSteps`'s own pattern match, which is
exactly what makes this compose). -/

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue

/-- Realization, found only by trying this and reading the real
    definition rather than assuming: `runSteps` can *only ever* output
    `Halt` or `Error` — landing on a non-terminal (`Eval`/`Return`) state
    with 0 fuel left is *always* converted to `Error`, even when more
    fuel would have reached `Halt` shortly after. So `runSteps` has no
    way to express "reached this intermediate configuration", which an
    induction over a recursive argument (a list) genuinely needs. `iterate`
    is the same thing minus that conversion — plain `n`-fold `step`,
    freezing once `Halt` is reached (since `step` itself does *not* fix
    `Halt` as a fixed point — applying it again turns `Halt` into `Error`,
    confirmed directly against `step`'s own wildcard case — so a naive
    "just iterate `step`" needs this freeze to stay meaningful at all). -/
def iterate (sv : PlutusCore.Default.Internal.BuiltinSemanticsVariant) : State → Nat → State
  | .Halt v, _ => .Halt v
  | Sigma, 0 => Sigma
  | Sigma, n + 1 => iterate sv (step sv Sigma) n

theorem iterate_add (sv : PlutusCore.Default.Internal.BuiltinSemanticsVariant)
    (Sigma : State) (a b : Nat) :
    iterate sv Sigma (a + b) = iterate sv (iterate sv Sigma a) b := by
  induction a generalizing Sigma with
  | zero => cases Sigma <;> simp [iterate]
  | succ a ih =>
    cases Sigma with
    | Halt v => simp [iterate]
    | Error => rw [Nat.succ_add]; simp only [iterate]; exact ih _
    | Eval s ρ t => rw [Nat.succ_add]; simp only [iterate]; exact ih _
    | Return s v => rw [Nat.succ_add]; simp only [iterate]; exact ih _

/-- `step` maps `Error` to itself (confirmed against `step`'s own
    wildcard case), so plain iteration never escapes it. -/
theorem iterate_error (sv : PlutusCore.Default.Internal.BuiltinSemanticsVariant) (n : Nat) :
    iterate sv State.Error n = State.Error := by
  induction n with
  | zero => simp [iterate]
  | succ n ih => simp [iterate, step, ih]

/-- Once `iterate` reaches `Halt` within `n` steps, `runSteps` reaches the
    *same* `Halt` within the same `n` — the two only disagree when fuel
    runs out before `Halt`, which the hypothesis rules out. -/
theorem runSteps_of_iterate_halt (sv : PlutusCore.Default.Internal.BuiltinSemanticsVariant)
    (Sigma : State) (n : Nat) (V : CekValue) (h : iterate sv Sigma n = State.Halt V) :
    runSteps sv Sigma n = State.Halt V := by
  induction n generalizing Sigma with
  | zero =>
    cases Sigma with
    | Halt v => simp only [iterate] at h; simp [runSteps, h]
    | Error => simp [iterate] at h
    | Eval _ _ _ => simp [iterate] at h
    | Return _ _ => simp [iterate] at h
  | succ n ih =>
    cases Sigma with
    | Halt v => simp only [iterate] at h; simp [runSteps, h]
    | Error => simp [iterate_error] at h
    | Eval s ρ t => simp only [iterate] at h; simp only [runSteps]; exact ih _ h
    | Return s v => simp only [iterate] at h; simp only [runSteps]; exact ih _ h

/-- The value a `Constr`-encoded list *becomes* once fully evaluated —
    mirrors `encodeIntListTerm` one level down, at the `CekValue` (not
    `Term`) level. -/
def encodeIntListValue : List Int → CekValue
  | [] => .VConstr 0 []
  | x :: xs => .VConstr 1 [.VCon (.Integer x), encodeIntListValue xs]

/-- Evaluating a `Constr`-encoded list to a value takes a number of steps
    that genuinely depends on its length (each cons cell costs a fixed,
    small number of extra steps: evaluate its head field, recurse into
    its tail field, combine) — this is the formal version of the
    step-counting explanation above, proved by induction on the list
    rather than assumed. Stated with `iterate`, not `runSteps` — the
    intermediate result (`Return s ...`, not `Halt`) is exactly what
    `runSteps` cannot express (see above). -/
theorem encodeList_eval (sv : PlutusCore.Default.Internal.BuiltinSemanticsVariant)
    (xs : List Int) (s : Stack) (ρ : Environment) :
    ∃ (k : Nat), iterate sv (State.Eval s ρ (encodeIntListTerm xs)) k
       = State.Return s (encodeIntListValue xs) := by
  induction xs generalizing s with
  | nil =>
    refine ⟨1, ?_⟩
    simp [encodeIntListTerm, encodeIntListValue, iterate, step]
  | cons x xs ih =>
    obtain ⟨k, hk⟩ := ih (Frame.ConstructorArgument 1 [CekValue.VCon (.Integer x)] [] ρ :: s)
    refine ⟨3 + (k + 1), ?_⟩
    rw [iterate_add]
    have h3 : iterate sv (State.Eval s ρ (encodeIntListTerm (x :: xs))) 3
        = State.Eval (Frame.ConstructorArgument 1 [CekValue.VCon (.Integer x)] [] ρ :: s) ρ
            (encodeIntListTerm xs) := by
      simp [encodeIntListTerm, iterate, step]
    rw [h3, iterate_add, hk]
    simp [iterate, step, encodeIntListValue]

/-- The general `head` certificate: for *every* `x` and *every* tail
    `xs`, not just the length-1 case. Reuses `encodeList_eval` as a black
    box for "evaluate the list argument to a value" (the part whose step
    count genuinely depends on `xs`), then a small, fixed number of
    further steps (drive the function application, dispatch the `case`,
    apply the matched branch to the two fields, look up the head) —
    traced by hand against `step`'s real definition, the same way
    `absInt_certificate`'s branching trace was, not guessed. -/
theorem head_certificate (x : Int) (xs : List Int) :
    ∃ (steps : Nat),
      PlutusCore.UPLC.CekMachine.cekExecuteProgram
        (toBlasterProgram headProgram)
        [encodeIntListTerm (x :: xs)]
        steps
      = PlutusCore.UPLC.CekMachine.State.Halt
          (PlutusCore.UPLC.CekValue.CekValue.VCon (.Integer x)) := by
  obtain ⟨k, hk⟩ := encodeList_eval default (x :: xs)
    [Frame.RightApplicationOfValue
      (CekValue.VLam "x0"
        (Term.Term.Case (Term.Term.Var 0)
          [Term.Term.Error, Term.Term.Lam "x1" (Term.Term.Lam "x2" (Term.Term.Var 1))]) [])]
    []
  refine ⟨k + 13, ?_⟩
  apply runSteps_of_iterate_halt
  simp only [CekMachine.applyParams, CekMachine.initialState, toBlasterTerm,
    headUplcTerm, List.map]
  have h3 : iterate default (State.Eval ([] : Stack) ([] : Environment)
        (Term.Term.Apply
          (Term.Term.Lam "x0"
            (Term.Term.Case (Term.Term.Var 0)
              [Term.Term.Error, Term.Term.Lam "x1" (Term.Term.Lam "x2" (Term.Term.Var 1))]))
          (encodeIntListTerm (x :: xs))))
        3
      = State.Eval
          [Frame.RightApplicationOfValue
            (CekValue.VLam "x0"
              (Term.Term.Case (Term.Term.Var 0)
                [Term.Term.Error, Term.Term.Lam "x1" (Term.Term.Lam "x2" (Term.Term.Var 1))])
              [])]
          []
          (encodeIntListTerm (x :: xs)) := by
    simp [iterate, step]
  rw [show (k + 13 : Nat) = 3 + (k + 10) from by omega, iterate_add, h3, iterate_add, hk]
  simp [iterate, step, step.folding, encodeIntListValue]

#print axioms head_certificate

/-- The full loop, closed for real: for *every* dependent index `n` and
    *every* length-`(n+1)` vector `v` (not just the singleton case), the
    erased program — `head`'s own compiled term, unchanged, with the
    index gone — still computes `vHead v`. This is the general version of
    the erasure-soundness statement the whole exercise was chasing. -/
theorem vHead_certificate (n : Nat) (v : {l : List Int // l.length = n + 1}) :
    ∃ (steps : Nat),
      PlutusCore.UPLC.CekMachine.cekExecuteProgram
        (toBlasterProgram headProgram)
        [encodeIntListTerm v.1]
        steps
      = PlutusCore.UPLC.CekMachine.State.Halt
          (PlutusCore.UPLC.CekValue.CekValue.VCon (.Integer (vHead v))) := by
  obtain ⟨x, xs, hv⟩ : ∃ x xs, v.1 = x :: xs := by
    rcases v with ⟨l, hl⟩
    cases l with
    | nil => simp at hl
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hval : vHead v = x := by
    rcases v with ⟨l, hl⟩
    simp only at hv
    subst hv
    rfl
  rw [hv, hval]
  exact head_certificate x xs

#print axioms vHead_certificate

end Poe.Examples.VecScratch
