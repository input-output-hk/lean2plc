import Poe.Translate
import Poe.Emit
import Poe.Examples.First
import Poe.Bridge
import Poe.TranslateTplc
import Poe.TplcOracle

/-!
Scratch, not a permanent example: exploring what a "Girard-erasure of a
dependent index" would look like for Poe. Not wired into any
translator, not a claim about what Poe supports today.
-/

namespace Poe.Experiments.VecScratch

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

/- `vHead` genuinely compiles and evaluates correctly through the typed
    backend, `n` and all — real evidence `Poe.TranslateTplc.translateTy`'s
    `Subtype` case (erasing `{l : List α // l.length = n + 1}` down to
    `listTy α`) and `translateLetValue`'s `Subtype.val` projection
    (the identity on `struct` itself) aren't just accepted structurally,
    checked against the real `plc` binary. -/
#eval show Lean.CoreM Unit from do
  let f ← Poe.TranslateTplc.translate ``vHead
  let applied := Poe.Tplc.Term.apply
    (Poe.Tplc.Term.apply (Poe.Tplc.Term.tyInst f (.builtin .integer)) (.constant (.integer 2)))
    (Poe.TplcOracle.encodeIntList [7, 8, 9])
  let program := Poe.EmitTplc.emit applied
  let _ ← Poe.TplcOracle.runPlcTypecheck program
  IO.println s!"vHead [7,8,9]: {← Poe.TplcOracle.runPlcEvaluate program}"

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

/-!
## A real inductive `Vec`, not the subtype encoding

Testing empirically, not assuming: does Poe's existing generic
`cases`/`constr` compilation already handle an ordinary two-constructor
user inductive, or does it need `List`-specific special-casing the way
`Data`'s accessors do (those need it because they map to real UPLC
*builtins*; an inductive with no builtin behind it might not)? -/

inductive Vec (X : Type) : Nat → Type
  | nil : Vec X 0
  | cons {n : Nat} : X → Vec X n → Vec X (n + 1)

def vecHead {X : Type} {n : Nat} : Vec X (n + 1) → X
  | .cons x _ => x

#eval Poe.Translate.dumpMonoLCNF ``vecHead
#eval Poe.Lint.check ``vecHead

#eval show Lean.CoreM Unit from do
  let t ← Poe.Translate.translate ``vecHead
  IO.println (Poe.Emit.emit t)

/-!
## A concrete shot at "no junk" — the paper's own aside, made real

Wadler's paper notes, in passing, that in a model supporting fixpoints,
⊥ inhabits the Church-encoded naturals without being a genuine one. Poe
doesn't use Church encoding (see the earlier discussion — real Plutus V3
has native `constr`/`case`, so Poe's own `Nat` would just be `constr 0
[]`/`constr 1 [n]`, dispatched natively, not a lambda-encoding at all).
This section builds the concrete, hands-on version: a genuine numeral
that halts to the expected value, and a "junk" term — Ω, the standard
non-terminating self-application combinator, `(λx.xx)(λx.xx)` — that
diverges, proved (not just observed) by exhibiting its exact CEK cycle. -/

/-- Built directly as a Blaster `Term.Term`, bypassing `toBlasterTerm`
    entirely — `omega` has no `.const` node at all, so it doesn't need
    the bridge, and building it directly sidesteps the `sorryAx` taint
    `toBlasterTerm`/`toBlasterConst` carry (from the unrelated
    `ByteArray`/`Data` gap), which blocks `#eval` outright regardless of
    whether a given execution path would ever touch it. -/
def omegaBlaster : Term.Term :=
  .Apply (.Lam "x" (.Apply (.Var 0) (.Var 0))) (.Lam "x" (.Apply (.Var 0) (.Var 0)))

#eval show Lean.CoreM Unit from do
  for n in List.range 12 do
    IO.println s!"n={n}: {repr (iterate default (State.Eval [] [] omegaBlaster) n)}"

/-- The state reached after 5 steps — confirmed by the trace above, not
    guessed: `n=5` and `n=10` print identically, i.e. Ω enters a genuine
    period-5 cycle after an initial 5-step transient. -/
def omegaVLam : CekValue := .VLam "x" (.Apply (.Var 0) (.Var 0)) []
def omegaSigma5 : State := .Eval [] [omegaVLam] (.Apply (.Var 0) (.Var 0))

theorem omega_reaches_sigma5 :
    iterate default (State.Eval [] [] omegaBlaster) 5 = omegaSigma5 := by
  simp [iterate, step, omegaBlaster, omegaSigma5, omegaVLam]

theorem omega_sigma5_period :
    iterate default omegaSigma5 5 = omegaSigma5 := by
  simp [iterate, step, omegaSigma5, omegaVLam]

/-- The genuine non-termination proof: not "we tried some fuel values
    and it didn't halt", but *for every* `n`, it doesn't halt — by strong
    induction, using the period-5 cycle to reduce any `n ≥ 5` to a
    strictly smaller case. -/
theorem omega_sigma5_never_halts (n : Nat) (V : CekValue) :
    iterate default omegaSigma5 n ≠ State.Halt V := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp [iterate, omegaSigma5]
    | 1 => simp [iterate, step, omegaSigma5]
    | 2 => simp [iterate, step, omegaSigma5]
    | 3 => simp [iterate, step, omegaSigma5]
    | 4 => simp [iterate, step, omegaSigma5]
    | (m + 5) =>
      have h : iterate default omegaSigma5 (m + 5) = iterate default omegaSigma5 m := by
        rw [show m + 5 = 5 + m from by omega, iterate_add, omega_sigma5_period]
      rw [h]
      exact ih m (by omega)

/-- The paper's aside, made concrete: Ω is a genuine `Poe.Uplc.Term` —
    syntactically well-formed, exactly the shape a native `constr 1 [n]`
    consumer would be handed if fed junk instead of a real numeral — and
    it provably never reaches `Halt`, for *any* amount of fuel. This is
    the hands-on version of "a model with fixpoints admits non-genuine
    inhabitants" — not asserted, proved. -/
theorem omega_never_halts (n : Nat) (V : CekValue) :
    iterate default (State.Eval [] [] omegaBlaster) n ≠ State.Halt V := by
  rcases Nat.lt_or_ge n 5 with hn | hn
  · match n, hn with
    | 0, _ => simp [iterate, omegaBlaster]
    | 1, _ => simp [iterate, step, omegaBlaster]
    | 2, _ => simp [iterate, step, omegaBlaster]
    | 3, _ => simp [iterate, step, omegaBlaster]
    | 4, _ => simp [iterate, step, omegaBlaster]
  · have h : iterate default (State.Eval [] [] omegaBlaster) (5 + (n - 5))
        = iterate default omegaSigma5 (n - 5) := by
      rw [iterate_add, omega_reaches_sigma5]
    have hn5 : (5 + (n - 5) : Nat) = n := by omega
    rw [hn5] at h
    rw [h]
    exact omega_sigma5_never_halts (n - 5) V

#print axioms omega_never_halts

/-!
## The other half of the contrast: a genuine numeral halts

Poe's real, native `Nat` (if it had one) would just be `constr 0 []`
(zero) / `constr 1 [n]` (succ n) — the same tagged-sum mechanism already
used for `List`/`Vec` all session, dispatched via native `case`, no
lambda-encoding involved. `two` below is exactly that, and — unlike
Ω, offered the same kind of consumer — halts to exactly the expected
nested value. -/

def natZeroBlaster : Term.Term := .Constr 0 []
def natSuccBlaster (n : Term.Term) : Term.Term := .Constr 1 [n]
def twoBlaster : Term.Term := natSuccBlaster (natSuccBlaster natZeroBlaster)
def twoValue : CekValue := .VConstr 1 [.VConstr 1 [.VConstr 0 []]]

theorem two_halts :
    runSteps default (State.Eval [] [] twoBlaster) 6 = State.Halt twoValue := by
  simp [runSteps, step, twoBlaster, natSuccBlaster, natZeroBlaster, twoValue]

#print axioms two_halts

/-!
## A concrete McBride (forcing) example

`vHead`'s index was dead in the body — erasable by the crudest possible
argument (never read at all), no forcing needed. `vlength` is the
minimal case where the index genuinely *is* used, so dead-code
elimination alone doesn't apply, yet it's still fully recoverable from
already-kept data (`v.1.length`), which is exactly what forcing (not
Girard's dead-code case, not Kreisel, not Reynolds) is for. Checked
empirically before claiming anything, same discipline as `vHead`. -/

def vlength {X : Type} {n : Nat} (v : {l : List X // l.length = n}) : Nat := n

#eval Poe.Translate.dumpMonoLCNF ``vlength

/- `n` comes back unchanged regardless of the list handed in — genuinely
    forced, not just dead: `List.length` is never actually recomputed at
    runtime (unlike `getTag` below, whose whole point is the value being
    read *is* already the stored index), the caller's own `n` is simply
    returned. Checked through the typed backend against real `plc`. -/
#eval show Lean.CoreM Unit from do
  let f ← Poe.TranslateTplc.translate ``vlength
  let applied := Poe.Tplc.Term.apply
    (Poe.Tplc.Term.apply (Poe.Tplc.Term.tyInst f (.builtin .integer)) (.constant (.integer 3)))
    (Poe.TplcOracle.encodeIntList [10, 20, 30])
  let program := Poe.EmitTplc.emit applied
  let _ ← Poe.TplcOracle.runPlcTypecheck program
  IO.println s!"vlength [10,20,30] (n=3): {← Poe.TplcOracle.runPlcEvaluate program}"

/-- A *cheap* forcing example: `tag` is literally stored as `Data.constr`'s
    own first field, so recovering it is a free O(1) projection — pattern-
    match `d.1`'s outer constructor and read the field — not a real
    recomputation the way `vlength`'s `List.length` traversal was. -/
def isTaggedData (tag : Nat) (d : Poe.PlutusData.Data) : Prop :=
  ∃ fields, d = .constr tag fields

def getTag {tag : Nat} (d : {d : Poe.PlutusData.Data // isTaggedData tag d}) : Nat := tag

#eval Poe.Translate.dumpMonoLCNF ``getTag

/- No type-former param at all (`tag : Nat`, not `Type`), so unlike
    `vlength`/`vHead` this compiles to a plain two-argument function —
    real evidence the `Subtype` fix handles a bare (non-`List`) carrier
    type too (`{d : Data // isTaggedData tag d}` erases to `Data` itself,
    not `listTy _`). -/
#eval show Lean.CoreM Unit from do
  let f ← Poe.TranslateTplc.translate ``getTag
  let applied := Poe.Tplc.Term.apply
    (Poe.Tplc.Term.apply f (.constant (.integer 5)))
    (.constant (.data (.b "x".toUTF8)))
  let program := Poe.EmitTplc.emit applied
  let _ ← Poe.TplcOracle.runPlcTypecheck program
  IO.println s!"getTag (tag=5): {← Poe.TplcOracle.runPlcEvaluate program}"

end Poe.Experiments.VecScratch
