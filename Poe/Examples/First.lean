import Poe.Uplc
import Poe.Emit
import Poe.Translate
import Poe.Oracle
import Poe.Lint
import Poe.Prelude

/-!
# First light

Four things:
1. A hand-built UPLC term + its emitted text — proves the emitter works
   before the translator exists (paste the output into `uplc evaluate`).
2. The first fragment programs the translator will be pointed at, with the
   ordinary-Lean ghost layer they should eventually carry.
3. D0: check each is actually accepted by the fragment linter (see
   `Poe.Examples.OutOfFragment` for the linter rejecting something).
4. D2: run each fragment program's translation through the real `uplc`
   oracle on generated inputs, checked against the actual Lean function
   (not a hand-copied expected value).
-/

namespace Poe.Examples

open Poe.Uplc Poe.Emit

/-- `\x -> addInteger x 1` applied to 41. Expected oracle result: 42. -/
def firstLight : Term :=
  .app (.lam "x" (.app (.app (.builtin .addInteger) (.var 0))
                       (.const (.integer 1))))
       (.const (.integer 41))

#eval emit firstLight

/-! ## Fragment programs (translator targets) -/

/-- Straight-line, non-recursive: the first translation target. -/
def double (x : Int) : Int := x + x

/-- Branching. -/
def absInt (x : Int) : Int := if x < 0 then -x else x

/-- Structural recursion over a list: the interesting target
    (recursion → fix via self-application). -/
def sumList : List Int → Int
  | []      => 0
  | x :: xs => x + sumList xs

/-- Ghost layer sample: an ordinary theorem about a fragment function.
    Never compiled; erased before LCNF. -/
theorem double_nonneg (x : Int) (h : 0 ≤ x) : 0 ≤ double x := by
  simp [double]; omega

/-- agda2hs's `error`/`@(tactic absurd)` trick (see `Poe.Prelude.poeError`):
    `xs ≠ []` is a real proof obligation on every caller, so the `[]` case
    can never actually be reached — `hne` refines to `[] ≠ []` in that
    branch, and `contradiction` (Lean's `autoParam` analogue of agda2hs's
    `absurd` tactic) discharges `poeError`'s hidden `False` argument from
    it automatically. Confirmed directly against the real oracle: a
    well-shaped call succeeds normally, and calling the compiled UPLC with
    an empty list anyway (something no well-typed Lean caller could ever
    actually do, but exactly what happens if raw arguments are supplied
    from outside Lean's own discipline) genuinely aborts. -/
def head (xs : List Int) (hne : xs ≠ []) : Int :=
  match xs, hne with
  | [], hne => Poe.Prelude.poeError "empty list"
  | x :: _, _ => x

/-! Once the LCNF dump works, start here: -/
#eval Poe.Translate.dumpMonoLCNF ``double
#eval Poe.Translate.dumpMonoLCNF ``absInt
#eval Poe.Translate.dumpMonoLCNF ``sumList

/-! D0: fragment linter accepts all three (contrast with
    `Poe.Examples.OutOfFragment`, which it rejects). -/
#eval Poe.Lint.check ``double
#eval Poe.Lint.check ``absInt
#eval Poe.Lint.check ``sumList
#eval Poe.Lint.check ``head

/-! D1 translator, exercised on the fragment targets so far. -/
#eval show Lean.CoreM Unit from do
  IO.println (emit (← Poe.Translate.translate ``double))
#eval show Lean.CoreM Unit from do
  IO.println (emit (← Poe.Translate.translate ``absInt))
#eval show Lean.CoreM Unit from do
  IO.println (emit (← Poe.Translate.translate ``sumList))
#eval show Lean.CoreM Unit from do
  IO.println (emit (← Poe.Translate.translate ``head))

/-! D2: oracle harness, generated inputs, checked against the real `#eval`
    value of each Lean function. -/

/-- -5..5. -/
def testInts : List Int := (List.range 11).map fun n => Int.ofNat n - 5

def testLists : List (List Int) := [[], [1], [1, 2, 3], [-3, -2, -1, 0, 1, 2, 3], [5, 5, 5]]

#eval show Lean.CoreM Unit from
  Poe.Oracle.runSuite ``double (testInts.map fun x => ([Poe.Oracle.encodeInt x], .integer (double x)))

#eval show Lean.CoreM Unit from
  Poe.Oracle.runSuite ``absInt (testInts.map fun x => ([Poe.Oracle.encodeInt x], .integer (absInt x)))

#eval show Lean.CoreM Unit from do
  let cases ← testLists.mapM fun xs => do
    return ([← Poe.Oracle.encodeIntList xs], .integer (sumList xs))
  Poe.Oracle.runSuite ``sumList cases

/- `head`'s proof argument is erased from the compiled arity (confirmed:
   the oracle only ever supplies the list, never a proof), so a nonempty
   list succeeds normally, and an empty list — unreachable for any real
   Lean caller, but exactly what the oracle poking raw arguments directly
   does here — genuinely aborts rather than doing anything else. -/
#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``head
    [ ([← Poe.Oracle.encodeIntList [3, 99]], .integer (head [3, 99] (by decide)))
    , ([← Poe.Oracle.encodeIntList [7]], .integer (head [7] (by decide)))
    ]
  Poe.Oracle.runSuiteAborts ``head
    [[← Poe.Oracle.encodeIntList []]]

end Poe.Examples
