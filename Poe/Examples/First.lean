import Poe.Uplc
import Poe.Emit
import Poe.Translate
import Poe.Oracle

/-!
# First light

Three things:
1. A hand-built UPLC term + its emitted text — proves the emitter works
   before the translator exists (paste the output into `uplc evaluate`).
2. The first fragment programs the translator will be pointed at, with the
   ordinary-Lean ghost layer they should eventually carry.
3. D2: run each fragment program's translation through the real `uplc`
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

/-! Once the LCNF dump works, start here: -/
#eval Poe.Translate.dumpMonoLCNF ``double
#eval Poe.Translate.dumpMonoLCNF ``absInt
#eval Poe.Translate.dumpMonoLCNF ``sumList

/-! D1 translator, exercised on the fragment targets so far. -/
#eval show Lean.CoreM Unit from do
  IO.println (emit (← Poe.Translate.translate ``double))
#eval show Lean.CoreM Unit from do
  IO.println (emit (← Poe.Translate.translate ``absInt))
#eval show Lean.CoreM Unit from do
  IO.println (emit (← Poe.Translate.translate ``sumList))

/-! D2: oracle harness, generated inputs, checked against the real `#eval`
    value of each Lean function. -/

/-- -5..5. -/
def testInts : List Int := (List.range 11).map fun n => Int.ofNat n - 5

def testLists : List (List Int) := [[], [1], [1, 2, 3], [-3, -2, -1, 0, 1, 2, 3], [5, 5, 5]]

#eval show Lean.CoreM Unit from
  Poe.Oracle.runSuite ``double (testInts.map fun x => ([Poe.Oracle.encodeInt x], double x))

#eval show Lean.CoreM Unit from
  Poe.Oracle.runSuite ``absInt (testInts.map fun x => ([Poe.Oracle.encodeInt x], absInt x))

#eval show Lean.CoreM Unit from do
  let cases ← testLists.mapM fun xs => do
    return ([← Poe.Oracle.encodeIntList xs], sumList xs)
  Poe.Oracle.runSuite ``sumList cases

end Poe.Examples
