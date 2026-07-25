import Poe.Uplc
import Poe.Emit
import Poe.Translate

/-!
# First light

Two things only:
1. A hand-built UPLC term + its emitted text — proves the emitter works
   before the translator exists (paste the output into `uplc evaluate`).
2. The first fragment programs the translator will be pointed at, with the
   ordinary-Lean ghost layer they should eventually carry.
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

end Poe.Examples
