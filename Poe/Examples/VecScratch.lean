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

end Poe.Examples.VecScratch
