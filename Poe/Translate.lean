import Lean
import Poe.Uplc

/-!
# D1: LCNF → UPLC translator (stub)

The tap point is mono-phase LCNF (`Lean.Compiler.LCNF`): strict,
let-normalized, types/proofs already erased. Mapping (see PLAN.md):

  let x := e; body        ~>  [(lam x body) e]
  fun / application       ~>  lam / app        (CEK does closures)
  constructor application ~>  (constr i ...)
  cases                   ~>  (case ...)
  projection              ~>  single-branch case
  join points             ~>  let-bound lams (nullary: delay/force)
  recursive def           ~>  fix via self-application
  Int/Bool/... primitives ~>  builtin shim table

Open questions 1-2 in PLAN.md (LCNF API surface at 4.24.0; what structural
recursion looks like post-compilation) get answered here first, by inspecting
`Lean.Compiler.LCNF.getMonoDecl?` output for the example functions before
any translation code is written.
-/

namespace Poe.Translate

open Lean Compiler.LCNF

/-- Debug entry point: print a declaration's mono-phase LCNF so we can see
    what we're translating before writing the translator. -/
def dumpMonoLCNF (declName : Name) : CoreM Unit := do
  let some decl ← getMonoDecl? declName
    | throwError "no mono LCNF for {declName}"
  IO.println (← ppDecl' decl)

end Poe.Translate
