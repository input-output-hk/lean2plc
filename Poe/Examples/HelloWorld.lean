import Poe.Lint
import Poe.Oracle

/-!
# D3: a real validator in plain Lean

Hello-world-grade: redeemer (message) check + signature membership over a
list — the same shape as Aiken's own `hello_world` template (message
check + datum-owner-signed check). `elem` is written as a plain recursive
function rather than via `List.elem`/`∈` so the translator sees an
ordinary named self-call, not a typeclass method (monomorphization
removing typeclasses is assumed, not itself exercised, per PLAN.md's
non-goals).
-/

namespace Poe.Examples.HelloWorld

def elem (x : String) : List String → Bool
  | []      => false
  | y :: ys => x == y || elem x ys

/-- Redeemer message must be exactly right, and the datum's `owner` must be
    among the transaction's `signatories`. -/
def validate (owner message : String) (signatories : List String) : Bool :=
  message == "Hello, World!" && elem owner signatories

/-! ## (a) Ordinary Lean correctness theorems about the source function -/

theorem elem_iff (x : String) : ∀ ys, elem x ys = true ↔ x ∈ ys
  | [] => by simp [elem]
  | y :: ys => by simp [elem, elem_iff x ys]

theorem validate_correct (owner message : String) (signatories : List String) :
    validate owner message signatories = true ↔
      message = "Hello, World!" ∧ owner ∈ signatories := by
  simp [validate, elem_iff]

/-- The rejection case: a direct corollary of `validate_correct` (`Bool` has
    only two values, so the `false` case is the negation of the `true`
    case), not a fact requiring separate reasoning about `validate`. -/
theorem validate_correct_false (owner message : String) (signatories : List String) :
    validate owner message signatories = false ↔
      message ≠ "Hello, World!" ∨ owner ∉ signatories := by
  rw [← Bool.not_eq_true, validate_correct]
  constructor
  · intro h
    by_cases hm : message = "Hello, World!"
    · exact Or.inr fun hs => h ⟨hm, hs⟩
    · exact Or.inl hm
  · intro h hp
    cases h with
    | inl h => exact h hp.1
    | inr h => exact h hp.2

/-! ## (b) Fragment-checked, emitted, and run through the oracle -/

#eval Poe.Lint.check ``elem
#eval Poe.Lint.check ``validate

/- Honest input: right message, owner signed. Dishonest: wrong message;
   right message but owner didn't sign. All checked against the real
   oracle, not just against Lean's own evaluator. -/
#eval show Lean.CoreM Unit from do
  let signers := ["bob", "alice", "carol"]
  let inputs : List (String × String × List String) :=
    [ ("alice", "Hello, World!", signers)    -- honest
    , ("alice", "wrong message", signers)    -- dishonest: bad message
    , ("mallory", "Hello, World!", [])       -- dishonest: owner didn't sign
    ]
  let cases ← inputs.mapM fun (owner, message, signatories) => do
    let args := [Poe.Oracle.encodeString owner, Poe.Oracle.encodeString message,
                 ← Poe.Oracle.encodeStringList signatories]
    return (args, Poe.Uplc.Const.bool (validate owner message signatories))
  Poe.Oracle.runSuite ``validate cases

end Poe.Examples.HelloWorld
