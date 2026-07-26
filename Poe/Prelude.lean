/-!
# Poe prelude: primitives the translator recognizes by name

Mirrors `PlutusTx.Prelude`'s role in real Plinth code: a validator signals
rejection by *evaluating to `error`*, not by returning `false` — a plain
`Bool` only gets you halfway to something deployable. `check` is the same
idiom `PlutusTx.Prelude.check` provides (`if b then unitval else
traceError ...`).

`abort`'s Lean body is a placeholder never inspected by the translator:
`Translate` special-cases the name `Poe.Prelude.abort` itself directly to
UPLC's `error` term, rather than trying to translate whatever is written
here. That's deliberate — the honest implementation would go through
Lean's real `panic!`, which drags in `mkPanicMessageWithDecl` and
source-location plumbing, nothing like the ghost-dependent fragment (this
was checked by dumping `panic!`'s mono LCNF before deciding against it).

The body has to be genuinely self-recursive (`partial`), not e.g. `PUnit.unit`
directly: a transparent body lets Lean's own optimizer see that `if b then
() else abort` reduces to `()` either way and collapse the whole `check`
away *before* mono LCNF, silently turning every rejection into success
(caught by the oracle: a `check`-wrapped validator kept returning `()` on
dishonest input). A self-recursive `partial def` can't be inlined away for
the same reason `sumList` itself survives to mono LCNF as a real call
instead of being unfolded.
-/

namespace Poe.Prelude

partial def abort (_ : Unit) : Unit := abort ()

/-- `check b`: `()` if `b`, otherwise abort — the shape a real validator's
    body ends in, instead of returning a `Bool`. -/
def check (b : Bool) : Unit := if b then () else abort ()

/-!
## `poeError`: agda2hs's `error`/`@(tactic absurd)` trick, in Lean

agda2hs's `Prelude.error : {@0 @(tactic absurd) i : ⊥} → String → a` lets a
function require a proof from its caller (e.g. `hd : (xs : List a) →
@0 ⦃ NonEmpty xs ⦄ → a`), then, in the branch that proof rules out,
call `error` — the `absurd` tactic finds the now-impossible instance in
context automatically and uses it, so no caller can ever actually reach
that branch. Lean has the same capability via `autoParam` (`:=
by tacticName`) instead of a custom reflection tactic: `contradiction`
plays exactly the role `absurd` does, searching the local context for a
hypothesis that's already false. -/

/-- Same role as agda2hs's `error`: put this in a branch a caller-supplied
    proof has already ruled out (see `hd`-style examples: a `xs ≠ []`
    hypothesis refines to `[] ≠ []` in the `xs = []` case, and
    `contradiction` finds it automatically). `msg` carries no runtime
    weight — see below, the call never survives to mono LCNF to have
    args at all.

    Confirmed directly by dumping mono LCNF: unlike `abort`, this does
    *not* need to survive as a named call for `Translate` to special-case
    — Lean's own optimizer fully inlines `poeError`'s body (`h.elim`,
    eliminating a value of the empty type `False`) down to `Code.unreach`
    (printed `⊥`) before mono LCNF, a structural marker with no name left
    to match on at all. `Translate` maps `Code.unreach` itself straight to
    UPLC `error`, so this works regardless of which helper (this one,
    `absurd`, a bare `False.elim`) produced the impossible branch. -/
def poeError {α : Sort u} (msg : String) (h : False := by contradiction) : α := h.elim

end Poe.Prelude
