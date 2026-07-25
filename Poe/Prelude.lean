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

end Poe.Prelude
