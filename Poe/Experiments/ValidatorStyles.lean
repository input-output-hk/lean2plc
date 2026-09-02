import Poe.Examples.HelloWorld
import Poe.Examples.HelloWorldCorrect
import Poe.Experiments.ValidatorDecidable
import Poe.Experiments.HelloWorldSubtype
import Poe.Experiments.VecScratch

/-!
# The validator styles, side by side

Every style below enforces the *same* business logic — Aiken's
`hello_world`: the redeemer's message must be exactly `"Hello, World!"`,
and the datum's `owner` must be among the transaction's `signatories`.
What differs is only how the well-formedness precondition and the
correctness postcondition get packaged into the validator's own type.

No new logic lives in this file — every definition below is a `#check`
into an already-built, already oracle-verified artifact:
`Poe.Examples.HelloWorld`, `Poe.Examples.HelloWorldCorrect`,
`Poe.Experiments.ValidatorDecidable`, `Poe.Experiments.HelloWorldSubtype`,
`Poe.Experiments.VecScratch`. This file exists only to lay them out
together for comparison — build it and read the `#check` output for each
signature, or open the source file named in each comment for the actual
definition and its oracle tests.
-/

namespace Poe.Experiments.ValidatorStyles

/-! ## 1. Plain `Bool`, precondition curried in separately

The flagship style (`Poe/Examples/HelloWorld.lean`). `wf : WellFormed ctx`
is an ordinary curried argument — this is already dependently typed
(`WellFormed`'s very statement depends on the value `ctx`), just with the
dependency confined to the *input* side. Nothing in the *output* type
(`Bool`) reflects what was decided; if you want to know `validatorB`
actually enforces the intended spec, you look elsewhere. -/

#check @Poe.Examples.HelloWorld.WellFormed
#check @Poe.Examples.HelloWorld.validatorB

/-! ## 2. Plain `Bool`, correctness proven afterward as a separate theorem

Same `validatorB` as style 1 — the *only* difference is a second,
independently-stated-and-proved artifact (`Poe/Examples/HelloWorldCorrect.lean`)
connecting the `Bool` result back to the abstract spec. Two maintained
artifacts, not one: if `validatorB`'s body changes, this theorem needs
re-proving by hand. Lean's type checker catches any drift immediately
(the theorem simply fails to compile) — it's a maintenance cost, not a
soundness risk. -/

#check @Poe.Examples.HelloWorld.validatorB_correct

/-! ## 3. `Decidable`-valued

`Poe/Experiments/ValidatorDecidable.lean`. `Accepted` names the same
proposition `validatorB_correct` states on its right-hand side — given a
name up front instead of discovered after the fact. Returning
`isTrue`/`isFalse` at all is only possible by actually producing a proof
of `Accepted`/`¬Accepted`, so "the answer matches the spec" is enforced by
the type checker at the point of construction, not proved afterward as in
style 2. -/

#check @Poe.Experiments.ValidatorDecidable.Accepted
#check @Poe.Experiments.ValidatorDecidable.validatorBDecidable

/-! ## 4. `Subtype`-bundled precondition (input only)

`Poe/Experiments/HelloWorldSubtype.lean`. Same body as `validatorB`, but
`ctx`/`wf` are bundled into one `{ctx : Data // WellFormed ctx}` argument
instead of curried separately — a stylistic repackaging of style 1's
*input* side, no change to what's decided or how it's proven. -/

#check @Poe.Experiments.HelloWorldSubtype.validatorBSubtype

/-! ## 5. `Subtype`-bundled pre *and* post condition (Hoare-triple style)

Also `Poe/Experiments/HelloWorldSubtype.lean`. The fullest packaging: the
*input* carries its precondition (`WellFormed`, as in style 4) and the
*output* carries its own postcondition (`b = true ↔ Accepted v.1 v.2`,
reusing `Accepted` from style 3 rather than restating it) in the same
definition. This and style 3 are the same content in different
encodings — a tag plus a proof it reflects the spec — not two different
ideas; style 3 curries the input, style 5 bundles it, but both carry
exactly as much proof obligation as each other. -/

#check @Poe.Experiments.HelloWorldSubtype.validatorBSubtypePost

/-! ## 6. Genuinely dependent typing: an index carried *in* the type

`Poe/Experiments/VecScratch.lean`. A different kind of dependency than
styles 1-5 — not a precondition or postcondition *attached to* a
`Data`/`Bool`, but a real inductive family (`Vec X n`) whose type itself
varies with a value (`n`, the length). Not a HelloWorld-shaped validator
at all (an earlier attempt at a `Vec`-based signatories decode for
*this* validator was tried and dropped as too tenuous a fit) — included
here purely to contrast *what kind* of dependent typing this is against
styles 1-5's precondition/postcondition style. `vecHead`'s own index `n`
carries no runtime content and erases entirely (see `Poe.TranslateTplc`'s
`Vec` handling and the erasure-completeness note in `VecScratch.lean`). -/

#check @Poe.Experiments.VecScratch.Vec
#check @Poe.Experiments.VecScratch.vecHead

end Poe.Experiments.ValidatorStyles
