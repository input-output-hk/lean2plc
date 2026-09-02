# Poe (proof of concept)

Contracts in a ghost-dependent fragment of Lean 4, compiled via LCNF to two
backends: untyped UPLC (`Poe.Translate`) and Typed Plutus Core
(`Poe.TranslateTplc`).

`nix develop` gives a devshell with the pinned Lean toolchain plus the real
`uplc`/`plc` executables as execution oracles (`Poe.Oracle`/`Poe.TplcOracle`
check translated output against them, not hand-copied expected values).

`Poe.Bridge` adds a real dependency, `PlutusCoreBlaster` — an independent
reference implementation of the UPLC CEK machine — used to state and prove
a small number of per-program correctness certificates (`Poe.Bridge`'s own
doc comments are explicit about how narrow this is: two hand-engineered
proofs, not a compiler-correctness result).

## Validator styles

`Poe/Experiments/ValidatorStyles.lean` lays out several ways of packaging
the same validator (plain `Bool` with a curried precondition, `Bool` with a
separate correctness theorem, `Decidable`-valued, and two `Subtype`-bundled
variants) side by side, self-contained, each checked against its canonical
original. It also compares the compiled UPLC size of each style's real,
`()`-or-`error` deployable form against Aiken's own official `hello_world`
example (flat-encoded bytes):

| definition | flat (bytes) |
|---|---:|
| **Aiken `hello_world`** | 285 |
| style4E / style5E (`Subtype`-bundled, check-wrapped) | 373 |
| style1E (`Bool`, curried, check-wrapped) | 379 |
| style3E (`Decidable`, check-wrapped) | 383 |

Every style comes out 30-35% bigger than Aiken's, most plausibly because
`Poe.Translate` runs no optimization passes at all (no CSE, inlining, or
dead-code elimination) — not because of which validator style is chosen,
where the spread is much smaller (373-383 bytes).
