# lean2plc (proof of concept)

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
