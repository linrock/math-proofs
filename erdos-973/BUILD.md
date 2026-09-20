# Build and audit Erdős #973

This project pins Lean `v4.33.1` and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. From this directory, with the
pinned toolchain provisioned, run:

```sh
lake exe cache get
lake build Challenge Solution AxiomAudit
lake env lean AxiomAudit.lean
```

The first command fetches Mathlib's build cache. The build compiles all 11
`Proofs/` modules plus `Challenge`, `Solution`, and `AxiomAudit`. `Proofs`,
`Solution`, and `AxiomAudit` use `-E hasSorry`. `Challenge` contains the
intentional statement placeholders.

The last command prints the transitive axioms of the two selected `Solution`
theorems. Expect only `propext`, `Classical.choice`, and `Quot.sound`.
