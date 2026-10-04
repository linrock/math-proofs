# Build and audit Erdős #973

This project pins Lean `v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55` in `lean-toolchain`,
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
