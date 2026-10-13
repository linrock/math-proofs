# Build and audit Erdős #306

This project pins Lean `v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55` in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. From this directory, with the
pinned toolchain provisioned, run:

```sh
lake exe cache get
lake build Challenge Solution AxiomAudit Statement
lake env lean AxiomAudit.lean
```

The first command fetches Mathlib's build cache. The build compiles the three
`Proofs/` modules plus `Challenge`, `Solution`, `AxiomAudit`, and `Statement`.
`Proofs`, `Solution`, `AxiomAudit`, and `Statement` use `-E hasSorry`.
`Challenge` contains the intentional statement placeholders.

The last command prints the transitive axioms of all 20 `Solution` theorems.
Expect only `propext`, `Classical.choice`, and `Quot.sound`.

`./verify.sh` runs the same build and axiom audit and checks the axiom report
count. `./verify.sh --no-sandbox` also runs the Comparator on `comparator.json`. Building the proof
modules takes about three minutes on one core and peaks near 16 GiB of memory.
