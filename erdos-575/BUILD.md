# Build and audit Erdős #575

Run the following commands from this directory. Elan selects the exact compiler from [lean-toolchain](lean-toolchain): Lean `v4.35.0-rc2`, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`. The canonical Mathlib commit is `065356127b1dc0016f66b7283ce0ce2c4055aa55`, pinned by [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json). Ordinary replay does not require `lake update`.

```sh
lake exe cache get
./verify.sh
```

The first command downloads canonical compiled Mathlib dependencies. The [verify.sh](verify.sh) script runs the Palomar preliminary checks, verifies the compiler and Mathlib revisions, builds `Statement`, `Solution`, `AxiomAudit`, and `Challenge` (including all three modules in `Proofs/` with `-j1 -M8192 -E hasSorry` and zero compiler warnings), and runs a standalone saved-source axiom audit on `AxiomAudit.lean` verifying that all 13 endpoint, statement-fidelity, and non-vacuity theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

A normal Lake build and explicit endpoint audit can also be run directly:

```sh
lake build Statement Solution AxiomAudit Challenge
lake env lean -j1 -M8192 -E hasSorry -Dformat.width=1000000 \
  --setup=.lake/build/ir/AxiomAudit.setup.json AxiomAudit.lean
```

[comparator.json](comparator.json) compares the nine independently stated theorems (`Erdos575.not_erdos_575_corrected`, `Erdos575.not_erdos_575`, `Erdos575.not_erdos_575_all_bipartite`, `Erdos575.correctedCounterexample`, `Erdos575.quantitativeCounterexample`, `Erdos575.ForestCounterexample.forestCounterexample`, `Erdos575.ForestCounterexample.forestFamily_not_isBipartiteCompact`, `Erdos575.erdos_575`, and `Erdos575.erdos_575_unrestricted`) in `Challenge` and `Solution`, permitting only `propext`, `Quot.sound`, and `Classical.choice` and enabling NanoDa:

```sh
lake env lake comparator --config comparator.json
```

The `verify.sh` script writes build, axiom-audit, and Comparator logs to the Git-ignored `.verification/` directory.
