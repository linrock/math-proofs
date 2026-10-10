# Build and audit Erdős #261

Run the following commands from this directory. Elan selects the exact compiler from [lean-toolchain](lean-toolchain): Lean `v4.35.0-rc2`, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`. The canonical Mathlib commit is `065356127b1dc0016f66b7283ce0ce2c4055aa55`, pinned by [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json). Ordinary replay does not require `lake update`.

```sh
lake exe cache get
./verify.sh
```

The first command downloads canonical compiled Mathlib dependencies. The [verify.sh](verify.sh) script runs the Palomar preliminary checks, verifies the compiler and Mathlib revisions, builds `Statement`, `Solution`, `AxiomAudit`, and `Challenge` (including all five modules in `Proofs/` with `-j1 -M8192 -E hasSorry`), and runs a standalone endpoint axiom audit on `AxiomAudit.lean` verifying that all 23 endpoint, statement-fidelity, and non-vacuity theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

A normal Lake build and explicit endpoint audit can also be run directly:

```sh
lake build Statement Solution AxiomAudit Challenge
lake env lean -j1 -M8192 -E hasSorry -Dformat.width=1000000 \
  --setup=.lake/build/ir/AxiomAudit.setup.json AxiomAudit.lean
```

[comparator.json](comparator.json) compares the twelve independently stated theorems (`Erdos261.Palomar.borwein_loring`, `Erdos261.Palomar.borwein_loring_property`, `Erdos261.Palomar.erdos_261_parts_i`, `Erdos261.Palomar.le_10000`, `Erdos261.Palomar.two_representations`, `Erdos261.Palomar.infinite_rationals_two_pow_reps`, `Erdos261.Palomar.max_n_bound`, `Erdos261.Palomar.exists_term_le_add_three`, `Erdos261.Palomar.last_term_gap_dvd`, `Erdos261.Palomar.borwein_loring_unique`, `Erdos261.Palomar.punctured_family_erdos261Prop`, `Erdos261.Palomar.arbitrary_length_rep_of_all_erdos261Prop`) in `Challenge` and `Solution`, permitting only `propext`, `Quot.sound`, and `Classical.choice` and enabling NanoDa:

```sh
lake env lake comparator --config comparator.json
```

The `verify.sh` script writes build, axiom-audit, and Comparator logs to the Git-ignored `.verification/` directory.
