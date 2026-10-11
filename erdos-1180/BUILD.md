# Build and audit Erdős #1180

Run the following commands from this directory. Elan selects the exact compiler from [lean-toolchain](lean-toolchain): Lean `v4.35.0-rc2`, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`. The canonical Mathlib commit is `065356127b1dc0016f66b7283ce0ce2c4055aa55`, pinned by [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json). Ordinary replay does not require `lake update`.

```sh
lake exe cache get
./verify.sh
```

The first command downloads canonical compiled Mathlib dependencies. The [verify.sh](verify.sh) script runs the Palomar preliminary checks, verifies the compiler and Mathlib revisions, builds `Statement`, `Solution`, `AxiomAudit`, and `Challenge` (including all three modules in `Proofs/` with `-j1 -M8192 -E hasSorry`), and runs a standalone endpoint axiom audit on `AxiomAudit.lean` verifying that all 30 endpoint, statement-fidelity, and non-vacuity theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

A normal Lake build and explicit endpoint audit can also be run directly:

```sh
lake build Statement Solution AxiomAudit Challenge
lake env lean -j1 -M8192 -E hasSorry -Dformat.width=1000000 \
  --setup=.lake/build/ir/AxiomAudit.setup.json AxiomAudit.lean
```

[comparator.json](comparator.json) compares the seventeen independently stated theorems (`Erdos1180.Palomar.erdos_1180`, `Erdos1180.Palomar.erdos_1180_variants_glibichuk`, `Erdos1180.Palomar.erdos_1180_variants_shparlinski`, `Erdos1180.Palomar.erdos_1180_variants_lower_bound`, `Erdos1180.Palomar.erdos_1180_variants_lower_bound_large_primes`, `Erdos1180.Palomar.not_erdos_1180_variants_optimal`, `Erdos1180.Palomar.two_rpow_inv_le_four_mul_C`, `Erdos1180.Palomar.inv_le_CAsymptotic`, `Erdos1180.Palomar.natCeil_inv_le_CAsymptotic`, `Erdos1180.Palomar.CAsymptotic_le_thirty_two_mul_inv_sq`, `Erdos1180.Palomar.CAsymptotic_le_eight_mul_sq_of_one_lt_mul`, `Erdos1180.Palomar.CAsymptotic_le_eight_mul_succ_of_two_lt_mul`, `Erdos1180.Palomar.CAsymptotic_le_eight_mul_of_lt_mul`, `Erdos1180.Palomar.CAsymptotic_le_sixteen_of_two_thirds_lt`, `Erdos1180.Palomar.CAsymptotic_le_eight_mul_floor_inv_add_one_sq`, `Erdos1180.Palomar.eventually_CAsymptotic_le_eight_add_mul_inv_sq`, `Erdos1180.Palomar.CAsymptotic_inv_nat_lt_C_inv_nat`) in `Challenge` and `Solution`, permitting only `propext`, `Quot.sound`, and `Classical.choice` and enabling NanoDa:

```sh
lake env lake comparator --config comparator.json
```

To also run `comparator` locally with both NanoDa and Lean's default kernel:

```sh
./verify.sh --no-sandbox
```

The `verify.sh` script writes build, axiom-audit, and Comparator logs to the Git-ignored `.verification/` directory.
