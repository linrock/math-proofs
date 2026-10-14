# Build and verify `erdos-18`

Toolchain pins: Lean `leanprover/lean4:v4.35.0-rc2` (selected by [lean-toolchain](lean-toolchain)) and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` (pinned by [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json)).

```sh
./verify.sh
```

`./verify.sh` builds `Statement`, `Solution`, `AxiomAudit`, and `Challenge`, and audits the transitive axioms of every exported theorem against `[propext, Classical.choice, Quot.sound]`. Passing `--no-sandbox` additionally runs `comparator` with both NanoDa and Lean's default kernel.
