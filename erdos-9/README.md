# Erdős Problem 9 — Standalone Proof Package

This standalone Lean 4.35.0-rc2 package proves the exact Formal Conjectures declaration `erdos_9.variants.infinite`: infinitely many odd integers are not the sum of a prime and two powers of two.

## Verification

Run `./verify.sh` to build `Statement`, `Solution`, `AxiomAudit`, and `Challenge` and verify that the exported theorem depends only on `[propext, Classical.choice, Quot.sound]`.
