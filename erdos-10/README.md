# Erdős Problem 10 — Standalone Proof Package

This standalone Lean 4.35.0-rc2 package proves the exact Formal Conjectures declaration that `1117175146` is not the sum of a prime and at most three powers of two. It also proves the stronger infinite even-exception variants for two and three powers.

## Verification

Run `./verify.sh` to build `Statement`, `Solution`, `AxiomAudit`, and `Challenge` and verify that all exported theorems depend only on `[propext, Classical.choice, Quot.sound]`.
