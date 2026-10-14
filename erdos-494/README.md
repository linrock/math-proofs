# Erdős Problem 494 — Palomar Standalone Proof Package

This standalone Lean 4.35.0-rc2 package proves the Selfridge–Straus (1958) theorems showing that a finite set `A ⊂ ℂ` is uniquely determined by its 2-sum multiset when `|A| ≠ 2^l`, and by its 3-sum multiset when `|A| > 6` and `|A| ∉ {27, 486}`. It proves two open variants from `FormalConjectures/ErdosProblems/494.lean`; the general Erdős Problem 494 remains out of scope.

## Verification

Run `./verify.sh` to build `Statement`, `Solution`, `AxiomAudit`, and `Challenge` and verify that all exported theorems depend only on `[propext, Classical.choice, Quot.sound]`.
