# Erdős Problem 18: practicality of factorials and the bound h(n!) < n

A standalone Lean 4 package for [Erdős Problem 18](https://www.erdosproblems.com/18) on practical numbers and representations of integers as sums of distinct divisors of factorials. A positive integer n is practical when every m ≤ n is a sum of distinct divisors of n; for a practical n, h(n) is the largest, over 1 ≤ m ≤ n, of the least number of distinct divisors of n whose sum is m.

## What is proved

- **Factorials are practical.** For every n, the number n! is practical, so that h(n!) is well defined.
- **The classical linear upper bound.** h(n!) < n for all sufficiently large n.

The practicality of n! is a textbook fact; the linear upper bound h(n!) < n is due to Erdős and Graham (1980). Both are formalized here in Lean 4 with no placeholders. The two declarations `Erdos18.Palomar.factorial_isPractical` and `Erdos18.Palomar.erdos_18_upper_bound` are matched by `Challenge.lean` and listed in `comparator.json`.

## Scope

The conjectures erdos_18a, erdos_18b, and erdos_18c on the true order of h(n!) remain open, and this package does not resolve them. The linear bound formalized here is the classical theorem, not the current state of the art: later work proves the much stronger asymptotic bound h(n!) ≤ (2 log 2 + o(1)) · n / log n (Hughes, arXiv:2609.10902).

## Verification

Run from this directory:

```sh
./verify.sh
```

This builds `Statement`, `Solution`, `AxiomAudit`, and `Challenge`, and checks that every exported theorem depends only on the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). Toolchain pins: Lean `leanprover/lean4:v4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. See [BUILD.md](BUILD.md) for build details and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution.
