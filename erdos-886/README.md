# Erdős Problem 886: divisors in short intervals above √n

A standalone Lean 4 package for [Erdős Problem 886](https://www.erdosproblems.com/886) on the number of divisors of n in the short interval (n^{1/2}, n^{1/2} + n^{1/2 − ε}). Erdős attributes the conjecture to Ruzsa. The open question is whether, for every ε > 0, that count is O_ε(1) for all sufficiently large n.

## What is proved

- **Both Erdős–Rosenfeld variants at the critical exponent ε = 1/4.** There are infinitely many n with at least four divisors in (n^{1/2}, n^{1/2} + 16 n^{1/4}), and for every C > 0 at most 1 + C² divisors of n lie in [n^{1/2}, n^{1/2} + C n^{1/4}] for all sufficiently large n. These are the theorems of Erdős and Rosenfeld (1997).
- **The unconditional regime ε ≥ 1/4.** For every n and every ε ≥ 1/4 the open interval (n^{1/2}, n^{1/2} + n^{1/2 − ε}) contains at most one divisor of n, because the complementary-divisor sum d + n/d is strictly increasing for d ≥ n^{1/2} and lies inside (2 n^{1/2}, 2 n^{1/2} + 1).
- **The exact reduction of the conjecture.** The main quantifier is equivalent to its restriction to the window 0 < ε < 1/4, so only that range remains.

Supporting results include the fifth-order hyperbolic Vandermonde determinant identities on 6-tuples of divisors (with the n² < V₆ bound), the complementary-divisor GCD and LCM dualities, the four-factor coprime-cofactor decomposition, Finset LCM divisibility, and prime-power valuation bounds.

## Scope

The main conjecture erdos_886 remains open for 0 < ε < 1/4. The obstruction in that window is that the complementary-sum interval has unbounded length n^{1/2 − 2ε}, and bounding the divisor count uniformly there would require Thue–Siegel–Roth or Subspace-Theorem diophantine approximation input on hyperbolic divisor curves that is not available in Mathlib.

The 24 declarations listed in `comparator.json` are matched by `Challenge.lean` and proved in `Solution.lean`.

## Verification

Run from this directory:

```sh
./verify.sh
```

This builds `Statement`, `Solution`, `AxiomAudit`, and `Challenge`, and checks that every exported theorem depends only on the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). Toolchain pins: Lean `leanprover/lean4:v4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. See [BUILD.md](BUILD.md) for build details and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution.
