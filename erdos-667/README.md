# Erdős 667: monotonicity and Ramsey bounds for locally dense clique exponents

This package formalizes the resolved variants and foundational bounds for Erdős problem 667 (Erdős, Faudree, Rousseau, and Schelp, 1994) on the clique growth exponent
$$c(p, q) = \liminf_{n \to \infty} \frac{\log H(n; p, q)}{\log n}$$
of $(p, q)$-locally dense graphs: monotonicity of $c(p, q)$ in $q$ (`erdos_667.variants.monotoneOn`), the right-endpoint identity $c\bigl(p, \binom{p-1}{2} + 1\bigr) = 1$ for $p \ge 2$ (`erdos_667.variants.endpoint`), and the Erdős–Szekeres Ramsey lower bounds $\frac{1}{p - 1} \le c(p, 1) \le c(p, q)$ for all $p \ge 2$ and $q \ge 1$.

See [Erdős problem #667](https://www.erdosproblems.com/667) for background and literature.

## Scope and main results

Proves the monotone-variant, endpoint-variant, Ramsey-lower-bound, and universal lower-bound declarations described below. The strict monotonicity conjecture across intermediate local densities (`erdos_667`) and the probabilistic Ramsey upper bound $c(p, 1) \le \frac{2}{p + 1}$ for $p \ge 3$ remain open.

[Solution.lean](Solution.lean) exports 4 unconditional theorems in `Erdos667` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) proved in [Proofs/LocalDensityEndpointAndRamseyBounds667.lean](Proofs/LocalDensityEndpointAndRamseyBounds667.lean), using only the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem in `Solution.lean` | Mathematical statement |
| --- | --- |
| `Erdos667.variants.monotoneOn` | **Formal Conjectures Erdős 667 `monotoneOn` variant.** Proves `MonotoneOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1))` for all `p : ℕ`. |
| `Erdos667.variants.endpoint` | **Formal Conjectures Erdős 667 `endpoint` variant.** Proves `c p (Nat.choose (p - 1) 2 + 1) = 1` for all `p ≥ 2`. |
| `Erdos667.variants.ramsey_lower_bound` | **Erdős–Szekeres Ramsey lower bound.** Proves `1 / ((p : ℝ) - 1) ≤ c p 1` for all `p ≥ 2`. |
| `Erdos667.variants.c_ge_inv_pred` | **Universal lower bound for `q ≥ 1`.** Proves `1 / ((p : ℝ) - 1) ≤ c p q` for all `p ≥ 2` and `q ≥ 1`. |

[Statement.lean](Statement.lean) records the benchmark statement without placeholders, and [AxiomAudit.lean](AxiomAudit.lean) verifies statement fidelity, non-vacuity (`H(n; 3, 2) = ⌊(n + 1)/2⌋`), and the transitive axioms of every exported endpoint.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license information.
