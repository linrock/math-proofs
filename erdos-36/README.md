# Erdős 36: the minimum overlap problem

This package formalizes foundational results and classical asymptotic bounds for Erdős's minimum overlap problem (Erdős problem 36). For balanced partitions (A, B) of {1, ..., 2N} into two sets of size N, it proves Fekete convergence of the normalized minimum maximum difference overlap M(N)/N to a limit c, establishes the classical bounds of Erdős (1/4 ≤ c ≤ 1/2), Scherk (1 - 1/√2 < c), Świerczkowski ((4 - √6)/5 < c), and Moser (√2/4 ≤ c), proves a combined Moser–Scherk quartic inequality, and certifies exact values of M(N) up to M(15) = 6.

See [Erdős problem #36](https://www.erdosproblems.com/36) for background and literature.

## Scope and main results

Proves existence of the asymptotic minimum-overlap constant c = lim M(N)/N, the classical lower and upper bounds of Erdős, Scherk, Świerczkowski, and Moser, the combined Moser–Scherk inequality, and exact finite values through N = 15. Determining the exact value of c remains open.

[Solution.lean](Solution.lean) exports 9 unconditional theorems in `Erdos36` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) across 2 self-contained proof modules in [Proofs/](Proofs), using only the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem in `Solution.lean` | Mathematical statement |
| --- | --- |
| `Erdos36.liminf_eq_limsup_minOverlapQuotient` | **Fekete limit equality liminf = limsup for M(N)/N.** Proves atTop.liminf MinOverlapQuotient = atTop.limsup MinOverlapQuotient. |
| `Erdos36.tendsto_minOverlapQuotient_liminf` | **Formal Conjectures Erdős 36 variants.exists.** Proves MinOverlapQuotient converges to its liminf. |
| `Erdos36.minimum_overlap_variants_lower_erdos_1955` | **Formal Conjectures minimum_overlap.variants.lower.erdos_1955.** Proves 1/4 ≤ liminf M(N)/N. |
| `Erdos36.minimum_overlap_variants_lower_scherk_1955` | **Formal Conjectures minimum_overlap.variants.lower.scherk_1955.** Proves 1 - 1/√2 < liminf M(N)/N. |
| `Erdos36.minimum_overlap_variants_lower_swierczkowski_1958` | **Formal Conjectures minimum_overlap.variants.lower.swierczkowski_1958.** Proves (4 - √6)/5 < liminf M(N)/N. |
| `Erdos36.moser_sqrt_two_div_four_le_liminf` | **Moser (1959) √2/4 second-moment lower bound.** Proves √2/4 ≤ liminf M(N)/N. |
| `Erdos36.minimum_overlap_variants_upper_erdos_1955` | **Formal Conjectures minimum_overlap.variants.upper.erdos_1955.** Proves limsup M(N)/N ≤ 1/2. |
| `Erdos36.moser_scherk_combined_le_M` | **Combined Moser–Scherk cap-and-moment lower bound.** Proves the combined quartic cap-and-moment inequality on M(n). |
| `Erdos36.exact_values_M` | **Exact finite evaluations of M(n) up to n = 15.** Proves M(1)=1, M(2)=1, M(3)=2, M(6)=3, M(7)=3, M(8)=4, M(9)=4, M(12)=5, M(14)=6, M(15)=6. |

[Statement.lean](Statement.lean) records the benchmark statement without placeholders, and [AxiomAudit.lean](AxiomAudit.lean) verifies statement fidelity, non-vacuity witnesses, and the transitive axioms of every exported endpoint.

## Proof modules

- [MinimumOverlapFoundations36.lean](Proofs/MinimumOverlapFoundations36.lean): Formalizes balanced partitions, difference-overlap histograms, Fekete subadditivity, Erdős's 1/4 and 1/2 bounds, and exact values of M(N) up to N = 15.
- [MoserScherkAndFeketeLimit36.lean](Proofs/MoserScherkAndFeketeLimit36.lean): Proves Fekete limit convergence and the lower bounds of Scherk (1 - 1/√2), Świerczkowski ((4 - √6)/5), and Moser (√2/4), plus the combined Moser–Scherk inequality.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license information. Running `./verify.sh --no-sandbox` builds all targets from source, audits transitive axioms, and runs `lake comparator` so both `nanoda_bin` and Lean's default kernel check `Solution` against `Challenge`.
