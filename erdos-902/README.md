# Erdős 902: Schütte's paradoxical tournaments

This package formalizes unconditional lower and upper bounds, exact small-case evaluations, Paley quadratic-residue tournament constructions, and second-moment domination criteria for Erdős problem 902 (Schütte's problem; Erdős 1963, Szekeres–Szekeres 1965) on the minimum number of vertices $f(n)$ of a tournament in which every $n$-element vertex subset is dominated by at least one vertex.

See [Erdős problem #902](https://www.erdosproblems.com/902) for background and literature.

## Scope and main results

Proves the exact small-case evaluations $f(0) = 1$, $f(1) = 3$, $f(2) = 7$ (via the 7-vertex Paley tournament $\mathrm{QR}_7$), the bracket $14 \le f(3) \le 19$ and the exact value $f(3) = 19$ (via the 19-vertex Paley tournament $\mathrm{QR}_{19}$), the $k = 4$ interval $47 \le f(4) \le 67$ (via $\mathrm{QR}_{67}$), Erdős's lower bound $f(k) \ge 2^{k+1} - 1$ and the Szekeres–Szekeres lower bound $f(k) \ge (k + 2) 2^{k-1} - 1$ for all $k \ge 1$, the finite tournament orientation-space union-bound bridge and unit-leading probabilistic upper bounds $f(n) \le n(n+1)2^n$ and $f(n) \le n + (n^2 + 5)2^n$ for all $n \ge 1$ (with $f(n) \le n^2 2^n$ for all $n \ge 11$), the general $\mathbb{Z}/p\mathbb{Z}$ Paley tournament construction and $(p-1)/2$-regularity for every prime $p \equiv 3 \pmod{4}$, the deterministic Cauchy–Schwarz second-moment pairwise out-neighborhood intersection criterion, and the complete falsification of the first-moment union-bound criterion at $N = n^2 2^n$ for $1 \le n \le 10$. Closing the asymptotic factor-$n$ gap between $\Omega(n 2^n)$ and $O(n^2 2^n)$ remains open.

[Solution.lean](Solution.lean) exports 16 theorems: twelve package-local results in `Erdos902.Core` — eight closed statements and four that carry explicit hypotheses (the range restriction `1 ≤ n`, the first-moment union bound, the second-moment intersection inequality, and the prime congruence `p ≡ 3 (mod 4)`) — and four upstream-anchored results in `Erdos902` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) proved across [Proofs/Erdos902Unified435.lean](Proofs/Erdos902Unified435.lean), [Proofs/SzekeresParityRefinementAndTightenedBinomialBounds902.lean](Proofs/SzekeresParityRefinementAndTightenedBinomialBounds902.lean), [Proofs/SecondOrderBinomialDecayAndTransitiveTripleCounting902.lean](Proofs/SecondOrderBinomialDecayAndTransitiveTripleCounting902.lean), [Proofs/QuinticBinomialDecayAndKendallBabingtonSmithBounds902.lean](Proofs/QuinticBinomialDecayAndKendallBabingtonSmithBounds902.lean), and [Proofs/Blueprint902.lean](Proofs/Blueprint902.lean), using only the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem in `Solution.lean` | Mathematical statement |
| --- | --- |
| `Erdos902.Core.hasParadoxicalTournament_zero_iff_and_f_zero` | **Base evaluation $f(0) = 1$.** Proves $\mathrm{HasParadoxicalTournament}(0, N) \iff 1 \le N$ and $f(0) = 1$. |
| `Erdos902.Core.hasParadoxicalTournament_one_iff_and_f_one` | **Exact value $f(1) = 3$.** Proves `IsParadoxicalTournament 1 paley3Digraph`, $\mathrm{HasParadoxicalTournament}(1, N) \iff 3 \le N$, and $f(1) = 3$. |
| `Erdos902.Core.paley7Digraph_dom2_and_f_two` | **Exact value $f(2) = 7$ via Paley $\mathrm{QR}_7$.** Proves `IsParadoxicalTournament 2 paley7Digraph`, $\mathrm{HasParadoxicalTournament}(2, N) \iff 7 \le N$, and $f(2) = 7$. |
| `Erdos902.Core.hasParadoxicalTournament_three_iff_and_f_three` | **Bounds $14 \le f(3) \le 19$ and exact value $f(3) = 19$ via Paley $\mathrm{QR}_{19}$.** Proves `IsParadoxicalTournament 3 paley19Digraph`, $\mathrm{HasParadoxicalTournament}(3, N) \iff 19 \le N$, $14 \le f(3) \le 19$, and $f(3) = 19$. |
| `Erdos902.Core.hasParadoxicalTournament_four_67_and_f_four_bounds` | **Paley $\mathrm{QR}_{67}$ witness and $n = 4$ bracket.** Proves `IsParadoxicalTournament 4 paley67Digraph` and $47 \le f(4) \le 67$. |
| `Erdos902.Core.erdos_and_szekeres_lower_bounds` | **Erdős and Szekeres–Szekeres lower bounds.** Proves $f(k) \ge 2^{k+1} - 1$ and $f(k) \ge (k + 2)2^{k-1} - 1$ for all $k \ge 1$. |
| `Erdos902.Core.hasParadoxicalTournament_of_erdosProbabilisticCriterion` | **Finite orientation-space union-bound bridge.** Proves $\binom{N}{n}(2^n - 1)^{N-n} < (2^n)^{N-n} \implies \mathrm{HasParadoxicalTournament}(n, N)$ for $n \le N$. |
| `Erdos902.Core.erdos_szekeres_f_sandwich` | **Erdős–Szekeres–Szekeres two-sided sandwich.** Proves $2^{n+1} - 1 \le f(n)$, $(n+2)2^{n-1} - 1 \le f(n)$, and $f(n) \le n + 2n(n+1)2^n \le 5n^2 2^n$ for all $n \ge 1$. |
| `Erdos902.Core.unit_leading_and_quintic_upper_bounds` | **Unit-leading and mid-range upper bounds.** Proves $f(n) \le n(n+1)2^n$ and $f(n) \le n + (n^2 + 5)2^n$ for $n \ge 1$, $f(n) \le n^2 2^n$ for $n \ge 11$, and explicit mid-range bounds for $5 \le n \le 10$. These bounds are weaker in the leading coefficient than Erdős's $\log 2$ bound. |
| `Erdos902.Core.isTournament_and_regular_paleyFinDigraph` | **General Paley tournament construction.** Proves that `paleyFinDigraph p` is a $(p-1)/2$-regular tournament on `Fin p` for every prime $p \equiv 3 \pmod{4}$. |
| `Erdos902.Core.isParadoxicalTournament_of_second_moment_commonOutNeigh` | **Second-moment pairwise-intersection criterion.** Proves `IsParadoxicalTournament k G` whenever $(\binom{N}{k} - 1)\sum_{u,v}\binom{|N^+(u)\cap N^+(v)|}{k} < (\sum_v \binom{|N^+(v)|}{k})^2$. |
| `Erdos902.Core.twenty_nine_seventy_nine_lower_bound_and_not_criterion_ten` | **Falsification of first-moment union bound at $N = n^2 2^n$ ($1 \le n \le 10$).** Proves $29 \cdot (2^n)^{2^n} \le 79 \cdot (2^n - 1)^{2^n}$ for $n \ge 8$ and $\neg \mathrm{ErdosProbabilisticCriterion}(n, n^2 2^n)$ for $1 \le n \le 10$. |
| `Erdos902.erdos_902.variants.f_two` | **Upstream `erdos_902.variants.f_two`.** Proves $f(2) = 7$. |
| `Erdos902.erdos_902.variants.erdos_lower` | **Upstream `erdos_902.variants.erdos_lower`.** Proves $2^{n+1} - 1 \le f(n)$ for every $n$. |
| `Erdos902.erdos_902.variants.szekeres_f_three` | **Upstream `erdos_902.variants.szekeres_f_three`.** Proves $f(3) = 19$. |
| `Erdos902.erdos_902.variants.szekeres_lower` | **Upstream `erdos_902.variants.szekeres_lower`.** Proves a linear-exponential lower bound $c \cdot n \cdot 2^n \le f(n)$ eventually, for some $c > 0$. |

[Statement.lean](Statement.lean) fixes the shared definitions used by the benchmark statements, and [AxiomAudit.lean](AxiomAudit.lean) verifies statement fidelity and the transitive axioms of every exported endpoint.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license information.
