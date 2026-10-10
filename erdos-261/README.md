# Erdős #261: dyadic weighted representations $n / 2^n = \sum_{k=1}^t a_k / 2^{a_k}$

This standalone Lean 4 project formalizes all known unconditional results for [Erdős problem #261](https://www.erdosproblems.com/261), proving all five solved statements in [`FormalConjectures/ErdosProblems/261.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/261.lean) together with the extremal bounds, structural divisibility and uniqueness theorems, punctured-interval family, and $n \le 10000$ verification of [Tengely, Ulas, and Zygadło (2020)](https://arxiv.org/abs/2008.01501).

Erdős and Graham posed three questions about representations of rational numbers as sums of distinct terms of the form $a / 2^a$ ($a \in \mathbb{N}_{>0}$):

- **Part (i) (Solved — Yes):** Are there infinitely many positive integers $n$ such that
  $$\frac{n}{2^n} = \sum_{k=1}^t \frac{a_k}{2^{a_k}}$$
  for some $t \ge 2$ and pairwise distinct positive integers $a_1, \dots, a_t$?
- **Part (ii) (Open, verified for $n \le 10000$):** Does every positive integer $n$ admit such a representation?
- **Part (iii) (Open for $2^{\aleph_0}$, solved for any finite $2^m$):** Is there a rational number $x$ with at least $2^{\aleph_0}$ (or, in Erdős's weaker phrasing, at least $2$) distinct infinite representations $x = \sum_{k=0}^\infty a_k / 2^{a_k}$ by strictly increasing positive integers $a_k$?

### Summary of formalized results

1. **Borwein–Loring identity and construction (`borwein_loring`, `borwein_loring_property`):** For every $m \ge 1$ and $n = 2^{m+1} - m - 2$,
   $$\frac{n}{2^n} = \sum_{k = n + 1}^{n + m} \frac{k}{2^k},$$
   giving an explicit $m$-term representation `Erdos261Prop (2 ^ (m + 1) - m - 2)` for every $m \ge 2$ ([Borwein and Loring 1990](https://doi.org/10.1090/S0025-5718-1990-0993927-5)).
2. **Erdős #261 Part (i) (`erdos_261_parts_i`):** Infinitely many positive integers $n$ admit a representation $n / 2^n = \sum_{k=1}^t a_k / 2^{a_k}$ with $t \ge 2$ distinct positive integers.
3. **Complete verification up to $n \le 10000$ (`le_10000`):** Every positive integer $1 \le n \le 10000$ satisfies `Erdos261Prop n`, formalizing Theorem 3.5 of [Tengely, Ulas, and Zygadło (*J. Number Theory* 214, 2020, 445–459)](https://arxiv.org/abs/2008.01501).
4. **Multiple infinite representations and $2^m$ family (`two_representations`, `infinite_rationals_two_pow_reps`):** For every $m \in \mathbb{N}$, infinitely many rationals $x \in \mathbb{Q}$ have at least $2^m$ distinct infinite representations $x = \sum_{k=0}^\infty a_k / 2^{a_k}$ by strictly increasing positive integers, constructed by independently toggling $m$ disjoint Borwein–Loring intervals $[n_r, n_r + r]$ ($n_r = 2^{r+1} - r - 2$) and appending any contiguous tail $[L + 1, \infty)$.
5. **Sharp extremal upper bound and uniqueness (`max_n_bound`, `borwein_loring_unique`):** In any $t$-term representation ($t \ge 2$) of $n / 2^n = \sum_{k=1}^t a_k / 2^{a_k}$ by distinct positive integers,
   $$n \le 2^{t+1} - t - 2,$$
   with equality if and only if the sorted terms are $a_k = n + 1 + k$ (Theorem 2.1(i) of Tengely, Ulas, and Zygadło 2020).
6. **First-term localization and last-term divisibility (`exists_term_le_add_three`, `last_term_gap_dvd`):** In any $t$-term representation ($t \ge 2$) of $n / 2^n$ ($n \ge 1$) by distinct positive integers, every term satisfies $a_k \ge n + 1$, at least one term satisfies $n + 1 \le a_k \le n + 3$, and for any strictly increasing $(t + 2)$-term representation, $2^{a_{t+1} - a_t} \mid a_{t+1}$ (Theorem 2.1(ii) of Tengely, Ulas, and Zygadło 2020).
7. **Punctured-interval non-Borwein–Loring infinite family (`punctured_family_erdos261Prop`):** For every $k \ge 1$, the integer $n_k = (2^{4k+2} + 1) / 5 - 4k$ (starting at $n_1 = 9$) satisfies `Erdos261Prop n_k` via the punctured interval $(n_k, n_k + 4k + 1] \setminus \{n_k + 4k - 1\}$ (Theorem 3.1 of Tengely, Ulas, and Zygadło 2020).
8. **Splicing representations to arbitrary length (`arbitrary_length_rep_of_all_erdos261Prop`):** Splicing any representation at its maximum element shows that if every positive integer satisfies `Erdos261Prop` (Part (ii)), then every $n \ge 1$ admits representations of arbitrarily large length $t \ge L$.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) proves twelve benchmark targets in `Erdos261.Palomar` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) along with the five literal `FormalConjectures` declarations in `Erdos261`:

| Declaration | Meaning |
| --- | --- |
| `Erdos261.Palomar.borwein_loring` | For $m > 0$ and $n = 2^{m+1} - m - 2$, $n / 2^n = \sum_{k \in (n, n+m]} k / 2^k$. |
| `Erdos261.Palomar.borwein_loring_property` | For $m \ge 2$, $n = 2^{m+1} - m - 2$ satisfies `Erdos261Prop n`. |
| `Erdos261.Palomar.erdos_261_parts_i` | Erdős #261 Part (i): infinitely many positive integers $n$ satisfy `Erdos261Prop n` (`True ↔ {n : ℕ \| 0 < n ∧ Erdos261Prop n}.Infinite`). |
| `Erdos261.Palomar.le_10000` | Every integer $1 \le n \le 10000$ satisfies `Erdos261Prop n` (Tengely–Ulas–Zygadło 2020, Theorem 3.5). |
| `Erdos261.Palomar.two_representations` | There exists a rational $x \in \mathbb{Q}$ with at least two distinct strictly increasing infinite representations $x = \sum_{k=0}^\infty a_k / 2^{a_k}$ (`True ↔ ...`). |
| `Erdos261.Palomar.infinite_rationals_two_pow_reps` | For every $m \in \mathbb{N}$, infinitely many rationals $x \in \mathbb{Q}$ admit at least $2^m$ distinct strictly increasing infinite representations. |
| `Erdos261.Palomar.max_n_bound` | Every $t$-term representation ($t \ge 2$) of $n / 2^n$ satisfies $n \le 2^{t+1} - t - 2$ (Tengely–Ulas–Zygadło 2020, Theorem 2.1(i)). |
| `Erdos261.Palomar.exists_term_le_add_three` | Every $t$-term representation ($t \ge 2$) of $n / 2^n$ ($n \ge 1$) contains a term $a_k \in [n + 1, n + 3]$ (Tengely–Ulas–Zygadło 2020, Theorem 2.1(ii)). |
| `Erdos261.Palomar.last_term_gap_dvd` | Every strictly increasing $(t + 2)$-term representation of $n / 2^n$ satisfies $2^{a_{t+1} - a_t} \mid a_{t+1}$ (Tengely–Ulas–Zygadło 2020, Theorem 2.1(ii)). |
| `Erdos261.Palomar.borwein_loring_unique` | For $n = 2^{t+1} - t - 2$ ($t \ge 2$), $a_k = n + 1 + k$ is the unique strictly increasing $t$-term representation of $n / 2^n$ (Tengely–Ulas–Zygadło 2020, Theorem 2.1(i)). |
| `Erdos261.Palomar.punctured_family_erdos261Prop` | For every $k \ge 1$, $n_k = (2^{4k+2} + 1) / 5 - 4k$ satisfies `Erdos261Prop n_k` (Tengely–Ulas–Zygadło 2020, Theorem 3.1). |
| `Erdos261.Palomar.arbitrary_length_rep_of_all_erdos261Prop` | If `∀ m > 0, Erdos261Prop m`, then every $n > 0$ has representations of length $t \ge L$ for all $L$. |

[Statement.lean](Statement.lean) records all five solved Formal Conjectures propositions without placeholders. [AxiomAudit.lean](AxiomAudit.lean) verifies definitional statement fidelity across all five Formal Conjectures statements, the explicit finite non-vacuity witness `nonvacuity_10000` at $n = 10000$, and the transitive axioms of all 23 endpoints.

## Mathematical idea and module outline

The five modules in [Proofs/](Proofs) implement the formal proofs:

1. **[Definitions261.lean](Proofs/Definitions261.lean)**: Defines `Erdos261Prop`, `Erdos261InfiniteRepresentation`, and `dyadicTerm`. Proves the telescoping interval identity
   $$\sum_{k \in (a, a+m]} \frac{k}{2^k} = \frac{a + 2}{2^a} - \frac{a + m + 2}{2^{a + m}},$$
   derives `borwein_loring`, `borwein_loring_property`, and `erdos_261_parts_i`, and proves the antotonicity of $k \mapsto k / 2^k$ for $k \ge 1$, the lower bound $a_k \ge n + 1$ for every term in a representation with $t \ge 2$, the majorization inequality $\sum_{a \in S} a / 2^a \le \sum_{b \in (n, n+t]} b / 2^b$, the sharp upper bound `max_n_bound` and its equality uniqueness `borwein_loring_unique`, the first-term localization `exists_term_le_add_three`, the 2-adic gap divisibility `last_term_gap_dvd`, the punctured-interval family `punctured_family_erdos261Prop`, and arbitrary-length splicing `arbitrary_length_rep_of_all_erdos261Prop`.
2. **[TwoRepresentations261.lean](Proofs/TwoRepresentations261.lean)**: Uses pairwise disjoint Borwein–Loring blocks $[n_r, n_r + r]$ ($n_r = 2^{r+1} - r - 2$) to construct $2^m$ distinct prefix sets `prefixFinset m c` ($c : \text{Fin } m \to \text{Bool}$) with identical dyadic sum, appends contiguous tails $[L + 1, \infty)$ via `Finset.orderEmbOfFin` (`seqOfFinset`), evaluates the infinite tail sum directly in $\mathbb{Q}$ from the telescoping partial sums, and proves `infinite_rationals_two_pow_reps` and `two_representations`.
3. **[CertificateCore261.lean](Proofs/CertificateCore261.lean)**: Pure `Init`-only module (no `Mathlib` import, 135 lines) implementing the finite-certificate evaluator for $2 \le n \le 10000$. At step $i$, a scaled remainder $v / 2^{i-1}$ transitions to $(2v - i \cdot \varepsilon_i) / 2^i$ ($\varepsilon_i \in \{0, 1\}$); grouping $b \le 64$ steps into a bitmask $M < 2^b$ updates $(i, v) \mapsto (i + b,\; 2^b v - i \cdot M - W_b(M))$, where the block weight $W_b(M) = \sum_{j=0}^{b-1} j \cdot \varepsilon_j 2^{b-1-j}$ (`wSpec`) is evaluated in constant time by a 64-bit bitwise sum (`w64`).
4. **[CertificateData261.lean](Proofs/CertificateData261.lean)**: Imports only `CertificateCore261` (keeping baseline memory at ~500 MiB) and kernel-checks (`decide +kernel`) the four coalesced trajectory forests `forest0..forest3` covering all $2 \le n \le 10000$ (`f0_ok..f3_ok` and `all_seq_ok`). By merging branches whenever two starting values of $n$ reach the same state $(i, v)$ and packing 64 steps into one 64-bit mask $M$, the ~119 million individual greedy/lazy steps across $2 \le n \le 10000$ compress into ~23,000 block steps.
5. **[CertificateEngine261.lean](Proofs/CertificateEngine261.lean)**: Proves the unified soundness of `wSpec`, `w64`, `stepVar`, `runB64`, `evalState`, `checkForestStates`, `mergeAllLists`, and `checkSeq`, and combines them with `CertificateData261` and the base case $n = 1$ ($1/2^1 = 3/2^3 + 6/2^6 + 8/2^8$) to establish `le_10000`.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution. Both `./verify.sh` and `lake env lake comparator --config comparator.json` pass, with both `nanoda_bin` and Lean's default kernel accepting `Solution`.
