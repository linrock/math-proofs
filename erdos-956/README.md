# Erdős #956: unit distances between disjoint convex translates

This standalone Lean 4 project gives a complete formal proof of the affirmative answer to the superlinear question in [Erdős problem #956](https://www.erdosproblems.com/956), together with explicit $\Omega(n^{4/3})$ lower bounds.

For a compact convex planar set $C \subset \mathbb{R}^2$, the distance between two translates $C + x$ and $C + y$ is the Euclidean minimum distance

$$\delta(C+x, C+y) = \inf_{c, d \in C} \|(c + x) - (d + y)\|_2,$$

and $h(n)$ denotes the maximum number of unordered pairs at distance $1$ among $n$ pairwise-disjoint translates of a single $C$ (where $C$ may depend on $n$). In [*Variations on the theme of repeated distances* (Combinatorica, 1990)](https://doi.org/10.1007/BF02122780), Erdős and Pach proved the upper bound $h(n) = O(n^{4/3})$ and asked whether $h(n) > n^{1+c}$ for some constant $c > 0$ and all sufficiently large $n$.

In [Oberwolfach Report 17/2005](https://ems.press/content/serial-article-files/45990?nt=1), Pavel Valtr announced $h(n) = \Theta(n^{4/3})$ using a parabolic norm construction, and in [April 2026](https://www.ulam.ai/research/erdos956.pdf), Przemysław Chojecki gave a six-page elementary Euclidean construction using a one-sided parabolic cap and two rectangular layers. This formalization extends that mechanism to a full **signed parabolic cap** and **four rectangular layers**, proving both the `FormalConjectures` superlinear statement and explicit $\Omega(n^{4/3})$ lower bounds with leading constant $2/5$.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) proves five benchmark targets in `Erdos956.Palomar` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) along with the explicit threshold theorem `erdos_956_two_fifths_from_204525328` and the literal `Erdos956.erdos_956` declaration:

| Declaration | Meaning |
| --- | --- |
| `Erdos956.Palomar.erdos_956_superlinear` | Direct affirmative solution: $\exists c > 0,\ \forall^\infty n \in \mathbb{N},\ n^{1+c} < h(n)$ (with $c = 1/4$). |
| `Erdos956.Palomar.erdos_956` | Elaborated Formal Conjectures `True ↔` form of Erdős #956. |
| `Erdos956.Palomar.erdos_956_omega_four_thirds` | Explicit all-$N$ lower bound: $\frac{1}{26} N^{4/3} < h(N)$ for all $N \ge 80$. |
| `Erdos956.Palomar.erdos_956_four_layer_polynomial` | Exact four-layer signed-grid bound: $72q^4 + 32q^3 + 24q^2 + 13q + 3 \le h(48q^3 + 16q^2 + 12q + 4)$ for all $q \ge 1$. |
| `Erdos956.Palomar.erdos_956_eventual_two_fifths` | Sharp eventual bound: $\forall^\infty N \in \mathbb{N},\ \frac{2}{5} N^{4/3} < h(N)$ (realized for all $N \ge 204{,}525{,}328$). |

[Statement.lean](Statement.lean) records the Formal Conjectures proposition `statement` with no placeholder. [AxiomAudit.lean](AxiomAudit.lean) verifies definitional statement fidelity (`statement_fidelity`), the finite non-vacuity witness `nonvacuity_h_80 : 144 ≤ h 80`, and the transitive axioms of all endpoints.

## Mathematical idea and module outline

Rather than analyzing nested infima over two arbitrary translates directly, we construct a centrally symmetric compact convex polygon $D$ and set $C = \frac{1}{2} D$. Because $C - C = D$, the translate distance $\delta(C+x, C+y)$ equals the point-to-body distance $\operatorname{dist}(y-x, D)$, and the closed translates $C+x$ and $C+y$ are disjoint if and only if $y - x \notin D$.

The six modules in [Proofs/](Proofs) implement this reduction and the four-layer signed parabolic-grid construction:

1. **[Geometry956.lean](Proofs/Geometry956.lean)**: Defines the parabolic curve $\gamma(\eta, t) = (t, 1 + \eta - t^2/2)$, unit normal $\nu(t) = (t, 1)/\sqrt{1+t^2}$, contact point $p(\eta, t) = \gamma(\eta, t) - \nu(t)$, and finite convex hull $D(\eta, T) = \operatorname{conv}\{\pm p(\eta, t) : t \in T\}$. Using the opposite-sign radical identity $(\sqrt{1+s^2}\sqrt{1+t^2} - (1 - st))(\sqrt{1+s^2}\sqrt{1+t^2} + (1 - st)) = (s + t)^2 \ge 0$, it proves the supporting-hyperplane inequality and $\operatorname{infDist}(\gamma(W^4, t), D(W^4, T)) = 1$ for every $t \in T \subseteq [-W, W]$, along with the bounding box $D(W^4, T) \subseteq [-W^3/2, W^3/2] \times [-W^4, W^4]$ and nonempty interior.
2. **[Parameters956.lean](Proofs/Parameters956.lean)**: Sets $W = \frac{1}{10k}$, $a = \frac{W}{k}$, $b = \frac{a^2}{2}$, and $\eta = W^4$, and proves the strict separation bounds $W^3/2 < a$, $\eta < b$, and $k^2 b < 1$.
3. **[DifferenceBody956.lean](Proofs/DifferenceBody956.lean)**: Proves the Minkowski difference-body bridge (`translateSetDistance_eq_infDist_sub`, `half_body_translates_disjoint_of_diff_not_mem`, `translateSetDistance_one_of_body`).
4. **[Padding956.lean](Proofs/Padding956.lean)**: Appends remote translates at $(10(j+1), 0)$ to reach any prescribed cardinality $N$ while preserving pairwise disjointness and all existing unit-distance pairs.
5. **[Extremal956.lean](Proofs/Extremal956.lean)**: Defines `Configuration N` and the `FormalConjectures` extremal function $h(n)$, bounds `(unitPairs C X).card` above by `n.choose 2` (`attainable_bddAbove`), and applies `le_csSup` to transfer configuration edge counts to $h(n)$.
6. **[FourLayer956.lean](Proofs/FourLayer956.lean)**: Formalizes the four-layer signed grid ($m = 3q$, $\ell = 4q^2$, $L = 4$) with $N_q = 48q^3 + 16q^2 + 12q + 4$ translates and $J_q = 72q^4 + 32q^3 + 24q^2 + 13q + 3$ unit-distance pairs ($J_1 = 144 \le h(80)$), derives all public lower bounds (`h_omega_four_thirds_from_80`, `h_eventual_two_fifths`, `erdos_956_superlinear`), and verifies the closed-form Faulhaber and degree-21 induced-subset tail polynomials.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands, [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution, and [SUBMISSION.md](SUBMISSION.md) for Palomar submission metadata. Both `./verify.sh --no-sandbox` and `lake env lake comparator --config comparator.json --inadvisably-no-sandbox` pass, with both `nanoda_bin` and Lean's default kernel accepting `Solution`.
