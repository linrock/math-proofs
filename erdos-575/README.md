# Erdős #575: bipartite extremal-graph compactness

This standalone Lean 4 project gives a complete formal proof of the negative
answer to [Erdős problem #575](https://www.erdosproblems.com/575) in both its
literal unrestricted formulation and its substantive cycle-containing
formulation.

Given a finite family $\mathcal{F}$ of finite simple graphs, write
$\operatorname{ex}(n;\mathcal{F})$ (`CompactnessConjecture.familyExtremal`) for
the maximum number of edges in an $n$-vertex simple graph containing no member
of $\mathcal{F}$ as a subgraph. In [*Compactness results in extremal graph theory* (Combinatorica, 1982)](https://doi.org/10.1007/BF02579424),
Erdős and Simonovits asked whether, whenever $\mathcal{F}$ contains at least
one bipartite graph, there must exist a **bipartite** member $H \in \mathcal{F}$
such that

$$\operatorname{ex}(n;H) = O_{\mathcal{F}}\!\left(\operatorname{ex}(n;\mathcal{F})\right).$$

The answer is **no** in both the literal unrestricted setting and the corrected
cycle-containing setting:

1. **Literal unrestricted formulation:** When acyclic graphs are allowed, the
   two-forest family $\mathcal{F}_0 = \{K_{1,2}, 2K_2\}$ consists of two
   bipartite graphs and satisfies $\operatorname{ex}(n;\mathcal{F}_0) \le 1$ for
   all $n$, whereas
   $\operatorname{ex}(n;K_{1,2}) \ge \lfloor n/2 \rfloor$ and
   $\operatorname{ex}(n;2K_2) \ge n - 1$. Neither member can control
   $\operatorname{ex}(n;\mathcal{F}_0)$ up to a constant factor.
2. **Cycle-containing formulation:** As noted in Yuval Wigderson's
   [*The Erdős–Simonovits Compactness Conjecture Needs More Assumptions*](https://ywigderson.math.ethz.ch/math/static/Compactness.pdf),
   excluding forests by requiring every forbidden graph $H \in \mathcal{F}$ to
   contain a cycle (`¬ H.IsAcyclic`) avoids trivial tree-versus-matching
   pathology. Even with this restriction, the conjecture is false: the explicit
   finite family `CompactnessConjecture.proposedFamily` constructed in
   [*Ten advances in mathematics and theoretical computer science* (OpenAI, 2026, Chapter 10)](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
   consists entirely of connected, **bipartite**, cyclic graphs, yet satisfies
   $$\operatorname{ex}(n;\mathcal{F}) \le C\, n^{21/16} = C\, n^{4/3 - 1/48}$$
   for all $n$ while every member $H \in \mathcal{F}$ satisfies
   $\operatorname{ex}(n;H) \ge c\, n^{4/3}$ for all sufficiently large $n$.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) exports nine proved theorems matched by
[Challenge.lean](Challenge.lean) and [comparator.json](comparator.json):

| Declaration | Meaning |
| --- | --- |
| `Erdos575.erdos_575` | Elaborated Formal Conjectures `False ↔` form of the cycle-containing statement (`CyclicBipartiteCompactnessStatement`). |
| `Erdos575.erdos_575_unrestricted` | Elaborated Formal Conjectures `False ↔` form of the literal unrestricted statement (`BipartiteCompactnessStatement`). |
| `Erdos575.not_erdos_575_corrected` | Direct disproof of `CyclicBipartiteCompactnessStatement`: not every finite nonempty cyclic family containing a bipartite member is controlled by one of its bipartite members. |
| `Erdos575.not_erdos_575` | Direct disproof of `BipartiteCompactnessStatement`. |
| `Erdos575.not_erdos_575_all_bipartite` | Direct disproof of `AllBipartiteCyclicCompactnessStatement`: even when *every* member of a finite nonempty cyclic family is bipartite, no single member need control the family extremal number. |
| `Erdos575.correctedCounterexample` | Qualitative non-forest counterexample: exhibits a finite nonempty cyclic family whose members are all connected, bipartite, and cyclic, yet which is not bipartite-compact. |
| `Erdos575.quantitativeCounterexample` | Quantitative polynomial-exponent separation with gap $1/48$: exhibits an all-bipartite, connected, cyclic family $\mathcal{F}$ and constants $c, C > 0$ such that every $H \in \mathcal{F}$ has $\operatorname{ex}(n;H) \ge c n^{4/3}$ eventually while $\operatorname{ex}(n;\mathcal{F})^{16} \le C n^{21}$ for all $n$. |
| `Erdos575.ForestCounterexample.forestFamily_not_isBipartiteCompact` | Direct disproof that the two-forest family $\mathcal{F}_0 = \{K_{1,2}, 2K_2\}$ is bipartite-compact. |
| `Erdos575.ForestCounterexample.forestCounterexample` | Self-contained quantitative package for $\mathcal{F}_0 = \{K_{1,2}, 2K_2\}$: proves nonemptiness, bipartiteness of both members, $\operatorname{ex}(n;\mathcal{F}_0) \le 1$, $\operatorname{ex}(n;K_{1,2}) \ge \lfloor n/2 \rfloor$, $\operatorname{ex}(n;2K_2) \ge n - 1$, and `¬ IsBipartiteCompactFamily forestFamily`. |

[Challenge.lean](Challenge.lean) states these nine targets using only Mathlib
and intentional `sorry` placeholders; `Solution.lean` never imports
`Challenge.lean`. [Statement.lean](Statement.lean) records the Formal
Conjectures propositions `statement` and `statement_unrestricted` with no
placeholder, and [AxiomAudit.lean](AxiomAudit.lean) verifies definitional
statement fidelity, domain non-vacuity for both the cyclic and forest
counterexamples, and the transitive axioms of all exported results.

## Mathematical idea and module outline

Note that Erdős #575 is distinct from the general Erdős–Simonovits compactness
conjecture (Erdős #180): in #575 the family $\mathcal{F}$ is assumed to contain
at least one bipartite graph (`ContainsBipartiteMember`), and the controlling
graph $H \in \mathcal{F}$ is *itself* required to be bipartite
(`IsBipartiteCompactFamily`). A black-box negation of #180 does not by itself
refute #575 unless one inspects the counterexample family and verifies both that
it contains a bipartite member and that no *bipartite* member controls the
family. Because *every* member of both $\mathcal{F}_0 = \{K_{1,2}, 2K_2\}$ and
`proposedFamily` is bipartite, the two notions `IsBipartiteCompactFamily` and
`IsCompactFamily` coincide on these families (`isBipartiteCompactFamily_iff_isCompactFamily`).

The three modules in [Proofs/](Proofs) organize both counterexamples as follows:

1. **Bipartite forest counterexample $\mathcal{F}_0 = \{K_{1,2}, 2K_2\}$**
   ([ForestCounterexample575.lean](Proofs/ForestCounterexample575.lean)):
   constructs the star graph `starSimpleGraph n` on `Fin n` centered at $0$ and
   the matching graph `matchingSimpleGraph n` pairing $2k$ with $2k + 1$, and
   defines `cherryGraph` ($K_{1,2}$ on `Fin 3`) and `twoMatchingGraph` ($2K_2$
   on `Fin 4`). Any graph on `Fin n` with at least two edges either has two
   incident edges (producing a copy of $K_{1,2}$) or two vertex-disjoint edges
   (producing a copy of $2K_2$), so $\operatorname{ex}(n;\mathcal{F}_0) \le 1$
   for all $n$. Conversely, `starSimpleGraph n` is $2K_2$-free with $n - 1$
   edges and `matchingSimpleGraph n` is $K_{1,2}$-free with $\lfloor n/2 \rfloor$
   edges, refuting `IsBipartiteCompactFamily forestFamily` completely from
   scratch in pure Mathlib.
2. **Characteristic-splitting cyclic family and symplectic quadrangle avoidance**
   ([CompactnessAndDegeneracy.lean](Proofs/CompactnessAndDegeneracy.lean)):
   ports the Erdős #180 construction from [`openai/ten-proofs`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean)
   to Lean `v4.35.0-rc2`. The family `proposedFamily` consists of $C_4$, $C_6$,
   and finite families of color-respecting quotients of two bipartite
   subdivision templates `jTemplate` and `kTemplate`. Over finite fields
   $\mathbb{F}_{2^j}$ of characteristic $2$, the symplectic polar space
   quadrangle `symplecticQuadrangle` avoids $C_4$, $C_6$, and all admissible
   $J$-quotients; over $\mathbb{F}_{3^j}$ of characteristic $3$, it avoids $C_4$,
   $C_6$, and all admissible $K$-quotients. Because the quadrangle on
   $\mathbb{F}_q^4$ has $(q + 1)(q^2 + 1)$ vertices and
   $\frac{1}{2}(q + 1)^2(q^2 + 1)$ edges, every member $H \in \mathcal{F}$
   satisfies $\operatorname{ex}(n;H) \ge c\, n^{4/3}$ eventually. Simultaneously,
   any host graph avoiding all of `proposedFamily` satisfies the supersaturation
   and bad-vertex bound $e(G)^{16} \le C\, n^{21}$, giving
   $\operatorname{ex}(n;\mathcal{F}) = O(n^{21/16}) = O(n^{4/3 - 1/48})$.
3. **Bridge from #180 to #575 and mixed-family hierarchy**
   ([Erdos575.lean](Proofs/Erdos575.lean)): defines `ContainsBipartiteMember`,
   `ControlsFamily`, `IsBipartiteCompactFamily`, `BipartiteCompactnessStatement`,
   `CyclicBipartiteCompactnessStatement`, and
   `AllBipartiteCyclicCompactnessStatement`; proves that `IsBipartiteCompactFamily`
   and `IsCompactFamily` are equivalent on all-bipartite families; verifies that
   every member of `proposedFamily` is connected, bipartite, and cyclic; and
   deduces `correctedCounterexample`, `quantitativeCounterexample`,
   `not_erdos_575_all_bipartite`, `not_erdos_575_corrected`, `not_erdos_575`,
   `erdos_575`, and `erdos_575_unrestricted`.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and
[THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license details.
Both `./verify.sh` and `lake env lake comparator --config comparator.json`
pass, with both `nanoda_bin` and Lean's default kernel accepting `Solution`.
