# Erdős #546: sparse graph Ramsey numbers

This standalone Lean 4 project gives a complete formal proof of the affirmative
answer to [Erdős problem #546](https://www.erdosproblems.com/546) (Sudakov's
theorem). For a finite simple graph $G$, its diagonal Ramsey number
$R(G) = R(G, G)$ (`SimpleGraph.diagonalGraphRamsey G`) is the smallest integer
$n$ such that every $2$-coloring of the edges of $K_n$ contains a monochromatic
(not necessarily induced) copy of $G$. Erdős asked whether there is an
absolute constant $C > 0$ such that every finite graph $G$ with $m$ edges and
no isolated vertices satisfies

$$R(G) \le 2^{C \sqrt{m}}.$$

The answer is **yes**.

In [*A conjecture of Erdős on graph Ramsey numbers* (Advances in Mathematics, 2011)](https://arxiv.org/abs/1002.0095),
Benny Sudakov resolved this conjecture with $C = 250$. This formalization
reconstructs Sudakov's proof from scratch in Lean 4 and establishes the uniform
explicit bound

$$R(G) \le 2^{4000 \sqrt{m}}$$

for every finite simple graph $G$ on any finite vertex type $V$ with no
isolated vertices and $m$ edges (including the empty graph at $m = 0$). Using
$C = 4000$ in place of $250$ absorbs all integer ceilings and initialization
slack directly without asymptotic approximations.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) exports seven proved theorems matched by
[Challenge.lean](Challenge.lean) and [comparator.json](comparator.json):

| Declaration | Meaning |
| --- | --- |
| `erdos_546_original_statement` | The literal Formal Conjectures `True ↔` statement at root scope over arbitrary `V : Type` with `[Fintype V]`. |
| `Erdos546.erdos_546` | The elaborated `True ↔ Erdos546.SparseRamseyStatement` form of Erdős #546. |
| `Erdos546.sudakov_sparse_bound` | Uniform explicit bound: $R(G) \le 2^{4000 \sqrt{m}}$ for every finite graph $G$ with $m$ edges and no isolated vertices. |
| `Erdos546.sparse_graph_ramsey_witness` | Direct Ramsey forcing witness on $\lceil 2^{2000\sqrt{m}} \rceil$ vertices for all $m \ge 64$ and $|V| \le 2m$, showing the `sInf` definition is non-vacuous. |
| `Erdos546.boundedDegree_sparse_cut` | Sudakov Lemma 2.4 (bounded-degree sparse cut): if a host graph $H$ on $W$ contains no copy of $G$ with $\Delta(G) \le \Delta$, then $W$ contains disjoint equal-size subsets $X, Y$ of size $\ge \varepsilon^\Delta |W| / (2(\Delta + 1))$ with at most $\varepsilon |X| |Y|$ edges between them. |
| `Erdos546.exists_monoPair_of_low_edgeDensity` | Sudakov Lemma 2.3 (low-density monochromatic pair): any vertex set $U$ of edge density $\le \varepsilon \le 1/8$ contains a monochromatic clique-to-reservoir pair $(X, Y)$ in $H$ or $H^c$ with $|X| = t$ and $|Y| \ge \varepsilon^{40 \varepsilon t} |U|$. |
| `Erdos546.quantitative_monoPair_amplification` | Sudakov Section 3 (amplification step): in a $G$-free host, a monochromatic pair $(X, Y)$ at scale $a$ with $|X| \ge a^3 \sqrt{m}$ and $|Y| \ge 2^{500 \sqrt{m} / a}$ yields a new monochromatic pair $(P, Q)$ inside $Y$ with $|P| \ge 2^{2a} \sqrt{m}$ and $|Q| \ge |Y| \cdot 2^{-400 \sqrt{m} / a}$. |

[Challenge.lean](Challenge.lean) states these seven targets using only Mathlib
and intentional `sorry` placeholders; `Solution.lean` never imports
`Challenge.lean`. [Statement.lean](Statement.lean) records the Formal
Conjectures proposition `statement` with no placeholder, and
[AxiomAudit.lean](AxiomAudit.lean) verifies definitional statement fidelity,
two non-vacuity witnesses (`Empty` at $m = 0$ and $K_2$ at $m = 1$), and the
transitive axioms of all exported results.

## Mathematical idea and module outline

A graph with $m$ edges can have a few vertices of high degree, which obstructs
direct bounded-degree embedding arguments. Sudakov's proof overcomes this by
tracking a **monochromatic pair** $(X, Y)$: a disjoint pair of vertex sets in a
2-colored complete graph where $X$ is a monochromatic clique and every edge
between $X$ and the reservoir $Y$ has that same color. If we delete the $|X|$
highest-degree vertices of $G$, the remaining induced subgraph $G'$ has maximum
degree at most $2m / (|X| + 1)$. Whenever we can embed $G'$ into the reservoir
$Y$ in the color of $X$, we can glue the $|X|$ deleted high-degree vertices
into the clique $X$ to obtain a full copy of $G$.

If no copy of $G$ exists in either color, the reservoir $Y$ cannot contain a
copy of $G'$ in the color of $X$. By the contrapositive of greedy bounded-degree
embedding, $Y$ must contain a sparse cut, and iterating this cut extracts a
still-large subset $U \subseteq Y$ of very low edge density in that color.
Within a low-density subset $U$, a pigeonhole and maximum-clique argument finds
a new monochromatic pair $(P, Q)$ whose clique $P$ is exponentially larger than
$X$ while the reservoir $Q$ shrinks by a controlled factor. Iterating this
amplification step along a geometric schedule quickly produces a clique of size
at least $2m \ge |V(G)|$, which trivially contains $G$.

The 30 modules in [Proofs/](Proofs) organize this argument into four stages:

1. **Ramsey foundations and small-edge baseline**
   ([MonochromaticPairs546](Proofs/MonochromaticPairs546.lean),
   [RamseyBasics546](Proofs/RamseyBasics546.lean),
   [DegreeDeletion546](Proofs/DegreeDeletion546.lean),
   [PairRamsey546](Proofs/PairRamsey546.lean)): connects concrete host sizes
   (`GraphRamseyWitness`) to `SimpleGraph.graphRamsey` and
   `SimpleGraph.diagonalGraphRamsey`, proves $|V| \le 2m$ when $G$ has no
   isolated vertices, and handles the small-edge regime $m \le 3600$ via the
   Erdős–Szekeres bound $R(G) \le 2^{4m} \le 2^{240\sqrt{m}}$.
2. **Greedy bounded-degree embedding and hereditary sparse cuts**
   ([BidenseEmbedding546](Proofs/BidenseEmbedding546.lean),
   [MeanSubsets546](Proofs/MeanSubsets546.lean),
   [SparseCut546](Proofs/SparseCut546.lean),
   [SparseCombination546](Proofs/SparseCombination546.lean),
   [FreeGraphSparse546](Proofs/FreeGraphSparse546.lean)): proves that a graph of
   maximum degree $\Delta$ embeds greedily unless the host admits a sparse
   bipartite cut (`boundedDegree_sparse_cut`), and combines hereditary sparse
   cuts with two-stage degree cleaning to extract a low-density subset in any
   $G'$-free reservoir.
3. **Low-density monochromatic-pair extraction**
   ([LowDensityDegreeCleaning546](Proofs/LowDensityDegreeCleaning546.lean),
   [LowDensityBinomial546](Proofs/LowDensityBinomial546.lean),
   [LowDensityPairs546](Proofs/LowDensityPairs546.lean),
   [LowDensityCleaningCorollaries546](Proofs/LowDensityCleaningCorollaries546.lean),
   [LowDensityRounded546](Proofs/LowDensityRounded546.lean)): formalizes
   Sudakov's Lemma 2.3 (`exists_monoPair_of_low_edgeDensity`) by pruning
   high-degree vertices, taking a maximum clique in the complement, and
   pigeonholing neighborhood masks to obtain a monochromatic pair in either
   color.
4. **High-degree deletion, copy gluing, and iterative amplification**
   ([DegreeMax546](Proofs/DegreeMax546.lean),
   [CopyGlue546](Proofs/CopyGlue546.lean),
   [PairLifting546](Proofs/PairLifting546.lean),
   [ResidualObstruction546](Proofs/ResidualObstruction546.lean),
   [AmplificationDegrees546](Proofs/AmplificationDegrees546.lean),
   [AmplificationGraph546](Proofs/AmplificationGraph546.lean),
   [SudakovScalars546](Proofs/SudakovScalars546.lean),
   [SudakovScalarsSuccessor546](Proofs/SudakovScalarsSuccessor546.lean),
   [SudakovAmplificationScalars546](Proofs/SudakovAmplificationScalars546.lean),
   [QuantitativeAmplificationParameters546](Proofs/QuantitativeAmplificationParameters546.lean),
   [Amplification546](Proofs/Amplification546.lean),
   [Initialization546](Proofs/Initialization546.lean),
   [PairIterationScalars546](Proofs/PairIterationScalars546.lean),
   [PairIteration546](Proofs/PairIteration546.lean),
   [Sudakov546](Proofs/Sudakov546.lean),
   [OriginalStatement546](Proofs/OriginalStatement546.lean)): deletes the
   $|X|$ highest-degree vertices so the residual subgraph has maximum degree
   $D \le 2m / (|X| + 1)$, proves the single-step amplification theorem
   (`quantitative_monoPair_amplification`), and iterates it from $a = 3$ up to
   $A = \lfloor \frac{1}{2} \log_2 m \rfloor$ where $2^{2A}\sqrt{m} \ge 2m \ge |V|$,
   concluding $R(G) \le \lceil 2^{2000\sqrt{m}} \rceil \le 2^{4000\sqrt{m}}$.

## Earlier Lean work and provenance

The pinned [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/6fbb54f24ccc2e64dcfaffc28c58950e377110d2/FormalConjectures/ErdosProblems/546.lean)
and Ramsey definitions in
[`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`](https://github.com/google-deepmind/formal-conjectures/blob/6fbb54f24ccc2e64dcfaffc28c58950e377110d2/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean)
are reproduced with their Apache-2.0 attribution and
[license text](third_party/FORMAL-CONJECTURES-LICENSE.txt). The upstream
`FormalConjectures/ErdosProblems/546.lean` declaration ends in `sorry`.

An independent Lean 4.33.0 formalization in
[`plby/lean-proofs`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos546.lean)
proves a variant restricted to graphs on `Fin v` using custom Ramsey and
isolated-vertex definitions with constant $C = 65536$; no code from that
repository is imported or adapted here. Compared with that formalization, this
package:

- proves the exact `FormalConjectures` theorem statement and definitions
  (`SimpleGraph.graphRamsey`, `SimpleGraph.diagonalGraphRamsey`,
  `∀ v, 0 < G.degree v`, and `G.edgeSet.ncard = m`) over arbitrary finite
  vertex types `V` (`[Fintype V]`, universe-polymorphic in
  `sudakov_sparse_bound`),
- establishes a $16\times$ sharper explicit exponent constant ($C = 4000$ vs.
  $C = 65536$, with a direct forcing witness at $\lceil 2^{2000\sqrt{m}} \rceil$
  for $m \ge 64$), and
- exports reusable, Comparator-verified formulations of Sudakov's three core
  structural lemmas (`boundedDegree_sparse_cut`,
  `exists_monoPair_of_low_edgeDensity`, and
  `quantitative_monoPair_amplification`) on general finite types in Lean
  `v4.35.0-rc2`.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and
[THIRD_PARTY.md](THIRD_PARTY.md) for source attribution. Both `./verify.sh`
and `lake env lake comparator --config comparator.json` pass, with both
`nanoda_bin` and Lean's default kernel accepting `Solution`.
