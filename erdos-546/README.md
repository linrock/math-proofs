# Erdős #546: sparse graph Ramsey numbers

This standalone Lean 4.35.0-rc2 project gives a complete formal proof of the
affirmative answer to Erdős problem 546 (Sudakov's theorem). For a finite
simple graph $G$, write $R(G) = R(G, G)$ (`SimpleGraph.diagonalGraphRamsey G`)
for the minimum host order $n$ such that every $2$-coloring of $K_n$ contains a
monochromatic (not necessarily induced) copy of $G$. Erdős asked whether there
exists an absolute constant $C > 0$ such that every finite graph $G$ with $m$
edges and no isolated vertices satisfies
$$R(G) \le 2^{C \sqrt{m}}.$$
The answer is **yes**.

This formalization proves the uniform explicit bound
$$R(G) \le 2^{4000 \sqrt{m}}$$
for every finite simple graph $G$ on any vertex type `V` (`[Fintype V]`,
`[DecidableRel G.Adj]`) with no isolated vertices (`∀ v, 0 < G.degree v`) and
`G.edgeSet.ncard = m` edges, including the empty graph at $m = 0$. The
contribution is a complete machine-checked proof of known mathematics: the
affirmative resolution was proved by
[Benny Sudakov](https://arxiv.org/abs/1002.0095) (*Advances in Mathematics*
227 (2011), 601–609) with constant $250$. Retaining integer-rounding and
initialization slack yields the explicit constant $C = 4000$ without asymptotic
approximations.

[Solution.lean](Solution.lean) exports the seven proved targets matched by
[Challenge.lean](Challenge.lean) and [comparator.json](comparator.json):
- `erdos_546_original_statement`: the literal Formal Conjectures `True ↔`
  statement at root scope over arbitrary `V : Type` with `[Fintype V]`.
- `Erdos546.erdos_546`: `True ↔ Erdos546.SparseRamseyStatement`.
- `Erdos546.sudakov_sparse_bound`: the uniform explicit bound
  $R(G) \le 2^{4000 \sqrt{m}}$.
- `Erdos546.sparse_graph_ramsey_witness`: the genuine forcing witness
  `GraphRamseyWitness G G ⌈2^{2000\sqrt{m}}⌉₊` for all $m \ge 64$, ruling out
  vacuous `sInf ∅ = 0` collapse.
- `Erdos546.boundedDegree_sparse_cut`: the rounded Sudakov Lemma 2.4
  bounded-degree embedding contrapositive producing disjoint equal-size sets
  $X, Y$ of cardinality $\ge \varepsilon^\Delta |W| / (2(\Delta + 1))$ and
  interedge count $\le \varepsilon |X| |Y|$.
- `Erdos546.exists_monoPair_of_low_edgeDensity`: the rounded Sudakov Lemma 2.3
  low-density monochromatic-pair theorem with exponent $40 \varepsilon t$.
- `Erdos546.quantitative_monoPair_amplification`: the Sudakov Section 3
  quantitative clique/reservoir amplification step.

[Challenge.lean](Challenge.lean) independently states the same seven targets
using only Mathlib and contains intentional statement placeholders. `Solution`
does not import `Challenge`. The 30 [Proofs](Proofs) modules provide the
complete mathematical development. [AxiomAudit.lean](AxiomAudit.lean) checks
the seven endpoints, definitional statement fidelity against
[Statement.lean](Statement.lean), and non-vacuity witnesses.

## Proof outline

1. **Ramsey foundations and small-edge baseline**
   ([MonochromaticPairs546](Proofs/MonochromaticPairs546.lean),
   [RamseyBasics546](Proofs/RamseyBasics546.lean),
   [DegreeDeletion546](Proofs/DegreeDeletion546.lean),
   [PairRamsey546](Proofs/PairRamsey546.lean)): establishes the genuine
   nonempty forcing-witness bridge for `SimpleGraph.graphRamsey` and
   `SimpleGraph.diagonalGraphRamsey`, proves $|V| \le 2m$ when there are no
   isolated vertices, and closes the small-edge regime $m \le 3600$ via the
   Erdős–Szekeres bound $R(G) \le 2^{4m} \le 2^{240\sqrt{m}}$.
2. **Greedy bounded-degree embedding and hereditary sparse cuts**
   ([BidenseEmbedding546](Proofs/BidenseEmbedding546.lean),
   [MeanSubsets546](Proofs/MeanSubsets546.lean),
   [SparseCut546](Proofs/SparseCut546.lean),
   [SparseCombination546](Proofs/SparseCombination546.lean),
   [FreeGraphSparse546](Proofs/FreeGraphSparse546.lean)): proves the greedy
   vertex-by-vertex embedding under local bidensity, derives the equal-size
   sparse-cut contrapositive (`boundedDegree_sparse_cut`), and iterates
   two-cleaning cuts to extract a low-density induced reservoir in any
   $G$-free host.
3. **Low-density dependent random choice and monochromatic pairs**
   ([LowDensityDegreeCleaning546](Proofs/LowDensityDegreeCleaning546.lean),
   [LowDensityBinomial546](Proofs/LowDensityBinomial546.lean),
   [LowDensityPairs546](Proofs/LowDensityPairs546.lean),
   [LowDensityCleaningCorollaries546](Proofs/LowDensityCleaningCorollaries546.lean),
   [LowDensityRounded546](Proofs/LowDensityRounded546.lean)): formalizes the
   mask-pigeonhole and maximum-complement-clique dichotomy inside a low-density
   reservoir (`exists_monoPair_of_low_edgeDensity`).
4. **Degree deletion, copy glueing, and density amplification**
   ([CopyGlue546](Proofs/CopyGlue546.lean),
   [PairLifting546](Proofs/PairLifting546.lean),
   [ResidualObstruction546](Proofs/ResidualObstruction546.lean),
   [AmplificationDegrees546](Proofs/AmplificationDegrees546.lean),
   [AmplificationGraph546](Proofs/AmplificationGraph546.lean),
   [QuantitativeAmplificationParameters546](Proofs/QuantitativeAmplificationParameters546.lean),
   [Amplification546](Proofs/Amplification546.lean),
   [PairIteration546](Proofs/PairIteration546.lean),
   [Sudakov546](Proofs/Sudakov546.lean)): deletes the $k = \lfloor a^3 \sqrt{m} \rfloor$
   highest-degree vertices so the residual induced subgraph has maximum degree
   $D \le 2m / (k + 1)$, amplifies the monochromatic clique/reservoir pair
   from scale $a$ to $2a - 1$ until $2^{2A}\sqrt{m} \ge 2m \ge |V|$, and
   concludes $R(G) \le \lceil 2^{2000\sqrt{m}} \rceil \le 2^{4000\sqrt{m}}$.

## Earlier Lean work and provenance

The pinned [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/6fbb54f24ccc2e64dcfaffc28c58950e377110d2/FormalConjectures/ErdosProblems/546.lean)
and Ramsey definitions in
[`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`](https://github.com/google-deepmind/formal-conjectures/blob/6fbb54f24ccc2e64dcfaffc28c58950e377110d2/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean)
are reproduced with their Apache-2.0 attribution and
[license text](third_party/FORMAL-CONJECTURES-LICENSE.txt). The upstream
`FormalConjectures/ErdosProblems/546.lean` declaration ends in `sorry`. An
independent Lean 4.33.0 formalization in
[`plby/lean-proofs`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos546.lean)
proves a `Fin v`-restricted variant with constant $C = 65536$; no code from
that repository is imported or adapted here.

## Reproduce and submission status

[BUILD.md](BUILD.md) gives the pinned toolchain, dependency, build, and axiom
checks. [comparator.json](comparator.json) names all seven theorem endpoints.
[formalization.yaml](formalization.yaml) records Linmiao Xu as author and
maintainer and the [MIT license](LICENSE) for locally authored material.
This remains a prepared candidate in `math-proofs/erdos-546` and has not been
submitted to or registered with Palomar.
