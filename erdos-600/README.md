# Erdős 600: Ruzsa–Szemerédi bound for triangle-covered graphs

This package formalizes the Ruzsa–Szemerédi upper bound for Erdős Problem #600 (Erdős, 1987; Ruzsa and Szemerédi, 1978) on the minimal number of edges $e(n, r)$ that forces an edge in at least $r$ triangles in an $n$-vertex triangle-covered simple graph, where every edge must lie in at least one triangle.

See [Erdős problem #600](https://www.erdosproblems.com/600) for background and literature.

## Scope and main results

The main theorem proves the subquadratic upper bound $e(n, r) = o(n^2)$ for every fixed $r$, which is the upstream declaration `erdos_600.variants.ruzsa_szemeredi_upper_bound`. The proof routes a dense graph whose edges all lie in fewer than $r$ triangles to the far-from-triangle-free predicate and then applies the triangle removal lemma of Dillies and Mehta, as formalized in Mathlib. The quantitative input is a sharp cover-charge inequality: for a triangle-covered graph whose edges all lie in fewer than $r$ triangles, and any triangle-free subgraph $H \le G$, one has $|E(G)| \le (2r - 1)(|E(G)| - |E(H)|)$.

The seventeen remaining theorems are auxiliary. They characterize locally linear graphs as the $r = 2$ case, identify $e(n, 2) = 3\,\mathrm{rs}(n) + 1$ with the locally linear extremal number, transfer the Behrend construction to obtain $n^2 \exp(-4\sqrt{\log n}) = O(e(n, r))$ for $r \ge 2$, and record the complete-graph saturation dichotomy $e(n, r) = \binom{n}{2} + 1 \iff n - 1 \le r$ for $n \ge 3$ together with disjoint-union superadditivity of the extremal edge count. Further bounds include a pointwise edge-degree-sum estimate, a parity-tightened locally linear packing bound, a global Cauchy–Schwarz triangle-incidence inequality, and a Mantel–Turán edge bound. On the constructive side the package proves the exact triangle multiplicity and edge count of weighted vertex blow-ups, gives the positive-weight admissibility criterion, and establishes uniform $c$-blowup scaling of the extremal count. It closes with a non-neighbor triangle partition identity for locally linear graphs, a heavy-edge triangle-incidence bound, and a conditional reduction of the ratio question to deleting a sublinear number of edges.

The two asymptotic questions remain open and are not claimed here. Those are whether the step difference $e(n, r + 1) - e(n, r)$ tends to infinity, and whether the ratio $e(n, r + 1) / e(n, r)$ tends to one, for every $r \ge 2$.

## Package layout

[Solution.lean](Solution.lean) re-exports the 18 theorems in the `Erdos600` namespace, matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json). The proofs live in [Proofs/Erdos600Unified435.lean](Proofs/Erdos600Unified435.lean), [Proofs/NeighborhoodDegreeAndTriangleClusterBounds600.lean](Proofs/NeighborhoodDegreeAndTriangleClusterBounds600.lean), [Proofs/LinkGraphCycleDeficitAndTriangleCauchySchwarz600.lean](Proofs/LinkGraphCycleDeficitAndTriangleCauchySchwarz600.lean), [Proofs/WeightedVertexBlowupAndStepDifferenceBounds600.lean](Proofs/WeightedVertexBlowupAndStepDifferenceBounds600.lean), and [Proofs/Blueprint600.lean](Proofs/Blueprint600.lean). Only the standard foundational axioms are used (`propext`, `Classical.choice`, `Quot.sound`).

| Theorem in `Solution.lean` | Mathematical statement |
| --- | --- |
| `Erdos600.erdos_600.variants.ruzsa_szemeredi_upper_bound` | **Ruzsa–Szemerédi subquadratic upper bound.** For all $r \in \mathbb{N}$, $e(n, r) = o(n^2)$ as $n \to \infty$. |
| `Erdos600.locallyLinear_iff_trianglesContaining` | **Locally linear characterization.** `G.LocallyLinear` holds iff every edge of $G$ lies in at least $1$ and fewer than $2$ triangles. |
| `Erdos600.eFunction_two_eq` | **Exact $r = 2$ Ruzsa–Szemerédi identity.** For all $n \in \mathbb{N}$, `eFunction n 2 = 3 * ruzsaSzemerediNumberNat n + 1`. |
| `Erdos600.behrend_asymptotic_lower_bound_eFunction` | **Behrend asymptotic lower bound.** For all $r \ge 2$, $n^2 \exp(-4\sqrt{\log n}) = O(e(n, r))$. |
| `Erdos600.card_edgeFinset_le_two_mul_sub_one_mul_sub_card` | **Sharp $(2r - 1)$ cover-charge bound.** For any triangle-free $H \le G$ in an $r$-book-free triangle-covered graph $G$, $|E(G)| \le (2r - 1)(|E(G)| - |E(H)|)$. |
| `Erdos600.eFunction_eq_choose_two_succ_iff_of_three_le` | **Complete-graph saturation dichotomy.** For $n \ge 3$, $e(n, r) = \binom{n}{2} + 1 \iff n - 1 \le r$. |
| `Erdos600.maxAdmissibleEdges_superadditive` | **Disjoint-union superadditivity.** `maxAdmissibleEdges m r + maxAdmissibleEdges n r ≤ maxAdmissibleEdges (m + n) r`. |
| `Erdos600.degree_add_degree_le_card_add_sub_one_of_isAdmissibleBookFree` | **Pointwise edge-degree-sum bound.** For any edge $uv$ in an $r$-book-free triangle-covered graph ($r \ge 1$), $\deg(u) + \deg(v) \le |V| + r - 1$. |
| `Erdos600.three_mul_ruzsaSzemerediNumberNat_le_mul_div_two` | **Parity-tightened Ruzsa–Szemerédi bound.** For all $n \in \mathbb{N}$, $3\,\mathrm{rs}(n) \le n \lfloor (n - 1)/2 \rfloor$. |
| `Erdos600.nine_mul_card_cliqueFinset_sq_le_card_edgeFinset_mul_edgeTriangleIncidenceSqSum` | **Global Cauchy–Schwarz triangle-incidence bound.** $9 |T(G)|^2 \le |E(G)| \sum_{e \in E(G)} \mathrm{mult}(e)^2$. |
| `Erdos600.maxAdmissibleEdges_le_mul_add_sub_one_div_four` | **Mantel–Turán $r$-book-free edge bound.** For $r \ge 1$, `maxAdmissibleEdges n r ≤ (n * (n + r - 1)) / 4`. |
| `Erdos600.card_trianglesContaining_weightedBlowupGraph_eq_commonNeighborWeightSum` | **Weighted-blowup triangle multiplicity.** Every edge in `weightedBlowupGraph H w` lies in `commonNeighborWeightSum H w x.1 y.1` triangles. |
| `Erdos600.isAdmissibleBookFree_weightedBlowupGraph_iff_of_pos` | **Weighted-blowup admissibility equivalence.** For positive weights $w \ge 1$, `IsAdmissibleBookFree (weightedBlowupGraph H w) r ↔ IsAdmissibleBlowupWeight H w r`. |
| `Erdos600.card_edgeFinset_weightedBlowupGraph_eq_blowupEdgeQuadraticForm` | **Weighted-blowup edge-count quadratic form.** `(weightedBlowupGraph H w).edgeFinset.card = blowupEdgeQuadraticForm H w`. |
| `Erdos600.sq_mul_maxAdmissibleEdges_le_maxAdmissibleEdges_mul` | **Uniform $c$-blowup quadratic scaling.** For $c, r \ge 1$, $c^2\,\mathrm{maxAdmissibleEdges}(m, r) \le \mathrm{maxAdmissibleEdges}(cm, c(r - 1) + 1)$. |
| `Erdos600.four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_eq_sum_degree` | **Locally linear non-neighbor triangle partition identity.** In any `IsAdmissibleBookFree G 2` graph, $4 t_1(u) + 6 t_3(u) = \sum_{w \in R(u)} \deg(w)$. |
| `Erdos600.card_edgeFinset_add_sub_one_mul_card_bookHeavyEdgeFinset_le_edgeTriangleIncidenceSum` | **Heavy-edge triangle-incidence bound.** In any triangle-covered graph ($r \ge 1$), $|E(G)| + (r - 1)|E_{\ge r}(G)| \le \sum_{e \in E(G)} \mathrm{mult}(e)$. |
| `Erdos600.erdos_600_parts_ii_of_forall_exists_deleteEdges_isLittleO` | **Conditional $r$-book edge-deletion reduction for Part (ii).** Conditionally reduces the open limit $e(n, r + 1)/e(n, r) \to 1$ to the unproved hypothesis of deleting $o(e(n, r))$ edges to eliminate $r$-books while preserving triangle coverage. |

[Statement.lean](Statement.lean) records six benchmark statements without placeholders, and [AxiomAudit.lean](AxiomAudit.lean) checks statement fidelity and the transitive axioms of every exported endpoint.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license information.
