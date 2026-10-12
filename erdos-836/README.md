# Erdős 836: Alon’s equitable-partition disproof of $O(r^2)$ vertices, linear pairwise edge intersection ($r \le 2t + 1$ and $c = 1/3$), and codimension-one avoiding hypergraph bounds

This package formalizes unconditional theorems resolving both main parts of Erdős Problem #836 (posed by Erdős and Shelah; Erdős and Lovász, 1975) together with structural bounds on $3$-chromatic intersecting $r$-uniform hypergraphs avoiding pairwise intersection $r - 1$.

See [Erdős problem #836](https://www.erdosproblems.com/836) for background and literature.

## Scope and main results

1. **Resolution of Part (i) (`erdos_836.parts.i`) via Noga Alon’s Equitable-Partition Construction**:
   For every $r \ge 2$, constructs Alon’s $r$-uniform intersecting $3$-chromatic hypergraph on `Fin n` with at least
   $$\mathrm{alonVertexCount}(r) = (2r - 2) + \frac{1}{2}\binom{2r - 2}{r - 1} \ge (2r - 2) + 2^{r - 2}$$
   active vertices (`exists_alon_fin_hypergraph`), unconditionally disproving the $O(r^2)$ active-vertex bound (`erdos_836.parts.i` and `not_erdos836QuadraticVertexQuestion`).
2. **Resolution of Part (ii) (`erdos_836.parts.ii`) via Minimal-Blue Bipartite Double Counting**:
   Adapts and generalizes Liam Price’s (2026) minimal-blue bipartite double-counting argument (formalized on `Fin N` in `WoshuaJolk/jig-verifier`, `Submissions/Erdos836LinearEdgeIntersection/PricePort.lean`, Apache-2.0) to prove the universal pairwise-intersection bound $r \le 2t + 1$ over arbitrary `[DecidableEq V]` whenever every pair of distinct edges in a non-$2$-colourable intersecting $r$-uniform hypergraph meets in at most $t$ vertices (`r_le_two_mul_add_one_of_forall_card_inter_le`). Specializing to $t = \lfloor (r - 1)/3 \rfloor$ proves that every $3$-chromatic intersecting $r$-uniform hypergraph ($r \ge 2$) contains two distinct edges meeting in at least $r/3$ vertices (`erdos_836.parts.ii` and `erdos836LinearIntersectionConjecture_proved` with $c = 1/3$).
3. **Erdős–Shelah Codimension-One Avoidance & 4-Uniform Structural Bounds**:
   - Proves universal $2$-colourability of linear intersecting $r$-uniform hypergraphs for all $r \ge 4$ (`isTwoColorable_of_four_le_r_of_isLinearHypergraph`) and the rank upper bound $r \le 5$ under pairwise-intersection-$3$ avoidance (`r_le_five_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable`).
   - Proves Lovász’s $r = 3$ Fano parameters theorem $|E(H)| = |V(H)| = 7$ (`card_eq_seven_and_card_activeVertices_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable`) and verifies the Fano plane witness `PG(2, 2)` on `Fin 7` (`hasCodimensionOneAvoidingWitness_three`).
   - Under codimension-one avoidance ($|e_1 \cap e_2| \le r - 2$), proves minimum active degree $\delta(H) \ge 3$, active-vertex lower bound $|V(H)| \ge 2r + 1$ ($r \ge 3$), the degree-$3$ vertex replacement and sunflower bound $d(v) \ge 4$ for every vertex in a multi-intersection $|e_1 \cap e_2| \ge 2$, the sharpened handshake inequality $3|V(H)| + 1 \le r|E(H)|$ ($r \ge 4$), and the combined $4$-uniform lower bounds $9 \le |E(H)|$ and $9 \le |V(H)|$ (ruling out $|E(H)| \le 8$).

[Solution.lean](Solution.lean) exports 16 unconditional theorems in `Erdos836.Palomar` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) proved across [Proofs/Erdos836Unified435.lean](Proofs/Erdos836Unified435.lean), [Proofs/FourUniformCodimensionOneAvoidingBounds836.lean](Proofs/FourUniformCodimensionOneAvoidingBounds836.lean), and [Proofs/DegreeThreeVertexReplacementAndNineEdgeBound836.lean](Proofs/DegreeThreeVertexReplacementAndNineEdgeBound836.lean), using only the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem in `Solution.lean` | Mathematical statement |
| --- | --- |
| `Erdos836.Palomar.erdos_836.parts.i` | **Disproof of Part (i) ($O(r^2)$ active vertices).** `False ↔ ∃ C > 0, ∀ r ≥ 2, ∀ n H, |(H.biUnion id)| ≤ C * r^2`. |
| `Erdos836.Palomar.erdos_836.parts.ii` | **Proof of Part (ii) (linear edge intersection, $c = 1/3$).** `True ↔ ∃ c > 0, ∀ r ≥ 2, ∀ n H, ∃ e ≠ f ∈ H, c * r ≤ |e ∩ f|`. |
| `Erdos836.Palomar.exists_alon_fin_hypergraph` | **Alon’s equitable-partition hypergraph for all $r \ge 2$.** Exhibits an $r$-uniform $3$-chromatic intersecting hypergraph on `Fin n` with $\ge (2r - 2) + \binom{2r - 2}{r - 1}/2$ active vertices. |
| `Erdos836.Palomar.not_erdos836QuadraticVertexQuestion` | **Refutation of `Erdos836QuadraticVertexQuestion`.** No natural constant $C > 0$ bounds $|V(H)| \le C r^2$ for all $r \ge 2$. |
| `Erdos836.Palomar.erdos836LinearIntersectionConjecture_proved` | **Affirmative resolution of `Erdos836LinearIntersectionConjecture`.** Proves linear pairwise intersection with $c = 1/3$. |
| `Erdos836.Palomar.r_le_two_mul_add_one_of_forall_card_inter_le` | **Universal minimal-blue double-counting bound $r \le 2t + 1$.** Holds over arbitrary `[DecidableEq V]` when pairwise intersections have size $\le t$. |
| `Erdos836.Palomar.isTwoColorable_of_four_le_r_of_isLinearHypergraph` | **Linear intersecting hypergraphs are $2$-colourable for $r \ge 4$.** Rules out non-$2$-colourable linear intersecting hypergraphs above $r = 3$. |
| `Erdos836.Palomar.r_le_five_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable` | **Pairwise-intersection-$2$ rank bound $r \le 5$.** Rules out intersection-$3$-avoiding witnesses for all $r \ge 6$. |
| `Erdos836.Palomar.hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting` | **Universal $3$-colourability of intersecting hypergraphs.** For $r \ge 2$, `HasChromaticNumberThree H ↔ ¬ IsTwoColorable H`. |
| `Erdos836.Palomar.three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable` | **Codimension-one avoiding minimum degree $\delta(H) \ge 3$.** Every active vertex has degree $\ge 3$ when pairwise intersections are $\le r - 2$. |
| `Erdos836.Palomar.two_mul_r_add_one_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one` | **Universal active-vertex lower bound $|V(H)| \ge 2r + 1$.** Holds for all $r \ge 3$ under codimension-one avoidance. |
| `Erdos836.Palomar.four_le_vertexDegree_of_mem_inter_of_two_le_card_inter_of_not_hasPairwiseIntersectionAtLeast_sub_one` | **Degree-$3$ vertex replacement & sunflower theorem.** Any vertex in a size-$\ge 2$ edge intersection has degree $\ge 4$ under codimension-one avoidance. |
| `Erdos836.Palomar.three_mul_card_activeVertices_add_one_le_card_mul_r_of_four_le_r` | **Sharpened handshake bound $3|V(H)| + 1 \le r|E(H)|$.** Holds for all $r \ge 4$ under codimension-one avoidance. |
| `Erdos836.Palomar.nine_le_card_and_nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three` | **$4$-uniform codimension-one avoiding bounds.** Proves $9 \le |E(H)|$, $9 \le |V(H)|$, and $3|V(H)| + 1 \le 4|E(H)|$. |
| `Erdos836.Palomar.card_eq_seven_and_card_activeVertices_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable` | **Lovász $r = 3$ Fano parameters theorem.** Every $3$-uniform non-$2$-colourable linear intersecting hypergraph has $|E(H)| = 7$ and $|V(H)| = 7$. |
| `Erdos836.Palomar.hasCodimensionOneAvoidingWitness_three` | **Fano plane witness at $r = 3$.** Exhibits `fanoPlane` (`PG(2, 2)`) on `Fin 7` as a $3$-uniform codimension-one avoiding witness. |

[Statement.lean](Statement.lean) records benchmark statements without placeholders, and [AxiomAudit.lean](AxiomAudit.lean) verifies statement fidelity and the transitive axioms of every exported endpoint.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license information.
