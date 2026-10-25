# Erdős 918: shift graphs and local chromatic equality

A Lean 4 formalization of the Erdős and Hajnal (1968) shift-graph theorem under the generalized continuum hypothesis and the impossibility of the Erdős (1969) local chromatic equality formulations for Erdős Problem 918. The induced-subgraph equality refutations use a successor-cardinal color-class pigeonhole argument that produces a large independent set, since the edgeless-subgraph observation for arbitrary subgraphs does not transfer directly to induced subgraphs.

See [Erdős problem #918](https://www.erdosproblems.com/918) for background and literature.

## Scope and main results

The seven exported theorems prove the Erdős–Hajnal (1968, Corollary 1) finite-index theorem under GCH, all four textbook local-equality refutations (for both induced subgraphs and arbitrary subgraphs in Parts (i) and (ii)), the exact ordinal dichotomy for the induced Part (ii) equality formulation, and the unconditional Erdős–Hajnal higher-order shift-graph chromatic threshold. The four open ≤ ℵ₀ existence questions—Parts (i) and (ii), for induced subgraphs and all subgraphs—remain open in ZFC and are not addressed here.

The equality and upper-bound statements have different scopes. A subgraph with chromatic cardinal 1 satisfies the bound ≤ ℵ₀, so ruling out chromatic cardinal exactly ℵ₀ says nothing about whether the open upper-bound questions have witnesses.

[Solution.lean](Solution.lean) exports 7 theorems in `Erdos918.variants` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) across 2 self-contained proof modules in [Proofs/](Proofs), using only the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem in `Solution.lean` | Mathematical statement |
| --- | --- |
| `Erdos918.variants.erdos_hajnal` | Proves Erdős–Hajnal (1968, Corollary 1) under GCH: for every finite $k > 0$, there is a graph on $\aleph_k$ vertices with chromatic cardinal $\aleph_1$ whose induced subgraphs on $< \aleph_k$ vertices have chromatic cardinal $\le \aleph_0$. |
| `Erdos918.variants.eq_aleph_0.parts.i` | Refutes the induced-subgraph equality formulation for Part (i). |
| `Erdos918.variants.eq_aleph_0_all_subgraphs.parts.i` | Refutes the all-subgraph equality formulation for Part (i). |
| `Erdos918.variants.eq_aleph_0.parts.ii` | Refutes the induced-subgraph equality formulation for Part (ii) at the first infinite ordinal. |
| `Erdos918.variants.eq_aleph_0_all_subgraphs.parts.ii` | Refutes the all-subgraph equality formulation for Part (ii) at the first infinite ordinal. |
| `Erdos918.variants.induced_eq_aleph0_parts_ii_negation_iff_one_le` | Gives the exact ordinal dichotomy: the induced Part (ii) equality statement is impossible if and only if the ordinal parameter is at least $1$. |
| `Erdos918.variants.chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow` | Formalizes the unconditional Erdős–Hajnal shift-graph threshold: chromatic cardinal at most $\mu$ iff the underlying linear order has cardinality at most $\exp_2^{(r)}(\mu)$. |

[Statement.lean](Statement.lean) records the five upstream variant statements, and [AxiomAudit.lean](AxiomAudit.lean) checks statement fidelity and the transitive axioms of the seven exported endpoints.

## Proof modules

- [PigeonholeAndEqualityRefutations918.lean](Proofs/PigeonholeAndEqualityRefutations918.lean): Proves the successor-cardinal pigeonhole and independent-set theorems, the four induced and all-subgraph equality refutations, and the exact ordinal dichotomy.
- [ShiftGraphHierarchy918.lean](Proofs/ShiftGraphHierarchy918.lean): Formalizes the Erdős–Hajnal (1968) Theorem 1–2 higher-order shift-graph chromatic threshold by induction on $r$ and derives Corollary 1 under GCH.

## Build and verification

See [BUILD.md](BUILD.md) for in-package reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license information. `./verify.sh` builds the package from source and checks the endpoint axiom audit; `./verify.sh --no-sandbox` also invokes the package's configured Comparator check.
