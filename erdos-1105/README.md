# Erdős #1105: anti-Ramsey numbers for cycles and paths

This standalone Lean 4 project gives a complete formal proof of both parts of
[Erdős problem #1105](https://www.erdosproblems.com/1105). For a finite simple
graph $H$ and host order $n$, the **anti-Ramsey number** $\mathrm{AR}(n, H)$
(`SimpleGraph.antiRamseyNum H n`) is the maximum number of colors in a
surjective edge-labeling of the complete graph $K_n$ that contains no
**rainbow** (injectively edge-colored) copy of $H$.

1. **Part (i) — Cycles ($C_k$):** For every fixed cycle order $k \ge 3$,
   $$\mathrm{AR}(n, C_k) = \left(\frac{k - 2}{2} + \frac{1}{k - 1}\right) n + O(1).$$
2. **Part (ii) — Paths ($P_k$):** For every path order $k \ge 5$ and host order
   $n \ge k$, with $\ell = \lfloor (k - 1) / 2 \rfloor$ and $\varepsilon = 1$ if
   $k$ is odd and $\varepsilon = 2$ if $k$ is even,
   $$\mathrm{AR}(n, P_k) = \max\left\{\binom{k - 2}{2} + 1,\; \binom{\ell - 1}{2} + (\ell - 1)(n - \ell + 1) + \varepsilon\right\}.$$

Both parts are celebrated theorems in extremal graph theory:
[Erdős, Simonovits, and Sós (1975)](https://real.mtak.hu/110457/1/1975-05.pdf)
introduced anti-Ramsey numbers, proved the exact triangle formula
$\mathrm{AR}(n, C_3) = n - 1$, and conjectured the cycle formula;
[Montellano-Ballesteros and Neumann-Lara (2005)](https://doi.org/10.1007/s00373-005-0619-3)
proved the exact formula for $\mathrm{AR}(n, C_k)$ across all $k \ge 3$ and
$n \ge k$, with a streamlined weak-block decomposition proof of the linear
upper bound given in Jongook Choi's 2011 Iowa State University dissertation
(*Problems in Graph Theory and Probability*, Chapter 3);
[Simonovits and Sós (1984)](https://doi.org/10.1007/BF02579163) formulated the
two-branch path formula and proved it for large $n$; and
[Yuan (2021)](https://arxiv.org/abs/2102.00807) established the exact path
formula across all $n \ge k \ge 5$.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) exports ten unconditional theorems with zero
`sorry` and only the standard foundational axioms (`propext`,
`Classical.choice`, `Quot.sound`):

| Declaration | Meaning |
| --- | --- |
| `Erdos1105.Palomar.erdos_1105_cycles` | Direct universal statement of Part (i) for all $k \ge 3$. |
| `Erdos1105.Palomar.erdos_1105_paths` | Direct universal statement of Part (ii) for all $k \ge 5$ and $n \ge k$. |
| `Erdos1105.Palomar.erdos_1105_parts_i` | Elaborated `True ↔` form of Part (i). |
| `Erdos1105.Palomar.erdos_1105_parts_ii` | Elaborated `True ↔` form of Part (ii). |
| `Erdos1105.Palomar.antiRamseyNum_triangle` | Erdős–Simonovits–Sós (1975) exact triangle theorem: $\mathrm{AR}(n, C_3) = n - 1$ for all $n \ge 3$. |
| `Erdos1105.Palomar.cycle_fullBlock_lower` | Ordered $(k - 1)$-clique block lower bound: $\lfloor n / (k - 1) \rfloor (\binom{k - 1}{2} + 1) - 1 \le \mathrm{AR}(n, C_k)$ for all $n \ge k \ge 3$. |
| `Erdos1105.Palomar.cycle_real_lower` | Explicit real linear lower bound: $(\frac{k - 2}{2} + \frac{1}{k - 1}) n - (\frac{k - 2}{2} + \frac{1}{k - 1})(k - 1) - 1 \le \mathrm{AR}(n, C_k)$ for all $n \ge k \ge 3$. |
| `Erdos1105.Palomar.cycle_linear_upper` | Explicit linear upper bound: $\mathrm{AR}(n, C_k) \le (\frac{k - 2}{2} + \frac{1}{k - 1}) n - 1$ for all $n \ge k \ge 3$. |
| `Erdos1105.erdos_1105.parts.i` | Literal Formal Conjectures Part (i) over `SimpleGraph.antiRamseyNum`. |
| `Erdos1105.erdos_1105.parts.ii` | Literal Formal Conjectures Part (ii) over `SimpleGraph.antiRamseyNum`. |

[Challenge.lean](Challenge.lean) is a standalone Mathlib-only benchmark
declaring `IsRainbow`, `antiRamseyNum`, and the eight `Erdos1105.Palomar`
theorem targets with intentional `sorry` placeholders; `Solution.lean` never
imports `Challenge.lean`. [comparator.json](comparator.json) compares all eight
theorems in `Challenge` and `Solution` using both NanoDa and Lean's default
kernel.

[Statement.lean](Statement.lean) records the literal Formal Conjectures
propositions `statement_i` and `statement_ii` using the attributed Apache-2.0
utility `FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex`,
with no admitted theorem or placeholder. [AxiomAudit.lean](AxiomAudit.lean)
proves definitional statement fidelity (`statement_i_fidelity` and
`statement_ii_fidelity`) and audits the transitive axioms of all exported
endpoints.

## Mathematical idea and module outline

To bound $\mathrm{AR}(n, H)$ from above, one selects a **representative
subgraph** $G \subseteq K_n$ containing one edge of each color present in the
host coloring. Any subgraph of $G$ is automatically rainbow, so if the host
coloring avoids rainbow copies of $H$, then $G$ is an $H$-free simple graph on
$n$ vertices with $q$ edges. Moreover, when $q$ exceeds the extremal threshold,
one can track **private ("NEW") colors** incident to individual vertices—colors
that disappear upon deleting a vertex $v$—and perform single-edge color
exchanges between components of $G$.

The 314 modules in [Proofs/](Proofs) organize the proofs of Part (i) and
Part (ii) into five main components:

1. **Cycle asymptotic formula**
   ([CycleOriginalHighNewStructureV5](Proofs/CycleOriginalHighNewStructureV5.lean),
   [CycleConditionalAsymptotic](Proofs/CycleConditionalAsymptotic.lean),
   [CycleConditionalUpper](Proofs/CycleConditionalUpper.lean),
   [CycleFullBlockRealLower](Proofs/CycleFullBlockRealLower.lean),
   [TriangleExact](Proofs/TriangleExact.lean),
   [CycleFourHighNewStructure](Proofs/CycleFourHighNewStructure.lean)):
   establishes the ordered-block lower bound by partitioning $K_n$ into cliques
   of order $k - 1$ (giving $\lfloor n / (k - 1) \rfloor \binom{k - 1}{2} + \lfloor n / (k - 1) \rfloor - 1$
   colors with no rainbow $C_k$) and proves the matching upper bound by
   inducting on vertices with few private colors and analyzing the minimum-degree
   high-NEW core via Hamiltonian component bounds, chord rotations, and
   3-component triangle splices across $k = 3$, $k = 4$, and $k \ge 5$.
2. **Universal path lower bound**
   ([PathMaxLower](Proofs/PathMaxLower.lean),
   [PathCliqueColor](Proofs/PathCliqueColor.lean),
   [PathCliqueBridge](Proofs/PathCliqueBridge.lean),
   [PathSetLower](Proofs/PathSetLower.lean),
   [PathSetColor](Proofs/PathSetColor.lean),
   [PathSetBridge](Proofs/PathSetBridge.lean)): constructs both extremal
   colorings on `Fin n`—the $(k - 2)$-clique coloring with one outside color
   ($\binom{k - 2}{2} + 1$ colors) and the $(\ell - 1)$-hub coloring with a
   1- or 2-color outside palette ($\binom{\ell - 1}{2} + (\ell - 1)(n - \ell + 1) + \varepsilon$
   colors)—and proves that neither admits a rainbow copy of $P_k$.
3. **Universal odd paths, $P_6$, and finite-window reduction**
   ([OddPathsUniversalExact1105](Proofs/OddPathsUniversalExact1105.lean),
   [Erdos1105UniversalPathReduction](Proofs/Erdos1105UniversalPathReduction.lean),
   [PathFiveExact](Proofs/PathFiveExact.lean),
   [PathSixOriginalAllHostExact1105](Proofs/PathSixOriginalAllHostExact1105.lean),
   [PathSevenOriginalAllHostExact1105](Proofs/PathSevenOriginalAllHostExact1105.lean),
   [OddUniversalUpper1105](Proofs/OddUniversalUpper1105.lean)): proves the exact
   formula for $\mathrm{AR}(n, P_5) = \max(4, n) = n$,
   $\mathrm{AR}(n, P_6) = \max(7, n + 1) = n + 1$,
   $\mathrm{AR}(n, P_7) = \max(11, 2n - 2) = 2n - 2$, and all odd paths
   $k = 2\ell + 1 \ge 9$ across all $n \ge k$ via cone-core elimination and residual component
   ledgers, and reduces all even paths $k = 2d + 2 \ge 8$ ($d \ge 3$) via
   low-NEW vertex deletion to the finite base window
   $2d + 2 \le n \le 2d + 2 + \lfloor (d - 1) / 2 \rfloor$.
4. **Even path kernel elimination and circumference ($k \ge 10$)**
   ([SmallKernelWholeSupport1105](Proofs/SmallKernelWholeSupport1105.lean),
   [EvenConnectedLargeKernel1105](Proofs/EvenConnectedLargeKernel1105.lean),
   [LargeKernelCircumference1105](Proofs/LargeKernelCircumference1105.lean),
   [LongCycleFromMinimumDegree1105](Proofs/LongCycleFromMinimumDegree1105.lean),
   [EvenOriginalNonemptyCore1105](Proofs/EvenOriginalNonemptyCore1105.lean)):
   eliminates nonempty $(d + 1)$-cone cores and all $d$-core kernel regimes
   $d + 3 \le |K| \le 2d + 2$ via additive seed-first path filling and residual
   $P_4$ / $P_3 \sqcup P_2$ / $3P_2$ star-center extraction, then proves
   2-connectedness and $2d$-cycle existence for $|K| \ge 2d + 3$ whenever the
   edge deficit satisfies $D_{\mathrm{rem}} < \binom{d}{2}$, establishing the
   exact formula for all even path orders $k = 2d + 2 \ge 10$ ($d \ge 4$).
5. **$P_8$ base window ($n \in \{8, 9\}$)**
   ([PathEightSpanningBase1105](Proofs/PathEightSpanningBase1105.lean),
   [PathEightNineBase1105](Proofs/PathEightNineBase1105.lean),
   [ActualCutDegreeLedger1105](Proofs/ActualCutDegreeLedger1105.lean),
   [ActualK8Rigidity1105](Proofs/ActualK8Rigidity1105.lean)): proves
   $\mathrm{AR}(8, P_8) = 16$ via cut-degree ledgers and 3-hub rigidity on
   $K_8$, and $\mathrm{AR}(9, P_8) = 17$ by showing that $|E(G)| \ge 17$ on
   $K_9$ forces at least three vertices of internal degree $\ge 4$ in the
   3-core $K$, closing $|K| \in \{6, 7, 8, 9\}$ and completing
   `erdos_1105_parts_ii_exact`.

## Earlier Lean work and provenance

The problem statements in `Statement.lean`, `Challenge.lean`, and
`Solution.lean` and the graph-coloring definitions in
[`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean)
and
[`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean`](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean)
are reproduced with their Apache-2.0 attribution and
[license text](third_party/FORMAL-CONJECTURES-LICENSE.txt). The upstream
[`FormalConjectures/ErdosProblems/1105.lean`](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjectures/ErdosProblems/1105.lean)
declarations end in `sorry`.

An independent Lean `v4.33.0` formalization of both parts of Erdős #1105 was
previously published in
[`plby/lean-proofs`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos1105.lean)
using a custom `Erdos1105.antiRamseyNum` definition over `(⊤ : SimpleGraph (Fin n)).edgeSet → Fin q`
(written before `formal-conjectures` updated `SimpleGraph.antiRamseyNum` to
`TopEdgeLabeling (Fin n) (Fin k)` in PR #5829); no code from that repository is
imported or adapted here. Compared with that formalization, this package is an
independent development on Lean `v4.35.0-rc2` that proves the literal upstream
`FormalConjectures` declarations `Erdos1105.erdos_1105.parts.i` and
`Erdos1105.erdos_1105.parts.ii` directly over `SimpleGraph.antiRamseyNum` and
`TopEdgeLabeling`, exports explicit non-asymptotic cycle lower and upper bounds
for all $n \ge k \ge 3$, and proves Part (ii) via a finite host-window
reduction, additive seed-first path filling, and 2-connected circumference
bounds.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and
[THIRD_PARTY.md](THIRD_PARTY.md) for source attribution. Both `./verify.sh`
and `lake env lake comparator --config comparator.json` pass, with both
`nanoda_bin` and Lean's default kernel accepting `Solution`.
