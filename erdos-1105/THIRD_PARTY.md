# Attribution and third-party sources

This package formalizes the published solutions to Erdős problem #1105 due to Erdős, Simonovits, and Sós (1975), Simonovits and Sós (1984), Montellano-Ballesteros and Neumann-Lara (2005), Choi (2011), and Yuan (2021). It is a formalization of known mathematics. An independent Lean `v4.33.0` formalization of Erdős #1105 is available in [`plby/lean-proofs`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos1105.lean); no code from that repository is imported or adapted here.

Locally authored proof modules in `Proofs/`, `Statement.lean`, `Challenge.lean`, `Solution.lean`, and `AxiomAudit.lean` are Copyright 2026 Linmiao Xu and licensed under the included `LICENSE` (Apache-2.0). The third-party utilities below originate from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) and retain their Apache-2.0 license terms.

| Included source | Upstream and exact revision | License |
| --- | --- | --- |
| `Proofs/CycleRepresentativeExchange.lean` (`SimpleGraph.IsRainbow`, `SimpleGraph.antiRamseyNum`) | [Formal Conjectures Vertex/EdgeLabeling utility](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean), `eb1c5ce1bf406e46a6af5f859f097a5c5350a462` | [Apache-2.0](third_party/FORMAL-CONJECTURES-LICENSE.txt), original copyright header preserved |
| `Proofs/PathRestorationAndCircumference.lean` (`Erdos58.cycleLengths`, `Erdos58.oddCycleLengths`) | [Formal Conjectures Circumference utility](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean), `eb1c5ce1bf406e46a6af5f859f097a5c5350a462` | [Apache-2.0](third_party/FORMAL-CONJECTURES-LICENSE.txt), original copyright header preserved |

The problem statement in `Challenge.lean`, `Statement.lean`, and `Solution.lean` is adapted from [FormalConjectures/ErdosProblems/1105.lean](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjectures/ErdosProblems/1105.lean) (Apache-2.0). The upstream unproved theorem file is not imported.
