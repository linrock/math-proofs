# Attribution and third-party sources

This package formalizes the published solutions to Erdős problem #1105 due to Erdős, Simonovits, and Sós (1975), Simonovits and Sós (1984), Montellano-Ballesteros and Neumann-Lara (2005), Choi (2011), and Yuan (2021). It is a formalization of known mathematics. An independent Lean `v4.33.0` formalization of Erdős #1105 is available in [`plby/lean-proofs`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos1105.lean); no code from that repository is imported or adapted here.

Locally authored proof modules in `Proofs/`, `Statement.lean`, `Solution.lean`, and `AxiomAudit.lean` are licensed under the included `LICENSE` (MIT). The two third-party utility files below originate from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) and retain their Apache-2.0 license terms.

| Included source | Upstream and exact revision | License |
| --- | --- | --- |
| `Proofs/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean` | [Formal Conjectures Clique utility](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean), `eb1c5ce1bf406e46a6af5f859f097a5c5350a462` | [Apache-2.0](third_party/FORMAL-CONJECTURES-LICENSE.txt), original copyright header preserved |
| `Proofs/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean` | [Formal Conjectures Vertex/EdgeLabeling utility](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean), `eb1c5ce1bf406e46a6af5f859f097a5c5350a462` | [Apache-2.0](third_party/FORMAL-CONJECTURES-LICENSE.txt), original copyright header preserved |

The problem statement in `Challenge.lean`, `Statement.lean`, and `Solution.lean` is adapted from [FormalConjectures/ErdosProblems/1105.lean](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjectures/ErdosProblems/1105.lean) (Apache-2.0). The upstream unproved theorem file is not imported.

## Pinned Mathlib sources for material imported definitions

Verbatim copies of the six pinned Mathlib (`065356127b1dc0016f66b7283ce0ce2c4055aa55`, [Apache-2.0](third_party/MATHLIB-LICENSE.txt)) source modules defining the imported graph, coloring, and asymptotic concepts used in `Challenge.lean` are included under [`third_party/mathlib/`](third_party/mathlib) so they can be audited directly alongside the kernel-checked definitional unfoldings in `Challenge.lean` and `AxiomAudit.lean`:

| Pinned Mathlib module (`065356127b1dc0016f66b7283ce0ce2c4055aa55`) | Material definitions audited | SHA-256 |
| --- | --- | --- |
| [`Mathlib/Combinatorics/SimpleGraph/Coloring/EdgeLabeling.lean`](third_party/mathlib/Mathlib/Combinatorics/SimpleGraph/Coloring/EdgeLabeling.lean) | `SimpleGraph.EdgeLabeling` (`G.edgeSet → K`), `SimpleGraph.TopEdgeLabeling` (`EdgeLabeling (⊤ : SimpleGraph V) K`), `SimpleGraph.EdgeLabeling.pullback` (`C ∘ f.mapEdgeSet`) | `a5dcae25730e2e5e36171bc1420f52ed837c32bc37b8414242c30ca91fcf1a68` |
| [`Mathlib/Combinatorics/SimpleGraph/Copy.lean`](third_party/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean) | `SimpleGraph.Copy` (`toHom : H →g G`, `injective' : Injective toHom`), `SimpleGraph.IsContained` (`H ⊑ G`), `SimpleGraph.Free` (`¬H ⊑ G`) | `4563363534e5159a9fb3f5e7b181697aecef5f2c7d394e2c19a229c65788c2fe` |
| [`Mathlib/Combinatorics/SimpleGraph/Maps.lean`](third_party/mathlib/Mathlib/Combinatorics/SimpleGraph/Maps.lean) | `SimpleGraph.Hom` (`H →g G := RelHom H.Adj G.Adj`), `SimpleGraph.Hom.mapEdgeSet`, `SimpleGraph.Embedding` (`H ↪g G`) | `1cbcdb71178ac50a3be430a614c058db6eb993ab3c7925d6596b55101b6fdb37` |
| [`Mathlib/Combinatorics/SimpleGraph/CycleGraph.lean`](third_party/mathlib/Mathlib/Combinatorics/SimpleGraph/CycleGraph.lean) | `SimpleGraph.cycleGraph` (`0 | 1 => ⊥`, `n + 2 => { Adj a b := a - b = 1 ∨ b - a = 1 }` on `Fin n`) | `e27eae54e744fce3023b38a003fe292111954fe492416a4d1d600cb8ff3fd524` |
| [`Mathlib/Combinatorics/SimpleGraph/Hasse.lean`](third_party/mathlib/Mathlib/Combinatorics/SimpleGraph/Hasse.lean) | `SimpleGraph.hasse` (`Adj a b := a ⋖ b ∨ b ⋖ a`), `SimpleGraph.pathGraph` (`hasse (Fin n)`, with `(pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val`) | `ff8591720b870f024c61df0abe8e9499da2466b9a07db0fe6a6a212cdbff65a4` |
| [`Mathlib/Analysis/Asymptotics/Defs.lean`](third_party/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean) | `Asymptotics.IsBigOWith`, `Asymptotics.IsBigO` (`f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖`) | `68ef9c1b2d13f99770bcd0c679a23f078f634ea344ff914d7d634ba1682104ed` |
