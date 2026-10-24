# Attribution and third-party sources

This package formalizes unconditional lower and upper bounds, exact small-case evaluations, Paley tournament constructions, and second-moment domination criteria for Erdős Problem #902 (Erdős, 1963; Szekeres–Szekeres, 1965).

Locally authored and adapted modules in `Proofs/`, `Statement.lean`, `Challenge.lean`, `Solution.lean`, and `AxiomAudit.lean` are Copyright 2026 The Formal Conjectures Authors and 2026 Linmiao Xu, and are licensed under the included `LICENSE` (Apache-2.0).

`Erdos902.IsTournament` restates `Digraph.IsTournament` from `google-deepmind/formal-conjectures` (`FormalConjecturesForMathlib/Combinatorics/Digraph/Tournament.lean`) under the [Apache-2.0 License](third_party/FORMAL-CONJECTURES-LICENSE.txt). The restatement keeps the package dependent on Mathlib alone.

## Mathematical sources

The quadratic-residue tournament construction follows Paley (1933), *On orthogonal matrices*, J. Math. Phys. 12, 311–320. The Erdős (1963) and Szekeres–Szekeres (1965) bounds and exact values are formalized here from their published statements. The cyclic-triad bounds follow Kendall and Babington Smith (1940), *On the method of paired comparisons*, Biometrika 31, 324–345, §8, theorem (1). No code from these sources is copied.
