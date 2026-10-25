# Attribution and third-party sources

This package formalizes the Ruzsa–Szemerédi subquadratic upper bound $e(n, r) = o(n^2)$ for Erdős Problem #600 (Erdős, 1987; Ruzsa and Szemerédi, 1978), together with auxiliary structural results on locally linear and $r$-book-free triangle-covered graphs, weighted vertex blow-ups, non-neighbor triangle partitions, and $r$-book edge-deletion reductions.

The statement definitions `SimpleGraph.trianglesContaining`, `Erdos600.Erdos600Prop` and `Erdos600.eFunction` are adapted from `google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/600.lean` and `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean`), Copyright 2025–2026 The Formal Conjectures Authors, under the Apache License, Version 2.0 (see [third_party/FORMAL-CONJECTURES-LICENSE.txt](third_party/FORMAL-CONJECTURES-LICENSE.txt)).

Locally authored modules in `Proofs/`, `Statement.lean`, `Challenge.lean`, `Solution.lean` and `AxiomAudit.lean` are Copyright 2026 Linmiao Xu, and are licensed under the included `LICENSE` (Apache-2.0).

All graph-theoretic and analytic foundations (`SimpleGraph`, `SimpleGraph.LocallyLinear`, `SimpleGraph.CliqueFree`, `SimpleGraph.FarFromTriangleFree`, `SimpleGraph.triangleRemovalBound`, `ruzsaSzemerediNumberNat` and `Asymptotics.IsLittleO`) come from `leanprover-community/mathlib4` at commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (Apache-2.0).

The main proof depends on Mathlib's `SimpleGraph.triangleRemovalBound` and the far-from-triangle-free machinery in `Mathlib/Combinatorics/SimpleGraph/Triangle/Removal.lean`, which formalize the triangle removal lemma of Yaël Dillies and Bhavik Mehta, *Formalising Szemerédi's regularity lemma in Lean*, ITP 2022. The package applies that lemma to the book-threshold problem and does not reprove it.

The lower bound for the $r = 2$ case transfers Mathlib's formalization of the Behrend construction, from `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` and `Mathlib/Combinatorics/Extremal/RuzsaSzemeredi.lean`, which combines Felix A. Behrend, *On sets of integers which contain no three terms in arithmetical progression* (Proc. Nat. Acad. Sci. USA 32, 1946) with the Ruzsa–Szemerédi reduction from the three-term-progression-free extremal function (`rothNumberNat`, named after Klaus F. Roth, *On certain sets of integers*, J. London Math. Soc. 28, 1953) to `ruzsaSzemerediNumberNat` in Mathlib.
