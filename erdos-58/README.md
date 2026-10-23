# Erdős 58: odd cycle lengths and chromatic number

This package proves the unrestricted statement of Erdős Problem 58 in Lean 4.35.0-rc2. If a simple graph has at most `k` distinct odd simple-cycle lengths, its chromatic number is at most `2 * k + 2`; equality holds exactly when it contains a copy of `K_(2 * k + 2)`. The vertex type is unrestricted, so infinite graphs are included.

The development proves the finite structural theorem of Gyárfás, removes the finite-vertex restriction by finite-target coloring compactness, and handles the bipartite and vertex-critical cases. The exported theorem is [Solution.lean](Solution.lean). Statement fidelity and transitive foundational axioms are checked by [AxiomAudit.lean](AxiomAudit.lean) and the package verifier.

## Provenance

The primary mathematical source is Gyárfás, *Graphs with k odd cycle lengths*, Discrete Mathematics 103 (1992), 41–48, answering a question of Bollobás and Erdős. The odd-cycle-length definitions follow the Formal Conjectures Authors' Apache-2.0 `Circumference.lean` and are restated here because the pinned Mathlib revision lacks them.

Two public Lean developments state related results: `plby/lean-proofs` at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` proves the finite-vertex case, and a public prize-submission package at `CHENLexiao8848/awards`, commit `73816cf2bec00082a6a1ffbf565ef0f0b1017c49`, proves the same unrestricted statement. Neither is imported here; this is an independent proof of the unrestricted Formal Conjectures declaration, with the finite-vertex restriction removed by finite-target coloring compactness. See `formalization.yaml` and `THIRD_PARTY.md` for attribution.

## Verification

The verifier checks package hygiene, manifest consistency, statement fidelity, the zero-sorry build, the environment comparison between challenge and solution, and the transitive axiom audit.
