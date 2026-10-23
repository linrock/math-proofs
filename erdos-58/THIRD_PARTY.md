# Third-party materials and attribution

The odd-cycle-length definitions `SimpleGraph.cycleLengths` and
`SimpleGraph.oddCycleLengths` are restated from the Formal Conjectures Authors'
Apache-2.0 file `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean`,
because they are absent from the pinned Mathlib revision. The exported theorem
matches `FormalConjectures/ErdosProblems/58.lean` exactly at the pinned commit
recorded in `formalization.yaml`.

The mathematical result is due to András Gyárfás, *Graphs with k odd cycle
lengths*, Discrete Mathematics 103 (1992), 41–48, answering a question of
Bollobás and Erdős. The proof in this package reconstructs Gyárfás's
longest-odd-cycle and common-contact arguments from the published exposition,
so the paper is the primary source and is cited throughout `Proofs/`.

Two public Lean developments state related results. `plby/lean-proofs` at
commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` proves the finite-vertex case
under Apache-2.0 and credits Gyárfás as the informal author. A public
prize-submission package at `CHENLexiao8848/awards`, commit
`73816cf2bec00082a6a1ffbf565ef0f0b1017c49`, proves the same unrestricted
statement for arbitrary vertex types. Neither is imported here. They are
recorded so that this package is described as an independent proof rather than
the first formalization of the statement.

The shortest-odd-closed-walk extraction in `Proofs/OddCycleExtraction108.lean`
is an elementary argument written for this package: a shortest odd closed walk
has no repeated vertex other than its base point, so its vertices induce an odd
cycle of the same length.

Apache-2.0 license notices and acknowledgements are retained in the Lean
headers, `formalization.yaml`, and `README.md`.
