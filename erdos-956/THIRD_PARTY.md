# Attribution and third-party sources

This package formalizes and extends the parabolic-cap lower-bound construction for Erdős problem #956, posed by Erdős and Pach (1990), whose $\Theta(n^{4/3})$ growth order was announced by Valtr (2005) and detailed in a one-sided two-layer construction by Chojecki (April 2026).

Locally authored proof modules in `Proofs/`, `Statement.lean`, `Solution.lean`, and `AxiomAudit.lean` are licensed under the included `LICENSE` (MIT).

The problem definitions (`Plane`, `translateDistance`, `IsConfiguration`, `unitPairs`, `h`) and statement (`erdos_956`) in `Challenge.lean`, `Statement.lean`, and `Solution.lean` are adapted from [FormalConjectures/ErdosProblems/956.lean](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjectures/ErdosProblems/956.lean) from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) under the [Apache-2.0 License](third_party/FORMAL-CONJECTURES-LICENSE.txt), with original copyright notices preserved. The upstream unproved theorem file is not imported.
