# Attribution and third-party sources

This package formalizes the probability-sieve proof of the negative answer to
Erdős problem #2 due to Paul Balister, Béla Bollobás, Robert Morris, Julian
Sahasrabudhe, and Marius Tiba, [*On the Erdős Covering Problem: the density of the uncovered set*](https://arxiv.org/abs/1811.03547)
(*Inventiones Mathematicae* 228 (2022), 377–414), resolving the problem first
solved by Bob Hough ([*Solution of the minimum modulus problem for covering systems*, *Annals of Mathematics* 181 (2015), 361–382](https://doi.org/10.4007/annals.2015.181.1.6)).
An independent Lean formalization is available in
[`plby/lean-proofs`](https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos2.md)
and [`Jayyhk/erdos-lean`](https://github.com/Jayyhk/erdos-lean/blob/ada6b53e46a2b1df91dd4ef6d30bd875c7e989c3/problems/2/Erdos2.lean);
no code from those repositories is imported or adapted here.

Locally authored proof modules in `Proofs/`, `Statement.lean`, `Solution.lean`,
and `AxiomAudit.lean` are licensed under the included `LICENSE` (MIT).
The third-party files below retain their original Apache-2.0 terms.

| Included source | Upstream and exact revision | License |
| --- | --- | --- |
| `Proofs/CoveringSystem2.lean` and adapted definitions in `Challenge.lean` | [Formal Conjectures covering-system utility](https://github.com/google-deepmind/formal-conjectures/blob/1f3951b7b0eb81f6b33ebc9bbe2b2c1feaf422d1/FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean) and [FormalConjectures/ErdosProblems/2.lean](https://github.com/google-deepmind/formal-conjectures/blob/1f3951b7b0eb81f6b33ebc9bbe2b2c1feaf422d1/FormalConjectures/ErdosProblems/2.lean), `1f3951b7b0eb81f6b33ebc9bbe2b2c1feaf422d1` | [Apache-2.0](third_party/FORMAL-CONJECTURES-LICENSE.txt), original copyright header preserved |
| `Proofs/PrimeNumberTheoremAnd/EulerMaclaurin.lean`, `Proofs/PrimeNumberTheoremAnd/IEANTN/Mertens.lean` | [ajirving/PrimeNumberTheoremAnd](https://github.com/ajirving/PrimeNumberTheoremAnd/tree/769d3b81fbff001d9fa7028df0168a8e546cf692), `769d3b81fbff001d9fa7028df0168a8e546cf692` | [Apache-2.0](third_party/PNT-LICENSE.txt) |
| `Proofs/Architect.lean` and eight `Proofs/Architect/*.lean` files | [hanwenzhu/LeanArchitect](https://github.com/hanwenzhu/LeanArchitect/tree/78dd66840d3efe8c824c699fc03381cec817c271), `78dd66840d3efe8c824c699fc03381cec817c271` | [Apache-2.0](third_party/ARCHITECT-LICENSE.txt) |

The vendored upstream sources in `Proofs/CoveringSystem2.lean`,
`Proofs/PrimeNumberTheoremAnd/`, and `Proofs/Architect*` are unchanged.
`Architect` supplies `@[blueprint]` attribute macros used by `Mertens.lean`;
none of the proof modules use `sorry`, and the standalone axiom audit verifies
that all exported theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`.
