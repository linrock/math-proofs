# Attribution and third-party sources

The local probability-sieve proof formalizes the published argument of Paul
Balister, Béla Bollobás, Robert Morris, Julian Sahasrabudhe, and Marius Tiba
(BBMST) for the negative answer to Erdős problem 2. It is a formalization of
known mathematics. Another public formalization is available in
[plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos2.md)
and is bundled in
[Jayyhk/erdos-lean](https://github.com/Jayyhk/erdos-lean/blob/ada6b53e46a2b1df91dd4ef6d30bd875c7e989c3/problems/2/Erdos2.lean).
Those implementations are references, not imported dependencies of this package.

The 31 saved local modules originate in the previously kernel-checked source
closure. Three product-bound applications are adapted to Mathlib's rc2 API;
their original and current hashes are recorded in `source-manifest.json`.
The full Lean 4.33.1 release is preserved in the baseline archive described in
`PORTING.md`. Existing proof comments are preserved as
historical source text; current verification is reported in `VERIFICATION.json`.
Locally authored material is licensed under the included `LICENSE` (MIT).
The third-party files below retain their original Apache-2.0 terms.

| Included source | Upstream and exact revision | License |
| --- | --- | --- |
| `Proofs/CoveringSystem2.lean` | [Formal Conjectures covering-system utility](https://github.com/google-deepmind/formal-conjectures/blob/1f3951b7b0eb81f6b33ebc9bbe2b2c1feaf422d1/FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean), `1f3951b7b0eb81f6b33ebc9bbe2b2c1feaf422d1` | [Apache-2.0](third_party/FORMAL-CONJECTURES-LICENSE.txt), original copyright header preserved |
| `Proofs/PrimeNumberTheoremAnd/EulerMaclaurin.lean`, `Proofs/PrimeNumberTheoremAnd/IEANTN/Mertens.lean` | [ajirving/PrimeNumberTheoremAnd](https://github.com/ajirving/PrimeNumberTheoremAnd/tree/769d3b81fbff001d9fa7028df0168a8e546cf692), `769d3b81fbff001d9fa7028df0168a8e546cf692` | [Apache-2.0](third_party/PNT-LICENSE.txt) |
| `Proofs/Architect.lean` and eight `Proofs/Architect/*.lean` files | [hanwenzhu/LeanArchitect](https://github.com/hanwenzhu/LeanArchitect/tree/78dd66840d3efe8c824c699fc03381cec817c271), `78dd66840d3efe8c824c699fc03381cec817c271` | [Apache-2.0](third_party/ARCHITECT-LICENSE.txt) |

The selected upstream sources are unchanged. Their upstream Lake configurations
are replaced by this package's scoped library declarations to use the exact
Lean 4.35.0-rc2/Mathlib pins and avoid unrelated packages. Architect supplies
blueprint metadata tooling; its definition of an admission tactic is not used
by any mathematical proof here. The endpoint audit permits only `propext`,
`Classical.choice`, and `Quot.sound`.

Mathlib and its normal transitive dependencies are fetched through the pinned
`lake-manifest.json`; their licenses remain in their respective checkouts.
The original statement is taken from
[Formal Conjectures #2](https://github.com/google-deepmind/formal-conjectures/blob/1f3951b7b0eb81f6b33ebc9bbe2b2c1feaf422d1/FormalConjectures/ErdosProblems/2.lean).
Its unproved theorem is not imported. The new `Solution.lean` wrapper applies
the proved local capstone, and `AxiomAudit.lean` checks statement fidelity.
