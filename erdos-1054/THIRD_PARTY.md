# Attribution and third-party sources

This package resolves all three parts of Erdős problem #1054 and establishes the
sharp $c / [A^3 (1 + \log A)^4]$ odd-density lower bound, the divisibility-preserving
Tao–Kovač $O(\delta^3 X)$ small-ratio upper bound, and the two-way cofactor-two
aliquot range density equivalence.

Locally authored proof modules in `Proofs/` (`Aliquot1054.lean`,
`AliquotEquivalence1054.lean`, `CofactorParity1054.lean`,
`Integration1054.lean`, `OddTail1054.lean`, `OriginalNth1054.lean`,
`SecondMoment1054.lean`, `SharpSecondMoment1054.lean`,
`SmallRatioKovac1054.lean`, `StatementAudit1054.lean`, and
`Unconditional1054.lean`), together with `Statement.lean`, `Solution.lean`, and
`AxiomAudit.lean`, are licensed under the included [MIT License](LICENSE).
The third-party files below retain their original Apache-2.0 license terms.

| Included source | Upstream and exact revision | License |
| --- | --- | --- |
| Problem definitions and statements in `Statement.lean`, `Challenge.lean`, and `Solution.lean` | [`FormalConjectures/ErdosProblems/1054.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1054.lean) | [Apache-2.0](third_party/FORMAL-CONJECTURES-LICENSE.txt), original copyright header preserved |
| `Proofs/Erdos1054Conditional.lean` and `Proofs/Goldbach*.lean` (`GoldbachSW1`–`GoldbachSW3`, `GoldbachCircleBase`, `GoldbachRatedWindow`, `GoldbachMajorArc`, `GoldbachArcTail`, `GoldbachChainMaster`) | [`antoshashakov/Principia-Math-Solutions`](https://github.com/antoshashakov/Principia-Math-Solutions/tree/c9910942522fbd3a07c034ac57947f56df6f0f6d/erdos1054), `c9910942522fbd3a07c034ac57947f56df6f0f6d` (ported to Lean `v4.35.0-rc2` and split into modules under 10,000 lines) | [Apache-2.0](third_party/PRINCIPIA-LICENSE.txt) |
| Eighteen modules in `Proofs/PrimeNumberTheoremAnd/` | [`ajirving/PrimeNumberTheoremAnd`](https://github.com/ajirving/PrimeNumberTheoremAnd/tree/769d3b81fbff001d9fa7028df0168a8e546cf692), `769d3b81fbff001d9fa7028df0168a8e546cf692` (with two unused `sorry` declarations removed from `Wiener.lean` so all modules compile with `-E hasSorry`) | [Apache-2.0](third_party/PNT-LICENSE.txt) |
| `Proofs/Architect.lean` and eight `Proofs/Architect/*.lean` files | [`hanwenzhu/LeanArchitect`](https://github.com/hanwenzhu/LeanArchitect/tree/78dd66840d3efe8c824c699fc03381cec817c271), `78dd66840d3efe8c824c699fc03381cec817c271` | [Apache-2.0](third_party/ARCHITECT-LICENSE.txt) |

None of the 47 modules in `Proofs/` use `sorry`, and the standalone axiom audit
verifies that all exported theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.
