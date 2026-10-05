# Attribution and third-party sources

This package formalizes unconditional mixed prime/prime-square covering
bridges, Prime Number Theorem primorial conductor asymptotics, fixed-parameter
squared-core deficiency classification, and reserve-omission maximal-gap and
normalized-limsup theorems for [Erdős problem #1139](https://www.erdosproblems.com/1139),
together with the complete conditional formalization of the June 2026
proposed solution ([forum thread #1139](https://www.erdosproblems.com/forum/thread/1139#post-7063),
attributed to Przemysław Chojecki, Liam Price, Gavin Sherry, and Terence Tao)
from the published Green–Tao–Ziegler von Mangoldt linear-forms asymptotic
(`HasFixedSignedMixedPublishedVonMangoldtAsymptotics`) and its reverse
reduction to arbitrary-length prime progressions.

Locally authored proof modules in `Proofs/`, `Statement.lean`, `Solution.lean`,
and `AxiomAudit.lean` are licensed under the [MIT License](LICENSE). The
third-party sources below retain their original licenses and attribution
notices.

| Included source | Upstream and exact revision | License |
| --- | --- | --- |
| `Statement.lean`, `Challenge.lean`, and `Solution.lean` | [Formal Conjectures Erdős #1139](https://github.com/google-deepmind/formal-conjectures/blob/eb1c5ce1bf406e46a6af5f859f097a5c5350a462/FormalConjectures/ErdosProblems/1139.lean), `eb1c5ce1bf406e46a6af5f859f097a5c5350a462` | [Apache-2.0](third_party/FORMAL-CONJECTURES-LICENSE.txt), original copyright header preserved |
| `Proofs/Architect.lean` and eight `Proofs/Architect/*.lean` files | [hanwenzhu/LeanArchitect](https://github.com/hanwenzhu/LeanArchitect/tree/78dd66840d3efe8c824c699fc03381cec817c271), `78dd66840d3efe8c824c699fc03381cec817c271` | [Apache-2.0](third_party/ARCHITECT-LICENSE.txt) |
| `Proofs/PrimeNumberTheoremAnd/*.lean` (25 modules) | [ajirving/PrimeNumberTheoremAnd](https://github.com/ajirving/PrimeNumberTheoremAnd/tree/769d3b81fbff001d9fa7028df0168a8e546cf692), `769d3b81fbff001d9fa7028df0168a8e546cf692` (with two unused admitted decay lemmas in `Wiener.lean` removed so all modules compile with `-E hasSorry`) | [Apache-2.0](third_party/PNT-LICENSE.txt) |
| `Proofs/ErdosProblems/Erdos730/*.lean` (2 modules) | [williamjblair/lean-proofs](https://github.com/williamjblair/lean-proofs/tree/5d10b4d91f257cfbe8c563cf927f543a868845e0), `5d10b4d91f257cfbe8c563cf927f543a868845e0` | [MIT](third_party/BLAIR-LICENSE.txt) and [NOTICE](third_party/BLAIR-NOTICE.txt) |
| `Proofs/GoldbachCircleBase.lean`, `Proofs/GoldbachSW1.lean`, `Proofs/GoldbachSW2.lean`, `Proofs/GoldbachSW3.lean`, `Proofs/GoldbachChainMaster.lean` | [antoshashakov/Principia-Math-Solutions](https://github.com/antoshashakov/Principia-Math-Solutions/tree/c9910942522fbd3a07c034ac57947f56df6f0f6d/erdos1054), `c9910942522fbd3a07c034ac57947f56df6f0f6d` (ported to Lean `v4.35.0-rc2`; see [third_party/goldbach_master_433.patch](third_party/goldbach_master_433.patch)) | [Apache-2.0](third_party/PRINCIPIA-LICENSE.txt) |
