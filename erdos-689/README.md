# Erdős #689: eventual double covering by prime residue classes

For every sufficiently large natural number `n`, there is one residue `a(p)`
for each prime `p ≤ n` such that every integer `1 ≤ m ≤ n` lies in at least
two selected classes. The two hits use distinct prime moduli. Both interval
endpoints are included. This package formalizes the two-fold statement for
sufficiently large `n` in Theorem 1.1 of the
[April 2026 working manuscript](https://www.ulam.ai/research/erdos689.pdf),
addressing the residue-class question posed in
[Erdős's 1979 paper](https://www.renyi.hu/~p_erdos/1979-23.pdf), with no
additional analytic hypothesis. The 1979 question also mentions an
at-least-`r` variant, which is outside this submission.

The contribution is a Lean reconstruction and integration of the analytic
covering argument, including the finite matching construction and the prime
estimates it needs. See the
[problem discussion](https://www.erdosproblems.com/forum/thread/689) for context.

Start with [BUILD.md](BUILD.md) to reproduce the build, or the
[proof guide](PROOF_GUIDE.md) for the mathematical argument.

## Exact statement and proof boundary

[Challenge.lean](Challenge.lean) states the assertion using Mathlib alone.
[Solution.lean](Solution.lean) independently states and proves
`Erdos689.Palomar.eventual_double_cover`, by applying
`Erdos689.erdos_689_original_statement` in
[ActualOfficialSolution433.lean](Proofs/ActualOfficialSolution433.lean).
The solution never imports the intentionally unproved Challenge.
[comparator.json](comparator.json) specifies the statement comparison and
permits only `propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical reading guide

The construction initially chooses the odd class at 2, nonzero classes at a
fixed finite set of auxiliary primes, and zero classes elsewhere. Some targets
still need more hits. A reserve of primes can be reassigned safely because
the auxiliary classes already cover their positive multiples up to `n`
twice. Pairing two deficient targets with one reserve prime saves enough
primes to finish the covering.

| Stage | Main result | Entry points |
| --- | --- | --- |
| Reserve and demand | Estimate available reserve primes and missing hits. | [ReserveDensity433](Proofs/ReserveDensity433.lean), [DeficiencyAsymptotic433](Proofs/DeficiencyAsymptotic433.lean) |
| Pairing edges | Count the required triples of primes and bound all three coordinate degrees. | [ThreePrimeWeightTransfer433](Proofs/ThreePrimeWeightTransfer433.lean), [ActualLeftVertexFinal433](Proofs/ActualLeftVertexFinal433.lean) |
| Matching and cleanup | With all three coordinate degrees at most `Δ > 0`, a maximal matching satisfies `|E| ≤ 3 Δ |M|`. Its pairs and the remaining reserve primes repair every missing hit. | [GreedyMatching](Proofs/GreedyMatching.lean), [MatchingAssembly](Proofs/MatchingAssembly.lean), [AnalyticScalarCapacity433](Proofs/AnalyticScalarCapacity433.lean) |
| Analytic completion | Prove the major-arc estimate and combine the inputs into the final theorem. | [ActualMajorArcFinalCoupling433](Proofs/ActualMajorArcFinalCoupling433.lean), [ActualOfficialSolution433](Proofs/ActualOfficialSolution433.lean) |

The main analytic step connects the actual major-arc integral to its signed
conductor model. This requires deduplicating translated rational centers,
retaining the different odd and doubled-conductor cutoffs, and controlling
boundary and error terms. The [proof guide](PROOF_GUIDE.md) explains this
connection, the order of parameter choices, and the matching budget, with
links to the exact declarations. Earlier modules state conditional results.
The final proof supplies every hypothesis used for the covering conclusion.

## Provenance, verification, and limitations

The analytic dependencies include a compatibility port of Principia's
Goldbach master, PrimeNumberTheoremAnd, and other sources identified by exact
revision and file hash in [source-manifest.json](source-manifest.json) and
[THIRD_PARTY.md](THIRD_PARTY.md). Two admitted Wiener lemmas in the upstream
tree are outside the final theorem's transitive dependencies. See
[BUILD.md](BUILD.md) for the endpoint axiom audit and Palomar verification
requirements.

No numerical sufficient threshold or extension to every fixed covering
multiplicity is asserted. This is a formalization of the cited argument. No
discovery priority, independent specialist review, or Palomar registration is
claimed. Locally authored material is released under the [MIT license](../LICENSE).
Included upstream sources retain the terms recorded in [THIRD_PARTY.md](THIRD_PARTY.md).
