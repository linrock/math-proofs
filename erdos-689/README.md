# Erdős #689: eventual double covering by prime residue classes

For every sufficiently large natural number `n`, there is one residue `a(p)`
for each prime `p ≤ n` such that every integer `1 ≤ m ≤ n` lies in at least
two selected classes. The two hits use distinct prime moduli; both interval
endpoints are included. This package formalizes the two-fold statement for
sufficiently large `n` in Theorem 1.1 of the
[April 2026 working manuscript](https://www.ulam.ai/research/erdos689.pdf),
addressing the residue-class question posed in
[Erdős's 1979 paper](https://www.renyi.hu/~p_erdos/1979-23.pdf), with no
additional analytic hypothesis. The 1979 question also mentions an
at-least-`r` variant, which is outside this submission.

The contribution is a Lean reconstruction and integration of the analytic
covering argument, including the finite matching construction and the prime
estimates it needs. Related discussion appears in the
[problem discussion](https://www.erdosproblems.com/forum/thread/689).
The package makes no discovery-priority or independent specialist-acceptance
claim.

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

The [detailed proof guide](PROOF_GUIDE.md) explains the localized three-prime
estimate, the exact integral-to-model coupling, the parameter order, and the
finite matching budget, with links to the declarations that discharge each
obligation.

The covering starts with the zero residue at most primes and changes residues
on a fixed finite support. These changes create both uncovered demand and a
protected supply of primes whose labels can be reassigned without losing
already required coverage. Pairing two demands with one available prime label
saves enough of this supply to finish the construction.

| Stage | Mathematical obligation | Entry points in the packaged proof |
| --- | --- | --- |
| Exact covering bookkeeping | Count missing hits and retain which prime labels can safely be switched. | [Structural](Proofs/Structural.lean), [DeficiencyClassification](Proofs/DeficiencyClassification.lean), [MatchingAssembly](Proofs/MatchingAssembly.lean) |
| Reserve and demand estimates | Count robust residue classes modulo the fixed support product; apply the prime number theorem in fixed progressions to obtain the supply, with its actual moving cutoff. Compare it with total deficiency. | [ReserveDensity433](Proofs/ReserveDensity433.lean), [DeficiencyAsymptotic433](Proofs/DeficiencyAsymptotic433.lean), [AnalyticScalarCapacity433](Proofs/AnalyticScalarCapacity433.lean) |
| Enough pairing edges | Establish a localized three-prime lower bound for the actual affine forms and residue restrictions. | [ThreePrimeMajorArcReduction433](Proofs/ThreePrimeMajorArcReduction433.lean), [ThreePrimeWeightTransfer433](Proofs/ThreePrimeWeightTransfer433.lean) |
| Controlled collisions | Bound all three graph-degree coordinates using the required prime estimates and finite Selberg sieve bounds. | [SelbergOptimizedBridge433](Proofs/SelbergOptimizedBridge433.lean), [ActualLeftVertexFinal433](Proofs/ActualLeftVertexFinal433.lean), [ActualRightVertexFinal433](Proofs/ActualRightVertexFinal433.lean) |
| Matching and cleanup | A maximal three-partite matching satisfies `|E| ≤ 3 Δ |M|`. Its edges repair paired demands; remaining reserve labels finish the covering. | [GreedyMatching](Proofs/GreedyMatching.lean), [ActualRightVertexFinalCovering433](Proofs/ActualRightVertexFinalCovering433.lean) |
| Close the analytic obligations | Identify the actual major-arc integral with the signed conductor model, discharge positivity and degree inputs, and conclude the selected eventual two-fold statement. | [ActualMajorArcFinalCoupling433](Proofs/ActualMajorArcFinalCoupling433.lean), [ActualOfficialSolution433](Proofs/ActualOfficialSolution433.lean) |

The delicate analytic interface is the last row. Translated rational centers
must be deduplicated before integration. The proof retains support-character
signs, the distinct odd and doubled-conductor cutoffs, boundary corrections,
and exceptional and tail terms. In particular, vanishing of a complete signed
orbit does not mean that each center vanishes separately. The capstone proves
`actualMajorArcExactCanonicalCenterReindex_unconditional`, obtains the genuine
localized lower bound, and finally proves `officialStatement_unconditional`.
Earlier modules expose conditional interfaces; their historical introductory
comments sometimes describe obligations subsequently closed by this capstone.
The final declarations and their transitive axioms determine the proof boundary.

The finite greedy-matching estimate, reserve bookkeeping, fixed-progression
prime-density transfer, and Selberg interfaces are useful separately. Reuse
requires preserving their support, cutoff, coprimality, and uniformity hypotheses;
the final theorem does not assert a general prime-pattern principle.

## Provenance, verification, and limitations

The analytic dependencies include a compatibility port of Principia's
Goldbach master, PrimeNumberTheoremAnd, and other sources identified by exact
revision and file hash in [source-manifest.json](source-manifest.json) and
[THIRD_PARTY.md](THIRD_PARTY.md). Their source location does not establish local
mathematical originality. Two unrelated admitted Wiener lemmas occur in the
upstream tree. [BUILD.md](BUILD.md) gives the source build and endpoint axiom
audit commands for this project.

No numerical sufficient threshold or extension to every fixed covering
multiplicity is asserted. Separate finite exclusions do not provide an upper
bound on the eventual threshold. Registration, specialist review, and catalog
recognition remain distinct from local kernel verification. Locally authored
material is released under the [MIT license](../LICENSE); included upstream
sources retain the terms recorded in [THIRD_PARTY.md](THIRD_PARTY.md).
