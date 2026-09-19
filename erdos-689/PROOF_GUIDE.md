# Reading the proof of Erdős #689

This guide explains the mathematical interfaces that connect the analytic
estimates to the final covering, with links to the Lean declarations.
All declaration names below are in namespace `Erdos689` unless indicated.

## What is proved

For every sufficiently large natural number $n$, there is a function
$a:\mathbb N\to\mathbb N$ such that every $m\in\{1,\ldots,n\}$
belongs to at least two classes $a(p)\pmod p$, with distinct primes
$p\le n$. The function may depend on $n$. Only its values modulo the
available primes matter. The theorem supplies neither an explicit threshold
nor a result for every fixed covering multiplicity.

The final type is written out in [Solution.lean](Solution.lean), and follows
through `erdos_689_original_statement` in
[ActualOfficialSolution433](Proofs/ActualOfficialSolution433.lean) from
`officialStatement_unconditional` in
[ActualMajorArcFinalCoupling433](Proofs/ActualMajorArcFinalCoupling433.lean).
There is no remaining analytic premise in that chain. In contrast,
[Challenge.lean](Challenge.lean) deliberately contains a proof hole: it is the
independent statement for comparison, and is not imported by Solution.

## The finite construction and its budget

Fix a finite support $S$ of primes greater than 3, and nonzero residues
$b(s)\pmod s$. Set $W=\prod_{s\in S}s$. The initial assignment chooses
the odd class at 2, the class $b(s)$ at each support prime, and the zero
class elsewhere. Define the total deficiency to be the sum, over all targets,
of the number of hits still needed to reach two.

A residue $r\pmod W$ is **robust** if it is a unit modulo $W$ and each
of $r,2r,\ldots,Jr$ has at least two support hits. A reserve prime $p$
lies outside $S\cup\{2\}$, is robust, and satisfies $n<(J+1)p$.
Consequently every positive multiple of $p$ up to $n$ already has two
support hits. Its zero class can be reassigned safely, even when other reserve
primes are reassigned at the same time. These are actual finite sets and
predicates in [AnalyticBridge](Proofs/AnalyticBridge.lean), not an assumed
density or an assumed covering.

One useful reassignment repairs two targets. Its edge is
$(A,B,P)$, where $P$ is a prime reserve label, $B=A+P$,
$A=aq$, and $B=2du$, with $a,d\mid W$ and prime cores $q,u$.
The repaired targets are **$2A$ and $2B$**. They lie in $[1,n]$,
are initially deficient, and are congruent modulo $P$. The label lies in
the actual strip $\tau n<P\le(\tau+\ell)n$. The edge definition also
requires that neither target lies in a selected support residue class.
See `manuscriptEdge` and
`robustManuscriptEdges` in AnalyticBridge, and
`manuscriptEdge_paired_targets` in [ManuscriptLocal](Proofs/ManuscriptLocal.lean).

A three-partite matching uses different left vertices, right vertices, and
prime labels. Odd left vertices and even right vertices make the two target
families disjoint as well. If all three coordinate degrees are at most
$\Delta>0$, a maximal matching $M$ satisfies

\[
|E|\le 3\Delta |M|.
\]

Each of its edges spends one reserve prime and removes at least two deficiency
units. Thus, writing $D_0$ for the initial deficiency and $R$ for the
reserve, it suffices to obtain $D_0\le |R|+|M|$. Remaining labels repair
the remaining deficiency one unit at a time. The simultaneous-switch proof
preserves two protected hits wherever they were already needed. It does not
assume that individually safe changes remain safe in combination. See
[GreedyMatching](Proofs/GreedyMatching.lean),
`matching_realizes_protected_ledger` in
[MatchingAssembly](Proofs/MatchingAssembly.lean), and
`covering_of_manuscript_edges` in ManuscriptLocal.

## The analytic estimate actually needed

The edge count is not supplied by a general conjecture about primes. The
formalized estimate counts the specific triples of primes

\[
q,\quad u,\quad P=2du-aq
\]

with $a,d\mid W$, $q,u\notin S$, the original edge windows and
selectors, and a robust residue $P\equiv r\pmod W$. Its weight is
$\log q\log u\log P$. The finite count is
`manuscriptWeightedResidueCount` in
[ThreePrimeMajorArcReduction433](Proofs/ThreePrimeMajorArcReduction433.lean).
In particular, it already filters for primes. It does not count prime powers
as successful graph edges.

The precise theorem `UniformLocalizedThreePrimeMajorArcLowerBound` says:
there exists an **absolute** $c>0$ such that, for every fixed
$S,b,J,\tau,\ell$ satisfying

\[
s>\max(3,J),\quad b(s)\not\equiv0\pmod s\quad(s\in S),\qquad
\tau>0,\quad\ell>0,\quad\tau+\ell<1/10,
\]

all sufficiently large $n$ satisfy, simultaneously for every robust $r$,

\[
T_r(n)\ge c\,L_{S,b}(r)\,\ell n^2.
\]

Here $T_r$ is the weighted count just defined and

\[
L_{S,b}(r)=\prod_{s\in S}\frac{F_s(r)}{s-1},\qquad
F_s(r)=
\begin{cases}
1-2/(s-1)^2,&2r\equiv b(s)\text{ or }2r+b(s)\equiv0\pmod s,\\
1-3/(s-1)^2,&\text{otherwise}.
\end{cases}
\]

These factors are positive. Their sum over robust residues is at least
$\#\mathrm{Robust}/(2\varphi(W))$, as proved by
`robust_local_singular_factor_sum_lower`. The constant $c$ is chosen
**before** the support. The eventual threshold may depend on all the fixed
parameters. There is no support-uniform numerical threshold. This distinction
is necessary when the covering construction chooses its parameters.

The residue classes partition the weighted total exactly. Each prime weight
is at most $\log n$, so division by $\log^3 n$ gives a lower bound
on the number of parameter tuples. Different admissible tuples encode
different edges: factoring a support divisor times a prime outside the
support recovers both factors. Therefore this count has no hidden
multiplicity loss. The relevant results are
`primePatternEncoding_injOn` in
[PrimePatternMultiplicity433](Proofs/PrimePatternMultiplicity433.lean) and
`manuscriptWeightedPrimePatternCount_div_log_cube_le_actual_edges` in
[ThreePrimePatternBridge433](Proofs/ThreePrimePatternBridge433.lean).

The outcome has scale $n^2/\log^3 n$, and the three degree bounds have scale
$n/\log^2 n$. This produces a matching of scale $n/\log n$, the same
scale as the reserve and deficiency. The final comparison uses a strict
margin, not just matching orders of magnitude. In
`officialStatement_of_fixed_support_analytic_rate_margin` in
[AnalyticScalarCapacity433](Proofs/AnalyticScalarCapacity433.lean), it is

\[
1<\rho_R+\frac{c\rho\ell}{3C},
\]

where $\rho_R$ is the reserve density, $\rho$ the robust-residue density,
$c$ the edge constant after transfers, and $C$ the degree constant.
The proof synthesizes integer matching and cleanup budgets from this margin
and the actual asymptotic estimates. It does not assume those budgets exist.

## Why the final major-arc coupling matters

Fourier inversion splits $T_r(n)$ exactly into the complete shifted
major-arc integral and its minor-arc complement. The full coefficient-summed
minor integral is $o(n^2)$, in absolute value, for fixed parameters.
Consequently positive quadratic major mass survives after absorbing the
minor error. This transfer is
`uniformLocalizedThreePrimeMajorArcLowerBound_of_actual_summed_major_positivity`
in [ActualMajorArcPrimeMinor433](Proofs/ActualMajorArcPrimeMinor433.lean).

Showing that a proposed singular series is positive would not suffice: it
must equal the model of the **actual integral**, up to a proved small error.
The closure in [ActualMajorArcFinalCoupling433](Proofs/ActualMajorArcFinalCoupling433.lean)
has three identifiable pieces:

1. The actual prime integral differs from its canonical smooth-center model
   by $o(n^2)$. This includes summed analytic errors, prime-power removal,
   and signed exceptional terms. The entry point is
   `actualMajorArcException_prime_minus_pure_smooth_tendsto_zero` in
   [ActualMajorArcExceptionClosure433](Proofs/ActualMajorArcExceptionClosure433.lean).
2. `actualMajorArcExactCanonicalCenterReindex_unconditional` proves a finite
   equality between the deduplicated smooth-center model and the signed
   conductor model, under the actual disjointness and robust-target conditions.
   The required disjointness holds eventually for the chosen moving cutoffs.
3. Signed conductor tails are $o(n^2)$. The corrected predicted main term
   is positive of quadratic size, with the local factor needed above.
   `actualMajorArcFinalCoupling_canonical_smooth_tendsto_zero` and
   `actualMajorArcFinalCoupling_corrected_of_exact_center_reindex` combine
   these facts by an absolute-error triangle inequality.

The finite equality is the place to inspect signs and multiplicities. Shifted
rational centers are deduplicated using a canonical widest anchor. The
boundary centers 0 and 1 together contribute one arc. Terms with forbidden
support-square conductors and conductors divisible by four vanish by the
proved cancellation identities. For noncoprime coefficient pairs, cancellation
occurs only after summing the **complete signed support-character orbit**.
Individual centers are not declared zero.

There is also a genuine finite parity correction. Write

\[
A(X)=\sum_{\substack{1\le v\le X \\ \gcd(v,2W)=1}}
\frac{\mu(v)}{\varphi(v)^2}.
\]

If $Q$ is the conductor cutoff, the odd and doubled conductors produce
$A(Q)+A(\lfloor Q/2\rfloor)$, rather than $2A(Q)$.
[ActualMajorArcCorrectedModel433](Proofs/ActualMajorArcCorrectedModel433.lean)
retains that exact finite model and proves that the difference from the older
doubled model, after multiplying by the actual coefficient-weighted lattice
mass, is $o(n^2)$.

The final theorem follows through these declarations:

| Proved declaration in ActualMajorArcFinalCoupling433 | Its role |
| --- | --- |
| `actualMajorArcExactCanonicalCenterReindex_unconditional` | Exact finite connection to the real center model. |
| `uniformActualDeduplicatedCorrectedSingularModelCoupling_unconditional` | The actual prime-only mass has the corrected asymptotic model. |
| `uniformActualCoefficientSummedMajorArcPositivity_unconditional` | Supplies the absolute positive constant before choosing the support. |
| `uniformLocalizedThreePrimeMajorArcLowerBound_unconditional` | Gives the required count of genuine prime patterns. |
| `officialStatement_unconditional` | Concludes the selected eventual two-fold covering assertion. |

The degree side is independently supplied by
`fixedModulusTwoFormDegreeBound_unconditional` in
[ActualLeftVertexFinal433](Proofs/ActualLeftVertexFinal433.lean).
[ActualLeftVertexMajorOnlyCovering433](Proofs/ActualLeftVertexMajorOnlyCovering433.lean)
shows explicitly how it combines with the localized estimate. Introductory
comments in earlier modules describe then-open conditional interfaces. The
final proof supplies the hypotheses it uses.

## Relationship to the manuscript and verification

The covering strategy and Theorem 1.1 are described in the
[April working manuscript](https://www.ulam.ai/research/erdos689.pdf) cited in
the [README](README.md). This package reconstructs its concrete
covering argument in Lean: finite greedy matching, protected reserve and
deficiency counts, a localized prime-pattern count, and sieve degree bounds.
The manuscript obtains its prime-triples estimate from Green–Tao. This
development proves the needed localized estimate through the major/minor-arc
analysis described above. The formalization makes center deduplication,
signed cancellation, the finite parity correction, moving windows, and all
three degree bounds explicit.

[BUILD.md](BUILD.md) documents the source build and endpoint axiom audit.
The endpoint should use only `propext`, `Classical.choice`, and `Quot.sound`.
The two upstream admitted Wiener lemmas are outside its transitive dependency
set. [THIRD_PARTY.md](THIRD_PARTY.md) records the pinned external dependencies.
For a mathematical review, compare the public statement with the displayed
type, inspect the parameter order and nonempty reserve construction, follow
the count-to-edge map, and check the final integral-to-model chain.
