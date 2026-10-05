# Erdős #1139: large gaps between almost-primes

This standalone Lean 4 project (`v4.35.0-rc2`) formalizes unconditional
maximal-gap, normalized-limsup, Chinese Remainder Theorem, Prime Number
Theorem, and core-classification theorems for
[Erdős problem #1139](https://www.erdosproblems.com/1139), together with a
complete conditional proof of the literal Formal Conjectures
infinite-limsup statement from the published Green–Tao–Ziegler von Mangoldt
linear-forms asymptotic and its reverse reduction to arbitrary-length prime
arithmetic progressions.

Let $1 \le u_1 < u_2 < \cdots$ enumerate the positive integers with at most
two prime factors counted with multiplicity ($\Omega(u_k) \le 2$). Erdős
Problem 1139 asks whether

$$\limsup_{k \to \infty} \frac{u_{k+1} - u_k}{\log(k + 1)} = \infty.$$

In [Erdős #689](../erdos-689/README.md), one residue class per prime $p \le y$
suffices to cover every integer in $[1, y]$ at least twice, which via the
Chinese Remainder Theorem produces an interval $[N + 1, N + y]$ of consecutive
integers with $\Omega(N + h) \ge 3$ at height $N \asymp \prod_{p \le y} p = e^{(1 + o(1)) y}$
and gives a baseline normalized gap limsup of at least $1$. Pushing this
normalized ratio strictly past $1$—and toward $\infty$—requires **subprimorial
CRT conductors**, achieved either by omitting a positive density of protected
reserve primes from the #689 matching construction (yielding an unconditional
strict improvement $G_2(X) \ge c \log X$ and $\limsup \ge A > 1$) or by
upgrading a small prime prefix $p \le z$ to nested prime-square moduli $p^2$
and covering the remaining prime and semiprime survivors with scale-adaptive
dyadic prime shells via the Green–Tao–Ziegler linear-forms theorem (following
the June 2026 manuscript of Chojecki, Price, Sherry, and Tao).

## Statements and proof entrypoints

[Solution.lean](Solution.lean) exports nine proved theorems with zero `sorry`
and only the standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`):

| Declaration | Scope & Meaning |
| --- | --- |
| `Erdos1139.Palomar.uniform_maximal_gap` | **Unconditional:** Uniform maximal gap bound $G_2(X) \ge c \log X$ ($c > 1$): below every sufficiently large height $X$, there is an interval $[N + 1, N + y] \subseteq [1, X]$ of length $y \ge c \log X$ on which $\Omega(N + h) \ge 3$ for all $1 \le h \le y$. |
| `Erdos1139.Palomar.limsup_strictly_gt_one` | **Unconditional:** Strict normalized limsup improvement: there exists $A > 1$ such that $\limsup_{k \to \infty} \frac{u_{k+1} - u_k}{\log(k + 1)} \ge A > 1$. |
| `Erdos1139.Palomar.cover_crt_interval` | **Unconditional:** Any unrestricted mixed prime/prime-square double cover on $[1, y]$ with conductor $Q = \prod_{p \in P} p^{e_p}$ forces an interval $[N + 1, N + y]$ with $Q < N \le 2Q$ on which $\Omega(N + h) \ge 3$ for all $1 \le h \le y$. |
| `Erdos1139.Palomar.seven_square_crt` | **Unconditional:** Explicit finite witness $N = 40323$ with modulus $Q = 44100 = 2^2 \cdot 3^2 \cdot 5^2 \cdot 7^2$ for the 7-target nested-square cover on $\{2, 3, 5, 7\}$. |
| `Erdos1139.Palomar.primorial_log_limit` | **Unconditional:** Prime Number Theorem asymptotic $\lim_{y \to \infty} \frac{\log(\mathrm{primorial}\; y)}{y} = 1$ for the base primorial CRT conductor. |
| `Erdos1139.Palomar.limsup_top_of_sparse` | **Unconditional:** Sublinear logarithmic CRT conductors ($\log Q \le \varepsilon y$ for every $\varepsilon > 0$) imply the literal Formal Conjectures infinite-limsup statement. |
| `Erdos1139.Palomar.erdos_1139_of_gtz` | **Conditional on GTZ:** Complete proof of the literal Formal Conjectures `True ↔` statement from `HasFixedSignedMixedPublishedVonMangoldtAsymptotics`. |
| `Erdos1139.Palomar.prime_ap_of_gtz` | **Reverse reduction:** Proves that `HasFixedSignedMixedPublishedVonMangoldtAsymptotics` implies arbitrary-length arithmetic progressions of primes. |
| `Erdos1139.Palomar.core_classification` | **Unconditional:** Exact four-family classification of deficient targets surviving the fixed-parameter squared-prime core ($z_1 = z$, $z_2 = y / z$). |

[Challenge.lean](Challenge.lean) is a standalone Mathlib-only benchmark
declaring all seven unconditional `Erdos1139.Palomar` theorem targets
(`uniform_maximal_gap`, `limsup_strictly_gt_one`, `cover_crt_interval`,
`seven_square_crt`, `primorial_log_limit`, `limsup_top_of_sparse`, and
`core_classification`) with intentional `sorry` placeholders; `Solution.lean`
never imports `Challenge.lean`. [comparator.json](comparator.json) compares
all seven unconditional theorems in `Challenge` and `Solution` using both
NanoDa and Lean's default kernel.

[Statement.lean](Statement.lean) records the literal Formal Conjectures
proposition `statement` with no admitted theorem or placeholder.
[AxiomAudit.lean](AxiomAudit.lean) proves `statement_fidelity` and audits the
transitive axioms of all 10 public endpoints and fidelity theorems.

## Mathematical idea and module outline

To force $\Omega(N + h) \ge 3$ for every offset $1 \le h \le y$, it suffices to
choose a finite set of primes $P$, a subset $\mathrm{squared} \subseteq P$ of
squared primes, and residue classes $a_p$ such that every $h \in [1, y]$
satisfies

$$\sum_{p \in P} \mathbf{1}_{h \equiv a_p \pmod{p}} + \sum_{p \in \mathrm{squared}} \mathbf{1}_{h \equiv a_p \pmod{p^2}} \ge 2.$$

By the Chinese Remainder Theorem with conductor
$Q = \prod_{p \in P \setminus \mathrm{squared}} p \cdot \prod_{p \in \mathrm{squared}} p^2$,
there is an integer $N \in (Q, 2Q]$ with $N \equiv -a_p \pmod{p^{e_p}}$ for all
$p \in P$. Each $N + h$ is then divisible by a divisor $d_h \mid Q$ with
$\Omega(d_h) = 2$ (either $p_1 p_2$ for two distinct primes or $p^2$ for a
squared prime), and because $d_h \le Q < N < N + h$, the quotient
$(N + h)/d_h > 1$ contributes a third prime factor, forcing
$\Omega(N + h) \ge 3$. Since the index $k$ of the last $P_2$ almost-prime at or
below $N$ satisfies $k \le N \le 2Q$, the normalized gap is at least
$y / \log(2Q + 1)$.

The 266 modules in [Proofs/](Proofs) organize the unconditional and
GTZ-conditional developments into five stages:

1. **Mixed prime/prime-square CRT bridges and PNT conductor baseline**
   ([SparseCoverBridge433](Proofs/SparseCoverBridge433.lean),
   [GoalRootSparseLimsup433](Proofs/GoalRootSparseLimsup433.lean),
   [GoalRootPNTLimsup433](Proofs/GoalRootPNTLimsup433.lean),
   [Reuse689Sparse1139](Proofs/Reuse689Sparse1139.lean)):
   formalizes `UnrestrictedPrimeSquareDoubleCover`, proves `cover_crt_interval`
   and the explicit finite witness `seven_square_crt` ($N = 40323$,
   $Q = 44100$), derives `primorial_log_limit`
   ($\log(\mathrm{primorial}\; y)/y \to 1$) from the Prime Number Theorem, and
   proves `limsup_top_of_sparse` together with the finite fresh-prime reserve
   cleanup bridge.
2. **Unconditional reserve-surplus conductor saving, $\limsup > 1$, and uniform maximal gap $G_2(X) \ge c \log X$**
   ([ProtectedReserveOmission1139](Proofs/ProtectedReserveOmission1139.lean),
   [ProtectedReserveConductor1139](Proofs/ProtectedReserveConductor1139.lean),
   [FixedSupportMargin1139](Proofs/FixedSupportMargin1139.lean),
   [ExpandedCoverConstruction1139](Proofs/ExpandedCoverConstruction1139.lean),
   [StrictGapIntervals1139](Proofs/StrictGapIntervals1139.lean),
   [UniformMaxGap1139](Proofs/UniformMaxGap1139.lean)):
   builds on the unconditional major/minor-arc three-prime double-covering
   proof (`ActualMajorArcFinalCoupling433` and its supporting #689/PNT/Goldbach
   modules). In that construction, each greedy hypergraph matching edge consumes
   one reserve prime to repair *two* deficient targets, leaving a positive-density
   subset of unused protected reserve primes whose zero residue classes can be
   simultaneously omitted from the CRT conductor. Omitting these primes reduces
   the logarithmic conductor to $\log Q \le (1 - \eta) y$ for an explicit fixed
   $\eta > 0$, proving `limsup_strictly_gt_one` ($\limsup \ge A > 1$) and
   `uniform_maximal_gap` ($G_2(X) \ge c \log X$ for a fixed $c > 1$ below every
   sufficiently large height $X$).
3. **Fixed-parameter squared-prime core and four-family deficiency classification**
   ([DeficientCoreConstruction1139](Proofs/DeficientCoreConstruction1139.lean),
   [FullCoreClassification1139](Proofs/FullCoreClassification1139.lean),
   [FixedCoreAsymptotic1139](Proofs/FixedCoreAsymptotic1139.lean)):
   assigns residue $0 \pmod{p^2}$ for primes $p \le z$ and $0 \pmod{p}$ for
   primes $z < p \le y / z$, paying logarithmic conductor
   $\log(\mathrm{primorial}(y / z) \cdot \mathrm{primorial}(z)) = (1/z + o_y(1)) y$,
   and proves `core_classification`: a target $h \in [1, y]$ remains deficient
   if and only if it belongs to one of four families—the unit $h = 1$, a prime,
   a semiprime $p q$ with $p < z$ and $q > y / z$ prime, or a prime power
   $p^e$ ($e \ge 2$) with prime base $z < p \le y / z$.
4. **Scale-adaptive dyadic prime shells, collision-aware singular series, and shared-target covolumes**
   ([SharedTargetFiberCovolume1139](Proofs/SharedTargetFiberCovolume1139.lean),
   [SharedTargetSingularFactorization1139](Proofs/SharedTargetSingularFactorization1139.lean),
   [AdaptiveMixedSingularSeries1139](Proofs/AdaptiveMixedSingularSeries1139.lean),
   [AdaptiveMixedSingularConvergence1139](Proofs/AdaptiveMixedSingularConvergence1139.lean),
   [AdaptiveMixedSignedDomainGeometry1139](Proofs/AdaptiveMixedSignedDomainGeometry1139.lean),
   [AdaptiveMixedVonMangoldtPrimeCountBridge1139](Proofs/AdaptiveMixedVonMangoldtPrimeCountBridge1139.lean),
   [AdaptiveMixedActualPublishedWeightedBridge1139](Proofs/AdaptiveMixedActualPublishedWeightedBridge1139.lean)):
   formalizes the typed affine prime-pattern systems across dyadic prime shells,
   proves unconditional convergence and strict positivity of every
   collision-aware singular Euler product, computes the exact same-type
   shared-target lattice covolume $(W / s)^2$ and physical Jacobian $s / W^2$
   that cancel pattern-degree weights, proves boundedness and positive volume of
   the signed convex windows, and removes proper prime-power contributions on
   all three primality-free lattices ($o(N^2)$, $o(N^3)$, and $o(N^3)$) to
   bridge the published von Mangoldt sums to unweighted simultaneous-prime
   counts.
5. **Two-color global budget transfer, GTZ capstone, and reverse prime-progression reduction**
   ([ScaleAdaptiveGTZGlobalCover1139](Proofs/ScaleAdaptiveGTZGlobalCover1139.lean),
   [ScaleAdaptiveActualGlobalBudgetTransfer1139](Proofs/ScaleAdaptiveActualGlobalBudgetTransfer1139.lean),
   [ScaleAdaptiveGTZConditionalOriginal1139](Proofs/ScaleAdaptiveGTZConditionalOriginal1139.lean),
   [AdaptiveMixedPublishedGTZCapstone1139](Proofs/AdaptiveMixedPublishedGTZCapstone1139.lean),
   [AdaptivePrimeProgressionStrength1139](Proofs/AdaptivePrimeProgressionStrength1139.lean),
   [AdaptivePrimeProgressionConsequence1139](Proofs/AdaptivePrimeProgressionConsequence1139.lean)):
   intersects the usable prime-label pools of the low-type and high-type
   pattern families across dyadic shells, bounds the exponential missing-hit
   load and fresh-prime cleanup conductor for fixed $z = 2^K + 1$ as $y \to \infty$,
   and sends $K \to \infty$ diagonally to derive `erdos_1139_of_gtz` from
   `HasFixedSignedMixedPublishedVonMangoldtAsymptotics`. Conversely,
   `prime_ap_of_gtz` decodes an open convex cell in the original-field portion
   of that hypothesis to produce arbitrary-length prime arithmetic progressions.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and
[THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and licenses. All 270
package modules (`Proofs/` plus `Statement`, `Solution`, `AxiomAudit`, and
`Challenge`) compile from source under Lean `4.35.0-rc2`
(`11acb17ec6b07a8f9e9173e6845197929540936b`) and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Both `./verify.sh` and
`lake env lake comparator --config comparator.json` pass, with both
`nanoda_bin` and Lean's default kernel accepting `Solution`.
