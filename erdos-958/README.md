# Erdős #958: planar point sets with distance multiplicities `{1, ..., n - 1}`

This standalone Lean 4 project gives a complete formal proof of the negative
answer to [Erdős problem #958](https://www.erdosproblems.com/958), formalizing
the explicit circular-arc-and-center counterexample construction of
[Clemen, Dumitrescu, and Liu (arXiv:2505.04283, 2025)](https://arxiv.org/abs/2505.04283)
for all $n \ge 4$, together with the positive multiplicity-profile theorems for
equidistant collinear point sets and short-arc circular equidistant point sets.

For a finite planar point set $A \subset \mathbb{R}^2$ of size $n$, let
$\{d_1, \dots, d_k\}$ be the set of distinct interpoint distances
(`distanceSet A`) and let $f(d)$ denote the multiplicity of $d$—the number of
unordered pairs of distinct points from $A$ at distance $d$
(`distanceMultiplicity A d`). Every progression of $n$ equally spaced points on
a line or on a sufficiently short circular arc determines $k = n - 1$ distinct
distances with multiplicities $\{1, 2, \dots, n - 1\}$. Erdős asked whether,
for all sufficiently large $n$, these two families are the only configurations
with $k = n - 1$ and $\{f(d_1), \dots, f(d_k)\} = \{1, \dots, n - 1\}$, and
conjectured that the answer is **no**.

In [*On multiplicities of interpoint distances* (arXiv:2505.04283, May 2025)](https://arxiv.org/abs/2505.04283),
Felix Clemen, Adrian Dumitrescu, and Dingyuan Liu confirmed Erdős's conjecture
by proving that placing $n - 1$ equidistant points on a short circular arc of
the unit circle together with the circle's center $(0, 0)$ yields $n - 1$
distinct distances with multiplicities $\{1, \dots, n - 1\}$ for every
$n \ge 4$, while neither being equidistant on a line nor equidistant on a
circle.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) exports five proved benchmark targets in
`Erdos958.Palomar` (matched by [Challenge.lean](Challenge.lean) and
[comparator.json](comparator.json)) along with the literal
`Erdos958.erdos_958` declaration:

| Declaration | Meaning |
| --- | --- |
| `Erdos958.Palomar.erdos_958` | Elaborated Formal Conjectures `False ↔` form of Erdős #958. |
| `Erdos958.Palomar.not_erdos_958` | Direct disproof of the large-$n$ classification statement (`¬ ∃ N : ℕ, ∀ n ≥ N, ...`). |
| `Erdos958.Palomar.clemen_dumitrescu_liu` | Explicit all-$n \ge 4$ theorem: for every $n \ge 4$, there exists $A \subset \mathbb{R}^2$ of size $n$ with $n - 1$ distinct distances of multiplicities $\{1, \dots, n - 1\}$ satisfying `¬ IsEquidistantOnLine A ∧ ¬ IsEquidistantOnCircle A`. |
| `Erdos958.Palomar.equidistantOnLine_has_profile` | Positive direction for collinear progressions: every $A \subset \mathbb{R}^2$ with `#A ≥ 2` and `IsEquidistantOnLine A` has `#(distanceSet A) = #A - 1` and multiplicities `{1, ..., #A - 1}`. |
| `Erdos958.Palomar.equidistantOnCircle_exists_has_profile` | Positive direction for circular arcs: for every $n \ge 2$, `arcSet (n + 1)` is an $n$-point set satisfying `IsEquidistantOnCircle` with $n - 1$ distinct distances and multiplicities `{1, ..., n - 1}`. |

[Challenge.lean](Challenge.lean) states these five targets using only Mathlib
and intentional `sorry` placeholders; `Solution.lean` never imports
`Challenge.lean`. [Statement.lean](Statement.lean) records the Formal
Conjectures proposition `Erdos958.Challenge.statement` with no placeholder, and
[AxiomAudit.lean](AxiomAudit.lean) verifies definitional statement fidelity
(`statement_fidelity`), the explicit finite non-vacuity witness
`nonvacuity_cdlSet_5` for `cdlSet 5`, and the transitive axioms (`propext`,
`Classical.choice`, `Quot.sound`) of all exported theorems.

## Mathematical idea and module outline

For each $n \ge 4$, we define `cdlSet n` to consist of the origin
$p_0 = (0, 0)$ together with the $n - 1$ unit-circle points

$$u_k = \left(\cos\frac{k}{n}, \sin\frac{k}{n}\right) \quad \text{for } 0 \le k < n - 1.$$

Because $0 \le \frac{k}{n} < 1 < \frac{\pi}{3}$ (since $\pi > 3$), all angular
separations $\frac{|i - j|}{n}$ lie in $[0, \pi / 3)$. On this arc, the chord
length between $u_i$ and $u_j$ depends strictly monotonically on step size
$s = |i - j| \in \{1, \dots, n - 2\}$ and stays strictly below $1$, while the
center $p_0$ has distance $1$ to all $n - 1$ arc points.

The three modules in [Proofs/](Proofs) implement this construction and its verification:

1. **[Definitions958.lean](Proofs/Definitions958.lean)**: Defines `distanceSet`, `distanceMultiplicity`, `IsEquidistantOnLine`, `IsEquidistantOnCircle`, `originPt`, `arcPt`, `arcSet`, `cdlSet`, and the chord length formula
   $$\operatorname{chordDist}(n, s) = \sqrt{2 - 2\cos(s / n)}.$$
   Proves $\operatorname{dist}(p_0, u_k) = 1$, $\operatorname{dist}(u_i, u_j) = \operatorname{chordDist}(n, |i - j|)$, strict monotonicity $0 < \operatorname{chordDist}(n, s_1) < \operatorname{chordDist}(n, s_2) < 1$ for $0 < s_1 < s_2 < n$ using `Real.strictAntiOn_cos`, and `#(cdlSet n) = n`.
2. **[Multiplicity958.lean](Proofs/Multiplicity958.lean)**: Establishes that for all $n \ge 2$,
   $$\operatorname{distanceSet}(\operatorname{cdlSet} n) = \{1\} \cup \{\operatorname{chordDist}(n, s) : 1 \le s \le n - 2\}$$
   has cardinality $n - 1$, with exact multiplicities $\operatorname{distanceMultiplicity}(\operatorname{cdlSet} n, 1) = n - 1$ and $\operatorname{distanceMultiplicity}(\operatorname{cdlSet} n, \operatorname{chordDist}(n, s)) = n - 1 - s$ for $1 \le s \le n - 2$, so that the multiplicity image is `Finset.Icc 1 (n - 1)`. Also proves the general progression theorem `image_range_has_profile` for any indexed point family whose pairwise distances depend injectively on $|i - j|$.
3. **[Obstruction958.lean](Proofs/Obstruction958.lean)**: Proves `¬ IsEquidistantOnLine (cdlSet n)` for $n \ge 3$ (eliminating linear coordinates across $p_0, u_0, u_1$ to contradict $\sin(1/n) \ne 0$) and `¬ IsEquidistantOnCircle (cdlSet n)` for $n \ge 4$ (eliminating circle equations across $p_0, u_0, u_1, u_2$ via the double-angle identities for $\cos(2/n)$ and $\sin(2/n)$ to contradict $\cos(1/n) < 1$). Also proves the positive theorems `equidistantOnLine_has_profile` and `equidistantOnCircle_exists_has_profile`, and assembles `clemen_dumitrescu_liu`, `not_erdos_958`, and `erdos_958`.

## Earlier Lean work and provenance

The pinned [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/0c92ca701538aba00014d1d6444df7954eea3f6d/FormalConjectures/ErdosProblems/958.lean)
and metric counting definitions in
[`FormalConjecturesForMathlib/Geometry/Metric.lean`](https://github.com/google-deepmind/formal-conjectures/blob/0c92ca701538aba00014d1d6444df7954eea3f6d/FormalConjecturesForMathlib/Geometry/Metric.lean)
are reproduced with their Apache-2.0 attribution and
[license text](third_party/FORMAL-CONJECTURES-LICENSE.txt). The upstream
`FormalConjectures/ErdosProblems/958.lean` declaration ends in `sorry`.

An independent Lean `v4.33.0` file in
[`plby/lean-proofs`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos958.lean)
verified only the single $4$-point exception $\{(0, 0), (1, 0), (0, 1), (0, -1)\}$
against an earlier unquantified formulation before Formal Conjectures PR #5513
added the asymptotic quantifier `∃ N : ℕ, ∀ n ≥ N`; no code from that
repository is imported or adapted here. This package formalizes the general
Clemen–Dumitrescu–Liu construction for every $n \ge 4$ and resolves the
quantified Formal Conjectures statement on Lean `v4.35.0-rc2`.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution. Both `./verify.sh` and `lake env lake comparator --config comparator.json` pass, with both `nanoda_bin` and Lean's default kernel accepting `Solution`.
