# Erdős #2: minimum modulus of distinct covering systems

This standalone Lean 4 project gives a complete formal proof of the negative
answer to [Erdős problem #2](https://www.erdosproblems.com/2). A **covering
system** of the integers is a finite collection of congruence classes
$z \equiv r_i \pmod{m_i}$ whose union covers all of $\mathbb{Z}$, and a
covering system is **strict** (or **distinct**) if its moduli
$1 < m_1 < m_2 < \dots < m_k$ are pairwise distinct. In 1950, Erdős asked
whether the minimum modulus $m_1$ of a finite distinct covering system can be
arbitrarily large.

The answer is **no**: there is an absolute constant $B \in \mathbb{N}$ such
that every finite covering of $\mathbb{Z}$ by distinct moduli $> 1$ contains a
modulus $m_i \le B$.

Bob Hough ([*Solution of the minimum modulus problem for covering systems*, Annals of Mathematics 181 (2015), 361–382](https://doi.org/10.4007/annals.2015.181.1.6))
first resolved Erdős's problem in the negative with $B = 10^{16}$, and Paul
Balister, Béla Bollobás, Robert Morris, Julian Sahasrabudhe, and Marius Tiba
([*On the Erdős Covering Problem: the density of the uncovered set*, Inventiones Mathematicae 228 (2022), 377–414; arXiv:1811.03547](https://arxiv.org/abs/1811.03547))
gave a streamlined proof via a recursive probability sieve with $B = 616000$.
This formalization follows the BBMST probability-sieve method in Lean
`v4.35.0-rc2`, using a fixed half-cap fiber distortion and qualitative summable
tails to establish the uniform existence of $B$ across all finite index types
and signed integer residues.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) exports four proved theorems matched by
[Challenge.lean](Challenge.lean) and [comparator.json](comparator.json):

| Declaration in `Erdos2.Standalone` | Meaning |
| --- | --- |
| `erdos_2` | The literal Formal Conjectures ideal statement (`False ↔ ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ...`). |
| `not_arbitrarilyLarge_ideal_coverings` | Direct disproof of strict ideal covering systems of `ℤ` with arbitrarily large minimum modulus. |
| `minimum_modulus_bound` | Uniform numerical bound: there exists $B \in \mathbb{N}$ such that every finite covering of $\mathbb{Z}$ by distinct positive moduli $m : \iota \to \mathbb{N}$ and signed residues $r : \iota \to \mathbb{Z}$ has some $m_i \le B$. |
| `finite_noncoverage_bound` | Uniform finite-set noncoverage: there exists $B \in \mathbb{N}$ such that for every finite set $D \subset \mathbb{N}$ with $\min D > B$ and every residue assignment $r : \mathbb{N} \to \mathbb{Z}$, some $z \in \mathbb{Z}$ satisfies $z \not\equiv r(d) \pmod{d}$ for all $d \in D$. |

The Formal Conjectures theorem statement is:

```lean
False ↔
  ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
    c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m
```

[Challenge.lean](Challenge.lean) states these four targets using only Mathlib
and intentional `sorry` placeholders; `Solution.lean` never imports
`Challenge.lean`. [Statement.lean](Statement.lean) records the Formal
Conjectures proposition `Erdos2.Challenge.statement` with no placeholder, and
[AxiomAudit.lean](AxiomAudit.lean) verifies definitional statement fidelity,
a single-modulus non-vacuity check (`nonvacuity_single_modulus`), and the
transitive axioms (`propext`, `Classical.choice`, `Quot.sound`) of all exported
theorems.

## Mathematical idea and module outline

Given a finite set $D$ of positive moduli all exceeding $B$, let
$N = \operatorname{lcm}(D) > 0$. By the Chinese Remainder Theorem and surjectivity
of $\mathbb{Z} \to \mathbb{Z}/N\mathbb{Z}$, the congruences $z \equiv r(d) \pmod{d}$
cover $\mathbb{Z}$ if and only if their projections cover $\mathbb{Z}/N\mathbb{Z}$.
To show that $\mathbb{Z}/N\mathbb{Z}$ is not covered when $B$ is large, the
BBMST sieve constructs a probability distribution $w$ on $\mathbb{Z}/N\mathbb{Z}$
prime by prime so that the total $w$-mass of the covered set remains strictly
below $1$:

1. **Base stage on $A$-smooth moduli**
   ([SmoothTail2](Proofs/SmoothTail2.lean),
   [UniformResidue2](Proofs/UniformResidue2.lean),
   [SieveBase2](Proofs/SieveBase2.lean),
   [FiniteLcm2](Proofs/FiniteLcm2.lean)): for a fixed prime cutoff $A$, the
   series $\sum_{P^+(d) \le A} 1/d$ of reciprocals of $A$-smooth numbers
   converges by Euler's product formula. Choosing $B = M$ large enough ensures
   that the uniform distribution on the $A$-smooth part of $N$ assigns mass
   $< 1/4$ to all moduli $d \in D$ whose prime factors are $\le A$, while
   satisfying the progression-mass bound $w(z \equiv a \pmod d) = 1/d \le 2^{\omega(d)}/d$.
2. **Half-cap fiber distortion and progression invariant**
   ([FiberUpdate2](Proofs/FiberUpdate2.lean),
   [ProductUpdate2](Proofs/ProductUpdate2.lean),
   [FiniteWeight2](Proofs/FiniteWeight2.lean),
   [SieveStep2](Proofs/SieveStep2.lean),
   [ProgressionArithmetic2](Proofs/ProgressionArithmetic2.lean),
   [CongruenceGeometry2](Proofs/CongruenceGeometry2.lean),
   [CoveringModel2](Proofs/CoveringModel2.lean),
   [ProgressionUpdate2](Proofs/ProgressionUpdate2.lean)): when adjoining the
   largest prime power $p^\gamma \parallel N$ with $p > A$ and $N = Q p^\gamma$,
   we identify $\mathbb{Z}/N\mathbb{Z} \cong \mathbb{Z}/Q\mathbb{Z} \times \mathbb{Z}/p^\gamma\mathbb{Z}$.
   Above each $x \in \mathbb{Z}/Q\mathbb{Z}$, let $B(x) \subseteq \mathbb{Z}/p^\gamma\mathbb{Z}$
   be the fiber of residues covered by moduli $m p^j \in D$ ($m \mid Q$, $1 \le j \le \gamma$)
   whose $\bmod\, m$ condition holds at $x$, and let $\alpha(x) = |B(x)| / p^\gamma$.
   The BBMST half-cap update sets the fiber weight on $B(x)$ to $0$ when
   $\alpha(x) \le 1/2$ and caps the relative boost on $\mathbb{Z}/p^\gamma\mathbb{Z} \setminus B(x)$
   at $2$ when $\alpha(x) > 1/2$. This preserves all cylinder masses on
   $\mathbb{Z}/Q\mathbb{Z}$, multiplies the mass of any congruence class involving
   $p^j$ ($j \ge 1$) by at most $2 / p^j$ (preserving the inductive invariant
   $w(z \equiv a \pmod d) \le 2^{\omega(d)}/d$ for all $d \mid Q p^\gamma$), and
   bounds the newly leaked covered mass by the second moment
   $\sum_{x \in \mathbb{Z}/Q\mathbb{Z}} w(x) \alpha(x)^2$.
3. **Rectangle second-moment expansion and Euler factorization**
   ([FractionRectangle2](Proofs/FractionRectangle2.lean),
   [MomentBound2](Proofs/MomentBound2.lean),
   [RectangleMoment2](Proofs/RectangleMoment2.lean),
   [RectangleCoefficient2](Proofs/RectangleCoefficient2.lean),
   [NaturalDivisorModel2](Proofs/NaturalDivisorModel2.lean),
   [EulerMoment2](Proofs/EulerMoment2.lean),
   [DivisorEulerBound2](Proofs/DivisorEulerBound2.lean),
   [LateMoment2](Proofs/LateMoment2.lean)): expanding $\alpha(x)^2$ over pairs
   of divisors $m_1, m_2 \mid Q$ and exponents $j_1, j_2 \ge 1$ bounds the
   second moment by
   $$\frac{1}{(p - 1)^2} \sum_{m_1 \mid Q} \sum_{m_2 \mid Q} \frac{2^{\omega(\operatorname{lcm}(m_1, m_2))}}{\operatorname{lcm}(m_1, m_2)} \le \frac{1}{(p - 1)^2} \prod_{q \mid Q} \left(1 + \frac{2(3q - 1)}{(q - 1)^2}\right).$$
4. **Mertens' third theorem, recursive assembly, and statement adapters**
   ([AnalyticTail2](Proofs/AnalyticTail2.lean),
   [MertensUpper2](Proofs/MertensUpper2.lean),
   [TailChoice2](Proofs/TailChoice2.lean),
   [StripPrime2](Proofs/StripPrime2.lean),
   [SieveStage2](Proofs/SieveStage2.lean),
   [SieveRecursion2](Proofs/SieveRecursion2.lean),
   [ResidueLift2](Proofs/ResidueLift2.lean),
   [FiniteIndexAdapter2](Proofs/FiniteIndexAdapter2.lean),
   [CoveringSystem2](Proofs/CoveringSystem2.lean),
   [StatementAdapter2](Proofs/StatementAdapter2.lean),
   [NoncoverageCapstone2](Proofs/NoncoverageCapstone2.lean)): using
   $1 + 2(3q - 1)/(q - 1)^2 \le (q / (q - 1))^6$ and Mertens' third theorem
   $\prod_{q \le p} (1 - 1/q)^{-1} = O(\log p)$ (supplied by the vendored
   [EulerMaclaurin](Proofs/PrimeNumberTheoremAnd/EulerMaclaurin.lean) and
   [Mertens](Proofs/PrimeNumberTheoremAnd/IEANTN/Mertens.lean) modules), the
   Euler product over $q < p$ is bounded by $C (\log p)^6$. Since
   $\sum_p C (\log p)^6 / (p - 1)^2 < \infty$, choosing $A$ large enough bounds
   the sum of late-prime losses over all $p > A$ by $1/4$. By strong induction
   stripping the largest prime factor of $N$, the final covered mass is
   $< 1/4 + 1/4 = 1/2 < 1$, leaving an uncovered residue in $\mathbb{Z}/N\mathbb{Z}$
   and hence an uncovered integer $z \in \mathbb{Z}$.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and
[THIRD_PARTY.md](THIRD_PARTY.md) for source attribution. Both `./verify.sh`
and `lake env lake comparator --config comparator.json` pass, with both
`nanoda_bin` and Lean's default kernel accepting `Solution`.
