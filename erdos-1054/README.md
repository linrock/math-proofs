# Erdős #1054: sums of smallest divisors

This standalone Lean 4 project gives a complete, unconditional formal proof of
all three parts of [Erdős problem #1054](https://www.erdosproblems.com/1054),
together with sharp quantitative lower-density bounds for large ratios,
Tao–Kovač small-ratio upper bounds, and a two-way aliquot range density
equivalence.

For a positive integer $n$, let $f(n)$ be the least integer $m \ge 1$ such that
$n$ can be written as the sum of the $k$ smallest positive divisors of $m$ for
some $k \ge 1$ (and $f(n) = 0$ if no such $m$ exists). Erdős asked three
questions about the growth of $f(n)$ relative to $n$:

1. **Part (i) (`answer_i` / `official_answer_i`)**: Is $f(n) = o(n)$?
   **No.**
2. **Part (ii) (`answer_ii` / `official_answer_ii` / `littleO_on_subtype_imp_represented_density_zero`)**:
   Is $f(n) = o(n)$ for almost all $n$ (i.e. along some subset $S \subseteq \mathbb{N}$
   of natural density $1$)?
   **No.** In fact, along *any* subset $S \subseteq \mathbb{N}$ on whose subtype
   $f(n) = o(n)$ holds, the represented members $\{n \in S : 0 < f(n)\}$ have
   natural density zero.
3. **Part (iii) (`answer_iii` / `official_answer_iii` / `limsup_on_every_density_one` / `odd_subtype_limsup`)**:
   Is $\limsup_{n \to \infty} f(n)/n = \infty$?
   **Yes**, both globally and when restricted to the subtype of *every*
   natural-density-one set $S \subseteq \mathbb{N}$ (or any set $S$ retaining
   relative density $1$ among the odd integers).

More strongly, the formalization proves the **sharp second-moment quantitative
lower-density bound** (`quantitative_odd_sharp_second_moment_logarithmic_endpoint`):
there is a single absolute constant $c > 0$ such that for every real threshold
$A \ge 1$ and every set $S \subseteq \mathbb{N}$ omitting only density-zero many
odd integers (`HasOddDensityOne S`),

$$\underline{d}\bigl(\{n \in S : n \text{ odd and } A n < f(n)\}\bigr) \ge \frac{c}{A^3 (1 + \log A)^4}.$$

Consequently, for every fixed $\varepsilon > 0$ (`quantitative_odd_almost_full_three_plus_epsilon`),

$$\underline{d}\bigl(\{n \in S : n \text{ odd and } A n < f(n)\}\bigr) \ge \frac{c_\varepsilon}{A^{3 + \varepsilon}},$$

and a fixed-exponent ($\beta = 1/2$) evaluation yields the logarithm-free
polynomial bound $c / A^6$ (`quantitative_odd_pure_power_six`).

In the opposite (small-ratio) regime, the package proves unconditionally:

- **Divisibility-preserving Tao–Kovač small-ratio bound (`small_ratio_count_le_cubic`, `small_ratio_upper_density_le_cubic`)**:
  There is an absolute constant $C > 0$ such that for every $\delta > 0$ and
  $X \ge 1$,
  $$\#\{n \le X : 0 < f(n) \le \delta n\} \le C \delta^3 X, \qquad \overline{d}\bigl(\{n : 0 < f(n) \le \delta n\}\bigr) \le C \delta^3.$$
  This directly implies `littleO_on_subtype_imp_represented_density_zero` without
  invoking the binary Goldbach circle method.
- **Unconditional zero liminf on represented integers (`f_sigma_le`, `frequently_represented_small_ratio`)**:
  Every divisor sum $\sigma(n)$ ($n \ge 1$) is represented with
  $0 < f(\sigma(n)) \le n$, and because $\sigma(n)/n$ is unbounded, for every
  $\varepsilon > 0$ there are arbitrarily large represented integers $N$ with
  $0 < f(N) < \varepsilon N$ (so $\liminf_{N \to \infty,\, f(N)>0} f(N)/N = 0$).
- **Two-way cofactor-two aliquot range density equivalence (`cofactor_two_lower_density_eq_even_aliquot`, `cofactor_two_upper_density_eq_even_aliquot`)**:
  For $m = 2d$, the sum of divisors of $2d$ at most $d$ is the classical aliquot
  sum $s(2d) = \sum_{q \mid 2d,\, q < 2d} q$. The cofactor-two range
  $\mathcal{R}_2 = \{s(2d) : d \ge 1\}$ and the classical set of even aliquot
  values $\mathcal{E}_s = \{N \text{ even} : \exists m \ge 1,\ N = s(m)\}$
  differ by $o(X)$ elements up to $X$, so $\underline{d}(\mathcal{R}_2) = \underline{d}(\mathcal{E}_s)$
  and $\overline{d}(\mathcal{R}_2) = \overline{d}(\mathcal{E}_s)$.

## Statements and proof entrypoints

[Solution.lean](Solution.lean) exports 21 unconditional theorems in
`Erdos1054.Palomar`, matched by [Challenge.lean](Challenge.lean) and
[comparator.json](comparator.json):

| Declaration in `Erdos1054.Palomar` | Meaning |
| --- | --- |
| `answer_i`, `official_answer_i` | Part (i): $f(n)$ is not $o(n)$ (both direct negation and `False ↔` form). |
| `answer_ii`, `official_answer_ii` | Part (ii): $f(n)$ is not $o(n)$ on the subtype of any natural-density-one set $S$ (both direct negation and `False ↔` form). |
| `answer_iii`, `official_answer_iii` | Part (iii): $\limsup_{n \to \infty} f(n)/n = \infty$ (both direct and `True ↔` form). |
| `limsup_on_every_density_one` | Stronger Part (iii): $\limsup_{n \in S} f(n)/n = \infty$ on the subtype of *every* natural-density-one set $S$. |
| `odd_subtype_limsup` | Odd-subtype strengthening: $\limsup f(n)/n = \infty$ on $\{n \in S : n \text{ odd}\}$ for every `HasOddDensityOne` set $S$. |
| `f_undefined_at_2`, `f_undefined_at_5` | Non-vacuity base checks: $2$ and $5$ have no divisor-prefix representation ($f(2) = f(5) = 0$). |
| `quantitative_odd_sharp_second_moment_logarithmic_endpoint` | Uniform lower density $\underline{d}(\{n \in S : n \text{ odd},\ A n < f(n)\}) \ge c / [A^3 (1 + \log A)^4]$ for all `HasOddDensityOne S` and $A \ge 1$. |
| `quantitative_odd_sharp_second_moment_logarithmic_endpoint_eventual_count` | Explicit finite-count form $\#\{n \le X : n \in S,\ n \text{ odd},\ A n < f(n)\} \ge \frac{c}{A^3 (1 + \log A)^4} X$ for $X \ge X_0$. |
| `quantitative_odd_almost_full_three_plus_epsilon` | Uniform lower density $\ge c_\varepsilon / A^{3+\varepsilon}$ for every $\varepsilon > 0$. |
| `quantitative_odd_pure_power_six` | Logarithm-free polynomial lower density $\ge c / A^6$. |
| `small_ratio_count_le_cubic` | Divisibility-preserving Tao–Kovač small-ratio bound $\#\{n \le X : 0 < f(n) \le \delta n\} \le C \delta^3 X$. |
| `small_ratio_upper_density_le_cubic` | Upper-density bound $\overline{d}(\{n : 0 < f(n) \le \delta n\}) \le C \delta^3$. |
| `littleO_on_subtype_imp_represented_density_zero` | Goldbach-free strong refutation: if $f|_S(n) = o(n)$ on $S \subseteq \mathbb{N}$, then $\{n \in S : 0 < f(n)\}$ has natural density zero. |
| `f_sigma_le` | Divisor-sum witness bound: $0 < f(\sigma(n)) \le n$ for every $n \ge 1$. |
| `frequently_represented_small_ratio` | Zero liminf on represented integers: for every $\varepsilon > 0$ and $B \in \mathbb{N}$, some $N \ge B$ satisfies $0 < f(N) < \varepsilon N$. |
| `cofactor_two_lower_density_eq_even_aliquot` | Lower-density equality $\underline{d}(\{s(2d) : d > 0\}) = \underline{d}(\{N \text{ even} : \exists m > 0,\ N = s(m)\})$. |
| `cofactor_two_upper_density_eq_even_aliquot` | Upper-density equality $\overline{d}(\{s(2d) : d > 0\}) = \overline{d}(\{N \text{ even} : \exists m > 0,\ N = s(m)\})$. |

[Challenge.lean](Challenge.lean) states these 21 targets using only Mathlib and
intentional `sorry` placeholders; `Solution.lean` never imports
`Challenge.lean`. [Statement.lean](Statement.lean) records the literal Formal
Conjectures propositions `statement_i`, `statement_ii`, and `statement_iii` with
no placeholder, and [AxiomAudit.lean](AxiomAudit.lean) verifies definitional
statement fidelity and checks that all 24 endpoint and fidelity declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical idea and module outline

Any divisor-prefix sum of $m$ ending at a divisor $d \mid m$ with cofactor
$e = m / d$ can be written by complementary-divisor reflection as

$$F(e, d) = \sum_{\substack{q \mid e d \\ q \le d}} q = e d \sum_{\substack{r \mid e d \\ r \ge e}} \frac{1}{r} = m \, g(e, m), \qquad g(e, m) = \sum_{\substack{r \mid m \\ r \ge e}} \frac{1}{r}.$$

Thus $m / F(e, d) = 1 / g(e, m)$. To show that a positive lower density of odd
integers $N$ have $f(N) > A N$, we must ensure simultaneously that (a) $N$ is
represented by some divisor prefix, (b) $N \ne F(e, d)$ for all small cofactors
$1 \le e \le E$, and (c) $N$ is not represented by any large cofactor $e > E$
with $m = e d \le A N$ (which forces $g(e, m) \ge 1 / A$).

The 47 modules in [Proofs/](Proofs) organize the proof into six components:

1. **Divisor-prefix reflection, small-cofactor sieve, and 7-variable decomposition**
   ([Erdos1054Conditional](Proofs/Erdos1054Conditional.lean),
   [Integration1054](Proofs/Integration1054.lean),
   [OriginalNth1054](Proofs/OriginalNth1054.lean),
   [StatementAudit1054](Proofs/StatementAudit1054.lean)):
   proves the reflection identity $F(e, d) = e d \, g(e, e d)$, shows that for
   each fixed $(e, R)$ with $R \subseteq [1, e)$ the reduced numerator $q_{e, R}$
   of $e \sum_{r \in R} 1/r$ divides $\sigma(e d) = F(1, e d)$ whenever $R$ is
   the set of divisors of $e d$ below $e$, and uses the divergence of
   $\sum_{p \equiv -1 \pmod q} 1/p$ to prove that almost all $d$ satisfy
   $q \mid \sigma(e d)$. Sifting $N$ to be coprime to the even modulus
   $Q_E = 2 \prod_{e \le E,\, R} p_{\min}(q_{e, R})$ therefore excludes all
   small-cofactor representations $N = F(e, d)$ ($1 \le e \le E$) outside a set
   of density zero. Also proves exact equivalence between the sorted-list `sInf`
   definition and the zero-padded `Nat.nth`/`Nat.find` definition at every
   $n \in \mathbb{N}$.
2. **Unconditional almost-all binary Goldbach theorem**
   ([GoldbachSW1](Proofs/GoldbachSW1.lean),
   [GoldbachSW2](Proofs/GoldbachSW2.lean),
   [GoldbachSW3](Proofs/GoldbachSW3.lean),
   [GoldbachCircleBase](Proofs/GoldbachCircleBase.lean),
   [GoldbachRatedWindow](Proofs/GoldbachRatedWindow.lean),
   [GoldbachMajorArc](Proofs/GoldbachMajorArc.lean),
   [GoldbachArcTail](Proofs/GoldbachArcTail.lean),
   [GoldbachChainMaster](Proofs/GoldbachChainMaster.lean),
   [Unconditional1054](Proofs/Unconditional1054.lean)):
   for any distinct primes $p < q$, the divisors of $m = p q$ not exceeding $q$
   are $1, p, q$, so $F(p, q) = 1 + p + q$ represents every odd integer $N$ for
   which $N - 1 = p + q$ is a sum of two distinct primes (`F_two_primes`,
   `odd_represented`). The `Goldbach*` modules prove the
   Siegel–Walfisz theorem (via Goldfeld's proof of Siegel's theorem and Perron's
   formula from `PrimeNumberTheoremAnd`) and execute the Hardy–Littlewood major/minor-arc
   variance method to prove unconditionally that almost all even integers are
   sums of two primes (`almost_all_binary_goldbach_proven`), discharging the
   sole analytic input of `Erdos1054Conditional`.
3. **Odd-density retention and relative density-one transfer**
   ([OddTail1054](Proofs/OddTail1054.lean)):
   since $2 \mid Q_E$, every sifted survivor coprime to $Q_E$ is odd. Proves that
   deleting any set of odd integers of natural density zero (`HasOddDensityOne S`)
   changes the count of every odd predicate up to $X$ by $o(X)$, preserving
   both lower and upper asymptotic densities.
4. **Linear sifted-density bound and sharp $c / [A^3 (1 + \log A)^4]$ second moment**
   ([SecondMoment1054](Proofs/SecondMoment1054.lean),
   [SharpSecondMoment1054](Proofs/SharpSecondMoment1054.lean)):
   bounds $\operatorname{lcm}(1, \dots, n) \le 4^n$ so that every prime dividing
   $Q_E$ is at most $E^2 4^E$; Mertens' third theorem then gives the linear
   sifted-density lower bound $\delta_E = \varphi(Q_E)/Q_E \ge c_1 / E$. On the
   upper-bound side, retaining $e \mid m$ in Markov's inequality for
   $g(e, m) \ge 1/A$ bounds the large-cofactor exception count by
   $$\# H_{A, E}(X) \le A^2 \sum_{m \le A X} \sum_{\substack{e \mid m \\ e > E}} g(e, m)^2 \le A^3 U(E) X, \qquad U(E) = \sum_{e > E} \sum_{r, s \ge e} \frac{1}{r s \operatorname{lcm}(e, r, s)}.$$
   In the 7-variable gcd/lcm parametrization $(e, r, s) \mapsto (h, u, v, w, R, S, T)$,
   summing the tail series over the three coprime singleton variables $S, T, R$
   first (via $\sum_{n \ge M} n^{-2} \le 2 M^{-\theta}$ and
   $\sum_{R \ge M} R^{-(2+\beta)} \le 2 M^{-(1+\beta)}$) eliminates three of the
   seven zeta factors and yields
   $$U(E) \le 8 E^{-(1+\beta)} \zeta(2 - \beta)^2 \zeta\!\left(\frac{3 - \beta}{2}\right)^2 \le 8192 (1 + \log A)^4 E^{-(2 - \frac{1}{2(1 + \log A)})}$$
   at $\beta = 1 - \frac{1}{2(1 + \log A)}$. Choosing $E \asymp A^3 (1 + \log A)^4$
   gives the uniform lower density $\ge c / [A^3 (1 + \log A)^4]$.
5. **Tao–Kovač small-ratio upper bound and Goldbach-free refutation of $f(n) = o(n)$**
   ([SmallRatioKovac1054](Proofs/SmallRatioKovac1054.lean)):
   evaluates the divisibility-preserving second moment at $E = 0$: since $U(0) < \infty$,
   truncating $m = e d \le \lfloor \delta X \rfloor$ (contributing one factor of $\delta$)
   and applying Markov's inequality to $g(e, m) \ge 1/\delta$ (contributing $\delta^2$)
   gives $\#\{n \le X : 0 < f(n) \le \delta n\} \le U(0) \delta^3 X$. Taking
   $\delta \to 0$ proves that any subset $S \subseteq \mathbb{N}$ on which
   $f|_S(n) = o(n)$ can contain only density-zero many represented integers.
6. **Small-ratio witnesses and two-way aliquot range equivalence**
   ([Aliquot1054](Proofs/Aliquot1054.lean),
   [CofactorParity1054](Proofs/CofactorParity1054.lean),
   [AliquotEquivalence1054](Proofs/AliquotEquivalence1054.lean)):
   proves $\sigma(n) = F(1, n) \in R$ with $0 < f(\sigma(n)) \le n$ and uses the
   unboundedness of $\sigma(n)/n$ to deduce $\liminf_{f(n)>0} f(n)/n = 0$.
   Characterizes odd values of $s(2d) = F(2, d)$ as $d \in \{s^2, 2s^2\}$
   (count $\le 2(\lfloor\sqrt{X}\rfloor + 1) = o(X)$) and odd preimages of even
   aliquot sums $s(m)$ as odd squares $m = (2k+1)^2$, proving that
   $\mathcal{R}_2 \triangle \mathcal{E}_s$ has density zero and hence
   $\underline{d}(\mathcal{R}_2) = \underline{d}(\mathcal{E}_s)$ and
   $\overline{d}(\mathcal{R}_2) = \overline{d}(\mathcal{E}_s)$.

## Prior work and provenance

The qualitative third-moment divisor-prefix argument, 7-variable gcd/lcm
decomposition, and almost-all binary Goldbach circle-method development are
adapted from the Apache-2.0
[Principia Erdős 1054 development](https://github.com/antoshashakov/Principia-Math-Solutions/tree/c9910942522fbd3a07c034ac57947f56df6f0f6d/erdos1054),
together with attributed Apache-2.0 modules from
[`PrimeNumberTheoremAnd`](https://github.com/ajirving/PrimeNumberTheoremAnd/tree/769d3b81fbff001d9fa7028df0168a8e546cf692)
and
[`LeanArchitect`](https://github.com/hanwenzhu/LeanArchitect/tree/78dd66840d3efe8c824c699fc03381cec817c271).
The problem statements and definitions in `Statement.lean`, `Challenge.lean`,
and `Solution.lean` are adapted from
[`FormalConjectures/ErdosProblems/1054.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1054.lean)
(Apache-2.0).

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and
[THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license details.
Both `./verify.sh` and `lake env lake comparator --config comparator.json` pass,
with both `nanoda_bin` and Lean's default kernel accepting `Solution`.
