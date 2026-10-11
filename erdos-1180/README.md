# Erdős 1180: representing residues as sums of modular inverses with small denominators

This standalone Lean 4 project gives complete formal proofs for [Erdős problem #1180](https://www.erdosproblems.com/1180) and its quantitative variants on representing every residue modulo a prime $p$ as a sum of modular inverses with small denominators.

Erdős and Graham (1980) asked whether, for every $\varepsilon > 0$, there exists a constant $C(\varepsilon)$ such that for every prime $p$, every residue $a \in \mathbb{Z}/p\mathbb{Z}$ is the sum of at most $C(\varepsilon)$ elements of
$$\{n^{-1} \pmod p : 1 \le n \le p^\varepsilon,\; \gcd(n, p) = 1\}.$$

The answer is **yes**. Shparlinski (2002) proved that $O(\varepsilon^{-3})$ summands suffice for all sufficiently large primes $p \ge P(\varepsilon)$, and Glibichuk (2006) improved the large-prime bound to $O(\varepsilon^{-2})$ via an 8-fold bilinear sum-product covering theorem over $\mathbb{Z}/p\mathbb{Z}$.

When stating quantitative bounds, it is essential to distinguish two constants:

- **The large-prime threshold constant $C_{\mathrm{asymp}}(\varepsilon)$** (`CAsymptotic ε`), the least bound valid for all sufficiently large primes $p \ge P(\varepsilon)$, which satisfies the two-sided polynomial sandwich
  $$\frac{1}{\varepsilon} \le \left\lceil \frac{1}{\varepsilon} \right\rceil \le C_{\mathrm{asymp}}(\varepsilon) \le 8\left(\left\lfloor \frac{1}{\varepsilon} \right\rfloor + 1\right)^2 = (8 + o(1))\varepsilon^{-2}.$$
- **The unthresholded all-primes constant $C(\varepsilon)$** (`C ε`), the least bound valid for *every* prime $p \ge 2$. Whenever $p^\varepsilon < 2$, the only admissible denominator is $n = 1$, so representing $p - 1 \pmod p$ requires $p - 1$ summands; Bertrand's postulate then forces the exponential lower bound
  $$2^{1/\varepsilon} \le 4 C(\varepsilon),$$
  which disproves the unthresholded all-primes formulation of `erdos_1180.variants.optimal` ($C(\varepsilon) \le \varepsilon^{-1-o(1)}$) while leaving the large-prime optimality question $C_{\mathrm{asymp}}(\varepsilon) \le \varepsilon^{-1-o(1)}$ open.

## Scope and main results

[Solution.lean](Solution.lean) exports 17 unconditional theorems in `Erdos1180.Palomar` (matched by [Challenge.lean](Challenge.lean) and [comparator.json](comparator.json)) along with the 6 literal `FormalConjectures` declarations in `Erdos1180` across 3 self-contained proof modules in [Proofs/](Proofs), using only the standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem in `Solution.lean` | Mathematical statement |
| --- | --- |
| `Erdos1180.Palomar.erdos_1180` | **Erdős #1180 (existence for all primes).** For every $\varepsilon > 0$, there exists $C$ such that for every prime $p$ and residue $a \in \mathbb{Z}/p\mathbb{Z}$, some multiset $s$ with $|s| \le C$ satisfies `Represents ε p a s`. |
| `Erdos1180.Palomar.erdos_1180_variants_glibichuk` | **Glibichuk's $O(\varepsilon^{-2})$ large-prime theorem (`variants.glibichuk`).** Proves the uniform bound with $K = 32$ on $(0, 1]$. |
| `Erdos1180.Palomar.erdos_1180_variants_shparlinski` | **Shparlinski's $O(\varepsilon^{-3})$ large-prime theorem (`variants.shparlinski`).** |
| `Erdos1180.Palomar.erdos_1180_variants_lower_bound` | **Unconditional $\Omega(\varepsilon^{-1})$ lower bound on $C(\varepsilon)$ (`variants.lower_bound`).** Proves $\exists K > 0,\; \forall \varepsilon \in (0, 1],\; K \varepsilon^{-1} \le C(\varepsilon)$. |
| `Erdos1180.Palomar.erdos_1180_variants_lower_bound_large_primes` | **Thresholded large-prime $\Omega(\varepsilon^{-1})$ lower bound (PR #6951).** For all $\varepsilon \in (0, 1]$ and primes $p \ge P(\varepsilon)$, some residue requires $\ge \frac{1}{2}\varepsilon^{-1}$ summands. |
| `Erdos1180.Palomar.not_erdos_1180_variants_optimal` | **Disproof of unthresholded `variants.optimal`.** Refutes $C(\varepsilon) \le \varepsilon^{-1-o(1)}$ for the all-primes constant $C(\varepsilon)$. |
| `Erdos1180.Palomar.two_rpow_inv_le_four_mul_C` | **Small-prime exponential lower bound.** Proves $2^{1/\varepsilon} \le 4 C(\varepsilon)$ for all $\varepsilon > 0$. |
| `Erdos1180.Palomar.inv_le_CAsymptotic` | **Large-prime pigeonhole reciprocal lower bound.** Proves $\varepsilon^{-1} \le C_{\mathrm{asymp}}(\varepsilon)$ for all $\varepsilon > 0$. |
| `Erdos1180.Palomar.natCeil_inv_le_CAsymptotic` | **Large-prime discrete ceiling lower bound.** Proves $\lceil \varepsilon^{-1} \rceil \le C_{\mathrm{asymp}}(\varepsilon)$ for all $\varepsilon > 0$. |
| `Erdos1180.Palomar.CAsymptotic_le_thirty_two_mul_inv_sq` | **Uniform Glibichuk bound on $(0, 1]$.** Proves $C_{\mathrm{asymp}}(\varepsilon) \le 32 \varepsilon^{-2}$ for all $0 < \varepsilon \le 1$. |
| `Erdos1180.Palomar.CAsymptotic_le_eight_mul_sq_of_one_lt_mul` | **Symmetric prime-block bound.** Proves $C_{\mathrm{asymp}}(\varepsilon) \le 8 k^2$ whenever $k \ge 1$ and $k \varepsilon > 1$. |
| `Erdos1180.Palomar.CAsymptotic_le_eight_mul_succ_of_two_lt_mul` | **Asymmetric $(k, k + 1)$ staircase bound.** Proves $C_{\mathrm{asymp}}(\varepsilon) \le 8 k (k + 1)$ whenever $k \ge 1$ and $(2k + 1)\varepsilon > 2$. |
| `Erdos1180.Palomar.CAsymptotic_le_eight_mul_of_lt_mul` | **Asymmetric $(1, k)$ linear staircase bound.** Proves $C_{\mathrm{asymp}}(\varepsilon) \le 8 k$ whenever $k \ge 1$ and $(2k - 1)\varepsilon > k$. |
| `Erdos1180.Palomar.CAsymptotic_le_sixteen_of_two_thirds_lt` | **Sub-32 bound on $(2/3, \infty)$.** Proves $C_{\mathrm{asymp}}(\varepsilon) \le 16$ for all $\varepsilon > 2/3$. |
| `Erdos1180.Palomar.CAsymptotic_le_eight_mul_floor_inv_add_one_sq` | **Discrete all-$\varepsilon$ Glibichuk bound.** Proves $C_{\mathrm{asymp}}(\varepsilon) \le 8(\lfloor \varepsilon^{-1} \rfloor + 1)^2$ for all $\varepsilon > 0$. |
| `Erdos1180.Palomar.eventually_CAsymptotic_le_eight_add_mul_inv_sq` | **Sharp asymptotic $(8 + o(1))\varepsilon^{-2}$ bound.** For every $\eta > 0$, eventually as $\varepsilon \to 0^+$, $C_{\mathrm{asymp}}(\varepsilon) \le (8 + \eta)\varepsilon^{-2}$. |
| `Erdos1180.Palomar.CAsymptotic_inv_nat_lt_C_inv_nat` | **Strict separation between $C_{\mathrm{asymp}}$ and $C$.** Proves $C_{\mathrm{asymp}}(1/n) < C(1/n)$ for all $n \ge 15$. |

[Statement.lean](Statement.lean) records the benchmark statement without placeholders, and [AxiomAudit.lean](AxiomAudit.lean) verifies statement fidelity, non-vacuity witnesses, and the transitive axioms of every exported endpoint.

## Proof modules

- [ModularInverseThresholds1180.lean](Proofs/ModularInverseThresholds1180.lean): Formalizes modular inverse representations (`Represents`, `C`, `CAsymptotic`), proves the small-prime exponential lower bound $2^{1/\varepsilon} \le 4 C(\varepsilon)$, establishes the finite-prime pigeonhole power bound $p \le (\lfloor p^\varepsilon \rfloor + 1)^B$, and evaluates $C_{\mathrm{asymp}}(\varepsilon) = 1$ for $\varepsilon \ge 1$.
- [GlibichukBilinearCover1180.lean](Proofs/GlibichukBilinearCover1180.lean): Formalizes Glibichuk's 8-fold bilinear covering theorem over `ZMod p` via additive energy (`Finset.addEnergy`) and Cauchy–Davenport, constructs prime-reciprocal fraction sets by induction on the block count (`IsFracStage`), proves the master asymmetric two-block bound $C_{\mathrm{asymp}}(\varepsilon) \le 8 k_1 k_2$ along with $8k^2$, $8k(k+1)$, $8k$, $8(\lfloor \varepsilon^{-1} \rfloor + 1)^2$, $(8 + \eta)\varepsilon^{-2}$, and $32 \varepsilon^{-2}$, resolves `erdos_1180`, `glibichuk`, `shparlinski`, and `lower_bound`, and disproves the unthresholded `Erdos1180OptimalConjecture`.
- [PigeonholeAndAsymptoticOptimality1180.lean](Proofs/PigeonholeAndAsymptoticOptimality1180.lean): Proves the large-prime pigeonhole lower bounds $\varepsilon^{-1} \le \lceil \varepsilon^{-1} \rceil \le C_{\mathrm{asymp}}(\varepsilon)$, the thresholded large-prime `lower_bound` (with $K = 1/2$), the exact characterization $C_{\mathrm{asymp}}(\varepsilon) = 1 \iff 1 \le \varepsilon$, and the strict separation $C_{\mathrm{asymp}}(1/n) < C(1/n)$ for $n \ge 15$.

## Build and verification

See [BUILD.md](BUILD.md) for reproduction commands and [THIRD_PARTY.md](THIRD_PARTY.md) for source attribution and license information. Running `./verify.sh --no-sandbox` builds all targets from source, audits transitive axioms, and runs `lake comparator` so both `nanoda_bin` and Lean's default kernel check `Solution` against `Challenge`.
