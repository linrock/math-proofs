# Erdős Problem 726 (`erdos-726`)

Standalone Lean 4 (`leanprover/lean4:v4.35.0-rc2`) formalization package for [Erdős Problem 726](https://www.erdosproblems.com/726) (Erdős–Graham–Ruzsa–Straus 1975, *Math. Comp.* 29, 83–92) on the asymptotic behavior of the upper-half prime-residue reciprocal sum
$$\sum_{p \le n,\; p/2 < n \bmod p} \frac{1}{p} \sim \frac{\log\log n}{2}.$$

## Main Verified Results (`Erdos726`)

- **Unconditional Mertens Estimate and Harmonic Quotient Windows (`Erdos726Unified435.lean`):**
  - `variants.mertens_estimate`: unconditionally proves the `FormalConjectures.ErdosProblems.726` solved variant $\sum_{p \le n} 1/p \sim \log\log n$ from the second Mertens theorem.
  - `upperHalfPrimeSum_cutoff_decomposition` and `quotient_window_discrepancy_sandwich`: partition the prime reciprocal sum at any quotient cutoff $K$ into a small-prime tail ($\lfloor n/p \rfloor \ge K+1$) and $K$ disjoint harmonic quotient windows $k = \lfloor n/p \rfloor \in [1, K]$, and establish bilateral prime-counting bounds on each window discrepancy $u_k(n) - \ell_k(n)$.
- **Small-Prime Tail Modular Reflection, Trapezoidal Abel Summation-by-Parts, and PNT Remainder Scale Cancellation (`SmallPrimeTailReflectionDiscrepancy726.lean`, `AbelSummationPrimeCountVariation726.lean`, `LogDensityTrapezoidalDefectDecomposition726.lean`):**
  - `abs_smallPrimeTail_discrepancy_le_of_modular_reflection` and `sum_window_midpoint_quadrature_defect_bounds`: bound the reflected small-prime tail discrepancy for odd primorial multiples $M$ and the cumulative midpoint-quadrature defect across $1 \le k \le K$ by $(\pi(n) - \pi(\lfloor n/(K+1) \rfloor))/(2n)$.
  - `sum_midpointWindowApprox_eq_trapezoidal_abel` and `sum_abs_abel_pnt_variation_le_of_linear_scale_remainder`: establish the trapezoidal summation-by-parts identity for the midpoint-weighted prime-count second differences and prove that under a relative prime-number-theorem remainder bound $|R(m)| \le \delta m$ ($m \le n$), the growing window weights $2k+1$, $k+1$, and $k$ cancel against $\lfloor (2n-1)/(2k+1) \rfloor$, $\lfloor n/(k+1) \rfloor$, and $\lfloor n/k \rfloor$ to bound the cumulative variation by $4K\delta$.
  - `floorTrapezoidalDefect_bilateral_and_abs_bounds` and `approxTrapezoidalDefect_logDensity_div_decompositions`: prove the sharp bounds $-(2k+1) \le \text{floorTrapezoidalDefect}(n, k) \le 2k - 2$ and $|\text{floorTrapezoidalDefect}(n, k)| \le 2k + 1$, and separate the logarithmic-density main-term trapezoidal defect into floor-discretization defects, reciprocal-logarithm second differences, and remainder coupling terms.
- **Floor-Quotient Multiplication Sandwich, Reciprocal-Logarithm Bounds, and Conditional Asymptotic Reductions for `erdos_726` (`Blueprint726.lean`):**
  - `div_succ_mul_succ_le_and_le_div_succ_mul_add_two`, `real_log_sub_log_div_succ_sandwich`, `inv_log_div_succ_sub_inv_log_sandwich`, `sum_abs_logDensity_trapezoidalDefect_div_le_log_add_two`, and `abs_sum_upperQuotientSum_sub_half_fiberSum_le_log_add_two`: prove the bilateral floor-quotient sandwich $\lfloor n/(K+1) \rfloor (K+1) \le n \le \lfloor n/(K+1) \rfloor (K+2)$ whenever $K + 1 \le \lfloor n/(K+1) \rfloor$, deduce $\log(K+1) \le \log n - \log\lfloor n/(K+1) \rfloor \le \log(K+2)$ and
    $$\frac{\log(K+1)}{\log\lfloor n/(K+1) \rfloor \cdot \log n} \le \frac{1}{\log\lfloor n/(K+1) \rfloor} - \frac{1}{\log n} \le \frac{\log(K+2)}{\log\lfloor n/(K+1) \rfloor \cdot \log n},$$
    and bound both the cumulative logarithmic-density trapezoidal defect and the deviation of $\sum_{k=1}^K u_k(n)$ from half the large-prime fiber sum.
  - `asymptotic_iff_discrepancy_isLittleO`, `iff_smallPrimeTail_of_log_add_two_bounds`, `of_smallPrimeTail_and_log_add_two_bounds`, and `of_modular_reflection_and_log_add_two_bounds`: unconditionally discharge the Mertens constant and error $(M + E_{2,p}(n))/\log\log n \to 0$ to prove that `Erdos726` holds if and only if $\text{upperHalfPrimeSum}(n) - \text{lowerComplementPrimeSum}(n) = o(\log\log n)$, and establish conditional asymptotic equivalence and top-down reductions to $o(\log\log n)$ small-prime tail discrepancy and modular period reflection.

## Scope

`variants.mertens_estimate` formalizes the classical second Mertens theorem, following the PrimeNumberTheoremAnd development of Leo Goldmakher's proof; it is not a new mathematical discovery. The other main results are new conditional reductions and do not resolve `erdos_726`, which remains open.
