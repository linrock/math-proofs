module

public import ScaleAdaptiveColoredEulerAmplification1139
public import ScaleAdaptiveDyadicShellGeometry1139
public import GoalRootPNTLimsup433

@[expose] public section


/-!
# Actual prime-product conductor of the genuine dyadic sampler

An admissible coefficient by itself is not a conductor bound.  The selected
labels are actual primes in integer-floored physical shells, and their
product is the integer charged by the eventual CRT construction.  This file
proves that every finite union of shells strictly above the lower exponent
divides the genuine primorial at the corresponding floored cutoff.  The
already kernel-proved prime number theorem gives the exact normalized cost
of that actual primorial, including its integer rounding.  Consequently the
true shell-union conductor has the advertised vanishing dyadic coefficient.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- Every actual prime in a strictly later physical shell is at most the
genuine integer-floored earlier cutoff. -/
theorem scaleAdaptiveDyadicPrimeShell_subset_cutoff_primes
    (length lower exponent : ℕ) (after : lower < exponent) :
    scaleAdaptiveDyadicPrimeShell length exponent ⊆
      Nat.primesLE (scaleAdaptiveDyadicPhysicalScale length lower) := by
  intro label selected
  obtain ⟨_, upper, prime⟩ :=
    mem_scaleAdaptiveDyadicPrimeShell.mp selected
  exact Nat.mem_primesLE.mpr
    ⟨upper.trans
      (scaleAdaptiveDyadicPhysicalScale_double_le_of_lt length after),
      prime⟩

/-- The complete union of all chosen physical prime-label shells lies in
the ONE actual primorial cutoff, without reusing or enlarging any label. -/
theorem scaleAdaptiveDyadicPrimeShell_biUnion_subset_cutoff_primes
    (length lower : ℕ) (exponents : Finset ℕ)
    (after : ∀ exponent ∈ exponents, lower < exponent) :
    exponents.biUnion (scaleAdaptiveDyadicPrimeShell length) ⊆
      Nat.primesLE (scaleAdaptiveDyadicPhysicalScale length lower) := by
  intro label selected
  obtain ⟨exponent, included, selected⟩ := Finset.mem_biUnion.mp selected
  exact scaleAdaptiveDyadicPrimeShell_subset_cutoff_primes
    length lower exponent (after exponent included) selected

/-- The exact integer product of the genuinely selected prime labels divides
the genuine cutoff primorial.  This is a real CRT conductor comparison, not
a statement merely about a numerical candidate coefficient. -/
theorem scaleAdaptiveDyadicPrimeShell_product_dvd_cutoff_primorial
    (length lower : ℕ) (exponents : Finset ℕ)
    (after : ∀ exponent ∈ exponents, lower < exponent) :
    (∏ prime ∈ exponents.biUnion
      (scaleAdaptiveDyadicPrimeShell length), prime) ∣
        primorial (scaleAdaptiveDyadicPhysicalScale length lower) := by
  rw [primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ id
    (scaleAdaptiveDyadicPrimeShell_biUnion_subset_cutoff_primes
      length lower exponents after)

/-- The actual selected-prime conductor is positive, including the empty
family case where its exact value is one. -/
theorem scaleAdaptiveDyadicPrimeShell_product_pos
    (length : ℕ) (exponents : Finset ℕ) :
    0 < (∏ prime ∈ exponents.biUnion
      (scaleAdaptiveDyadicPrimeShell length), prime) := by
  apply Finset.prod_pos
  intro prime selected
  obtain ⟨exponent, _, selected⟩ := Finset.mem_biUnion.mp selected
  exact (mem_scaleAdaptiveDyadicPrimeShell.mp selected).2.2.pos

/-- The ACTUAL logarithmic conductor of every finite genuine shell union
is bounded by the logarithm of its one integer-floored cutoff primorial. -/
theorem scaleAdaptiveDyadicPrimeShell_product_log_le_cutoff_primorial
    (length lower : ℕ) (exponents : Finset ℕ)
    (after : ∀ exponent ∈ exponents, lower < exponent) :
    Real.log
      ((∏ prime ∈ exponents.biUnion
        (scaleAdaptiveDyadicPrimeShell length), prime : ℕ) : ℝ) ≤
      Real.log
        (primorial (scaleAdaptiveDyadicPhysicalScale length lower) : ℝ) := by
  have divides := scaleAdaptiveDyadicPrimeShell_product_dvd_cutoff_primorial
    length lower exponents after
  have bound :
      (∏ prime ∈ exponents.biUnion
        (scaleAdaptiveDyadicPrimeShell length), prime) ≤
        primorial (scaleAdaptiveDyadicPhysicalScale length lower) :=
    Nat.le_of_dvd (primorial_pos _) divides
  apply Real.log_le_log
  · exact_mod_cast scaleAdaptiveDyadicPrimeShell_product_pos length exponents
  · exact_mod_cast bound

/-- PNT gives the exact actual cutoff-primorial cost `2^(-lower)`, with
the original interval length in the denominator and the true natural-number
floor inside the primorial. -/
theorem scaleAdaptiveDyadicCutoffPrimorial_log_normalized_tendsto
    (lower : ℕ) :
    Tendsto
      (fun length : ℕ =>
        Real.log
          (primorial (scaleAdaptiveDyadicPhysicalScale length lower) : ℝ) /
            (length : ℝ))
      atTop (nhds (((2 ^ lower : ℕ) : ℝ)⁻¹)) := by
  have power_positive : 0 < (2 ^ lower : ℕ) := by positivity
  have local_limit := original_primorial_log_div_length_tendsto_one.comp
    (scaleAdaptiveDyadicPhysicalScale_tendsto_atTop lower)
  have ratio := Erdos689.nat_div_cast_ratio_tendsto
    (2 ^ lower) power_positive
  have combined := local_limit.mul ratio
  have prepared :
      Tendsto
        (fun length : ℕ =>
          (Real.log
            (primorial (scaleAdaptiveDyadicPhysicalScale length lower) : ℝ) /
            (scaleAdaptiveDyadicPhysicalScale length lower : ℝ)) *
          ((scaleAdaptiveDyadicPhysicalScale length lower : ℝ) /
            (length : ℝ)))
        atTop (nhds (((2 ^ lower : ℕ) : ℝ)⁻¹)) := by
    simpa [scaleAdaptiveDyadicPhysicalScale] using combined
  apply prepared.congr'
  filter_upwards [eventually_ge_atTop (2 ^ lower)] with length large
  have positive : 0 < scaleAdaptiveDyadicPhysicalScale length lower := by
    unfold scaleAdaptiveDyadicPhysicalScale
    exact Nat.div_pos_iff.mpr ⟨power_positive, large⟩
  have nonzero : (scaleAdaptiveDyadicPhysicalScale length lower : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : scaleAdaptiveDyadicPhysicalScale length lower ≠ 0)
  field_simp [nonzero]

/-- For every fixed finite family of genuine shells, its REAL selected
prime-product conductor is eventually bounded by the exact PNT coefficient
plus any arbitrarily small positive slack. -/
theorem scaleAdaptiveDyadicPrimeShell_product_eventually_log_le
    (lower : ℕ) (exponents : Finset ℕ)
    (after : ∀ exponent ∈ exponents, lower < exponent)
    (slack : ℝ) (positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      Real.log
        ((∏ prime ∈ exponents.biUnion
          (scaleAdaptiveDyadicPrimeShell length), prime : ℕ) : ℝ) ≤
        ((((2 ^ lower : ℕ) : ℝ)⁻¹ + slack) * (length : ℝ)) := by
  have upper :
      ∀ᶠ length : ℕ in atTop,
        Real.log
          (primorial (scaleAdaptiveDyadicPhysicalScale length lower) : ℝ) /
            (length : ℝ) < (((2 ^ lower : ℕ) : ℝ)⁻¹ + slack) :=
    (scaleAdaptiveDyadicCutoffPrimorial_log_normalized_tendsto lower).eventually
      (Iio_mem_nhds (by linarith))
  filter_upwards [upper, eventually_ge_atTop (1 : ℕ)] with length bound large
  have length_positive : 0 < (length : ℝ) := by exact_mod_cast large
  have cutoff_bound := (div_lt_iff₀ length_positive).mp bound
  exact (scaleAdaptiveDyadicPrimeShell_product_log_le_cutoff_primorial
    length lower exponents after).trans cutoff_bound.le

/-- For the explicit integer family used by both actual low/high Euler
amplification estimates, the REAL selected prime-product conductor can be
made smaller than any prescribed positive fraction of the interval length.
The limit order is the genuine one: fix the parameter first, then let the
original target length tend to infinity. -/
theorem scaleAdaptiveColoredActualPrimeProductConductor_sublinear
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ parameter : ℕ in atTop,
      ∀ exponents : Finset ℕ,
        (∀ exponent ∈ exponents,
          scaleAdaptiveColoredLowerExponent parameter < exponent) →
          ∀ᶠ length : ℕ in atTop,
            Real.log
              ((∏ prime ∈ exponents.biUnion
                (scaleAdaptiveDyadicPrimeShell length), prime : ℕ) : ℝ) ≤
                  epsilon * (length : ℝ) := by
  have coefficient_small :
      ∀ᶠ parameter : ℕ in atTop,
        scaleAdaptiveColoredConductorDensity parameter < epsilon / 2 :=
    scaleAdaptiveColoredConductorDensity_tendsto_zero.eventually
      (Iio_mem_nhds (by linarith))
  filter_upwards [coefficient_small] with parameter small
  intro exponents after
  have eventual := scaleAdaptiveDyadicPrimeShell_product_eventually_log_le
    (scaleAdaptiveColoredLowerExponent parameter) exponents after
      (epsilon / 2) (by linarith)
  filter_upwards [eventual] with length bound
  have coefficient_bound :
      (((2 ^ scaleAdaptiveColoredLowerExponent parameter : ℕ) : ℝ)⁻¹ +
        epsilon / 2) ≤ epsilon := by
    change scaleAdaptiveColoredConductorDensity parameter + epsilon / 2 ≤ epsilon
    linarith
  exact bound.trans
    (mul_le_mul_of_nonneg_right coefficient_bound (Nat.cast_nonneg length))


end Erdos1139
