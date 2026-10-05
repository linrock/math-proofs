module

public import SelbergHarmonicBlocks

@[expose] public section


/-!
# Explicit moving-prime Selberg constants without Mertens estimates

The sharp finite residue-block theorem already gives the genuine squarefree
Selberg denominator with its exact fixed-modulus totient factor.  This module
performs the remaining *finite* numerical transfer used in the adversarial
sieve audit: once the actual logarithmic cutoff dominates `log n / 11`, an
arbitrary moving outside prime retains the coefficient `3 / 605`, and the
reciprocal denominator has coefficient `605 / 3`.

No prime-product asymptotic, Mertens estimate, growing-modulus PNT, affine
sieve instantiation, or prime-pattern theorem is assumed or proved here.
-/

namespace Erdos689

/-- The complete two-variable least-common-multiple remainder sum at Selberg
coefficient cutoff `z` is bounded by `z ^ 4`, with no squarefree or
root-count multiplicity silently discarded. -/
theorem selberg_double_lcm_sum_le_fourth_power (z : ℕ) :
    (∑ d ∈ Finset.Icc 1 z,
      ∑ e ∈ Finset.Icc 1 z, Nat.lcm d e) ≤ z ^ 4 := by
  calc
    (∑ d ∈ Finset.Icc 1 z,
      ∑ e ∈ Finset.Icc 1 z, Nat.lcm d e) ≤
        ∑ _d ∈ Finset.Icc 1 z,
          ∑ _e ∈ Finset.Icc 1 z, z ^ 2 := by
            apply Finset.sum_le_sum
            intro d hd
            obtain ⟨hdpos, hdz⟩ := Finset.mem_Icc.mp hd
            apply Finset.sum_le_sum
            intro e he
            obtain ⟨hepos, hez⟩ := Finset.mem_Icc.mp he
            have hproduct : 0 < d * e := Nat.mul_pos hdpos hepos
            have hlcm : Nat.lcm d e ≤ d * e :=
              Nat.le_of_dvd hproduct (Nat.lcm_dvd
                (dvd_mul_right d e) (dvd_mul_left e d))
            calc
              Nat.lcm d e ≤ d * e := hlcm
              _ ≤ z * z := Nat.mul_le_mul hdz hez
              _ = z ^ 2 := by ring
    _ = z ^ 4 := by simp [pow_succ]; ring

/-- Optimized Selberg weights of absolute value at most one and the exact
CRT remainder bound `|r_h| ≤ h` give the complete `z ^ 4` two-variable
remainder.  Unlike the coarser collapsed bound, this theorem introduces no
additional `3 ^ ω(h)` multiplier. -/
theorem selberg_two_variable_remainder_le_fourth_power
    (z : ℕ) (weights remainder : ℕ → ℝ)
    (hweights : ∀ d : ℕ, |weights d| ≤ 1)
    (hremainder : ∀ d : ℕ, |remainder d| ≤ (d : ℝ)) :
    (∑ d ∈ Finset.Icc 1 z,
      ∑ e ∈ Finset.Icc 1 z,
        |weights d * weights e * remainder (Nat.lcm d e)|) ≤
      (z : ℝ) ^ 4 := by
  calc
    (∑ d ∈ Finset.Icc 1 z,
      ∑ e ∈ Finset.Icc 1 z,
        |weights d * weights e * remainder (Nat.lcm d e)|) ≤
        ∑ d ∈ Finset.Icc 1 z,
          ∑ e ∈ Finset.Icc 1 z, (Nat.lcm d e : ℝ) := by
            apply Finset.sum_le_sum
            intro d hd
            apply Finset.sum_le_sum
            intro e he
            have hproduct : |weights d * weights e| ≤ (1 : ℝ) := by
              rw [abs_mul]
              nlinarith [abs_nonneg (weights d), abs_nonneg (weights e),
                hweights d, hweights e]
            rw [abs_mul]
            calc
              |weights d * weights e| * |remainder (Nat.lcm d e)| ≤
                  1 * |remainder (Nat.lcm d e)| :=
                mul_le_mul_of_nonneg_right hproduct (abs_nonneg _)
              _ ≤ (Nat.lcm d e : ℝ) := by
                simpa using hremainder (Nat.lcm d e)
    _ = ((∑ d ∈ Finset.Icc 1 z,
          ∑ e ∈ Finset.Icc 1 z, Nat.lcm d e : ℕ) : ℝ) := by
            norm_cast
    _ ≤ (z : ℝ) ^ 4 := by
          exact_mod_cast selberg_double_lcm_sum_le_fourth_power z

/-- The already-audited moving-prime denominator has the explicit finite
`3 / 605` logarithm-square lower bound at every admissible cutoff. -/
theorem twoRootSelbergDenominator_excluded_prime_ge_explicit_log_sq
    (M q L n : ℕ) (hMeven : 2 ∣ M) (hM : 2 ≤ M)
    (hq : q.Prime) (hqM : Nat.Coprime q M) (hqfive : 5 ≤ q)
    (hn : 2 ≤ n)
    (hcutoff : Real.log (n : ℝ) / 11 ≤
      Real.log ((L / M + 1 : ℕ) : ℝ)) :
    (3 / 605 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
        (Real.log (n : ℝ)) ^ 2 ≤
      twoRootSelbergDenominator (M * q) (L ^ 2) := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hnlog : 0 ≤ Real.log (n : ℝ) :=
    (Real.log_pos hnreal).le
  have hblocklog : 0 ≤ Real.log ((L / M + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.le_add_left 1 (L / M)
  calc
    (3 / 605 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
        (Real.log (n : ℝ)) ^ 2 =
      (3 / 5 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
        (Real.log (n : ℝ) / 11) ^ 2 := by ring
    _ ≤ (3 / 5 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
        (Real.log ((L / M + 1 : ℕ) : ℝ)) ^ 2 := by
          gcongr
    _ ≤ twoRootSelbergDenominator (M * q) (L ^ 2) :=
      twoRootSelbergDenominator_excluded_prime_ge_totient_log_sq
        M q L hMeven hM hq hqM hqfive

/-- The corresponding actual reciprocal squarefree denominator has explicit
coefficient `605 / 3`, with the sharp fixed-modulus totient normalization. -/
theorem twoRootSelbergDenominator_excluded_prime_inv_le_explicit
    (M q L n : ℕ) (hMeven : 2 ∣ M) (hM : 2 ≤ M)
    (hq : q.Prime) (hqM : Nat.Coprime q M) (hqfive : 5 ≤ q)
    (hn : 2 ≤ n)
    (hcutoff : Real.log (n : ℝ) / 11 ≤
      Real.log ((L / M + 1 : ℕ) : ℝ)) :
    (twoRootSelbergDenominator (M * q) (L ^ 2))⁻¹ ≤
      (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) /
        (Real.log (n : ℝ)) ^ 2 := by
  have hMpositive : 0 < M := by omega
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpositive
  have htotient : 0 < M.totient := Nat.totient_pos.mpr hMpositive
  have htotientreal : (0 : ℝ) < M.totient := by exact_mod_cast htotient
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hpositive : 0 <
      (3 / 605 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
        (Real.log (n : ℝ)) ^ 2 := by positivity
  have hlower := twoRootSelbergDenominator_excluded_prime_ge_explicit_log_sq
    M q L n hMeven hM hq hqM hqfive hn hcutoff
  calc
    (twoRootSelbergDenominator (M * q) (L ^ 2))⁻¹ ≤
        ((3 / 605 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
          (Real.log (n : ℝ)) ^ 2)⁻¹ := inv_anti₀ hpositive hlower
    _ = (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) /
        (Real.log (n : ℝ)) ^ 2 := by
          field_simp

/-- Restoring the worst possible generic Euler-product loss `4 / 3` still
leaves the exact rational prefactor strictly below the convenient integer
upper bound `270`. -/
theorem twoRootSelberg_explicit_singular_prefactor_lt :
    (605 / 3 : ℝ) * (4 / 3) < 270 := by norm_num

/-- The unrestricted formal edge includes the genuine exceptional core
`q = 3`: parity, that local factor, and one moving determinant prime give
the exact leading constant `2025 / 2`. -/
theorem unrestricted_formal_degree_leading_constant_eq :
    (270 : ℝ) * 2 * (3 / 2) * (5 / 4) = 2025 / 2 := by norm_num

/-- Doubling the strict leading coefficient absorbs the fixed-modulus
power-saving Selberg remainder in the final eventual degree estimate. -/
theorem unrestricted_formal_degree_eventual_constant_eq :
    (2 : ℝ) * (270 * 2 * (3 / 2) * (5 / 4)) = 2025 := by norm_num


end Erdos689
