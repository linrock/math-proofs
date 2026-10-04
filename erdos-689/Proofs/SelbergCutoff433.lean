module

public import SelbergExplicitConstant433

@[expose] public section


/-!
# Genuine fifth-root Selberg cutoff for Erdős problem #689

The existing sharp denominator theorem assumes a logarithmic lower bound for
its finite block cutoff.  Here the block cutoff is chosen concretely as
`sqrt (nthRoot 5 n)`, and the assumed logarithmic comparison is proved
eventually for every fixed positive modulus.  The elementary argument uses
only exact natural-root and floor-division inequalities.
-/

open Filter
open scoped Topology

namespace Erdos689

/-- The actual natural Selberg sieve cutoff. -/
def selbergFifthRootCutoff (n : ℕ) : ℕ := Nat.nthRoot 5 n

/-- The actual natural square-root block cutoff used by the sharp squarefree
denominator estimate. -/
def selbergSquareRootBlockCutoff (n : ℕ) : ℕ :=
  Nat.sqrt (selbergFifthRootCutoff n)

/-- The exact integer fifth-root cutoff has fifth power at most the endpoint. -/
theorem selbergFifthRootCutoff_pow_five_le (n : ℕ) :
    selbergFifthRootCutoff n ^ 5 ≤ n := by
  unfold selbergFifthRootCutoff
  exact Nat.pow_nthRoot_le (Or.inl (by norm_num))

/-- The natural square-root block has square at most the actual sieve cutoff. -/
theorem selbergSquareRootBlockCutoff_sq_le (n : ℕ) :
    selbergSquareRootBlockCutoff n ^ 2 ≤ selbergFifthRootCutoff n := by
  unfold selbergSquareRootBlockCutoff
  exact Nat.sqrt_le' _

/-- Combining both exact natural-root upper errors gives a strict tenth-power
upper bound for the original endpoint. -/
theorem endpoint_lt_succ_selbergSquareRootBlockCutoff_pow_ten (n : ℕ) :
    n < (selbergSquareRootBlockCutoff n + 1) ^ 10 := by
  let z := selbergFifthRootCutoff n
  let L := selbergSquareRootBlockCutoff n
  have hnroot : n < (z + 1) ^ 5 := by
    exact Nat.lt_pow_nthRoot_add_one (by norm_num) n
  have hzroot : z < (L + 1) ^ 2 := by
    exact Nat.lt_succ_sqrt' z
  have hzsucc : z + 1 ≤ (L + 1) ^ 2 := by omega
  calc
    n < (z + 1) ^ 5 := hnroot
    _ ≤ ((L + 1) ^ 2) ^ 5 := by gcongr
    _ = (L + 1) ^ 10 := by rw [← pow_mul]

/-- Once the endpoint passes an explicit fixed-modulus threshold, the natural
block cutoff dominates the eleventh power of that modulus. -/
theorem modulus_pow_eleven_le_selbergSquareRootBlockCutoff
    (M n : ℕ) (hn : (M ^ 11) ^ 10 ≤ n) :
    M ^ 11 ≤ selbergSquareRootBlockCutoff n := by
  apply (Nat.le_sqrt').2
  unfold selbergFifthRootCutoff
  apply (Nat.le_nthRoot_iff (by norm_num : (5 : ℕ) ≠ 0)).2
  simpa only [← pow_mul] using hn

/-- Exact floor-division upper bound with no lost remainder term. -/
theorem nat_succ_le_modulus_mul_succ_div
    (L M : ℕ) (hM : 0 < M) :
    L + 1 ≤ M * (L / M + 1) := by
  have hremainder : L % M < M := Nat.mod_lt L hM
  have hdecomposition : L % M + M * (L / M) = L :=
    Nat.mod_add_div L M
  calc
    L + 1 = L % M + M * (L / M) + 1 := by omega
    _ ≤ M + M * (L / M) := by omega
    _ = M * (L / M + 1) := by ring

/-- Above the explicit fixed-modulus threshold, the original endpoint is less
than the eleventh power of the genuine complete-block count. -/
theorem endpoint_lt_selberg_complete_blocks_pow_eleven
    (M n : ℕ) (hM : 0 < M)
    (hn : (M ^ 11) ^ 10 ≤ n) :
    n < (selbergSquareRootBlockCutoff n / M + 1) ^ 11 := by
  let L := selbergSquareRootBlockCutoff n
  let K := L / M + 1
  have hLlarge : M ^ 11 ≤ L :=
    modulus_pow_eleven_le_selbergSquareRootBlockCutoff M n hn
  have hquotient : M ^ 10 ≤ L / M := by
    apply (Nat.le_div_iff_mul_le hM).2
    simpa [pow_succ] using hLlarge
  have hKlarge : M ^ 10 ≤ K := by
    dsimp [K]
    omega
  have hblock : L + 1 ≤ M * K :=
    nat_succ_le_modulus_mul_succ_div L M hM
  calc
    n < (L + 1) ^ 10 :=
      endpoint_lt_succ_selbergSquareRootBlockCutoff_pow_ten n
    _ ≤ (M * K) ^ 10 := by gcongr
    _ = M ^ 10 * K ^ 10 := by rw [mul_pow]
    _ ≤ K * K ^ 10 := Nat.mul_le_mul_right (K ^ 10) hKlarge
    _ = K ^ 11 := by ring

/-- The exact logarithmic block-cutoff hypothesis required by the previously
audited `3 / 605` Selberg denominator theorem holds above a fixed threshold. -/
theorem selberg_complete_block_log_lower_of_threshold
    (M n : ℕ) (hM : 0 < M)
    (hn : (M ^ 11) ^ 10 ≤ n) (hnpositive : 0 < n) :
    Real.log (n : ℝ) / 11 ≤
      Real.log ((selbergSquareRootBlockCutoff n / M + 1 : ℕ) : ℝ) := by
  let K := selbergSquareRootBlockCutoff n / M + 1
  have hpower : n ≤ K ^ 11 :=
    (endpoint_lt_selberg_complete_blocks_pow_eleven M n hM hn).le
  have hreal : (n : ℝ) ≤ (K : ℝ) ^ 11 := by
    exact_mod_cast hpower
  have hlog := Real.log_le_log
    (by exact_mod_cast hnpositive : (0 : ℝ) < n) hreal
  rw [Real.log_pow] at hlog
  change Real.log (n : ℝ) / 11 ≤ Real.log (K : ℝ)
  norm_num at hlog ⊢
  linarith

/-- Every fixed positive modulus eventually meets the genuine fifth-root,
square-root, floor-division logarithmic cutoff condition. -/
theorem selberg_complete_block_log_lower_eventually
    (M : ℕ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) / 11 ≤
        Real.log ((selbergSquareRootBlockCutoff n / M + 1 : ℕ) : ℝ) := by
  filter_upwards [eventually_ge_atTop ((M ^ 11) ^ 10),
    eventually_ge_atTop 1] with n hn hnpositive
  exact selberg_complete_block_log_lower_of_threshold M n hM hn
    (by omega)

/-- The exact `3 / 605` denominator bound now holds at the actual fifth-root
sieve cutoff, uniformly for every moving admissible outside prime. -/
theorem twoRootSelbergDenominator_fifth_root_eventually_ge_explicit_log_sq
    (M : ℕ) (hMeven : 2 ∣ M) (hM : 2 ≤ M) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ,
      q.Prime → Nat.Coprime q M → 5 ≤ q →
        (3 / 605 : ℝ) * (((M.totient : ℝ) / M) ^ 2) *
            (Real.log (n : ℝ)) ^ 2 ≤
          twoRootSelbergDenominator (M * q)
            (selbergSquareRootBlockCutoff n ^ 2) := by
  have hMpositive : 0 < M := by omega
  filter_upwards [selberg_complete_block_log_lower_eventually M hMpositive,
    eventually_ge_atTop 2] with n hcutoff hn
  intro q hq hqM hqfive
  exact twoRootSelbergDenominator_excluded_prime_ge_explicit_log_sq
    M q (selbergSquareRootBlockCutoff n) n
    hMeven hM hq hqM hqfive hn hcutoff

/-- The matching sharp reciprocal denominator estimate is likewise uniform
in every moving outside prime at the actual natural fifth-root cutoff. -/
theorem twoRootSelbergDenominator_fifth_root_eventually_inv_le_explicit
    (M : ℕ) (hMeven : 2 ∣ M) (hM : 2 ≤ M) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ,
      q.Prime → Nat.Coprime q M → 5 ≤ q →
        (twoRootSelbergDenominator (M * q)
          (selbergSquareRootBlockCutoff n ^ 2))⁻¹ ≤
            (605 / 3 : ℝ) * (((M : ℝ) / M.totient) ^ 2) /
              (Real.log (n : ℝ)) ^ 2 := by
  have hMpositive : 0 < M := by omega
  filter_upwards [selberg_complete_block_log_lower_eventually M hMpositive,
    eventually_ge_atTop 2] with n hcutoff hn
  intro q hq hqM hqfive
  exact twoRootSelbergDenominator_excluded_prime_inv_le_explicit
    M q (selbergSquareRootBlockCutoff n) n
    hMeven hM hq hqM hqfive hn hcutoff

/-- The exact natural fifth-root cutoff is no greater than the corresponding
nonnegative real fifth root. -/
theorem selbergFifthRootCutoff_le_real_fifth_root (n : ℕ) :
    (selbergFifthRootCutoff n : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
  have hpower : (selbergFifthRootCutoff n : ℝ) ^ 5 ≤ (n : ℝ) := by
    exact_mod_cast selbergFifthRootCutoff_pow_five_le n
  have hroot := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (selbergFifthRootCutoff n : ℝ) ^ 5)
    hpower (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hidentity :
      ((selbergFifthRootCutoff n : ℝ) ^ 5) ^ (1 / 5 : ℝ) =
        (selbergFifthRootCutoff n : ℝ) := by
    convert Real.pow_rpow_inv_natCast
      (by positivity : (0 : ℝ) ≤ (selbergFifthRootCutoff n : ℝ))
      (by norm_num : (5 : ℕ) ≠ 0) using 1
    norm_num
  rw [hidentity] at hroot
  exact hroot

/-- The complete natural Selberg fourth-power remainder is bounded by the
correct real endpoint exponent `4 / 5`. -/
theorem selbergFifthRootCutoff_fourth_power_le_real_four_fifths (n : ℕ) :
    (selbergFifthRootCutoff n : ℝ) ^ 4 ≤ (n : ℝ) ^ (4 / 5 : ℝ) := by
  have hroot := selbergFifthRootCutoff_le_real_fifth_root n
  calc
    (selbergFifthRootCutoff n : ℝ) ^ 4 ≤
        ((n : ℝ) ^ (1 / 5 : ℝ)) ^ 4 := by gcongr
    _ = (n : ℝ) ^ (4 / 5 : ℝ) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 5 : ℝ)) 4,
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
      norm_num

/-- Two logarithms are negligible against the fifth-root power on the actual
natural endpoint sequence. -/
theorem log_sq_div_fifth_rpow_nat_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ))
      atTop (nhds 0) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop 2
      (by norm_num : 0 < (1 / 5 : ℝ))).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def, Real.rpow_two] using hnat

/-- The exact fourth-power Selberg remainder at the genuine natural fifth-root
cutoff is little-o of the required `n / log(n)^2` degree scale. -/
theorem selbergFifthRootCutoff_fourth_power_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        (selbergFifthRootCutoff n : ℝ) ^ 4 /
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2))
      atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds log_sq_div_fifth_rpow_nat_tendsto_zero ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 0 < n)
    have hnone : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnone
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 0 < n)
    have hnone : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnone
    have hfifth : 0 < (n : ℝ) ^ (1 / 5 : ℝ) :=
      Real.rpow_pos_of_pos hnreal _
    have hdenominator : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
      positivity
    have hpower :
        (n : ℝ) ^ (4 / 5 : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) =
          (n : ℝ) := by
      rw [← Real.rpow_add hnreal]
      norm_num
    have hratio :
        (n : ℝ) ^ (4 / 5 : ℝ) / (n : ℝ) =
          1 / (n : ℝ) ^ (1 / 5 : ℝ) := by
      apply (div_eq_div_iff hnreal.ne' hfifth.ne').mpr
      simpa using hpower
    calc
      (selbergFifthRootCutoff n : ℝ) ^ 4 /
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤
        (n : ℝ) ^ (4 / 5 : ℝ) /
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
        exact (div_le_div_iff_of_pos_right hdenominator).mpr
          (selbergFifthRootCutoff_fourth_power_le_real_four_fifths n)
      _ = ((n : ℝ) ^ (4 / 5 : ℝ) / (n : ℝ)) *
            (Real.log (n : ℝ)) ^ 2 := by
        field_simp
      _ = (1 / (n : ℝ) ^ (1 / 5 : ℝ)) *
            (Real.log (n : ℝ)) ^ 2 := by rw [hratio]
      _ = (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ) := by
        ring

/-- Every genuine two-variable Selberg remainder with bounded optimized
weights and the proved affine CRT remainder contract vanishes on the exact
degree scale when the cutoff is the natural fifth root. -/
theorem selberg_two_variable_fifth_root_remainder_normalized_tendsto_zero
    (weights remainder : ℕ → ℕ → ℝ)
    (hweights : ∀ n d : ℕ, |weights n d| ≤ 1)
    (hremainder : ∀ n d : ℕ, |remainder n d| ≤ (d : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        (∑ d ∈ Finset.Icc 1 (selbergFifthRootCutoff n),
          ∑ e ∈ Finset.Icc 1 (selbergFifthRootCutoff n),
            |weights n d * weights n e *
              remainder n (Nat.lcm d e)|) /
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2))
      atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    selbergFifthRootCutoff_fourth_power_normalized_tendsto_zero ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 0 < n)
    have hnone : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnone
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 0 < n)
    have hnone : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnone
    have hdenominator : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
      positivity
    apply (div_le_div_iff_of_pos_right hdenominator).mpr
    exact selberg_two_variable_remainder_le_fourth_power
      (selbergFifthRootCutoff n) (weights n) (remainder n)
      (hweights n) (hremainder n)

#print axioms Erdos689.selbergFifthRootCutoff_pow_five_le
#print axioms Erdos689.selbergSquareRootBlockCutoff_sq_le
#print axioms Erdos689.endpoint_lt_succ_selbergSquareRootBlockCutoff_pow_ten
#print axioms Erdos689.modulus_pow_eleven_le_selbergSquareRootBlockCutoff
#print axioms Erdos689.nat_succ_le_modulus_mul_succ_div
#print axioms Erdos689.endpoint_lt_selberg_complete_blocks_pow_eleven
#print axioms Erdos689.selberg_complete_block_log_lower_of_threshold
#print axioms Erdos689.selberg_complete_block_log_lower_eventually
#print axioms Erdos689.twoRootSelbergDenominator_fifth_root_eventually_ge_explicit_log_sq
#print axioms Erdos689.twoRootSelbergDenominator_fifth_root_eventually_inv_le_explicit
#print axioms Erdos689.selbergFifthRootCutoff_le_real_fifth_root
#print axioms Erdos689.selbergFifthRootCutoff_fourth_power_le_real_four_fifths
#print axioms Erdos689.log_sq_div_fifth_rpow_nat_tendsto_zero
#print axioms Erdos689.selbergFifthRootCutoff_fourth_power_normalized_tendsto_zero
#print axioms Erdos689.selberg_two_variable_fifth_root_remainder_normalized_tendsto_zero

end Erdos689
