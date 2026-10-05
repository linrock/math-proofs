module

public import ScaleAdaptivePrimeSliceVariance1139

@[expose] public section


/-!
# Genuine disjoint dyadic prime-label shells

The global adaptive sampler must use each actual prime label at most once.
Taking `N_j = Y / 2^j` and the genuine half-open prime shell `(N_j, 2N_j]`
gives disjoint shells even when integer flooring is retained.  This file
keeps the exact physical scales, actual prime labels, and target-cell
endpoints; it never replaces shell disjointness by an independence premise.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- Exact integer-floored physical prime-label scale. -/
def scaleAdaptiveDyadicPhysicalScale (length exponent : ℕ) : ℕ :=
  length / 2 ^ exponent

/-- The ACTUAL dyadic prime labels already used by the signed physical
prime-pattern construction, now at their exact global floored scale. -/
def scaleAdaptiveDyadicPrimeShell (length exponent : ℕ) : Finset ℕ :=
  scaleAdaptiveSignedDegreePrimeLabels
    (scaleAdaptiveDyadicPhysicalScale length exponent)

/-- The scale at exponent zero is the original integer length. -/
theorem scaleAdaptiveDyadicPhysicalScale_zero (length : ℕ) :
    scaleAdaptiveDyadicPhysicalScale length 0 = length := by
  simp [scaleAdaptiveDyadicPhysicalScale]

/-- Successive floored global scales are EXACT natural halvings. -/
theorem scaleAdaptiveDyadicPhysicalScale_succ
    (length exponent : ℕ) :
    scaleAdaptiveDyadicPhysicalScale length (exponent + 1) =
      scaleAdaptiveDyadicPhysicalScale length exponent / 2 := by
  simp only [scaleAdaptiveDyadicPhysicalScale, pow_succ]
  rw [Nat.div_div_eq_div_mul]

/-- The doubled next integer-floored scale never exceeds the previous
scale.  This is the key exact endpoint preventing prime-label reuse. -/
theorem scaleAdaptiveDyadicPhysicalScale_succ_double_le
    (length exponent : ℕ) :
    2 * scaleAdaptiveDyadicPhysicalScale length (exponent + 1) ≤
      scaleAdaptiveDyadicPhysicalScale length exponent := by
  rw [scaleAdaptiveDyadicPhysicalScale_succ]
  simpa [Nat.mul_comm] using
    Nat.div_mul_le_self
      (scaleAdaptiveDyadicPhysicalScale length exponent) 2

/-- Larger exponents give weakly smaller ACTUAL integer-floored scales. -/
theorem scaleAdaptiveDyadicPhysicalScale_antitone
    (length : ℕ) {first second : ℕ} (ordered : first ≤ second) :
    scaleAdaptiveDyadicPhysicalScale length second ≤
      scaleAdaptiveDyadicPhysicalScale length first := by
  unfold scaleAdaptiveDyadicPhysicalScale
  exact Nat.div_le_div_left
    (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ordered)
    (pow_pos (by omega : 0 < (2 : ℕ)) first)

/-- Strictly different dyadic exponents have separated genuine physical
label intervals, including all integer-flooring endpoint effects. -/
theorem scaleAdaptiveDyadicPhysicalScale_double_le_of_lt
    (length : ℕ) {first second : ℕ} (ordered : first < second) :
    2 * scaleAdaptiveDyadicPhysicalScale length second ≤
      scaleAdaptiveDyadicPhysicalScale length first := by
  calc
    2 * scaleAdaptiveDyadicPhysicalScale length second ≤
        2 * scaleAdaptiveDyadicPhysicalScale length (first + 1) :=
      Nat.mul_le_mul_left 2
        (scaleAdaptiveDyadicPhysicalScale_antitone length (by omega))
    _ ≤ scaleAdaptiveDyadicPhysicalScale length first :=
      scaleAdaptiveDyadicPhysicalScale_succ_double_le length first

/-- Membership exposes actual primality and the true half-open physical
prime-label endpoints. -/
theorem mem_scaleAdaptiveDyadicPrimeShell
    {length exponent label : ℕ} :
    label ∈ scaleAdaptiveDyadicPrimeShell length exponent ↔
      scaleAdaptiveDyadicPhysicalScale length exponent < label ∧
      label ≤ 2 * scaleAdaptiveDyadicPhysicalScale length exponent ∧
      label.Prime := by
  simp [scaleAdaptiveDyadicPrimeShell,
    scaleAdaptiveSignedDegreePrimeLabels, and_assoc]

/-- Distinct physical shell exponents use DISJOINT actual primes. -/
theorem scaleAdaptiveDyadicPrimeShell_disjoint_of_lt
    (length : ℕ) {first second : ℕ} (ordered : first < second) :
    Disjoint (scaleAdaptiveDyadicPrimeShell length first)
      (scaleAdaptiveDyadicPrimeShell length second) := by
  apply Finset.disjoint_left.mpr
  intro label in_first in_second
  obtain ⟨first_lower, _, _⟩ :=
    mem_scaleAdaptiveDyadicPrimeShell.mp in_first
  obtain ⟨_, second_upper, _⟩ :=
    mem_scaleAdaptiveDyadicPrimeShell.mp in_second
  have separated :=
    scaleAdaptiveDyadicPhysicalScale_double_le_of_lt length ordered
  omega

/-- Distinct arbitrary shell indices use DISJOINT genuine prime pools. -/
theorem scaleAdaptiveDyadicPrimeShell_disjoint
    (length : ℕ) {first second : ℕ} (different : first ≠ second) :
    Disjoint (scaleAdaptiveDyadicPrimeShell length first)
      (scaleAdaptiveDyadicPrimeShell length second) := by
  rcases lt_or_gt_of_ne different with ordered | ordered
  · exact scaleAdaptiveDyadicPrimeShell_disjoint_of_lt length ordered
  · exact
      (scaleAdaptiveDyadicPrimeShell_disjoint_of_lt length ordered).symm

/-- The cardinality of a finite union of actual dyadic prime-label shells
is EXACTLY the sum of their cardinalities; no label is charged twice. -/
theorem scaleAdaptiveDyadicPrimeShell_biUnion_card
    (length : ℕ) (exponents : Finset ℕ) :
    (exponents.biUnion
      (scaleAdaptiveDyadicPrimeShell length)).card =
      ∑ exponent ∈ exponents,
        (scaleAdaptiveDyadicPrimeShell length exponent).card := by
  apply Finset.card_biUnion
  intro first _ second _ different
  exact scaleAdaptiveDyadicPrimeShell_disjoint length different

/-- Every positive-exponent shell consists of genuine primes no larger
than the actual original target length. -/
theorem scaleAdaptiveDyadicPrimeShell_subset_original_primes
    (length : ℕ) {exponent : ℕ} (positive : 0 < exponent) :
    scaleAdaptiveDyadicPrimeShell length exponent ⊆ Nat.primesLE length := by
  intro label selected
  obtain ⟨_, upper, prime⟩ :=
    mem_scaleAdaptiveDyadicPrimeShell.mp selected
  apply Nat.mem_primesLE.mpr
  refine ⟨?_, prime⟩
  have separated :=
    scaleAdaptiveDyadicPhysicalScale_double_le_of_lt length positive
  simpa [scaleAdaptiveDyadicPhysicalScale_zero] using upper.trans separated

/-- Every fixed physical shell scale tends to infinity as the actual
original target length tends to infinity; this is the valid fixed-pattern
limit order for invoking a signed Green--Tao theorem. -/
theorem scaleAdaptiveDyadicPhysicalScale_tendsto_atTop
    (exponent : ℕ) :
    Tendsto (fun length : ℕ =>
      scaleAdaptiveDyadicPhysicalScale length exponent) atTop atTop := by
  exact Nat.tendsto_div_const_atTop
    (pow_ne_zero exponent (by omega : (2 : ℕ) ≠ 0))

/-- Ordinary PNT gives exact density one in EACH shell's own genuine
physical prime-label normalization. -/
theorem scaleAdaptiveDyadicPrimeShell_local_normalized_tendsto_one
    (exponent : ℕ) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveDyadicPrimeShell length exponent).card : ℝ) *
          Real.log
            (scaleAdaptiveDyadicPhysicalScale length exponent : ℝ) /
          (scaleAdaptiveDyadicPhysicalScale length exponent : ℝ))
      atTop (nhds (1 : ℝ)) := by
  exact scaleAdaptiveSignedDegreePrimeLabels_normalized_tendsto_one.comp
    (scaleAdaptiveDyadicPhysicalScale_tendsto_atTop exponent)

/-- Every genuine dyadic shell has the correct original-length prime-scale
density `2^(-j)`, retaining both its exact integer flooring and the already
proved ordinary prime number theorem. -/
theorem scaleAdaptiveDyadicPrimeShell_global_normalized_tendsto
    (exponent : ℕ) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveDyadicPrimeShell length exponent).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (((2 ^ exponent : ℕ) : ℝ)⁻¹)) := by
  have power_positive : 0 < (2 ^ exponent : ℕ) :=
    pow_pos (by omega : 0 < (2 : ℕ)) exponent
  have local_limit :=
    scaleAdaptiveDyadicPrimeShell_local_normalized_tendsto_one exponent
  have ratio :=
    Erdos689.nat_div_prime_scale_ratio_tendsto
      (2 ^ exponent) power_positive
  have combined := local_limit.mul ratio
  have prepared :
      Tendsto
        (fun length : ℕ =>
          (((scaleAdaptiveDyadicPrimeShell length exponent).card : ℝ) *
            Real.log
              (scaleAdaptiveDyadicPhysicalScale length exponent : ℝ) /
            (scaleAdaptiveDyadicPhysicalScale length exponent : ℝ)) *
          (((scaleAdaptiveDyadicPhysicalScale length exponent : ℕ) : ℝ) /
            Real.log
              (scaleAdaptiveDyadicPhysicalScale length exponent : ℝ) /
              ((length : ℝ) / Real.log (length : ℝ))))
        atTop (nhds (((2 ^ exponent : ℕ) : ℝ)⁻¹)) := by
    simpa [scaleAdaptiveDyadicPhysicalScale] using combined
  apply prepared.congr'
  filter_upwards [eventually_ge_atTop (2 * 2 ^ exponent)] with length large
  have scale_large :
      2 ≤ scaleAdaptiveDyadicPhysicalScale length exponent := by
    apply (Nat.le_div_iff_mul_le power_positive).mpr
    simpa [scaleAdaptiveDyadicPhysicalScale] using large
  have length_positive : 0 < length := by
    have power_nonzero : 0 < 2 * 2 ^ exponent := by positivity
    omega
  have scale_nonzero :
      (scaleAdaptiveDyadicPhysicalScale length exponent : ℝ) ≠ 0 := by
    exact_mod_cast (by omega :
      scaleAdaptiveDyadicPhysicalScale length exponent ≠ 0)
  have length_nonzero : (length : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : length ≠ 0)
  have scale_log_nonzero :
      Real.log
        (scaleAdaptiveDyadicPhysicalScale length exponent : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (by omega :
        0 < scaleAdaptiveDyadicPhysicalScale length exponent)
    · exact_mod_cast (by omega :
        scaleAdaptiveDyadicPhysicalScale length exponent ≠ 1)
  have length_log_nonzero : Real.log (length : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast length_positive
    · exact_mod_cast (by
        have : 2 ≤ length := by
          have : 2 ≤ 2 * 2 ^ exponent := by
            have : 1 ≤ 2 ^ exponent := by omega
            omega
          omega
        omega : length ≠ 1)
  field_simp [scale_nonzero, length_nonzero,
    scale_log_nonzero, length_log_nonzero]

/-- Every finite genuine shell union has exactly the sum of its distinct
physical prime-label densities at the ORIGINAL target scale. -/
theorem scaleAdaptiveDyadicPrimeShell_biUnion_global_normalized_tendsto
    (exponents : Finset ℕ) :
    Tendsto
      (fun length : ℕ =>
        ((exponents.biUnion
          (scaleAdaptiveDyadicPrimeShell length)).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds
        (∑ exponent ∈ exponents, (((2 ^ exponent : ℕ) : ℝ)⁻¹))) := by
  have each := tendsto_finsetSum exponents
    (fun exponent _ =>
      scaleAdaptiveDyadicPrimeShell_global_normalized_tendsto exponent)
  apply each.congr'
  exact Filter.Eventually.of_forall fun length => by
    dsimp
    rw [scaleAdaptiveDyadicPrimeShell_biUnion_card, Nat.cast_sum]
    rw [Finset.sum_mul, Finset.sum_div]

/-- Once the original length is at least the square of the fixed dyadic
denominator, every scale strictly exceeds any fixed smaller prime cutoff.
This retains the integer remainder; no real-scale approximation is used. -/
theorem scaleAdaptiveDyadicPhysicalScale_above_core
    (length exponent cutoff : ℕ)
    (inside : 2 ^ exponent < cutoff)
    (large : 2 ^ exponent * 2 ^ exponent ≤ length) :
    length / cutoff < scaleAdaptiveDyadicPhysicalScale length exponent := by
  let denominator : ℕ := 2 ^ exponent
  have denominator_positive : 0 < denominator := by
    dsimp [denominator]
    positivity
  have cutoff_positive : 0 < cutoff := by
    dsimp [denominator] at denominator_positive
    omega
  have quotient_large : denominator ≤ length / denominator := by
    apply (Nat.le_div_iff_mul_le denominator_positive).mpr
    simpa [denominator] using large
  have remainder_small : length % denominator < length / denominator :=
    lt_of_lt_of_le (Nat.mod_lt length denominator_positive) quotient_large
  have cutoff_large : denominator + 1 ≤ cutoff := by
    dsimp [denominator]
    omega
  have product_bound : length < (length / denominator) * cutoff := by
    calc
      length = length % denominator +
          denominator * (length / denominator) :=
        (Nat.mod_add_div length denominator).symm
      _ < length / denominator +
          denominator * (length / denominator) :=
        Nat.add_lt_add_right remainder_small _
      _ = (length / denominator) * (denominator + 1) := by ring
      _ ≤ (length / denominator) * cutoff :=
        Nat.mul_le_mul_left _ cutoff_large
  exact (Nat.div_lt_iff_lt_mul cutoff_positive).mpr product_bound

/-- At every sufficiently large target length, each genuine dyadic shell
strictly below the fixed denominator cutoff consists only of actual FRESH
primes above the true old-core threshold `length / cutoff`. -/
theorem scaleAdaptiveDyadicPrimeShell_eventually_fresh
    (exponent cutoff : ℕ) (inside : 2 ^ exponent < cutoff) :
    ∀ᶠ length : ℕ in atTop,
      ∀ label ∈ scaleAdaptiveDyadicPrimeShell length exponent,
        length / cutoff < label := by
  filter_upwards [eventually_ge_atTop
    (2 ^ exponent * 2 ^ exponent)] with length large label selected
  have scale_fresh := scaleAdaptiveDyadicPhysicalScale_above_core
    length exponent cutoff inside large
  exact scale_fresh.trans
    (mem_scaleAdaptiveDyadicPrimeShell.mp selected).1

/-- Actual moving target endpoints that must be deleted before applying an
OPEN signed prime-pattern cell at the integer-floored physical scale. -/
def scaleAdaptiveDyadicTargetBoundaries
    (length exponent : ℕ) : Finset ℕ :=
  (Finset.Icc 1 length).filter fun target =>
    target % scaleAdaptiveDyadicPhysicalScale length exponent = 0

/-- Distinct true target-cell boundaries have distinct integer quotient
indices, so their number is at most the exact quotient count. -/
theorem scaleAdaptiveDyadicTargetBoundaries_card_le_quotient
    (length exponent : ℕ)
    (scale_positive :
      0 < scaleAdaptiveDyadicPhysicalScale length exponent) :
    (scaleAdaptiveDyadicTargetBoundaries length exponent).card ≤
      length / scaleAdaptiveDyadicPhysicalScale length exponent := by
  let scale := scaleAdaptiveDyadicPhysicalScale length exponent
  have injection := Finset.card_le_card_of_injOn
    (s := scaleAdaptiveDyadicTargetBoundaries length exponent)
    (t := Finset.Icc 1 (length / scale))
    (fun target : ℕ => target / scale)
    (by
      intro target selected
      obtain ⟨interval, divisible⟩ :=
        Finset.mem_filter.mp selected
      obtain ⟨positive, bounded⟩ := Finset.mem_Icc.mp interval
      apply Finset.mem_Icc.mpr
      constructor
      · apply (Nat.le_div_iff_mul_le scale_positive).mpr
        simpa using Nat.le_of_dvd (by omega : 0 < target)
          (Nat.dvd_of_mod_eq_zero divisible)
      · exact Nat.div_le_div_right bounded)
    (by
      intro first first_selected second second_selected equal
      have first_remainder :=
        (Finset.mem_filter.mp first_selected).2
      have second_remainder :=
        (Finset.mem_filter.mp second_selected).2
      change first % scale = 0 at first_remainder
      change second % scale = 0 at second_remainder
      change first / scale = second / scale at equal
      have first_identity : scale * (first / scale) = first := by
        simpa [first_remainder] using Nat.mod_add_div first scale
      have second_identity : scale * (second / scale) = second := by
        simpa [second_remainder] using Nat.mod_add_div second scale
      calc
        first = scale * (first / scale) := first_identity.symm
        _ = scale * (second / scale) := by rw [equal]
        _ = second := second_identity)
  simpa using injection

/-- The total number of moving target-cell endpoints is uniformly bounded
by TWICE the genuine fixed dyadic denominator, independently of the
original target length. -/
theorem scaleAdaptiveDyadicTargetBoundaries_card_le_two_pow
    (length exponent : ℕ)
    (scale_positive :
      0 < scaleAdaptiveDyadicPhysicalScale length exponent) :
    (scaleAdaptiveDyadicTargetBoundaries length exponent).card ≤
      2 * 2 ^ exponent := by
  let denominator : ℕ := 2 ^ exponent
  let scale : ℕ := scaleAdaptiveDyadicPhysicalScale length exponent
  have denominator_positive : 0 < denominator := by
    dsimp [denominator]
    positivity
  have denominator_le_product : denominator ≤ denominator * scale :=
    Nat.le_mul_of_pos_right denominator scale_positive
  have remainder_small : length % denominator < denominator :=
    Nat.mod_lt length denominator_positive
  have scale_eq : scale = length / denominator := rfl
  have length_bound : length < (2 * denominator) * scale := by
    calc
      length = length % denominator + denominator * scale := by
        simpa [scale_eq] using (Nat.mod_add_div length denominator).symm
      _ < denominator + denominator * scale :=
        Nat.add_lt_add_right remainder_small _
      _ ≤ denominator * scale + denominator * scale :=
        Nat.add_le_add_right denominator_le_product _
      _ = (2 * denominator) * scale := by ring
  have quotient_bound : length / scale < 2 * denominator :=
    (Nat.div_lt_iff_lt_mul scale_positive).mpr length_bound
  exact (scaleAdaptiveDyadicTargetBoundaries_card_le_quotient
    length exponent scale_positive).trans (by
      change length / scale ≤ 2 * 2 ^ exponent
      exact (Nat.le_of_lt quotient_bound).trans (by
        simp [denominator]))

/-- Deleting ALL moving open-cell endpoints of any fixed physical shell
has zero cost at the ORIGINAL genuine prime-target normalization. -/
theorem scaleAdaptiveDyadicTargetBoundaries_normalized_tendsto_zero
    (exponent : ℕ) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveDyadicTargetBoundaries length exponent).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have log_ratio :
      Tendsto
        (fun length : ℕ => Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ)) := by
    have real_limit := Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 1 one_ne_zero
    simpa [Function.comp_def] using real_limit.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have upper :
      Tendsto
        (fun length : ℕ =>
          ((2 * 2 ^ exponent : ℕ) : ℝ) *
            (Real.log (length : ℝ) / (length : ℝ)))
        atTop (nhds (0 : ℝ)) := by
    simpa using log_ratio.const_mul ((2 * 2 ^ exponent : ℕ) : ℝ)
  apply squeeze_zero' _ _ upper
  · filter_upwards [eventually_ge_atTop 2] with length large
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ length))))
      (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop
        (max (2 ^ exponent) 2)] with length large
    have denominator_positive : 0 < (2 ^ exponent : ℕ) := by positivity
    have scale_positive :
        0 < scaleAdaptiveDyadicPhysicalScale length exponent := by
      exact Nat.div_pos
        ((le_max_left _ _).trans large) denominator_positive
    have cardinal := scaleAdaptiveDyadicTargetBoundaries_card_le_two_pow
      length exponent scale_positive
    have real_cardinal :
        ((scaleAdaptiveDyadicTargetBoundaries length exponent).card : ℝ) ≤
          (2 * 2 ^ exponent : ℕ) := by exact_mod_cast cardinal
    have log_nonnegative : 0 ≤ Real.log (length : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (by
        have : 2 ≤ length := (le_max_right _ _).trans large
        omega : 1 ≤ length)
    have length_nonnegative : 0 ≤ (length : ℝ) := Nat.cast_nonneg _
    simpa [mul_div_assoc] using
      mul_le_mul_of_nonneg_right real_cardinal
        (div_nonneg log_nonnegative length_nonnegative)

/-- Every original target away from the explicitly deleted moving
boundaries lies in its exact OPEN physical integer cell. -/
theorem scaleAdaptiveDyadicTarget_mem_open_cell_of_not_boundary
    {length exponent target : ℕ}
    (scale_positive :
      0 < scaleAdaptiveDyadicPhysicalScale length exponent)
    (target_positive : 0 < target)
    (target_bounded : target ≤ length)
    (not_boundary :
      target ∉ scaleAdaptiveDyadicTargetBoundaries length exponent) :
    let scale := scaleAdaptiveDyadicPhysicalScale length exponent
    let cell := target / scale
    cell * scale < target ∧ target < (cell + 1) * scale := by
  dsimp
  let scale := scaleAdaptiveDyadicPhysicalScale length exponent
  change 0 < scale at scale_positive
  change (target / scale) * scale < target ∧
    target < (target / scale + 1) * scale
  have remainder_nonzero : target % scale ≠ 0 := by
    intro zero
    apply not_boundary
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, target_bounded⟩, zero⟩
  have decomposition := Nat.mod_add_div target scale
  have lower : (target / scale) * scale < target := by
    have remainder_positive : 0 < target % scale :=
      Nat.pos_of_ne_zero remainder_nonzero
    have reordered : scale * (target / scale) =
        (target / scale) * scale := Nat.mul_comm _ _
    omega
  have upper : target < (target / scale + 1) * scale :=
    (Nat.div_lt_iff_lt_mul scale_positive).mp (by omega)
  exact ⟨lower, upper⟩


end Erdos1139
