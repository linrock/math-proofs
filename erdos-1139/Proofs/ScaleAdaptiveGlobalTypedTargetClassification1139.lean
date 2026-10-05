module

public import ScaleAdaptiveMultiShellActualLoad1139
public import SemiprimeIncidenceBarrier1139
public import DeficiencyPrimePower433

@[expose] public section


/-!
# Exact global colored classification of the original fixed-core targets

The adaptive construction has to address the original closed interval of
integer targets, not merely the open prime-pattern cells.  Above the actual
core cutoff every prime belongs to BOTH colored target families, while every
genuine deficient semiprime belongs to exactly the family of its unique
small prime type.  The endpoint `1`, primes at or below the integer core
cutoff, proper prime powers, and moving physical-cell boundaries are charged
to an explicit exceptional set.

All supports and shell exponents are fixed before the target length tends to
infinity.  The exception for proper prime powers has zero genuine prime-scale
density; the small primes retain their exact, nonzero `1/z` coefficient.
No covering, matching, prime-pattern asymptotic, or additional correlation
hypothesis is assumed in this target-classification interface.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- The actual typed semiprime pairs whose unique small prime lies in the
low colored family.  The strict cutoff `s < z` remains in the parent set. -/
def scaleAdaptiveGlobalLowSemiprimePairs (length parameter cutoff : ℕ) :
    Finset (Σ _s : ℕ, ℕ) :=
  (fixedCoreTypedSemiprimePairs length parameter).filter
    fun pair => pair.1 ≤ cutoff

/-- The complementary actual typed semiprime pairs. -/
def scaleAdaptiveGlobalHighSemiprimePairs (length parameter cutoff : ℕ) :
    Finset (Σ _s : ℕ, ℕ) :=
  (fixedCoreTypedSemiprimePairs length parameter).filter
    fun pair => cutoff < pair.1

/-- Actual integer targets of the low semiprime family. -/
def scaleAdaptiveGlobalLowSemiprimeTargets
    (length parameter cutoff : ℕ) : Finset ℕ :=
  (scaleAdaptiveGlobalLowSemiprimePairs length parameter cutoff).image
    fun pair => pair.1 * pair.2

/-- Actual integer targets of the high semiprime family. -/
def scaleAdaptiveGlobalHighSemiprimeTargets
    (length parameter cutoff : ℕ) : Finset ℕ :=
  (scaleAdaptiveGlobalHighSemiprimePairs length parameter cutoff).image
    fun pair => pair.1 * pair.2

/-- Every large prime requires a hit of EACH color; low semiprimes require
only their low-colored hit. -/
def scaleAdaptiveGlobalLowTargets
    (length parameter cutoff : ℕ) : Finset ℕ :=
  fixedCoreLargePrimeTargets length parameter ∪
    scaleAdaptiveGlobalLowSemiprimeTargets length parameter cutoff

/-- Every large prime again belongs to this separate colored target family;
high semiprimes require only their high-colored hit. -/
def scaleAdaptiveGlobalHighTargets
    (length parameter cutoff : ℕ) : Finset ℕ :=
  fixedCoreLargePrimeTargets length parameter ∪
    scaleAdaptiveGlobalHighSemiprimeTargets length parameter cutoff

/-- An explicit finite over-cover of all genuine proper prime powers,
retaining the original closed interval.  Bases and exponents have their
true `sqrt(length)` and `log₂(length)` bounds. -/
def scaleAdaptiveGlobalProperPowerExceptions (length : ℕ) : Finset ℕ :=
  Finset.Icc 1 length ∩
    (((Finset.range (length.sqrt + 1)).product
      (Finset.range (Nat.log 2 length + 1))).image
        fun pair : ℕ × ℕ => pair.1 ^ pair.2)

/-- All moving cell endpoints for a FIXED finite family of physical shells. -/
def scaleAdaptiveGlobalMovingBoundaryExceptions
    (length : ℕ) (exponents : Finset ℕ) : Finset ℕ :=
  exponents.biUnion (scaleAdaptiveDyadicTargetBoundaries length)

/-- The complete explicit exception family.  Unlike the negligible proper
powers and physical boundaries, small primes have true coefficient `1/z`. -/
def scaleAdaptiveGlobalTargetExceptions
    (length parameter : ℕ) (exponents : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 length ∩ ({1} ∪ Nat.primesLE (length / parameter))) ∪
    scaleAdaptiveGlobalProperPowerExceptions length ∪
    scaleAdaptiveGlobalMovingBoundaryExceptions length exponents

/-- Low/high semiprime pair sets partition the ACTUAL complete typed pair
set, with no type copied and no eligible small prime discarded. -/
theorem scaleAdaptiveGlobalSemiprimePairs_union
    (length parameter cutoff : ℕ) :
    scaleAdaptiveGlobalLowSemiprimePairs length parameter cutoff ∪
      scaleAdaptiveGlobalHighSemiprimePairs length parameter cutoff =
        fixedCoreTypedSemiprimePairs length parameter := by
  ext pair
  simp only [scaleAdaptiveGlobalLowSemiprimePairs,
    scaleAdaptiveGlobalHighSemiprimePairs, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · rintro (⟨selected, _⟩ | ⟨selected, _⟩)
    · exact selected
    · exact selected
  · intro selected
    by_cases low : pair.1 ≤ cutoff
    · exact Or.inl ⟨selected, low⟩
    · exact Or.inr ⟨selected, by omega⟩

/-- The actual low/high integer target images exhaust every typed deficient
semiprime. -/
theorem scaleAdaptiveGlobalSemiprimeTargets_union
    (length parameter cutoff : ℕ) :
    scaleAdaptiveGlobalLowSemiprimeTargets length parameter cutoff ∪
      scaleAdaptiveGlobalHighSemiprimeTargets length parameter cutoff =
        fixedCoreTypedSemiprimeTargets length parameter := by
  unfold fixedCoreTypedSemiprimeTargets
    scaleAdaptiveGlobalLowSemiprimeTargets
    scaleAdaptiveGlobalHighSemiprimeTargets
  rw [← Finset.image_union,
    scaleAdaptiveGlobalSemiprimePairs_union length parameter cutoff]

/-- Uniqueness of the genuinely ordered small/large factors prevents an
actual semiprime target from belonging to both colored families. -/
theorem scaleAdaptiveGlobalSemiprimeTargets_disjoint
    {length parameter cutoff : ℕ} (positive : 0 < parameter)
    (square_threshold : parameter ≤ length / parameter) :
    Disjoint (scaleAdaptiveGlobalLowSemiprimeTargets
      length parameter cutoff)
      (scaleAdaptiveGlobalHighSemiprimeTargets
        length parameter cutoff) := by
  apply Finset.disjoint_left.mpr
  intro target in_low in_high
  obtain ⟨first, first_selected, first_equal⟩ :=
    Finset.mem_image.mp in_low
  obtain ⟨second, second_selected, second_equal⟩ :=
    Finset.mem_image.mp in_high
  obtain ⟨first_pair, first_small⟩ := Finset.mem_filter.mp first_selected
  obtain ⟨second_pair, second_large⟩ := Finset.mem_filter.mp second_selected
  have same_pair :=
    fixedCoreTypedSemiprimePairs_multiplication_injOn
      positive square_threshold first_pair second_pair
      (first_equal.trans second_equal.symm)
  have same_type : first.1 = second.1 := congrArg Sigma.fst same_pair
  omega

/-- Exact membership preserves primality, strict type bounds, original
closed endpoints, and the low-family cutoff. -/
theorem mem_scaleAdaptiveGlobalLowSemiprimeTargets
    {length parameter cutoff target : ℕ} (positive : 0 < parameter) :
    target ∈ scaleAdaptiveGlobalLowSemiprimeTargets
      length parameter cutoff ↔
      ∃ s q : ℕ, s.Prime ∧ s < parameter ∧ s ≤ cutoff ∧ q.Prime ∧
        length / parameter < q ∧ s * q ≤ length ∧ target = s * q := by
  constructor
  · intro selected
    obtain ⟨pair, selected, equal⟩ := Finset.mem_image.mp selected
    obtain ⟨pair_selected, small⟩ := Finset.mem_filter.mp selected
    obtain ⟨prime, bounded, partner_prime, large, endpoint⟩ :=
      (mem_fixedCoreTypedSemiprimePairs positive).mp pair_selected
    exact ⟨pair.1, pair.2, prime, bounded, small, partner_prime,
      large, endpoint, equal.symm⟩
  · rintro ⟨s, q, prime, bounded, small, partner_prime,
      large, endpoint, equal⟩
    subst target
    exact Finset.mem_image.mpr
      ⟨⟨s, q⟩, Finset.mem_filter.mpr
        ⟨(mem_fixedCoreTypedSemiprimePairs positive).mpr
          ⟨prime, bounded, partner_prime, large, endpoint⟩, small⟩, rfl⟩

/-- Exact complementary membership uses the genuinely strict lower type
cutoff, not a silently duplicated boundary type. -/
theorem mem_scaleAdaptiveGlobalHighSemiprimeTargets
    {length parameter cutoff target : ℕ} (positive : 0 < parameter) :
    target ∈ scaleAdaptiveGlobalHighSemiprimeTargets
      length parameter cutoff ↔
      ∃ s q : ℕ, s.Prime ∧ s < parameter ∧ cutoff < s ∧ q.Prime ∧
        length / parameter < q ∧ s * q ≤ length ∧ target = s * q := by
  constructor
  · intro selected
    obtain ⟨pair, selected, equal⟩ := Finset.mem_image.mp selected
    obtain ⟨pair_selected, large_type⟩ := Finset.mem_filter.mp selected
    obtain ⟨prime, bounded, partner_prime, large, endpoint⟩ :=
      (mem_fixedCoreTypedSemiprimePairs positive).mp pair_selected
    exact ⟨pair.1, pair.2, prime, bounded, large_type,
      partner_prime, large, endpoint, equal.symm⟩
  · rintro ⟨s, q, prime, bounded, large_type, partner_prime,
      large, endpoint, equal⟩
    subst target
    exact Finset.mem_image.mpr
      ⟨⟨s, q⟩, Finset.mem_filter.mpr
        ⟨(mem_fixedCoreTypedSemiprimePairs positive).mpr
          ⟨prime, bounded, partner_prime, large, endpoint⟩, large_type⟩,
        rfl⟩

/-- Low type eligibility on an actual adaptive support is EXACTLY the
additional physical scale inequality `s ≤ T`. -/
theorem scaleAdaptiveGlobalLowType_eligible_iff
    {scale cutoff s : ℕ} :
    s ∈ adaptiveLowPrimeSupport scale cutoff ↔
      s.Prime ∧ s ≤ cutoff ∧ s ≤ scale := by
  rw [mem_adaptiveLowPrimeSupport]
  tauto

/-- Every high deficient type belongs to the actual high support; the
historical strict inequality `s < z` is stronger than its closed endpoint. -/
theorem scaleAdaptiveGlobalHighType_eligible
    {parameter cutoff s : ℕ}
    (prime : s.Prime) (small : s < parameter) (large : cutoff < s) :
    s ∈ adaptiveHighPrimeSupport parameter cutoff := by
  exact mem_adaptiveHighPrimeSupport.mpr
    ⟨prime, large, Nat.le_of_lt small⟩

/-- Every genuine proper prime power inside the original closed target
interval belongs to the explicit finite power exception. -/
theorem scaleAdaptiveGlobalProperPower_mem_exceptions
    {length p exponent : ℕ} (prime : p.Prime)
    (proper : 2 ≤ exponent) (bounded : p ^ exponent ≤ length) :
    p ^ exponent ∈ scaleAdaptiveGlobalProperPowerExceptions length := by
  have positive : 0 < p ^ exponent := pow_pos prime.pos exponent
  have square_le : p ^ 2 ≤ p ^ exponent :=
    Nat.pow_le_pow_right prime.pos proper
  have root_bound : p ≤ length.sqrt :=
    Nat.le_sqrt'.mpr (square_le.trans bounded)
  have binary_bound : 2 ^ exponent ≤ length :=
    (Nat.pow_le_pow_left prime.two_le exponent).trans bounded
  have exponent_bound : exponent ≤ Nat.log 2 length :=
    Nat.le_log_of_pow_le (by norm_num) binary_bound
  apply Finset.mem_inter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, bounded⟩, ?_⟩
  exact Finset.mem_image.mpr
    ⟨(p, exponent), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩, rfl⟩

/-- Exact elementary finite complexity bound for the true proper-power
exception; no prime-number theorem or prime-pattern estimate is used. -/
theorem scaleAdaptiveGlobalProperPowerExceptions_card_le
    (length : ℕ) :
    (scaleAdaptiveGlobalProperPowerExceptions length).card ≤
      (length.sqrt + 1) * (Nat.log 2 length + 1) := by
  unfold scaleAdaptiveGlobalProperPowerExceptions
  calc
    (Finset.Icc 1 length ∩
        (((Finset.range (length.sqrt + 1)).product
          (Finset.range (Nat.log 2 length + 1))).image
            fun pair : ℕ × ℕ => pair.1 ^ pair.2)).card ≤
      (((Finset.range (length.sqrt + 1)).product
          (Finset.range (Nat.log 2 length + 1))).image
            fun pair : ℕ × ℕ => pair.1 ^ pair.2).card :=
        Finset.card_le_card Finset.inter_subset_right
    _ ≤ ((Finset.range (length.sqrt + 1)).product
          (Finset.range (Nat.log 2 length + 1))).card :=
        Finset.card_image_le
    _ = _ := by simp

/-- Both complete colored target families remain inside the original closed
interval; in particular large primes retain their actual endpoint. -/
theorem scaleAdaptiveGlobalLowTargets_subset_interval
    {length parameter cutoff : ℕ} (positive : 0 < parameter) :
    scaleAdaptiveGlobalLowTargets length parameter cutoff ⊆
      Finset.Icc 1 length := by
  intro target selected
  rcases Finset.mem_union.mp selected with prime | semiprime
  · obtain ⟨prime, _, bounded⟩ := mem_fixedCoreLargePrimeTargets.mp prime
    exact Finset.mem_Icc.mpr ⟨prime.one_le, bounded⟩
  · obtain ⟨s, q, sprime, _, _, qprime, _, bounded, equal⟩ :=
      (mem_scaleAdaptiveGlobalLowSemiprimeTargets positive).mp semiprime
    subst target
    exact Finset.mem_Icc.mpr
      ⟨(Nat.mul_pos sprime.pos qprime.pos), bounded⟩

theorem scaleAdaptiveGlobalHighTargets_subset_interval
    {length parameter cutoff : ℕ} (positive : 0 < parameter) :
    scaleAdaptiveGlobalHighTargets length parameter cutoff ⊆
      Finset.Icc 1 length := by
  intro target selected
  rcases Finset.mem_union.mp selected with prime | semiprime
  · obtain ⟨prime, _, bounded⟩ := mem_fixedCoreLargePrimeTargets.mp prime
    exact Finset.mem_Icc.mpr ⟨prime.one_le, bounded⟩
  · obtain ⟨s, q, sprime, _, _, qprime, _, bounded, equal⟩ :=
      (mem_scaleAdaptiveGlobalHighSemiprimeTargets positive).mp semiprime
    subst target
    exact Finset.mem_Icc.mpr
      ⟨(Nat.mul_pos sprime.pos qprime.pos), bounded⟩

/-- Every exceptional family, including all moving endpoints, is supported
on the original closed target interval. -/
theorem scaleAdaptiveGlobalTargetExceptions_subset_interval
    (length parameter : ℕ) (exponents : Finset ℕ) :
    scaleAdaptiveGlobalTargetExceptions length parameter exponents ⊆
      Finset.Icc 1 length := by
  intro target selected
  rcases Finset.mem_union.mp selected with base | boundary
  · rcases Finset.mem_union.mp base with endpoint | power
    · exact (Finset.mem_inter.mp endpoint).1
    · exact (Finset.mem_inter.mp power).1
  · obtain ⟨exponent, _, selected⟩ := Finset.mem_biUnion.mp boundary
    exact (Finset.mem_filter.mp selected).1

/-- EXACT original two-hit demand after removing the explicit exceptions.
Every large prime is in both colors, every deficient semiprime is in exactly
its supported color, and no prime power, small prime, or endpoint is omitted. -/
theorem scaleAdaptiveGlobalColoredTargetDemand
    {length parameter cutoff : ℕ} (exponents : Finset ℕ)
    (positive : 0 < parameter)
    (square_threshold : parameter ≤ length / parameter) :
    ∀ target ∈ Finset.Icc 1 length,
      target ∉ scaleAdaptiveGlobalTargetExceptions
        length parameter exponents →
      2 ≤ fixedParameterCoreHits length parameter target +
        (if target ∈ scaleAdaptiveGlobalLowTargets
          length parameter cutoff then 1 else 0) +
        (if target ∈ scaleAdaptiveGlobalHighTargets
          length parameter cutoff then 1 else 0) := by
  intro target interval not_exception
  by_cases already : 2 ≤ fixedParameterCoreHits length parameter target
  · omega
  have deficient : target ∈ deficientTargets length
      (fixedParameterCorePrimes length parameter)
      (fixedParameterCoreSquared length parameter) (fun _ => 0) := by
    apply Finset.mem_filter.mpr
    exact ⟨interval, by
      change fixedParameterCoreHits length parameter target < 2
      omega⟩
  have target_type := deficient_fixedParameterCore_has_exact_type
    positive square_threshold deficient
  rcases target_type with one | prime | semiprime | power
  · apply False.elim
    apply not_exception
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_inter.mpr
      ⟨interval, Finset.mem_union_left _ (Finset.mem_singleton.mpr one)⟩
  · by_cases small : target ≤ length / parameter
    · apply False.elim
      apply not_exception
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_inter.mpr
      exact ⟨interval, Finset.mem_union_right _
        (Nat.mem_primesLE.mpr ⟨small, prime⟩)⟩
    · have large : length / parameter < target := by omega
      have selected : target ∈
          fixedCoreLargePrimeTargets length parameter :=
        mem_fixedCoreLargePrimeTargets.mpr
          ⟨prime, large, (Finset.mem_Icc.mp interval).2⟩
      have low : target ∈ scaleAdaptiveGlobalLowTargets
          length parameter cutoff := Finset.mem_union_left _ selected
      have high : target ∈ scaleAdaptiveGlobalHighTargets
          length parameter cutoff := Finset.mem_union_left _ selected
      simp [low, high]
  · obtain ⟨s, q, sprime, qprime, small, large, equal⟩ := semiprime
    have bounded : s * q ≤ length := by
      rw [← equal]
      exact (Finset.mem_Icc.mp interval).2
    have hits : fixedParameterCoreHits length parameter target = 1 := by
      rw [equal]
      exact fixedParameterCoreHits_typed_semiprime
        square_threshold sprime qprime small large
    by_cases low_type : s ≤ cutoff
    · have typed : target ∈ scaleAdaptiveGlobalLowSemiprimeTargets
          length parameter cutoff :=
        (mem_scaleAdaptiveGlobalLowSemiprimeTargets positive).mpr
          ⟨s, q, sprime, small, low_type, qprime,
            large, bounded, equal⟩
      have low : target ∈ scaleAdaptiveGlobalLowTargets
          length parameter cutoff := Finset.mem_union_right _ typed
      simp [hits, low]
    · have high_type : cutoff < s := by omega
      have typed : target ∈ scaleAdaptiveGlobalHighSemiprimeTargets
          length parameter cutoff :=
        (mem_scaleAdaptiveGlobalHighSemiprimeTargets positive).mpr
          ⟨s, q, sprime, small, high_type, qprime,
            large, bounded, equal⟩
      have high : target ∈ scaleAdaptiveGlobalHighTargets
          length parameter cutoff := Finset.mem_union_right _ typed
      simp [hits, high]
  · obtain ⟨p, exponent, prime, _, _, proper, equal⟩ := power
    apply False.elim
    apply not_exception
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [equal]
    apply scaleAdaptiveGlobalProperPower_mem_exceptions prime proper
    rw [← equal]
    exact (Finset.mem_Icc.mp interval).2

/-- Explicit real bound for the actual proper-power exception.  Its exponent
is the genuine square-root exponent, stronger than the fourth-power slack
needed to dispose of this family. -/
theorem scaleAdaptiveGlobalProperPowerExceptions_card_real_le
    {length : ℕ} (large : 2 ≤ length) :
    ((scaleAdaptiveGlobalProperPowerExceptions length).card : ℝ) ≤
      (4 / Real.log 2) * (length : ℝ) ^ (1 / 2 : ℝ) *
        Real.log (length : ℝ) := by
  have real_positive : (0 : ℝ) < length := by exact_mod_cast (by omega : 0 < length)
  have real_one : (1 : ℝ) ≤ length := by exact_mod_cast (by omega : 1 ≤ length)
  have log_two : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have log_mono : Real.log (2 : ℝ) ≤ Real.log (length : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast large)
  have root_one : (1 : ℝ) ≤ Real.sqrt (length : ℝ) :=
    Real.one_le_sqrt.mpr real_one
  have root_nat : (length.sqrt : ℝ) ≤ Real.sqrt (length : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have root_bound :
      (length.sqrt : ℝ) + 1 ≤ 2 * (length : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    linarith
  have binary := Real.natLog_le_logb length 2
  simp only [Real.logb, Nat.cast_ofNat] at binary
  have log_one : (1 : ℝ) ≤ Real.log (length : ℝ) / Real.log 2 :=
    (le_div_iff₀ log_two).mpr (by simpa using log_mono)
  have log_bound :
      (Nat.log 2 length : ℝ) + 1 ≤
        2 * (Real.log (length : ℝ) / Real.log 2) := by
    linarith
  have finite_bound :
      ((scaleAdaptiveGlobalProperPowerExceptions length).card : ℝ) ≤
        ((length.sqrt : ℝ) + 1) * ((Nat.log 2 length : ℝ) + 1) := by
    exact_mod_cast scaleAdaptiveGlobalProperPowerExceptions_card_le length
  calc
    ((scaleAdaptiveGlobalProperPowerExceptions length).card : ℝ) ≤
        ((length.sqrt : ℝ) + 1) * ((Nat.log 2 length : ℝ) + 1) :=
      finite_bound
    _ ≤ (2 * (length : ℝ) ^ (1 / 2 : ℝ)) *
          (2 * (Real.log (length : ℝ) / Real.log 2)) := by
      gcongr
    _ = (4 / Real.log 2) * (length : ℝ) ^ (1 / 2 : ℝ) *
          Real.log (length : ℝ) := by ring

/-- Proper prime powers have ZERO density on the actual original prime
scale `Y / log Y`; they are never silently treated as absent. -/
theorem scaleAdaptiveGlobalProperPowerExceptions_normalized_tendsto_zero :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalProperPowerExceptions length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  let constant : ℝ := 4 / Real.log 2
  have log_squared :
      Tendsto
        (fun length : ℕ =>
          Real.log (length : ℝ) ^ 2 /
            (length : ℝ) ^ (1 / 2 : ℝ))
        atTop (nhds (0 : ℝ)) := by
    have real_limit :=
      (isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : 0 < (1 / 2 : ℝ))).tendsto_div_nhds_zero
    simpa [Function.comp_def, Real.rpow_two] using
      real_limit.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have upper : Tendsto
      (fun length : ℕ => constant *
        (Real.log (length : ℝ) ^ 2 /
          (length : ℝ) ^ (1 / 2 : ℝ)))
      atTop (nhds (0 : ℝ)) := by
    simpa using log_squared.const_mul constant
  apply squeeze_zero' _ _ upper
  · filter_upwards [eventually_ge_atTop 2] with length large
    have real_one : (1 : ℝ) ≤ length := by
      exact_mod_cast (by omega : 1 ≤ length)
    positivity
  · filter_upwards [eventually_ge_atTop 2] with length large
    have real_positive : (0 : ℝ) < length := by
      exact_mod_cast (by omega : 0 < length)
    have log_positive : 0 < Real.log (length : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < length))
    have root_positive : 0 < (length : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos real_positive _
    have card_bound :=
      scaleAdaptiveGlobalProperPowerExceptions_card_real_le large
    change ((scaleAdaptiveGlobalProperPowerExceptions length).card : ℝ) ≤
      constant * (length : ℝ) ^ (1 / 2 : ℝ) *
        Real.log (length : ℝ) at card_bound
    have root_square :
        (length : ℝ) ^ (1 / 2 : ℝ) *
          (length : ℝ) ^ (1 / 2 : ℝ) = (length : ℝ) := by
      rw [← Real.rpow_add real_positive]
      norm_num
    calc
      ((scaleAdaptiveGlobalProperPowerExceptions length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ) ≤
        (constant * (length : ℝ) ^ (1 / 2 : ℝ) *
          Real.log (length : ℝ)) *
            Real.log (length : ℝ) / (length : ℝ) := by
          gcongr
      _ = constant * (Real.log (length : ℝ) ^ 2 /
          (length : ℝ) ^ (1 / 2 : ℝ)) := by
          field_simp [real_positive.ne', root_positive.ne']
          rw [pow_two, root_square]

/-- A fixed finite family of moving physical target-cell endpoints is
negligible at the ORIGINAL normalization, despite exact integer flooring. -/
theorem scaleAdaptiveGlobalMovingBoundaryExceptions_normalized_tendsto_zero
    (exponents : Finset ℕ) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalMovingBoundaryExceptions length exponents).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveGlobalMovingBoundaryExceptions
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro exponent _
  exact scaleAdaptiveDyadicTargetBoundaries_normalized_tendsto_zero exponent

/-- The small prime exceptions have their TRUE nonzero leading coefficient
`1/z`.  Fixed `z` is held fixed before the interval endpoint tends to infinity. -/
theorem scaleAdaptiveGlobalSmallPrimeExceptions_normalized_tendsto
    (parameter : ℕ) (positive : 0 < parameter) :
    Tendsto
      (fun length : ℕ =>
        ((Nat.primesLE (length / parameter)).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds ((parameter : ℝ)⁻¹)) := by
  simpa [Nat.primesLE_card_eq_primeCounting, div_div_eq_mul_div] using
    primeCounting_fixed_cutoff_normalized_tendsto parameter positive

/-- Every actual small prime really is in the global exception family; the
fixed-core prime contribution therefore cannot be called negligible. -/
theorem scaleAdaptiveGlobalSmallPrimes_subset_exceptions
    (length parameter : ℕ) (exponents : Finset ℕ) :
    Nat.primesLE (length / parameter) ⊆
      scaleAdaptiveGlobalTargetExceptions length parameter exponents := by
  intro target selected
  obtain ⟨bounded, prime⟩ := Nat.mem_primesLE.mp selected
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_inter.mpr
  refine ⟨Finset.mem_Icc.mpr
    ⟨prime.one_le, bounded.trans (Nat.div_le_self length parameter)⟩, ?_⟩
  exact Finset.mem_union_right _ selected

/-- Explicit global count of every exception, including the original
endpoint and every genuinely moving physical-cell boundary. -/
theorem scaleAdaptiveGlobalTargetExceptions_card_le
    (length parameter : ℕ) (exponents : Finset ℕ) :
    (scaleAdaptiveGlobalTargetExceptions
      length parameter exponents).card ≤
      1 + (Nat.primesLE (length / parameter)).card +
        (scaleAdaptiveGlobalProperPowerExceptions length).card +
        (scaleAdaptiveGlobalMovingBoundaryExceptions
          length exponents).card := by
  let base := Finset.Icc 1 length ∩
    ({1} ∪ Nat.primesLE (length / parameter))
  have base_bound : base.card ≤
      1 + (Nat.primesLE (length / parameter)).card := by
    calc
      base.card ≤ ({1} ∪ Nat.primesLE (length / parameter)).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ ≤ ({1} : Finset ℕ).card +
            (Nat.primesLE (length / parameter)).card :=
        Finset.card_union_le _ _
      _ = _ := by simp
  have first := Finset.card_union_le base
    (scaleAdaptiveGlobalProperPowerExceptions length)
  have second := Finset.card_union_le
    (base ∪ scaleAdaptiveGlobalProperPowerExceptions length)
    (scaleAdaptiveGlobalMovingBoundaryExceptions length exponents)
  change (base ∪ scaleAdaptiveGlobalProperPowerExceptions length ∪
    scaleAdaptiveGlobalMovingBoundaryExceptions length exponents).card ≤ _
  omega

/-- EXACT global cleanup coefficient.  Proper powers, endpoint `1`, and all
fixed-shell moving boundaries disappear; the small primes contribute the
unavoidable, retained coefficient `1/z`. -/
theorem scaleAdaptiveGlobalTargetExceptions_normalized_tendsto
    (parameter : ℕ) (exponents : Finset ℕ)
    (positive : 0 < parameter) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalTargetExceptions
          length parameter exponents).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds ((parameter : ℝ)⁻¹)) := by
  have small := scaleAdaptiveGlobalSmallPrimeExceptions_normalized_tendsto
    parameter positive
  have power :=
    scaleAdaptiveGlobalProperPowerExceptions_normalized_tendsto_zero
  have boundary :=
    scaleAdaptiveGlobalMovingBoundaryExceptions_normalized_tendsto_zero
      exponents
  have endpoint :
      Tendsto
        (fun length : ℕ => Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ)) := by
    have real_limit := Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 1 one_ne_zero
    simpa [Function.comp_def] using real_limit.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have upper : Tendsto
      (fun length : ℕ =>
        ((1 : ℝ) + ((Nat.primesLE (length / parameter)).card : ℝ) +
          ((scaleAdaptiveGlobalProperPowerExceptions length).card : ℝ) +
          ((scaleAdaptiveGlobalMovingBoundaryExceptions
            length exponents).card : ℝ)) *
              Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds ((parameter : ℝ)⁻¹)) := by
    convert ((endpoint.add small).add power).add boundary using 1
    · ext length
      ring
    · simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    small upper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with length large
    have cardinal := Finset.card_le_card
      (scaleAdaptiveGlobalSmallPrimes_subset_exceptions
        length parameter exponents)
    have log_nonnegative : 0 ≤ Real.log (length : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ length)
    have length_nonnegative : 0 ≤ (length : ℝ) := Nat.cast_nonneg _
    have real_cardinal :
        ((Nat.primesLE (length / parameter)).card : ℝ) ≤
          ((scaleAdaptiveGlobalTargetExceptions
            length parameter exponents).card : ℝ) := by
      exact_mod_cast cardinal
    gcongr
  · filter_upwards [eventually_ge_atTop 2] with length large
    have cardinal := scaleAdaptiveGlobalTargetExceptions_card_le
      length parameter exponents
    have real_cardinal :
        ((scaleAdaptiveGlobalTargetExceptions
          length parameter exponents).card : ℝ) ≤
            (1 : ℝ) + ((Nat.primesLE (length / parameter)).card : ℝ) +
              ((scaleAdaptiveGlobalProperPowerExceptions length).card : ℝ) +
              ((scaleAdaptiveGlobalMovingBoundaryExceptions
                length exponents).card : ℝ) := by
      exact_mod_cast cardinal
    have log_nonnegative : 0 ≤ Real.log (length : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ length)
    have length_nonnegative : 0 ≤ (length : ℝ) := Nat.cast_nonneg _
    gcongr

/-- A genuine finite union of two independently negligible ACTUAL target
sets is negligible at the same original normalization. -/
theorem scaleAdaptiveGlobalBadUnion_normalized_tendsto_zero
    (first second : ℕ → Finset ℕ)
    (first_negligible : Tendsto
      (fun length : ℕ => ((first length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ)) atTop (nhds (0 : ℝ)))
    (second_negligible : Tendsto
      (fun length : ℕ => ((second length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ)) atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ => ((first length ∪ second length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ)) atTop (nhds (0 : ℝ)) := by
  have union := scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
    (Finset.univ : Finset Bool)
    (fun choice length => if choice then second length else first length)
    (by
      intro choice _
      cases choice
      · simpa using first_negligible
      · simpa using second_negligible)
  simpa [Finset.union_comm] using union

/-- All actual bad semiprime targets across every true small-prime type and
every physically ELIGIBLE shell.  Shells not supporting the type are not
pretended to supply that type. -/
noncomputable def scaleAdaptiveGlobalSupportedSemiprimeBadTargets
    (parameter : ℕ) (exponents : Finset ℕ)
    (support : ℕ → Finset ℕ) (lower upper : ℝ)
    (length : ℕ) : Finset ℕ :=
  (Nat.primesLE (parameter - 1)).biUnion fun targetType =>
    scaleAdaptiveMultiShellSemiprimeBadTargets
      (exponents.filter fun exponent => targetType ∈ support exponent)
      support targetType lower upper length

/-- The finite union over every genuine typed semiprime has zero ORIGINAL
prime-scale density, with the exact support-dependent eligible-shell filter. -/
theorem scaleAdaptiveGlobalSupportedSemiprimeBadTargets_normalized_tendsto_zero
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ) (exponents : Finset ℕ)
    (support : ℕ → Finset ℕ) (lower upper : ℝ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ support exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalSupportedSemiprimeBadTargets
          parameter exponents support lower upper length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveGlobalSupportedSemiprimeBadTargets
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro targetType _
  apply scaleAdaptiveMultiShellSemiprimeBadTargets_global_tendsto_zero_of_GTZ
    green_tao (exponents.filter fun exponent => targetType ∈ support exponent)
    support targetType lower upper
  · intro exponent selected prime selected_prime
    exact primes exponent (Finset.mem_filter.mp selected).1
      prime selected_prime
  · intro exponent selected
    exact (Finset.mem_filter.mp selected).2
  · exact lower_nonnegative
  · exact band_nonempty
  · exact upper_bounded

/-- All bad ACTUAL prime and semiprime targets for BOTH colored shell
families, preserving shared outcomes, integer degrees, and every true type. -/
noncomputable def scaleAdaptiveGlobalActualPatternBadTargets
    (parameter : ℕ) (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ) (length : ℕ) : Finset ℕ :=
  (scaleAdaptiveMultiShellPrimeBadTargets
      lowExponents lowSupport lower upper length ∪
    scaleAdaptiveMultiShellPrimeBadTargets
      highExponents highSupport lower upper length) ∪
  (scaleAdaptiveGlobalSupportedSemiprimeBadTargets
      parameter lowExponents lowSupport lower upper length ∪
    scaleAdaptiveGlobalSupportedSemiprimeBadTargets
      parameter highExponents highSupport lower upper length)

/-- The entire BOTH-color actual-pattern bad union has zero original-scale
density under the sole explicit fixed-parameter signed Green--Tao input. -/
theorem scaleAdaptiveGlobalActualPatternBadTargets_normalized_tendsto_zero
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ) (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (low_primes : ∀ exponent ∈ lowExponents,
      ∀ prime ∈ lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ highExponents,
      ∀ prime ∈ highSupport exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalActualPatternBadTargets
          parameter lowExponents highExponents lowSupport highSupport
          lower upper length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveGlobalActualPatternBadTargets
  apply scaleAdaptiveGlobalBadUnion_normalized_tendsto_zero
  · apply scaleAdaptiveGlobalBadUnion_normalized_tendsto_zero
    · exact scaleAdaptiveMultiShellPrimeBadTargets_global_tendsto_zero_of_GTZ
        green_tao lowExponents lowSupport lower upper low_primes
          lower_nonnegative band_nonempty upper_bounded
    · exact scaleAdaptiveMultiShellPrimeBadTargets_global_tendsto_zero_of_GTZ
        green_tao highExponents highSupport lower upper high_primes
          lower_nonnegative band_nonempty upper_bounded
  · apply scaleAdaptiveGlobalBadUnion_normalized_tendsto_zero
    · exact
        scaleAdaptiveGlobalSupportedSemiprimeBadTargets_normalized_tendsto_zero
          green_tao parameter lowExponents lowSupport lower upper low_primes
            lower_nonnegative band_nonempty upper_bounded
    · exact
        scaleAdaptiveGlobalSupportedSemiprimeBadTargets_normalized_tendsto_zero
          green_tao parameter highExponents highSupport lower upper high_primes
            lower_nonnegative band_nonempty upper_bounded

/-- COMPLETE actual exceptions for the joint colored construction: original
core-deficiency exceptions, BOTH moving shell families, and every actual
both-color prime/semiprime bad-pattern target, restricted to the true domain. -/
noncomputable def scaleAdaptiveGlobalCompleteTargetExceptions
    (length parameter : ℕ)
    (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ) : Finset ℕ :=
  scaleAdaptiveGlobalTargetExceptions
    length parameter (lowExponents ∪ highExponents) ∪
      (Finset.Icc 1 length ∩
        scaleAdaptiveGlobalActualPatternBadTargets
          parameter lowExponents highExponents
            lowSupport highSupport lower upper length)

/-- The full actual exceptional union stays within the exact original
closed target interval. -/
theorem scaleAdaptiveGlobalCompleteTargetExceptions_subset_interval
    (length parameter : ℕ)
    (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ) :
    scaleAdaptiveGlobalCompleteTargetExceptions
      length parameter lowExponents highExponents
        lowSupport highSupport lower upper ⊆ Finset.Icc 1 length := by
  intro target selected
  rcases Finset.mem_union.mp selected with base | bad
  · exact scaleAdaptiveGlobalTargetExceptions_subset_interval
      length parameter (lowExponents ∪ highExponents) base
  · exact (Finset.mem_inter.mp bad).1

/-- Full original TWO-hit demand after deleting the actual BOTH-color
prime-pattern exceptions; no missing type, color, endpoint, or prime power. -/
theorem scaleAdaptiveGlobalCompleteColoredTargetDemand
    {length parameter cutoff : ℕ}
    (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (positive : 0 < parameter)
    (square_threshold : parameter ≤ length / parameter) :
    ∀ target ∈ Finset.Icc 1 length,
      target ∉ scaleAdaptiveGlobalCompleteTargetExceptions
        length parameter lowExponents highExponents
          lowSupport highSupport lower upper →
      2 ≤ fixedParameterCoreHits length parameter target +
        (if target ∈ scaleAdaptiveGlobalLowTargets
          length parameter cutoff then 1 else 0) +
        (if target ∈ scaleAdaptiveGlobalHighTargets
          length parameter cutoff then 1 else 0) := by
  intro target interval outside
  apply scaleAdaptiveGlobalColoredTargetDemand
    (lowExponents ∪ highExponents) positive square_threshold
      target interval
  intro selected
  exact outside (Finset.mem_union_left _ selected)

/-- Even after deleting ALL actual both-color, all-type, all-shell bad
targets, the exact exceptional cleanup coefficient remains `1/z`. -/
theorem scaleAdaptiveGlobalCompleteTargetExceptions_normalized_tendsto
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ) (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (positive : 0 < parameter)
    (low_primes : ∀ exponent ∈ lowExponents,
      ∀ prime ∈ lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ highExponents,
      ∀ prime ∈ highSupport exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalCompleteTargetExceptions
          length parameter lowExponents highExponents
            lowSupport highSupport lower upper).card : ℝ) *
              Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds ((parameter : ℝ)⁻¹)) := by
  have base := scaleAdaptiveGlobalTargetExceptions_normalized_tendsto
    parameter (lowExponents ∪ highExponents) positive
  have bad := scaleAdaptiveGlobalActualPatternBadTargets_normalized_tendsto_zero
    green_tao parameter lowExponents highExponents
      lowSupport highSupport lower upper low_primes high_primes
        lower_nonnegative band_nonempty upper_bounded
  have upper_limit : Tendsto
      (fun length : ℕ =>
        (((scaleAdaptiveGlobalTargetExceptions
          length parameter (lowExponents ∪ highExponents)).card : ℝ) +
          ((scaleAdaptiveGlobalActualPatternBadTargets
            parameter lowExponents highExponents
              lowSupport highSupport lower upper length).card : ℝ)) *
                Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds ((parameter : ℝ)⁻¹)) := by
    convert base.add bad using 1
    · ext length
      ring
    · simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    base upper_limit ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with length large
    have cardinal := Finset.card_le_card (Finset.subset_union_left :
      scaleAdaptiveGlobalTargetExceptions
        length parameter (lowExponents ∪ highExponents) ⊆
          scaleAdaptiveGlobalCompleteTargetExceptions
            length parameter lowExponents highExponents
              lowSupport highSupport lower upper)
    have log_nonnegative : 0 ≤ Real.log (length : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ length)
    have length_nonnegative : 0 ≤ (length : ℝ) := Nat.cast_nonneg _
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast cardinal)
        log_nonnegative) length_nonnegative
  · filter_upwards [eventually_ge_atTop 2] with length large
    have union_card := Finset.card_union_le
      (scaleAdaptiveGlobalTargetExceptions
        length parameter (lowExponents ∪ highExponents))
      (Finset.Icc 1 length ∩
        scaleAdaptiveGlobalActualPatternBadTargets
          parameter lowExponents highExponents
            lowSupport highSupport lower upper length)
    have intersection_card := Finset.card_le_card
      (Finset.inter_subset_right :
        Finset.Icc 1 length ∩
          scaleAdaptiveGlobalActualPatternBadTargets
            parameter lowExponents highExponents
              lowSupport highSupport lower upper length ⊆
          scaleAdaptiveGlobalActualPatternBadTargets
            parameter lowExponents highExponents
              lowSupport highSupport lower upper length)
    have cardinal :
        (scaleAdaptiveGlobalCompleteTargetExceptions
          length parameter lowExponents highExponents
            lowSupport highSupport lower upper).card ≤
          (scaleAdaptiveGlobalTargetExceptions
            length parameter (lowExponents ∪ highExponents)).card +
            (scaleAdaptiveGlobalActualPatternBadTargets
              parameter lowExponents highExponents
                lowSupport highSupport lower upper length).card := by
      change
        (scaleAdaptiveGlobalTargetExceptions
          length parameter (lowExponents ∪ highExponents) ∪
          (Finset.Icc 1 length ∩
            scaleAdaptiveGlobalActualPatternBadTargets
              parameter lowExponents highExponents
                lowSupport highSupport lower upper length)).card ≤ _
      omega
    have real_cardinal :
        ((scaleAdaptiveGlobalCompleteTargetExceptions
          length parameter lowExponents highExponents
            lowSupport highSupport lower upper).card : ℝ) ≤
          ((scaleAdaptiveGlobalTargetExceptions
            length parameter (lowExponents ∪ highExponents)).card : ℝ) +
            ((scaleAdaptiveGlobalActualPatternBadTargets
              parameter lowExponents highExponents
                lowSupport highSupport lower upper length).card : ℝ) := by
      exact_mod_cast cardinal
    have log_nonnegative : 0 ≤ Real.log (length : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ length)
    have length_nonnegative : 0 ≤ (length : ℝ) := Nat.cast_nonneg _
    gcongr

/-- The true fixed-core cutoff has the same original-scale prime counting
coefficient `1/z` as the unavoidable small-prime target exceptions. -/
theorem scaleAdaptiveGlobalCorePrimeCount_normalized_tendsto
    (parameter : ℕ) (positive : 0 < parameter) :
    Tendsto
      (fun length : ℕ =>
        ((fixedParameterCorePrimes length parameter).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds ((parameter : ℝ)⁻¹)) := by
  simpa [fixedParameterCorePrimes] using
    scaleAdaptiveGlobalSmallPrimeExceptions_normalized_tendsto
      parameter positive

/-- Prime counting alone eventually supplies two distinct fresh cleanup
primes for every member of ANY family with true coefficient `1/z`, while
also excluding every actual fixed-core prime.  No reserve distribution or
prime-pattern estimate is hidden in this implication. -/
theorem scaleAdaptiveGlobalCleanupPrimeCounting_eventually
    (parameter : ℕ) (large_parameter : 3 < parameter)
    (exceptions : ℕ → Finset ℕ)
    (exception_density : Tendsto
      (fun length : ℕ => ((exceptions length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds ((parameter : ℝ)⁻¹))) :
    ∀ᶠ length : ℕ in atTop,
      2 * (exceptions length).card +
        (fixedParameterCorePrimes length parameter).card ≤
          Nat.primeCounting length := by
  have positive : 0 < parameter := by omega
  have core := scaleAdaptiveGlobalCorePrimeCount_normalized_tendsto
    parameter positive
  have cost : Tendsto
      (fun length : ℕ =>
        ((2 * (exceptions length).card +
          (fixedParameterCorePrimes length parameter).card : ℕ) : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds ((3 : ℝ) * (parameter : ℝ)⁻¹)) := by
    convert (exception_density.const_mul (2 : ℝ)).add core using 1
    · ext length
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · congr 1
      ring
  have supply : Tendsto
      (fun length : ℕ =>
        (Nat.primeCounting length : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (1 : ℝ)) := by
    simpa [div_div_eq_mul_div] using primeCounting_normalized_tendsto_one
  have parameter_positive : (0 : ℝ) < parameter := by
    exact_mod_cast positive
  have parameter_large : (3 : ℝ) < parameter := by
    exact_mod_cast large_parameter
  have inverse_positive : (0 : ℝ) < (parameter : ℝ)⁻¹ :=
    inv_pos.mpr parameter_positive
  have cancellation : (parameter : ℝ) * (parameter : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ parameter_positive.ne'
  have gap : 0 < (1 : ℝ) - 3 * (parameter : ℝ)⁻¹ := by
    have strict := mul_pos (sub_pos.mpr parameter_large) inverse_positive
    nlinarith
  have difference := supply.sub cost
  have eventually_positive :=
    difference.eventually (Ioi_mem_nhds gap)
  filter_upwards [eventually_positive, eventually_ge_atTop 2] with
    length separation large
  have real_positive : (0 : ℝ) < length := by
    exact_mod_cast (by omega : 0 < length)
  have log_positive : 0 < Real.log (length : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < length)
  have scale_positive : 0 < Real.log (length : ℝ) / (length : ℝ) :=
    div_pos log_positive real_positive
  have weighted :
      ((2 * (exceptions length).card +
        (fixedParameterCorePrimes length parameter).card : ℕ) : ℝ) *
          (Real.log (length : ℝ) / (length : ℝ)) <
        (Nat.primeCounting length : ℝ) *
          (Real.log (length : ℝ) / (length : ℝ)) := by
    change 0 <
      (Nat.primeCounting length : ℝ) *
          Real.log (length : ℝ) / (length : ℝ) -
        ((2 * (exceptions length).card +
          (fixedParameterCorePrimes length parameter).card : ℕ) : ℝ) *
            Real.log (length : ℝ) / (length : ℝ) at separation
    have ordering := sub_pos.mp separation
    simpa [mul_div_assoc] using ordering
  have real_count :
      ((2 * (exceptions length).card +
        (fixedParameterCorePrimes length parameter).card : ℕ) : ℝ) <
          (Nat.primeCounting length : ℝ) := by
    by_contra not_less
    have reversed := mul_le_mul_of_nonneg_right
      (le_of_not_gt not_less) scale_positive.le
    exact (not_lt_of_ge reversed) weighted
  have natural_count :
      2 * (exceptions length).card +
        (fixedParameterCorePrimes length parameter).card <
          Nat.primeCounting length := by
    exact_mod_cast real_count
  omega

/-- For the COMPLETE actual both-color exceptional target set, the genuine
prime number theorem alone supplies two fresh primes per exception. -/
theorem scaleAdaptiveGlobalCompleteCleanupPrimeCounting_eventually
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ) (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (large_parameter : 3 < parameter)
    (low_primes : ∀ exponent ∈ lowExponents,
      ∀ prime ∈ lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ highExponents,
      ∀ prime ∈ highSupport exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∀ᶠ length : ℕ in atTop,
      2 * (scaleAdaptiveGlobalCompleteTargetExceptions
        length parameter lowExponents highExponents
          lowSupport highSupport lower upper).card +
        (fixedParameterCorePrimes length parameter).card ≤
          Nat.primeCounting length := by
  apply scaleAdaptiveGlobalCleanupPrimeCounting_eventually
    parameter large_parameter
      (fun length => scaleAdaptiveGlobalCompleteTargetExceptions
        length parameter lowExponents highExponents
          lowSupport highSupport lower upper)
  exact scaleAdaptiveGlobalCompleteTargetExceptions_normalized_tendsto
    green_tao parameter lowExponents highExponents
      lowSupport highSupport lower upper (by omega)
        low_primes high_primes lower_nonnegative
          band_nonempty upper_bounded

/-- Actual fresh cleanup reserve, not merely an abstract cardinality: every
selected label is a genuine prime at most the original length, disjoint from
the true core, and at least TWO labels are available per complete exception. -/
theorem scaleAdaptiveGlobalCompleteFreshCleanupReserve_eventually
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ) (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (large_parameter : 3 < parameter)
    (low_primes : ∀ exponent ∈ lowExponents,
      ∀ prime ∈ lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ highExponents,
      ∀ prime ∈ highSupport exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∀ᶠ length : ℕ in atTop,
      ∃ reserve : Finset ℕ,
        (∀ prime ∈ reserve, prime.Prime) ∧
        Disjoint (fixedParameterCorePrimes length parameter) reserve ∧
        2 * (scaleAdaptiveGlobalCompleteTargetExceptions
          length parameter lowExponents highExponents
            lowSupport highSupport lower upper).card ≤ reserve.card ∧
        ∀ prime ∈ reserve, prime ≤ length := by
  filter_upwards [
    scaleAdaptiveGlobalCompleteCleanupPrimeCounting_eventually
      green_tao parameter lowExponents highExponents
        lowSupport highSupport lower upper large_parameter
          low_primes high_primes lower_nonnegative
            band_nonempty upper_bounded] with length supply
  exact fresh_bounded_prime_reserve_of_primeCounting
    (fixedParameterCorePrimes length parameter) length
    (scaleAdaptiveGlobalCompleteTargetExceptions
      length parameter lowExponents highExponents
        lowSupport highSupport lower upper).card supply

/-- Any genuine natural cleanup charge with normalized coefficient strictly
below one is eventually dominated by ordinary prime counting. -/
theorem scaleAdaptiveGlobalPrimeCountingDominates_eventually
    (charge : ℕ → ℕ) (coefficient : ℝ)
    (below_one : coefficient < 1)
    (charge_density : Tendsto
      (fun length : ℕ => (charge length : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds coefficient)) :
    ∀ᶠ length : ℕ in atTop, charge length ≤ Nat.primeCounting length := by
  have supply : Tendsto
      (fun length : ℕ =>
        (Nat.primeCounting length : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (1 : ℝ)) := by
    simpa [div_div_eq_mul_div] using primeCounting_normalized_tendsto_one
  have difference := supply.sub charge_density
  have gap : 0 < (1 : ℝ) - coefficient := sub_pos.mpr below_one
  have eventually_positive :=
    difference.eventually (Ioi_mem_nhds gap)
  filter_upwards [eventually_positive, eventually_ge_atTop 2] with
    length separation large
  have real_positive : (0 : ℝ) < length := by
    exact_mod_cast (by omega : 0 < length)
  have log_positive : 0 < Real.log (length : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < length)
  have scale_positive : 0 < Real.log (length : ℝ) / (length : ℝ) :=
    div_pos log_positive real_positive
  have weighted :
      (charge length : ℝ) *
          (Real.log (length : ℝ) / (length : ℝ)) <
        (Nat.primeCounting length : ℝ) *
          (Real.log (length : ℝ) / (length : ℝ)) := by
    change 0 <
      (Nat.primeCounting length : ℝ) *
          Real.log (length : ℝ) / (length : ℝ) -
        (charge length : ℝ) *
            Real.log (length : ℝ) / (length : ℝ) at separation
    simpa [mul_div_assoc] using (sub_pos.mp separation)
  have real_count : (charge length : ℝ) <
      (Nat.primeCounting length : ℝ) := by
    by_contra not_less
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right
      (le_of_not_gt not_less) scale_positive.le)) weighted
  have natural_count : charge length < Nat.primeCounting length := by
    exact_mod_cast real_count
  omega

/-- COMPLETE cleanup counting while retaining the actual selected prime
pool.  The true margin is `2δ + 1/z + ρ < 1`, where `δ` is the cleanup
deficit coefficient and `ρ` is the ACTUAL selected-prime density. -/
theorem scaleAdaptiveGlobalCleanupWithSelectedPrimeCounting_eventually
    (parameter : ℕ) (positive : 0 < parameter)
    (deficit : ℕ → ℕ) (selected : ℕ → Finset ℕ)
    (deficitCoefficient selectedCoefficient : ℝ)
    (deficit_density : Tendsto
      (fun length : ℕ => (deficit length : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds deficitCoefficient))
    (selected_density : Tendsto
      (fun length : ℕ => ((selected length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds selectedCoefficient))
    (margin : 2 * deficitCoefficient +
      (parameter : ℝ)⁻¹ + selectedCoefficient < 1) :
    ∀ᶠ length : ℕ in atTop,
      2 * deficit length +
        ((fixedParameterCorePrimes length parameter) ∪
          selected length).card ≤ Nat.primeCounting length := by
  have core := scaleAdaptiveGlobalCorePrimeCount_normalized_tendsto
    parameter positive
  have total_density : Tendsto
      (fun length : ℕ =>
        ((2 * deficit length +
          (fixedParameterCorePrimes length parameter).card +
          (selected length).card : ℕ) : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds
        (2 * deficitCoefficient +
          (parameter : ℝ)⁻¹ + selectedCoefficient)) := by
    convert ((deficit_density.const_mul (2 : ℝ)).add core).add
      selected_density using 1
    · ext length
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
  have dominates := scaleAdaptiveGlobalPrimeCountingDominates_eventually
    (fun length => 2 * deficit length +
      (fixedParameterCorePrimes length parameter).card +
        (selected length).card)
    (2 * deficitCoefficient +
      (parameter : ℝ)⁻¹ + selectedCoefficient)
    margin total_density
  filter_upwards [dominates] with length counting
  have union_bound := Finset.card_union_le
    (fixedParameterCorePrimes length parameter) (selected length)
  omega

/-- Exact global prime-counting supply after excluding BOTH the true fixed
core and every actual selected prime from all low/high dyadic shells. -/
theorem scaleAdaptiveGlobalCompleteShellCleanupPrimeCounting_eventually
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ) (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (positive : 0 < parameter)
    (low_primes : ∀ exponent ∈ lowExponents,
      ∀ prime ∈ lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ highExponents,
      ∀ prime ∈ highSupport exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (margin : 3 * (parameter : ℝ)⁻¹ +
      (∑ exponent ∈ lowExponents ∪ highExponents,
        (((2 ^ exponent : ℕ) : ℝ)⁻¹)) < 1) :
    ∀ᶠ length : ℕ in atTop,
      2 * (scaleAdaptiveGlobalCompleteTargetExceptions
        length parameter lowExponents highExponents
          lowSupport highSupport lower upper).card +
        ((fixedParameterCorePrimes length parameter) ∪
          ((lowExponents ∪ highExponents).biUnion
            (scaleAdaptiveDyadicPrimeShell length))).card ≤
              Nat.primeCounting length := by
  apply scaleAdaptiveGlobalCleanupWithSelectedPrimeCounting_eventually
    parameter positive
      (fun length =>
        (scaleAdaptiveGlobalCompleteTargetExceptions
          length parameter lowExponents highExponents
            lowSupport highSupport lower upper).card)
      (fun length =>
        (lowExponents ∪ highExponents).biUnion
          (scaleAdaptiveDyadicPrimeShell length))
      ((parameter : ℝ)⁻¹)
      (∑ exponent ∈ lowExponents ∪ highExponents,
        (((2 ^ exponent : ℕ) : ℝ)⁻¹))
  · exact scaleAdaptiveGlobalCompleteTargetExceptions_normalized_tendsto
      green_tao parameter lowExponents highExponents
        lowSupport highSupport lower upper positive
          low_primes high_primes lower_nonnegative
            band_nonempty upper_bounded
  · exact scaleAdaptiveDyadicPrimeShell_biUnion_global_normalized_tendsto
      (lowExponents ∪ highExponents)
  · convert margin using 1
    ring

/-- ACTUAL fresh cleanup primes remain after removing BOTH the original
core and every selected low/high shell label; no prime is reused. -/
theorem scaleAdaptiveGlobalCompleteFreshShellCleanupReserve_eventually
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ) (lowExponents highExponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (positive : 0 < parameter)
    (low_primes : ∀ exponent ∈ lowExponents,
      ∀ prime ∈ lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ highExponents,
      ∀ prime ∈ highSupport exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (margin : 3 * (parameter : ℝ)⁻¹ +
      (∑ exponent ∈ lowExponents ∪ highExponents,
        (((2 ^ exponent : ℕ) : ℝ)⁻¹)) < 1) :
    ∀ᶠ length : ℕ in atTop,
      ∃ reserve : Finset ℕ,
        (∀ prime ∈ reserve, prime.Prime) ∧
        Disjoint
          ((fixedParameterCorePrimes length parameter) ∪
            ((lowExponents ∪ highExponents).biUnion
              (scaleAdaptiveDyadicPrimeShell length))) reserve ∧
        2 * (scaleAdaptiveGlobalCompleteTargetExceptions
          length parameter lowExponents highExponents
            lowSupport highSupport lower upper).card ≤ reserve.card ∧
        ∀ prime ∈ reserve, prime ≤ length := by
  filter_upwards [
    scaleAdaptiveGlobalCompleteShellCleanupPrimeCounting_eventually
      green_tao parameter lowExponents highExponents
        lowSupport highSupport lower upper positive
          low_primes high_primes lower_nonnegative
            band_nonempty upper_bounded margin] with length supply
  exact fresh_bounded_prime_reserve_of_primeCounting
    ((fixedParameterCorePrimes length parameter) ∪
      ((lowExponents ∪ highExponents).biUnion
        (scaleAdaptiveDyadicPrimeShell length))) length
    (scaleAdaptiveGlobalCompleteTargetExceptions
      length parameter lowExponents highExponents
        lowSupport highSupport lower upper).card supply


end Erdos1139
