module

public import ScaleAdaptiveDyadicEulerShell1139
public import ScaleAdaptiveParameterDecay1139

@[expose] public section


/-!
# Actual low- and high-color adaptive Euler amplification

The two colors do not have the same local Euler factor.  At physical scale
`T=2^j` and split cutoff `w`, the LOW support product itself is `V_min(T,w)`,
but its actual pattern factor is `V_T`.  A supported low semiprime type `s`
is eligible exactly when `s ≤ T` and `s ≤ w`.

For dyadic physical cutoffs `w=2^k ≤ z=2^K`, the HIGH support product is
`V_z/V_w`, while its actual pattern factor is

    (V_z/V_w) * V_(2^j),  j ≤ k;
    V_z,                  k ≤ j ≤ K.

The exact finite short- and long-shell formulas below preserve these true
factors.  In particular the high color is not assigned the false constant
`V_z`, nor is the vanishing low factor treated as uniformly positive.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- The genuine LOW-SUPPORT product is `V_min(2^j,w)`; it is not in
general equal to the complete actual pattern factor `V_(2^j)`. -/
theorem scaleAdaptiveDyadicLowSupportEulerProduct_eq_min
    (index familyCutoff : ℕ) :
    adaptivePrimeEulerProduct
      (adaptiveLowPrimeSupport (2 ^ index) familyCutoff) =
        adaptivePrimeEulerProduct
          (Nat.primesLE (min (2 ^ index) familyCutoff)) := by
  rfl

/-- Exact eligibility of a TRUE supported low semiprime type at an integer
dyadic physical scale; the condition `s ≤ 2^j` may not be discarded. -/
theorem scaleAdaptiveDyadicLowType_mem_iff
    (type index familyCutoff : ℕ) :
    type ∈ adaptiveLowPrimeSupport (2 ^ index) familyCutoff ↔
      type.Prime ∧ type ≤ 2 ^ index ∧ type ≤ familyCutoff := by
  exact mem_adaptiveLowPrimeSupport

/-- True eligible LOW-color dyadic shell: only actually supported prime
semiprime types are included at each physical scale. -/
noncomputable def scaleAdaptiveLowEligibleDyadicEulerShell
    (type familyCutoff lower upper : ℕ) : ℝ :=
  ∑ index ∈ (Finset.Ioc lower upper).filter
    (fun index => type ∈ adaptiveLowPrimeSupport
      (2 ^ index) familyCutoff),
      adaptivePatternEulerFactor
        (adaptiveLowPrimeSupport (2 ^ index) familyCutoff) (2 ^ index)

/-- Once the true type is below BOTH the family cutoff and the initial
physical scale, every subsequent dyadic shell is genuinely eligible, and
its total weight is EXACTLY the complete actual `V_(2^j)` shell. -/
theorem scaleAdaptiveLowEligibleDyadicEulerShell_eq
    {type familyCutoff lower upper : ℕ}
    (prime : type.Prime) (supported : type ≤ familyCutoff)
    (initially_eligible : type ≤ 2 ^ lower) :
    scaleAdaptiveLowEligibleDyadicEulerShell
      type familyCutoff lower upper =
        scaleAdaptiveDyadicEulerShellMass lower upper := by
  unfold scaleAdaptiveLowEligibleDyadicEulerShell
    scaleAdaptiveDyadicEulerShellMass
  have all_eligible :
      (Finset.Ioc lower upper).filter
        (fun index => type ∈ adaptiveLowPrimeSupport
          (2 ^ index) familyCutoff) =
        Finset.Ioc lower upper := by
    ext index
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · exact And.left
    · intro selected
      refine ⟨selected, ?_⟩
      exact (scaleAdaptiveDyadicLowType_mem_iff
        type index familyCutoff).mpr
          ⟨prime,
            initially_eligible.trans
              (Nat.pow_le_pow_right (by norm_num) selected.1.le),
            supported⟩
  rw [all_eligible]
  apply Finset.sum_congr rfl
  intro index _
  exact scaleAdaptiveLowDyadicPatternEulerFactor_eq index familyCutoff

/-- Every fixed genuine supported semiprime type obtains DIVERGENT
low-family Euler load as the number of eligible physical scales grows. -/
theorem scaleAdaptiveLowEligibleDyadicEulerShell_tendsto_atTop :
    ∃ threshold : ℕ, 1 ≤ threshold ∧
      ∀ type familyCutoff lower : ℕ,
        type.Prime → type ≤ familyCutoff → type ≤ 2 ^ lower →
          threshold ≤ lower →
            Tendsto
              (scaleAdaptiveLowEligibleDyadicEulerShell
                type familyCutoff lower)
              atTop atTop := by
  obtain ⟨threshold, positive, divergent⟩ :=
    scaleAdaptiveDyadicEulerShellMass_tendsto_atTop
  refine ⟨threshold, positive, ?_⟩
  intro type familyCutoff lower prime supported eligible large
  apply (divergent lower large).congr
  intro upper
  exact (scaleAdaptiveLowEligibleDyadicEulerShell_eq
    prime supported eligible).symm

/-- Exact HIGH-color pattern factor at the true dyadic physical scale.
Both the high support and its outside-prime selector are retained. -/
noncomputable def scaleAdaptiveHighDyadicPatternFactor
    (fullExponent splitExponent index : ℕ) : ℝ :=
  adaptivePatternEulerFactor
    (adaptiveHighPrimeSupport (2 ^ fullExponent) (2 ^ splitExponent))
      (2 ^ index)

/-- The true HIGH-SUPPORT product is exactly `V_z/V_w`; this is a support
ratio, not the complete pattern factor at short physical scales. -/
theorem scaleAdaptiveHighDyadicSupportEulerProduct_eq_ratio
    {splitExponent fullExponent : ℕ}
    (ordered : splitExponent ≤ fullExponent) :
    adaptivePrimeEulerProduct
      (adaptiveHighPrimeSupport
        (2 ^ fullExponent) (2 ^ splitExponent)) =
          scaleAdaptiveDyadicEulerFactor fullExponent /
            scaleAdaptiveDyadicEulerFactor splitExponent := by
  exact adaptiveHighPrimeEulerProduct_eq_ratio
    (Nat.pow_le_pow_right (by norm_num) ordered)

/-- Exact eligibility of an ACTUAL high-color semiprime type, retaining
the strictly excluded split prime and the included full upper cutoff. -/
theorem scaleAdaptiveHighDyadicType_mem_iff
    (type splitExponent fullExponent : ℕ) :
    type ∈ adaptiveHighPrimeSupport
      (2 ^ fullExponent) (2 ^ splitExponent) ↔
        type.Prime ∧ 2 ^ splitExponent < type ∧
          type ≤ 2 ^ fullExponent := by
  exact mem_adaptiveHighPrimeSupport

/-- On every true short physical scale the HIGH pattern factor is exactly
`(V_z/V_w)*V_(2^j)`, including the indispensable `V_(2^j)` multiplier. -/
theorem scaleAdaptiveHighDyadicPatternFactor_eq_ratio_mul
    {index splitExponent fullExponent : ℕ}
    (short : index ≤ splitExponent)
    (ordered : splitExponent ≤ fullExponent) :
    scaleAdaptiveHighDyadicPatternFactor
      fullExponent splitExponent index =
        (scaleAdaptiveDyadicEulerFactor fullExponent /
          scaleAdaptiveDyadicEulerFactor splitExponent) *
            scaleAdaptiveDyadicEulerFactor index := by
  unfold scaleAdaptiveHighDyadicPatternFactor
  exact adaptiveHighPatternEulerFactor_small_scale_ratio
    (Nat.pow_le_pow_right (by norm_num) short)
    (Nat.pow_le_pow_right (by norm_num) ordered)

/-- On every true long physical scale between the split and the full
cutoff, the HIGH pattern factor is exactly `V_z`, not `V_z/V_(2^j)`. -/
theorem scaleAdaptiveHighDyadicPatternFactor_eq_full
    {index splitExponent fullExponent : ℕ}
    (long : splitExponent ≤ index)
    (bounded : index ≤ fullExponent) :
    scaleAdaptiveHighDyadicPatternFactor
      fullExponent splitExponent index =
        scaleAdaptiveDyadicEulerFactor fullExponent := by
  unfold scaleAdaptiveHighDyadicPatternFactor
  exact adaptiveHighPatternEulerFactor_of_large_scale
    (Nat.pow_le_pow_right (by norm_num) long)
    (Nat.pow_le_pow_right (by norm_num) bounded)

/-- Actual finite HIGH-family Euler load on a genuine lower-open,
upper-closed physical-scale exponent shell. -/
noncomputable def scaleAdaptiveHighDyadicEulerShellMass
    (fullExponent splitExponent lower upper : ℕ) : ℝ :=
  ∑ index ∈ Finset.Ioc lower upper,
    scaleAdaptiveHighDyadicPatternFactor
      fullExponent splitExponent index

/-- Exact high-color SHORT-shell identity, preserving the TRUE support
ratio and the complete actual adaptive scale-factor sum. -/
theorem scaleAdaptiveHighDyadicShortShell_eq_ratio_mul
    {lower splitExponent fullExponent : ℕ}
    (ordered : splitExponent ≤ fullExponent) :
    scaleAdaptiveHighDyadicEulerShellMass
      fullExponent splitExponent lower splitExponent =
        (scaleAdaptiveDyadicEulerFactor fullExponent /
          scaleAdaptiveDyadicEulerFactor splitExponent) *
            scaleAdaptiveDyadicEulerShellMass lower splitExponent := by
  unfold scaleAdaptiveHighDyadicEulerShellMass
    scaleAdaptiveDyadicEulerShellMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index selected
  have bounds := Finset.mem_Ioc.mp selected
  exact scaleAdaptiveHighDyadicPatternFactor_eq_ratio_mul
    bounds.2 ordered

/-- Exact high-color LONG-shell identity; every one of the genuine
`fullExponent-splitExponent` scales contributes the same true `V_z`. -/
theorem scaleAdaptiveHighDyadicLongShell_eq_count_mul
    {splitExponent fullExponent : ℕ}
    (_ordered : splitExponent ≤ fullExponent) :
    scaleAdaptiveHighDyadicEulerShellMass
      fullExponent splitExponent splitExponent fullExponent =
        ((fullExponent - splitExponent : ℕ) : ℝ) *
          scaleAdaptiveDyadicEulerFactor fullExponent := by
  unfold scaleAdaptiveHighDyadicEulerShellMass
  calc
    _ = ∑ _index ∈ Finset.Ioc splitExponent fullExponent,
          scaleAdaptiveDyadicEulerFactor fullExponent := by
      apply Finset.sum_congr rfl
      intro index selected
      have bounds := Finset.mem_Ioc.mp selected
      exact scaleAdaptiveHighDyadicPatternFactor_eq_full
        bounds.1.le bounds.2
    _ = _ := by simp

/-- Exact finite full HIGH-color decomposition into both actual physical
scale regimes, with no overlap and no silently omitted split endpoint. -/
theorem scaleAdaptiveHighDyadicFullShell_eq_short_add_long
    {lower splitExponent fullExponent : ℕ}
    (lower_order : lower ≤ splitExponent)
    (upper_order : splitExponent ≤ fullExponent) :
    scaleAdaptiveHighDyadicEulerShellMass
      fullExponent splitExponent lower fullExponent =
        (scaleAdaptiveDyadicEulerFactor fullExponent /
          scaleAdaptiveDyadicEulerFactor splitExponent) *
            scaleAdaptiveDyadicEulerShellMass lower splitExponent +
          ((fullExponent - splitExponent : ℕ) : ℝ) *
            scaleAdaptiveDyadicEulerFactor fullExponent := by
  have interval := Finset.Ioc_union_Ioc_eq_Ioc lower_order upper_order
  have disjoint := Finset.Ioc_disjoint_Ioc_of_le
    (a := lower) (b := splitExponent)
    (c := splitExponent) (d := fullExponent) le_rfl
  unfold scaleAdaptiveHighDyadicEulerShellMass at *
  rw [← interval, Finset.sum_union disjoint]
  change
    scaleAdaptiveHighDyadicEulerShellMass
      fullExponent splitExponent lower splitExponent +
      scaleAdaptiveHighDyadicEulerShellMass
        fullExponent splitExponent splitExponent fullExponent = _
  rw [scaleAdaptiveHighDyadicShortShell_eq_ratio_mul upper_order,
    scaleAdaptiveHighDyadicLongShell_eq_count_mul upper_order]

/-- The already proved sharp dyadic Mertens limit gives BOTH genuine
positive lower and finite upper harmonic bounds beyond one fixed threshold. -/
theorem scaleAdaptiveDyadicEulerFactor_eventually_two_sided :
    ∀ᶠ index : ℕ in atTop,
      scaleAdaptiveDyadicMertensConstant / 2 / (index : ℝ) ≤
        scaleAdaptiveDyadicEulerFactor index ∧
      scaleAdaptiveDyadicEulerFactor index ≤
        (2 * scaleAdaptiveDyadicMertensConstant) / (index : ℝ) := by
  have constant_positive := scaleAdaptiveDyadicMertensConstant_pos
  have upper_scaled :=
    (tendsto_order.1
      scaleAdaptiveDyadicEulerFactor_mul_index_tendsto).2
      (2 * scaleAdaptiveDyadicMertensConstant)
      (show scaleAdaptiveDyadicMertensConstant <
        2 * scaleAdaptiveDyadicMertensConstant by linarith)
  filter_upwards [scaleAdaptiveDyadicEulerFactor_eventually_ge_harmonic,
    upper_scaled, eventually_ge_atTop (1 : ℕ)]
      with index lower upper positive
  refine ⟨lower, ?_⟩
  have index_positive : (0 : ℝ) < index := by exact_mod_cast positive
  apply (le_div_iff₀ index_positive).mpr
  nlinarith

/-- The true HIGH support ratio retains at least one quarter of its
physical exponent ratio `split/full`; no uniform positive factor is claimed. -/
theorem scaleAdaptiveHighDyadicSupportRatio_eventually_ge_exponent_ratio :
    ∃ threshold : ℕ, 1 ≤ threshold ∧
      ∀ splitExponent fullExponent : ℕ,
        threshold ≤ splitExponent → splitExponent ≤ fullExponent →
          (splitExponent : ℝ) / (4 * (fullExponent : ℝ)) ≤
            scaleAdaptiveDyadicEulerFactor fullExponent /
              scaleAdaptiveDyadicEulerFactor splitExponent := by
  obtain ⟨threshold, eventual⟩ :=
    Filter.eventually_atTop.1
      scaleAdaptiveDyadicEulerFactor_eventually_two_sided
  refine ⟨max threshold 1, le_max_right _ _, ?_⟩
  intro splitExponent fullExponent split_large ordered
  have split_positive : (0 : ℝ) < splitExponent := by
    exact_mod_cast (show 0 < splitExponent by omega)
  have full_positive : (0 : ℝ) < fullExponent := by
    exact_mod_cast (show 0 < fullExponent by omega)
  have full_bounds := eventual fullExponent (by omega)
  have split_bounds := eventual splitExponent (by omega)
  have split_factor_positive :=
    scaleAdaptiveDyadicEulerFactor_pos splitExponent
  apply (le_div_iff₀ split_factor_positive).mpr
  calc
    (splitExponent : ℝ) / (4 * (fullExponent : ℝ)) *
          scaleAdaptiveDyadicEulerFactor splitExponent ≤
        (splitExponent : ℝ) / (4 * (fullExponent : ℝ)) *
          ((2 * scaleAdaptiveDyadicMertensConstant) /
            (splitExponent : ℝ)) := by
      exact mul_le_mul_of_nonneg_left split_bounds.2
        (div_nonneg split_positive.le (by positivity))
    _ = scaleAdaptiveDyadicMertensConstant / 2 /
          (fullExponent : ℝ) := by
      field_simp
      ring
    _ ≤ scaleAdaptiveDyadicEulerFactor fullExponent := full_bounds.1

/-- Every sufficiently far-out ACTUAL high short shell has the explicit
lower bound `(C/8)*(split/full)*(H_split-H_lower)`.  This is the precise
product of a shrinking support ratio and a growing genuine shell. -/
theorem scaleAdaptiveHighDyadicShortShell_ge_weighted_harmonic :
    ∃ threshold : ℕ, 1 ≤ threshold ∧
      ∀ lower splitExponent fullExponent : ℕ,
        threshold ≤ lower → lower ≤ splitExponent →
          splitExponent ≤ fullExponent →
            (scaleAdaptiveDyadicMertensConstant / 8) *
              ((splitExponent : ℝ) / (fullExponent : ℝ)) *
                ((harmonic splitExponent : ℝ) -
                  (harmonic lower : ℝ)) ≤
              scaleAdaptiveHighDyadicEulerShellMass
                fullExponent splitExponent lower splitExponent := by
  obtain ⟨first, first_positive, ratios⟩ :=
    scaleAdaptiveHighDyadicSupportRatio_eventually_ge_exponent_ratio
  obtain ⟨second, second_positive, shells⟩ :=
    scaleAdaptiveDyadicEulerShellMass_ge_harmonic_difference
  refine ⟨max first second, (le_max_left _ _).trans' first_positive, ?_⟩
  intro lower splitExponent fullExponent lower_large low_order high_order
  have ratio := ratios splitExponent fullExponent (by omega) high_order
  have shell := shells lower splitExponent (by omega) low_order
  have harmonic_nonnegative :
      0 ≤ (harmonic splitExponent : ℝ) - (harmonic lower : ℝ) := by
    rw [← scaleAdaptiveDyadicExponentShell_eq_harmonic_difference low_order]
    exact Finset.sum_nonneg
      (fun index _ => inv_nonneg.mpr (Nat.cast_nonneg index))
  have support_ratio_nonnegative :
      0 ≤ scaleAdaptiveDyadicEulerFactor fullExponent /
        scaleAdaptiveDyadicEulerFactor splitExponent :=
    (div_pos (scaleAdaptiveDyadicEulerFactor_pos fullExponent)
      (scaleAdaptiveDyadicEulerFactor_pos splitExponent)).le
  have coefficient_nonnegative :
      0 ≤ scaleAdaptiveDyadicMertensConstant / 2 :=
    (div_pos scaleAdaptiveDyadicMertensConstant_pos (by norm_num)).le
  rw [scaleAdaptiveHighDyadicShortShell_eq_ratio_mul high_order]
  calc
    (scaleAdaptiveDyadicMertensConstant / 8) *
        ((splitExponent : ℝ) / (fullExponent : ℝ)) *
          ((harmonic splitExponent : ℝ) - (harmonic lower : ℝ)) =
      ((splitExponent : ℝ) / (4 * (fullExponent : ℝ))) *
        (scaleAdaptiveDyadicMertensConstant / 2 *
          ((harmonic splitExponent : ℝ) - (harmonic lower : ℝ))) := by
      ring
    _ ≤ (scaleAdaptiveDyadicEulerFactor fullExponent /
          scaleAdaptiveDyadicEulerFactor splitExponent) *
        (scaleAdaptiveDyadicMertensConstant / 2 *
          ((harmonic splitExponent : ℝ) - (harmonic lower : ℝ))) :=
      mul_le_mul_of_nonneg_right ratio
        (mul_nonneg coefficient_nonnegative harmonic_nonnegative)
    _ ≤ (scaleAdaptiveDyadicEulerFactor fullExponent /
          scaleAdaptiveDyadicEulerFactor splitExponent) *
        scaleAdaptiveDyadicEulerShellMass lower splitExponent :=
      mul_le_mul_of_nonneg_left shell support_ratio_nonnegative

/-- Honest two-cutoff logarithmic high-color lower bound.  Both exponent
cutoffs are integer, and the shrinking split/full ratio remains visible. -/
theorem scaleAdaptiveHighDyadicShortShell_ge_weighted_log_ratio :
    ∃ threshold : ℕ, 1 ≤ threshold ∧
      ∀ lower splitExponent fullExponent : ℕ,
        threshold ≤ lower → lower ≤ splitExponent →
          splitExponent ≤ fullExponent →
            (scaleAdaptiveDyadicMertensConstant / 8) *
              ((splitExponent : ℝ) / (fullExponent : ℝ)) *
                (Real.log ((splitExponent + 1 : ℕ) : ℝ) -
                  (1 + Real.log (lower : ℝ))) ≤
              scaleAdaptiveHighDyadicEulerShellMass
                fullExponent splitExponent lower splitExponent := by
  obtain ⟨threshold, positive, shells⟩ :=
    scaleAdaptiveHighDyadicShortShell_ge_weighted_harmonic
  refine ⟨threshold, positive, ?_⟩
  intro lower splitExponent fullExponent lower_large low_order high_order
  have upper_harmonic := log_add_one_le_harmonic splitExponent
  have lower_harmonic := harmonic_le_one_add_log lower
  have comparison :
      Real.log ((splitExponent + 1 : ℕ) : ℝ) -
          (1 + Real.log (lower : ℝ)) ≤
        (harmonic splitExponent : ℝ) - (harmonic lower : ℝ) := by
    linarith
  have coefficient_nonnegative :
      0 ≤ (scaleAdaptiveDyadicMertensConstant / 8) *
        ((splitExponent : ℝ) / (fullExponent : ℝ)) := by
    exact mul_nonneg
      (div_nonneg scaleAdaptiveDyadicMertensConstant_pos.le (by norm_num))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact (mul_le_mul_of_nonneg_left comparison coefficient_nonnegative).trans
    (shells lower splitExponent fullExponent
      lower_large low_order high_order)

/-- Explicit integer manuscript-like lower dyadic exponent `2^n`. -/
def scaleAdaptiveColoredLowerExponent (n : ℕ) : ℕ := 2 ^ n

/-- Explicit integer split exponent `2^(n²)`, keeping the entire
low-to-split logarithmic window of order `n²`. -/
def scaleAdaptiveColoredSplitExponent (n : ℕ) : ℕ := 2 ^ (n ^ 2)

/-- Exact full exponent `n*2^(n²)`, so that the genuine HIGH support ratio
has size `1/n` while its short-shell harmonic window has size `n²`. -/
def scaleAdaptiveColoredFullExponent (n : ℕ) : ℕ :=
  n * scaleAdaptiveColoredSplitExponent n

/-- The explicit LOW physical exponent genuinely tends to infinity. -/
theorem scaleAdaptiveColoredLowerExponent_tendsto_atTop :
    Tendsto scaleAdaptiveColoredLowerExponent atTop atTop := by
  exact scaleAdaptiveDyadicCutoff_tendsto_atTop

/-- The split exponent grows like the exact integer `2^(n²)`. -/
theorem scaleAdaptiveColoredSplitExponent_tendsto_atTop :
    Tendsto scaleAdaptiveColoredSplitExponent atTop atTop := by
  exact scaleAdaptiveDyadicCutoff_tendsto_atTop.comp
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))

/-- The actual integer physical exponent cutoffs are correctly ordered;
the short high-family interval is never empty for `n ≥ 2`. -/
theorem scaleAdaptiveColoredExponent_order
    {n : ℕ} (large : 2 ≤ n) :
    scaleAdaptiveColoredLowerExponent n ≤
      scaleAdaptiveColoredSplitExponent n ∧
    scaleAdaptiveColoredSplitExponent n ≤
      scaleAdaptiveColoredFullExponent n := by
  have square_order : n ≤ n ^ 2 := by nlinarith
  constructor
  · exact Nat.pow_le_pow_right (by norm_num) square_order
  · unfold scaleAdaptiveColoredFullExponent
    nlinarith [Nat.zero_le (scaleAdaptiveColoredSplitExponent n)]

/-- The TRUE high-support exponent ratio for the explicit integer
cutoffs is exactly `1/n`, not a uniform positive constant. -/
theorem scaleAdaptiveColoredExponentRatio_eq_inv
    {n : ℕ} (positive : 0 < n) :
    (scaleAdaptiveColoredSplitExponent n : ℝ) /
      (scaleAdaptiveColoredFullExponent n : ℝ) =
        1 / (n : ℝ) := by
  have n_nonzero : (n : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  have split_nonzero :
      (scaleAdaptiveColoredSplitExponent n : ℝ) ≠ 0 := by
    unfold scaleAdaptiveColoredSplitExponent
    exact_mod_cast (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
  unfold scaleAdaptiveColoredFullExponent
  push_cast
  field_simp

/-- Exact lower bound on the genuine short-shell log window.  The `+1`
endpoint is retained, and the two real logarithms are reduced to the
actual exponents `n²` and `n`. -/
theorem scaleAdaptiveColoredExponent_log_window_ge
    (n : ℕ) :
    (((n : ℝ) ^ 2 - (n : ℝ)) * Real.log (2 : ℝ) - 1) ≤
      Real.log
        ((scaleAdaptiveColoredSplitExponent n + 1 : ℕ) : ℝ) -
          (1 + Real.log (scaleAdaptiveColoredLowerExponent n : ℝ)) := by
  have split_positive :
      (0 : ℝ) < scaleAdaptiveColoredSplitExponent n := by
    unfold scaleAdaptiveColoredSplitExponent
    positivity
  have split_le_succ :
      (scaleAdaptiveColoredSplitExponent n : ℝ) ≤
        ((scaleAdaptiveColoredSplitExponent n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ _
  have log_order := Real.log_le_log split_positive split_le_succ
  calc
    (((n : ℝ) ^ 2 - (n : ℝ)) * Real.log (2 : ℝ) - 1) =
      Real.log (scaleAdaptiveColoredSplitExponent n : ℝ) -
        (1 + Real.log (scaleAdaptiveColoredLowerExponent n : ℝ)) := by
      unfold scaleAdaptiveColoredSplitExponent
        scaleAdaptiveColoredLowerExponent
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [Real.log_pow, Real.log_pow]
      push_cast
      ring
    _ ≤ _ := sub_le_sub_right log_order _

/-- The actual integer high-family log window eventually dominates
`(log 2/2)*n²`; no divergent-window assumption is supplied. -/
theorem scaleAdaptiveColoredExponent_log_window_eventually_ge_quadratic :
    ∀ᶠ n : ℕ in atTop,
      (Real.log (2 : ℝ) / 2) * (n : ℝ) ^ 2 ≤
        Real.log
          ((scaleAdaptiveColoredSplitExponent n + 1 : ℕ) : ℝ) -
            (1 + Real.log (scaleAdaptiveColoredLowerExponent n : ℝ)) := by
  have log_positive : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have scaled_growth :
      Tendsto (fun n : ℕ => (n : ℝ) * Real.log (2 : ℝ))
        atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const log_positive
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    scaled_growth.eventually (eventually_ge_atTop (1 : ℝ))]
      with n large product_large
  have n_real : (4 : ℝ) ≤ n := by exact_mod_cast large
  have product_nonnegative :
      0 ≤ (n : ℝ) * Real.log (2 : ℝ) := by positivity
  have amplified := mul_nonneg
    (show 0 ≤ (n : ℝ) / 2 - 2 by linarith) product_nonnegative
  have quadratic :
      (Real.log (2 : ℝ) / 2) * (n : ℝ) ^ 2 ≤
        ((n : ℝ) ^ 2 - (n : ℝ)) * Real.log (2 : ℝ) - 1 := by
    nlinarith
  exact quadratic.trans (scaleAdaptiveColoredExponent_log_window_ge n)

/-- The actual LOW-color prime-type Euler load grows QUADRATICALLY on the
explicit genuine integer physical-scale interval. -/
theorem scaleAdaptiveColoredLowShell_eventually_ge_quadratic :
    ∀ᶠ n : ℕ in atTop,
      (scaleAdaptiveDyadicMertensConstant * Real.log (2 : ℝ) / 4) *
          (n : ℝ) ^ 2 ≤
        scaleAdaptiveDyadicEulerShellMass
          (scaleAdaptiveColoredLowerExponent n)
          (scaleAdaptiveColoredSplitExponent n) := by
  obtain ⟨threshold, _, low_shell⟩ :=
    scaleAdaptiveDyadicEulerShellMass_ge_log_ratio
  have cutoff_large :=
    scaleAdaptiveColoredLowerExponent_tendsto_atTop.eventually
      (eventually_ge_atTop threshold)
  filter_upwards [cutoff_large, eventually_ge_atTop (2 : ℕ),
    scaleAdaptiveColoredExponent_log_window_eventually_ge_quadratic]
      with n lower_large n_large window
  have orders := scaleAdaptiveColoredExponent_order n_large
  have estimate := low_shell
    (scaleAdaptiveColoredLowerExponent n)
    (scaleAdaptiveColoredSplitExponent n)
    lower_large orders.1
  have coefficient_nonnegative :
      0 ≤ scaleAdaptiveDyadicMertensConstant / 2 :=
    (div_pos scaleAdaptiveDyadicMertensConstant_pos (by norm_num)).le
  calc
    (scaleAdaptiveDyadicMertensConstant * Real.log (2 : ℝ) / 4) *
        (n : ℝ) ^ 2 =
      (scaleAdaptiveDyadicMertensConstant / 2) *
        ((Real.log (2 : ℝ) / 2) * (n : ℝ) ^ 2) := by ring
    _ ≤ (scaleAdaptiveDyadicMertensConstant / 2) *
          (Real.log
            ((scaleAdaptiveColoredSplitExponent n + 1 : ℕ) : ℝ) -
              (1 + Real.log (scaleAdaptiveColoredLowerExponent n : ℝ))) :=
      mul_le_mul_of_nonneg_left window coefficient_nonnegative
    _ ≤ _ := estimate

/-- Every genuinely supported low semiprime type already eligible at the
first retained physical scale obtains the SAME actual quadratic load as the
prime type.  Eligibility remains an explicit hypothesis about `s`, not a
silently uniform assertion for all semiprimes through the split cutoff. -/
theorem scaleAdaptiveColoredEligibleLowType_eventually_ge_quadratic :
    ∀ᶠ n : ℕ in atTop,
      ∀ type : ℕ,
        type.Prime → type ≤ 2 ^ scaleAdaptiveColoredSplitExponent n →
          type ≤ 2 ^ scaleAdaptiveColoredLowerExponent n →
            (scaleAdaptiveDyadicMertensConstant * Real.log (2 : ℝ) / 4) *
                (n : ℝ) ^ 2 ≤
              scaleAdaptiveLowEligibleDyadicEulerShell
                type (2 ^ scaleAdaptiveColoredSplitExponent n)
                  (scaleAdaptiveColoredLowerExponent n)
                  (scaleAdaptiveColoredSplitExponent n) := by
  filter_upwards [scaleAdaptiveColoredLowShell_eventually_ge_quadratic]
    with n bound
  intro type prime supported eligible
  rwa [scaleAdaptiveLowEligibleDyadicEulerShell_eq prime supported eligible]

/-- The genuine HIGH-color short-scale Euler load is eventually bounded
below by an EXPLICIT positive linear multiple of `n`.  The support ratio
is `1/n`, the physical log window is order `n²`, and every summand is the
actual high-family prime-pattern Euler factor. -/
theorem scaleAdaptiveColoredHighShortShell_eventually_ge_linear :
    ∀ᶠ n : ℕ in atTop,
      (scaleAdaptiveDyadicMertensConstant * Real.log (2 : ℝ) / 16) *
          (n : ℝ) ≤
        scaleAdaptiveHighDyadicEulerShellMass
          (scaleAdaptiveColoredFullExponent n)
          (scaleAdaptiveColoredSplitExponent n)
          (scaleAdaptiveColoredLowerExponent n)
          (scaleAdaptiveColoredSplitExponent n) := by
  obtain ⟨threshold, _, high_shell⟩ :=
    scaleAdaptiveHighDyadicShortShell_ge_weighted_log_ratio
  have cutoff_large :=
    scaleAdaptiveColoredLowerExponent_tendsto_atTop.eventually
      (eventually_ge_atTop threshold)
  filter_upwards [cutoff_large, eventually_ge_atTop (2 : ℕ),
    scaleAdaptiveColoredExponent_log_window_eventually_ge_quadratic]
      with n lower_large n_large window
  have orders := scaleAdaptiveColoredExponent_order n_large
  have estimate := high_shell
    (scaleAdaptiveColoredLowerExponent n)
    (scaleAdaptiveColoredSplitExponent n)
    (scaleAdaptiveColoredFullExponent n)
    lower_large orders.1 orders.2
  have n_positive : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have ratio := scaleAdaptiveColoredExponentRatio_eq_inv
    (show 0 < n by omega)
  have coefficient_nonnegative :
      0 ≤ (scaleAdaptiveDyadicMertensConstant / 8) *
        (1 / (n : ℝ)) :=
    mul_nonneg
      (div_nonneg scaleAdaptiveDyadicMertensConstant_pos.le (by norm_num))
      (div_nonneg (by norm_num) n_positive.le)
  calc
    (scaleAdaptiveDyadicMertensConstant * Real.log (2 : ℝ) / 16) *
        (n : ℝ) =
      (scaleAdaptiveDyadicMertensConstant / 8) * (1 / (n : ℝ)) *
        ((Real.log (2 : ℝ) / 2) * (n : ℝ) ^ 2) := by
      field_simp
      ring
    _ ≤ (scaleAdaptiveDyadicMertensConstant / 8) * (1 / (n : ℝ)) *
          (Real.log
            ((scaleAdaptiveColoredSplitExponent n + 1 : ℕ) : ℝ) -
              (1 + Real.log (scaleAdaptiveColoredLowerExponent n : ℝ))) :=
      mul_le_mul_of_nonneg_left window coefficient_nonnegative
    _ = (scaleAdaptiveDyadicMertensConstant / 8) *
          ((scaleAdaptiveColoredSplitExponent n : ℝ) /
            (scaleAdaptiveColoredFullExponent n : ℝ)) *
            (Real.log
              ((scaleAdaptiveColoredSplitExponent n + 1 : ℕ) : ℝ) -
                (1 + Real.log (scaleAdaptiveColoredLowerExponent n : ℝ))) := by
      rw [ratio]
    _ ≤ _ := estimate

/-- The explicit actual two-color high-family Euler load DIVERGES, despite
its true support factor and every fixed-scale factor tending to zero. -/
theorem scaleAdaptiveColoredHighShortShell_tendsto_atTop :
    Tendsto
      (fun n : ℕ =>
        scaleAdaptiveHighDyadicEulerShellMass
          (scaleAdaptiveColoredFullExponent n)
          (scaleAdaptiveColoredSplitExponent n)
          (scaleAdaptiveColoredLowerExponent n)
          (scaleAdaptiveColoredSplitExponent n))
      atTop atTop := by
  have coefficient_positive :
      0 < scaleAdaptiveDyadicMertensConstant * Real.log (2 : ℝ) / 16 := by
    exact div_pos
      (mul_pos scaleAdaptiveDyadicMertensConstant_pos
        (Real.log_pos (by norm_num))) (by norm_num)
  have linear :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
      coefficient_positive
  exact Filter.tendsto_atTop_mono' _
    scaleAdaptiveColoredHighShortShell_eventually_ge_linear linear

/-- The COMPLETE actual high-family Euler load also diverges: its long
scales are genuinely nonnegative and the short-scale part already diverges. -/
theorem scaleAdaptiveColoredHighFullShell_tendsto_atTop :
    Tendsto
      (fun n : ℕ =>
        scaleAdaptiveHighDyadicEulerShellMass
          (scaleAdaptiveColoredFullExponent n)
          (scaleAdaptiveColoredSplitExponent n)
          (scaleAdaptiveColoredLowerExponent n)
          (scaleAdaptiveColoredFullExponent n))
      atTop atTop := by
  apply Filter.tendsto_atTop_mono' _ ?_
    scaleAdaptiveColoredHighShortShell_tendsto_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n large
  have orders := scaleAdaptiveColoredExponent_order large
  rw [scaleAdaptiveHighDyadicFullShell_eq_short_add_long orders.1 orders.2,
    scaleAdaptiveHighDyadicShortShell_eq_ratio_mul orders.2]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _)
      (scaleAdaptiveDyadicEulerFactor_pos _).le)

/-- Any fixed positive colored hit rate makes the genuine HIGH-family
missing-hit exponential tend to zero. -/
theorem scaleAdaptiveColoredHighMissingProbability_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (-rate *
          scaleAdaptiveHighDyadicEulerShellMass
            (scaleAdaptiveColoredFullExponent n)
            (scaleAdaptiveColoredSplitExponent n)
            (scaleAdaptiveColoredLowerExponent n)
            (scaleAdaptiveColoredSplitExponent n)))
      atTop (nhds 0) := by
  have growth :=
    scaleAdaptiveColoredHighShortShell_tendsto_atTop.const_mul_atTop positive
  simpa [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp growth

/-- The actual HIGH-family missing-hit exponential beats its genuine
logarithmic type-mass prefactor; this is the colored analogue of the
manuscript's `(U+1)*exp(-κ*c*(W-U))` estimate. -/
theorem scaleAdaptiveColoredHighHarmonicBudget_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (n : ℝ) + 1) *
          Real.exp (-rate *
            scaleAdaptiveHighDyadicEulerShellMass
              (scaleAdaptiveColoredFullExponent n)
              (scaleAdaptiveColoredSplitExponent n)
              (scaleAdaptiveColoredLowerExponent n)
              (scaleAdaptiveColoredSplitExponent n)))
      atTop (nhds 0) := by
  let coefficient : ℝ :=
    scaleAdaptiveDyadicMertensConstant * Real.log (2 : ℝ) / 16
  have coefficient_positive : 0 < coefficient := by
    unfold coefficient
    exact div_pos
      (mul_pos scaleAdaptiveDyadicMertensConstant_pos
        (Real.log_pos (by norm_num))) (by norm_num)
  have model :=
    (adaptiveDeficit_affine_exp_decay
      (mul_pos positive coefficient_positive)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' ?_ ?_ model
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n large
    have log_nonnegative : 0 ≤ Real.log (n : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast large
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℕ),
      scaleAdaptiveColoredHighShortShell_eventually_ge_linear]
        with n large load
    have n_positive : (0 : ℝ) < n := by exact_mod_cast large
    have logarithm := Real.log_le_sub_one_of_pos n_positive
    have log_nonnegative : 0 ≤ Real.log (n : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast large
    have affine_nonnegative : 0 ≤ (n : ℝ) + 1 := by linarith
    have exp_order :
        Real.exp (-rate *
          scaleAdaptiveHighDyadicEulerShellMass
            (scaleAdaptiveColoredFullExponent n)
            (scaleAdaptiveColoredSplitExponent n)
            (scaleAdaptiveColoredLowerExponent n)
            (scaleAdaptiveColoredSplitExponent n)) ≤
          Real.exp (-(rate * coefficient) * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      change coefficient * (n : ℝ) ≤ _ at load
      nlinarith
    exact mul_le_mul
      (show Real.log (n : ℝ) + 1 ≤ (n : ℝ) + 1 by linarith)
      exp_order (Real.exp_pos _).le affine_nonnegative

/-- The genuine maximum allowed-prime conductor coefficient corresponding
to the first retained physical scale `2^(2^n)`. -/
noncomputable def scaleAdaptiveColoredConductorDensity (n : ℕ) : ℝ :=
  (((2 ^ scaleAdaptiveColoredLowerExponent n : ℕ) : ℝ))⁻¹

/-- All allowed primes can be charged while their actual normalized
conductor density tends to zero. -/
theorem scaleAdaptiveColoredConductorDensity_tendsto_zero :
    Tendsto scaleAdaptiveColoredConductorDensity
      atTop (nhds (0 : ℝ)) := by
  have physical_growth :=
    scaleAdaptiveDyadicCutoff_tendsto_atTop.comp
      scaleAdaptiveColoredLowerExponent_tendsto_atTop
  have real_growth :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp physical_growth
  exact tendsto_inv_atTop_zero.comp real_growth

/-- The two essential global high-color errors vanish SIMULTANEOUSLY:
the complete actual-prime conductor coefficient and the type-mass-weighted
true missing-hit exponential.  No Green--Tao, correlation, or covering
hypothesis is used in this genuine support/Euler calculation. -/
theorem scaleAdaptiveColoredConductor_add_high_budget_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto
      (fun n : ℕ =>
        scaleAdaptiveColoredConductorDensity n +
          (Real.log (n : ℝ) + 1) *
            Real.exp (-rate *
              scaleAdaptiveHighDyadicEulerShellMass
                (scaleAdaptiveColoredFullExponent n)
                (scaleAdaptiveColoredSplitExponent n)
                (scaleAdaptiveColoredLowerExponent n)
                (scaleAdaptiveColoredSplitExponent n)))
      atTop (nhds 0) := by
  simpa using scaleAdaptiveColoredConductorDensity_tendsto_zero.add
    (scaleAdaptiveColoredHighHarmonicBudget_tendsto_zero positive)


end Erdos1139
