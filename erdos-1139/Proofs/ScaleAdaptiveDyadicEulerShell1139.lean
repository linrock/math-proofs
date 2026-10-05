module

public import AdaptiveMertens1139
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section


/-!
# Genuine amplification across adaptive dyadic prime-pattern scales

The fixed-scale constant-band target bound contains the genuine local Euler
factor `V_T`, which tends to zero as its supported prime set grows.  It is
therefore insufficient to prove merely that every fixed shell has positive
target load.  At the physical dyadic scales `T = 2^j`, the already proved
third Mertens theorem gives

    j * V_{2^j} → exp(-γ) / log 2 > 0.

Consequently the sum of the ACTUAL adaptive low-family Euler factors over
dyadic scales diverges like a positive harmonic series.  All cutoffs below
are genuine integers, the prime support is exactly `Nat.primesLE (2^j)`,
and the adaptive support cancellation is the exact finite identity already
proved for the construction.  These are analytic bookkeeping results, not
a claim of a prime-pattern covering or of the original Erdős conjecture.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- The genuine local Euler factor at the exact integer dyadic physical
scale `2^index`, with its closed actual prime support. -/
noncomputable def scaleAdaptiveDyadicEulerFactor (index : ℕ) : ℝ :=
  adaptivePrimeEulerProduct (Nat.primesLE (2 ^ index))

/-- The exact positive asymptotic coefficient at integer dyadic scales. -/
noncomputable def scaleAdaptiveDyadicMertensConstant : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) / Real.log (2 : ℝ)

/-- The dyadic Mertens coefficient is genuinely strictly positive. -/
theorem scaleAdaptiveDyadicMertensConstant_pos :
    0 < scaleAdaptiveDyadicMertensConstant := by
  unfold scaleAdaptiveDyadicMertensConstant
  exact div_pos (Real.exp_pos _) (Real.log_pos (by norm_num))

/-- The exact integer physical cutoffs `2^j` tend to infinity. -/
theorem scaleAdaptiveDyadicCutoff_tendsto_atTop :
    Tendsto (fun index : ℕ => 2 ^ index) atTop atTop := by
  exact Filter.tendsto_atTop_mono
    (fun index => (index.lt_two_pow_self).le) tendsto_id

/-- Exact third-Mertens identity on a genuine nontrivial dyadic cutoff,
including its actual signed error term and the true `j * log 2` divisor. -/
theorem scaleAdaptiveDyadicEulerFactor_eq_mertens
    {index : ℕ} (positive : 0 < index) :
    scaleAdaptiveDyadicEulerFactor index =
      Real.exp (-Real.eulerMascheroniConstant) *
        Real.exp (Mertens.E₃ ((2 ^ index : ℕ) : ℝ)) /
          ((index : ℝ) * Real.log (2 : ℝ)) := by
  have cutoff_large : 2 ≤ (2 ^ index : ℕ) := by
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ index := Nat.pow_le_pow_right (by norm_num) positive
  unfold scaleAdaptiveDyadicEulerFactor
  rw [adaptivePrimeEulerProduct_eq_mertens cutoff_large]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_pow]

/-- The genuine actual Euler factors on integer dyadic scales have the
SHARP positive asymptotic constant `exp(-γ)/log 2`; no extra estimate is
assumed. -/
theorem scaleAdaptiveDyadicEulerFactor_mul_index_tendsto :
    Tendsto
      (fun index : ℕ =>
        (index : ℝ) * scaleAdaptiveDyadicEulerFactor index)
      atTop (nhds scaleAdaptiveDyadicMertensConstant) := by
  have restricted := adaptivePrimeEulerProduct_mul_log_tendsto.comp
    scaleAdaptiveDyadicCutoff_tendsto_atTop
  have normalized := restricted.div_const (Real.log (2 : ℝ))
  have log_nonzero : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  change Tendsto _ atTop
    (nhds (Real.exp (-Real.eulerMascheroniConstant) /
      Real.log (2 : ℝ)))
  apply normalized.congr'
  apply Filter.Eventually.of_forall
  intro index
  unfold scaleAdaptiveDyadicEulerFactor
  change
    adaptivePrimeEulerProduct (Nat.primesLE (2 ^ index)) *
      Real.log (((2 ^ index : ℕ) : ℝ)) / Real.log (2 : ℝ) =
        (index : ℝ) * adaptivePrimeEulerProduct (Nat.primesLE (2 ^ index))
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_pow]
  field_simp

/-- Eventually the true adaptive dyadic Euler factor dominates the
EXPLICIT positive harmonic weight `exp(-γ)/(2*log(2)*j)`. -/
theorem scaleAdaptiveDyadicEulerFactor_eventually_ge_harmonic :
    ∀ᶠ index : ℕ in atTop,
      scaleAdaptiveDyadicMertensConstant / 2 / (index : ℝ) ≤
        scaleAdaptiveDyadicEulerFactor index := by
  have constant_positive := scaleAdaptiveDyadicMertensConstant_pos
  have eventually_scaled :=
    (tendsto_order.1
      scaleAdaptiveDyadicEulerFactor_mul_index_tendsto).1
      (scaleAdaptiveDyadicMertensConstant / 2)
      (show scaleAdaptiveDyadicMertensConstant / 2 <
        scaleAdaptiveDyadicMertensConstant by linarith)
  filter_upwards [eventually_scaled, eventually_ge_atTop (1 : ℕ)]
    with index scaled positive
  have index_positive : (0 : ℝ) < index := by exact_mod_cast positive
  apply (div_le_iff₀ index_positive).mpr
  nlinarith

/-- The actual adaptive low-family factor on a genuine dyadic physical
scale is EXACTLY the Euler product above, for EVERY fixed family cutoff. -/
theorem scaleAdaptiveLowDyadicPatternEulerFactor_eq
    (index familyCutoff : ℕ) :
    adaptivePatternEulerFactor
      (adaptiveLowPrimeSupport (2 ^ index) familyCutoff) (2 ^ index) =
        scaleAdaptiveDyadicEulerFactor index := by
  exact adaptiveLowPatternEulerFactor_eq_scale_product
    (2 ^ index) familyCutoff

/-- Every actual dyadic low-family factor is strictly positive, including
all finite small scales before the asymptotic threshold. -/
theorem scaleAdaptiveDyadicEulerFactor_pos (index : ℕ) :
    0 < scaleAdaptiveDyadicEulerFactor index := by
  exact adaptivePrimeEulerProduct_pos (Nat.primesLE (2 ^ index))
    (fun prime selected => Nat.prime_of_mem_primesLE selected)

/-- Exact dyadic-scale shell mass on a lower-OPEN/upper-CLOSED exponent
interval; every summand is a genuine finite prime-support Euler product. -/
noncomputable def scaleAdaptiveDyadicEulerShellMass
    (lower upper : ℕ) : ℝ :=
  ∑ index ∈ Finset.Ioc lower upper,
    scaleAdaptiveDyadicEulerFactor index

/-- The exact exponent-reciprocal shell is the difference of the two true
rational harmonic numbers, with neither endpoint silently shifted. -/
theorem scaleAdaptiveDyadicExponentShell_eq_harmonic_difference
    {lower upper : ℕ} (ordered : lower ≤ upper) :
    (∑ index ∈ Finset.Ioc lower upper, (index : ℝ)⁻¹) =
      (harmonic upper : ℝ) - (harmonic lower : ℝ) := by
  have subset : Finset.Icc 1 lower ⊆ Finset.Icc 1 upper := by
    intro index selected
    have bounds := Finset.mem_Icc.mp selected
    exact Finset.mem_Icc.mpr ⟨bounds.1, bounds.2.trans ordered⟩
  have difference :
      Finset.Icc 1 upper \ Finset.Icc 1 lower =
        Finset.Ioc lower upper := by
    ext index
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have decomposition :=
    Finset.sum_sdiff subset (f := fun index : ℕ => (index : ℝ)⁻¹)
  rw [difference] at decomposition
  have cast_harmonic : ∀ n : ℕ,
      (harmonic n : ℝ) = ∑ index ∈ Finset.Icc 1 n, (index : ℝ)⁻¹ := by
    intro n
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [cast_harmonic, cast_harmonic]
  linarith

/-- There is ONE fixed finite threshold after which EVERY true dyadic
Euler-factor shell has its sharp positive harmonic lower bound.  Both
integer cutoffs are genuine and vary independently. -/
theorem scaleAdaptiveDyadicEulerShellMass_ge_harmonic_difference :
    ∃ threshold : ℕ, 1 ≤ threshold ∧
      ∀ lower upper : ℕ, threshold ≤ lower → lower ≤ upper →
        scaleAdaptiveDyadicMertensConstant / 2 *
          ((harmonic upper : ℝ) - (harmonic lower : ℝ)) ≤
            scaleAdaptiveDyadicEulerShellMass lower upper := by
  obtain ⟨threshold, eventually⟩ :=
    Filter.eventually_atTop.1
      scaleAdaptiveDyadicEulerFactor_eventually_ge_harmonic
  refine ⟨max threshold 1, le_max_right _ _, ?_⟩
  intro lower upper lower_large ordered
  have termwise : ∀ index ∈ Finset.Ioc lower upper,
      scaleAdaptiveDyadicMertensConstant / 2 * (index : ℝ)⁻¹ ≤
        scaleAdaptiveDyadicEulerFactor index := by
    intro index selected
    have index_large : threshold ≤ index := by
      have bounds := Finset.mem_Ioc.mp selected
      omega
    simpa [div_eq_mul_inv] using eventually index index_large
  have summed := Finset.sum_le_sum termwise
  rw [← Finset.mul_sum] at summed
  rw [scaleAdaptiveDyadicExponentShell_eq_harmonic_difference ordered]
    at summed
  exact summed

/-- Explicit TWO-CUTOFF logarithmic amplification from the genuine exact
integer shell; the additive `1` is retained rather than discarded. -/
theorem scaleAdaptiveDyadicEulerShellMass_ge_log_ratio :
    ∃ threshold : ℕ, 1 ≤ threshold ∧
      ∀ lower upper : ℕ, threshold ≤ lower → lower ≤ upper →
        scaleAdaptiveDyadicMertensConstant / 2 *
          (Real.log ((upper + 1 : ℕ) : ℝ) -
            (1 + Real.log (lower : ℝ))) ≤
          scaleAdaptiveDyadicEulerShellMass lower upper := by
  obtain ⟨threshold, threshold_positive, shells⟩ :=
    scaleAdaptiveDyadicEulerShellMass_ge_harmonic_difference
  refine ⟨threshold, threshold_positive, ?_⟩
  intro lower upper lower_large ordered
  have upper_harmonic := log_add_one_le_harmonic upper
  have lower_harmonic := harmonic_le_one_add_log lower
  have harmonic_comparison :
      Real.log ((upper + 1 : ℕ) : ℝ) -
          (1 + Real.log (lower : ℝ)) ≤
        (harmonic upper : ℝ) - (harmonic lower : ℝ) := by
    linarith
  have coefficient_nonnegative :
      0 ≤ scaleAdaptiveDyadicMertensConstant / 2 :=
    (div_pos scaleAdaptiveDyadicMertensConstant_pos (by norm_num)).le
  exact (mul_le_mul_of_nonneg_left harmonic_comparison
    coefficient_nonnegative).trans
      (shells lower upper lower_large ordered)

/-- The actual rational harmonic numbers diverge along genuine integer
cutoffs; this follows directly from the kernel-proved integral lower bound. -/
theorem scaleAdaptiveHarmonic_tendsto_atTop :
    Tendsto (fun index : ℕ => (harmonic index : ℝ)) atTop atTop := by
  have cutoff_growth :
      Tendsto (fun index : ℕ => ((index + 1 : ℕ) : ℝ))
        atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (tendsto_add_atTop_nat 1)
  have log_growth := Real.tendsto_log_atTop.comp cutoff_growth
  exact Filter.tendsto_atTop_mono
    (fun index => log_add_one_le_harmonic index) log_growth

/-- For EVERY fixed admissible lower physical-scale cutoff, the genuine
adaptive dyadic Euler-factor shell mass tends to infinity.  Thus the
decaying per-shell factor `V_{2^j}` does not prevent global amplification. -/
theorem scaleAdaptiveDyadicEulerShellMass_tendsto_atTop :
    ∃ threshold : ℕ, 1 ≤ threshold ∧
      ∀ lower : ℕ, threshold ≤ lower →
        Tendsto (fun upper : ℕ =>
          scaleAdaptiveDyadicEulerShellMass lower upper) atTop atTop := by
  obtain ⟨threshold, threshold_positive, shells⟩ :=
    scaleAdaptiveDyadicEulerShellMass_ge_harmonic_difference
  refine ⟨threshold, threshold_positive, ?_⟩
  intro lower lower_large
  have difference_growth :
      Tendsto (fun upper : ℕ =>
        (harmonic upper : ℝ) - (harmonic lower : ℝ)) atTop atTop := by
    simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right
      atTop (-(harmonic lower : ℝ)) scaleAdaptiveHarmonic_tendsto_atTop
  have constant_positive :
      0 < scaleAdaptiveDyadicMertensConstant / 2 := by
    exact div_pos scaleAdaptiveDyadicMertensConstant_pos (by norm_num)
  have amplified := difference_growth.const_mul_atTop constant_positive
  apply Filter.tendsto_atTop_mono' _ ?_ amplified
  filter_upwards [Filter.eventually_ge_atTop lower] with upper ordered
  exact shells lower upper lower_large ordered

/-- The same divergent shell uses the EXACT adaptive low-family pattern
factor at every scale and every fixed family cutoff, not a proxy product. -/
theorem scaleAdaptiveLowDyadicPatternEulerShell_tendsto_atTop :
    ∃ threshold : ℕ, 1 ≤ threshold ∧
      ∀ lower familyCutoff : ℕ, threshold ≤ lower →
        Tendsto
          (fun upper : ℕ =>
            ∑ index ∈ Finset.Ioc lower upper,
              adaptivePatternEulerFactor
                (adaptiveLowPrimeSupport (2 ^ index) familyCutoff)
                (2 ^ index))
          atTop atTop := by
  obtain ⟨threshold, positive, shells⟩ :=
    scaleAdaptiveDyadicEulerShellMass_tendsto_atTop
  refine ⟨threshold, positive, ?_⟩
  intro lower familyCutoff lower_large
  have shell := shells lower lower_large
  apply shell.congr
  intro upper
  unfold scaleAdaptiveDyadicEulerShellMass
  apply Finset.sum_congr rfl
  intro index _
  exact (scaleAdaptiveLowDyadicPatternEulerFactor_eq
    index familyCutoff).symm


end Erdos1139
