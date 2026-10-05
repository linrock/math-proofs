module

public import ActualMajorArcPositivityTruncation433
public import ActualLeftVertexMajorIntegration433
public import ShiftedMajorArcDedup433

@[expose] public section


/-!
# Polynomially summed genuine Siegel--Walfisz errors

The actual major-arc cutoff is `P(n)=floor(log n)^12`, the common cell
modulus is `L=lcm(q,W)`, and the shifted major region uses deduplicated
translated rational centers.  This file proves that the imported
Siegel--Walfisz exponential saving dominates every polynomial in that
exact cutoff, including all actual center and three-residue-cell counts.

No unproved integrated three-prime main term is asserted.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos689

/-- The independently proved Goldbach Siegel--Walfisz saving beats every
FIXED power of the actual natural-scale logarithm. -/
theorem actualMajorArcError_log_power_exp_tendsto_zero
    (c : ℝ) (hc : 0 < c) (power : ℕ) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) ^ power *
          Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro lower hlower
    exact Filter.Eventually.of_forall fun n => by
      have hnonnegative :
          0 ≤ Real.log (n : ℝ) ^ power *
            Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10)) := by
        positivity
      linarith
  · intro upper hupper
    obtain ⟨N, hN⟩ := GoldbachChain.exp_dominates_polylog
      c hc power (upper / 2) (by linarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hbound := hN n hn
    linarith

/-- The actual twelfth-power floored logarithmic Farey cutoff is dominated
at every natural scale by the corresponding honest logarithmic power. -/
theorem actualMajorArcError_cutoff_power_le_log_power
    (n power : ℕ) :
    (compatibleLogMinorCutoff n : ℝ) ^ power ≤
      Real.log (n : ℝ) ^ (12 * power) := by
  calc
    (compatibleLogMinorCutoff n : ℝ) ^ power ≤
        (Real.log (n : ℝ) ^ 12) ^ power :=
      pow_le_pow_left₀ (by positivity)
        (compatibleLogMinorCutoff_le_log_pow_twelve n) power
    _ = Real.log (n : ℝ) ^ (12 * power) := by
      rw [← pow_mul]

/-- ANY fixed polynomial number of actual Farey-denominator factors is
absorbed by the genuine Siegel--Walfisz exponential saving. -/
theorem actualMajorArcError_cutoff_power_exp_tendsto_zero
    (c : ℝ) (hc : 0 < c) (power : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (compatibleLogMinorCutoff n : ℝ) ^ power *
          Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity)
    _ (actualMajorArcError_log_power_exp_tendsto_zero
      c hc (12 * power))
  exact Filter.Eventually.of_forall fun n =>
    mul_le_mul_of_nonneg_right
      (actualMajorArcError_cutoff_power_le_log_power n power)
      (Real.exp_pos _).le

/-- Every FIXED logarithmic power is negligible compared with the genuine
square-root scale of the manuscript endpoint. -/
theorem actualMajorArcError_log_power_div_root_tendsto_zero
    (power : ℕ) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) ^ power /
          (n : ℝ) ^ ((1 : ℝ) / 2))
      atTop (nhds 0) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop (power : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hnatural :=
    hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def, Real.rpow_natCast] using hnatural

/-- The COMPLETE actual three-coordinate proper-prime-power bound has the
explicit genuine logarithmic-over-square-root majorant at every `n≥2`. -/
theorem actualMajorArcError_prime_power_normalized_le
    (n : ℕ) (hn : 2 ≤ n) :
    ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2 ≤
      (6 / Real.log 2) *
        (Real.log (n : ℝ) ^ 4 /
          (n : ℝ) ^ ((1 : ℝ) / 2)) := by
  have hlogtwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnpositive : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n)
  have hlog : (0 : ℝ) < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogmono : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hnatlog := Real.natLog_le_logb n 2
  simp only [Real.logb, Nat.cast_ofNat] at hnatlog
  have honeLog : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlogtwo).mpr (by simpa using hlogmono)
  have hbinary :
      (Nat.log 2 n : ℝ) + 1 ≤
        2 * (Real.log (n : ℝ) / Real.log 2) := by
    linarith
  have hroot : (Nat.sqrt n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.nat_sqrt_le_real_sqrt
  have hrootpos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hpow :
      (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = n := by
    rw [← Real.rpow_add hnpositive]
    norm_num
  have hratio :
      (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) =
        1 / (n : ℝ) ^ (1 / 2 : ℝ) := by
    apply (div_eq_div_iff hnpositive.ne' hrootpos.ne').mpr
    simpa using hpow
  unfold ternaryPrimePowerErrorBound
  calc
    (3 * (n : ℝ) * (Nat.sqrt n : ℝ) *
        ((Nat.log 2 n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 3) /
        (n : ℝ) ^ 2 ≤
      (3 * (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) *
        (2 * (Real.log (n : ℝ) / Real.log 2)) *
          (Real.log (n : ℝ)) ^ 3) / (n : ℝ) ^ 2 := by
        gcongr
    _ = (6 / Real.log 2) * (Real.log (n : ℝ)) ^ 4 *
        ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ)) := by
        field_simp
        ring
    _ = (6 / Real.log 2) *
        (Real.log (n : ℝ) ^ 4 / (n : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [hratio]
        ring

/-- Even an ARBITRARY fixed polynomial number of residue cells, rational
anchors, and coefficient branches cannot prevent the exact proper-prime-power
error from being `o(n²)`. -/
theorem actualMajorArcError_cutoff_power_prime_power_normalized_tendsto_zero
    (power : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (compatibleLogMinorCutoff n : ℝ) ^ power *
          (ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2))
      atTop (nhds 0) := by
  have hmajorant :=
    (actualMajorArcError_log_power_div_root_tendsto_zero
      (12 * power + 4)).const_mul (6 / Real.log 2)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => by
      unfold ternaryPrimePowerErrorBound
      positivity)
    _ (by simpa using hmajorant)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hpower := actualMajorArcError_cutoff_power_le_log_power n power
  have hprime := actualMajorArcError_prime_power_normalized_le n hn
  calc
    (compatibleLogMinorCutoff n : ℝ) ^ power *
        (ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2) ≤
      Real.log (n : ℝ) ^ (12 * power) *
        ((6 / Real.log 2) *
          (Real.log (n : ℝ) ^ 4 /
            (n : ℝ) ^ ((1 : ℝ) / 2))) := by
      apply mul_le_mul hpower hprime
      · unfold ternaryPrimePowerErrorBound
        positivity
      · positivity
    _ = (6 / Real.log 2) *
          (Real.log (n : ℝ) ^ (12 * power + 4) /
            (n : ℝ) ^ ((1 : ℝ) / 2)) := by
      rw [pow_add]
      ring
    _ = (6 / Real.log 2) *
          (Real.log (n : ℝ) ^ (12 * power + 4) /
            (n : ℝ) ^ ((2 : ℝ)⁻¹)) := by
      norm_num

/-- The EXACT upstream reduced-anchor family has at most `4*P^2` members;
negative and positive integer numerator representatives are both included. -/
theorem actualMajorArcError_goldbach_anchor_card_le
    (cutoff : ℕ) (hcutoff : 0 < cutoff) :
    (GoldbachChain.anchors cutoff).card ≤ 4 * cutoff ^ 2 := by
  have hfirst :
      (GoldbachChain.anchors cutoff).card ≤
        cutoff * (3 * cutoff + 1) := by
    calc
      (GoldbachChain.anchors cutoff).card ≤
          (Finset.Icc 1 cutoff ×ˢ
            Finset.Icc (-(cutoff : ℤ)) (2 * cutoff)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = (Finset.Icc 1 cutoff).card *
            (Finset.Icc (-(cutoff : ℤ)) (2 * cutoff)).card :=
        Finset.card_product _ _
      _ = cutoff * (3 * cutoff + 1) := by
        rw [Nat.card_Icc, Int.card_Icc]
        congr 1
        omega
  calc
    (GoldbachChain.anchors cutoff).card ≤
        cutoff * (3 * cutoff + 1) := hfirst
    _ ≤ 4 * cutoff ^ 2 := by nlinarith

/-- Including EVERY actual support-character shift and BOTH needed periodic
lifts creates at most `8*W*P²` translated Farey anchors. -/
theorem actualMajorArcError_shifted_anchor_card_le
    (supportModulus cutoff : ℕ) (hcutoff : 0 < cutoff) :
    (actualShiftedFareyAnchors supportModulus cutoff).card ≤
      8 * supportModulus * cutoff ^ 2 := by
  have hanchor :=
    actualMajorArcError_goldbach_anchor_card_le cutoff hcutoff
  unfold actualShiftedFareyAnchors
  calc
    ((((GoldbachChain.anchors cutoff).product
        (Finset.range supportModulus)).product
          (Finset.Icc (0 : ℤ) 1)).image fun t =>
            (t.1.1.1,
              t.1.1.2 + t.2 * (t.1.1.1 : ℤ),
              (t.1.2 : ℤ))).card ≤
        (((GoldbachChain.anchors cutoff).product
          (Finset.range supportModulus)).product
            (Finset.Icc (0 : ℤ) 1)).card :=
      Finset.card_image_le
    _ = (GoldbachChain.anchors cutoff).card * supportModulus * 2 := by
      simp
    _ ≤ (4 * cutoff ^ 2) * supportModulus * 2 := by
      exact Nat.mul_le_mul_right 2
        (Nat.mul_le_mul_right supportModulus hanchor)
    _ = 8 * supportModulus * cutoff ^ 2 := by ring

/-- Deduplicating all genuinely coincident shifted rational centers can
never increase the true translated-anchor count. -/
theorem actualMajorArcError_shifted_center_card_le
    (supportModulus cutoff : ℕ) (hcutoff : 0 < cutoff) :
    (shiftedFareyCenterClasses supportModulus
      (actualShiftedFareyAnchors supportModulus cutoff)).card ≤
        8 * supportModulus * cutoff ^ 2 := by
  exact Finset.card_image_le.trans
    (actualMajorArcError_shifted_anchor_card_le
      supportModulus cutoff hcutoff)

/-- For EVERY genuine rational denominator `q≤P`, the exact common
modulus `lcm(q,W)` gives at most `(W*P)^3` actual three-residue cells. -/
theorem actualMajorArcError_lcm_triple_cell_card_le
    (S : Finset ℕ) (denominator cutoff : ℕ)
    (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hsupport : ∀ p ∈ S, p.Prime) :
    (actualMajorArcLcmResidueModulus S denominator) ^ 3 ≤
      ((∏ p ∈ S, p) * cutoff) ^ 3 := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hdivisor : Nat.lcm denominator W ∣ denominator * W := by
    apply Nat.lcm_dvd
    · exact dvd_mul_right denominator W
    · exact dvd_mul_left W denominator
  have hfirst : Nat.lcm denominator W ≤ denominator * W :=
    Nat.le_of_dvd (Nat.mul_pos hdenominator hW) hdivisor
  have hsecond : denominator * W ≤ W * cutoff := by
    nlinarith [Nat.mul_le_mul_right W hcutoff]
  apply Nat.pow_le_pow_left
  exact hfirst.trans hsecond

/-- The exact number of deduplicated shifted centers, times ALL possible
three-residue cells and any additional fixed polynomial in `P(n)`, is still
annihilated by the proven Siegel--Walfisz saving.  This is the actual
`#centers * L^3 * P^k` summation cost of the original major-arc expansion. -/
theorem actualMajorArcError_shifted_center_triple_cells_exp_tendsto_zero
    (supportModulus : ℕ) (c : ℝ) (hc : 0 < c)
    (extraPower : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((shiftedFareyCenterClasses supportModulus
          (actualShiftedFareyAnchors supportModulus
            (compatibleLogMinorCutoff n))).card : ℝ) *
          ((supportModulus * compatibleLogMinorCutoff n : ℕ) : ℝ) ^ 3 *
          (compatibleLogMinorCutoff n : ℝ) ^ extraPower *
          Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
  have hmajorant :=
    (actualMajorArcError_cutoff_power_exp_tendsto_zero
      c hc (extraPower + 5)).const_mul
        (8 * (supportModulus : ℝ) ^ 4)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity)
    _ (by simpa using hmajorant)
  filter_upwards
    [(tendsto_atTop.1 compatibleLogMinorCutoff_tendsto_atTop 1)]
      with n hcutoff
  let P := compatibleLogMinorCutoff n
  have hcard := actualMajorArcError_shifted_center_card_le
    supportModulus P hcutoff
  calc
    ((shiftedFareyCenterClasses supportModulus
        (actualShiftedFareyAnchors supportModulus P)).card : ℝ) *
        ((supportModulus * P : ℕ) : ℝ) ^ 3 *
        (P : ℝ) ^ extraPower *
        Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10)) ≤
      ((8 * supportModulus * P ^ 2 : ℕ) : ℝ) *
        ((supportModulus * P : ℕ) : ℝ) ^ 3 *
        (P : ℝ) ^ extraPower *
        Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10)) := by
          gcongr
    _ = (8 * (supportModulus : ℝ) ^ 4) *
          ((P : ℝ) ^ (extraPower + 5) *
            Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10))) := by
      push_cast
      ring
    _ = (8 * (supportModulus : ℝ) ^ 4) *
          ((compatibleLogMinorCutoff n : ℝ) ^ (extraPower + 5) *
            Real.exp (-(c * Real.log (n : ℝ) ^ ((10 : ℝ)⁻¹)))) := by
      simp [P, neg_mul]


end Erdos689
