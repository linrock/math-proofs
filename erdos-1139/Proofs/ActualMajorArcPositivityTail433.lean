module

public import ActualMajorArcPositivityArchimedean433

@[expose] public section


/-!
# Actual three-interval Farey tails, including every affine resonance

The true coefficient-dependent smooth cubic has frequencies `1`, `a`, and
`-2d`. Bounding all three interval sums by inverse distance independently
would silently lose the nonzero resonances of `a` and `2d`. Instead the
frequency-one LABEL interval supplies the genuine Dirichlet-kernel cutoff,
while the other two original windows are controlled by their exact dilated
full-circle Parseval identities. This retains every resonance and proves a
true signed smooth-tail estimate for the original Farey radius.

No signed support/conductor complement is discarded, and no global prime
major-arc positivity is assumed.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The exact imported interval Dirichlet-kernel cap, including its integer
resonance branch. -/
noncomputable def actualMajorArcTailIntervalCap
    (length : ℕ) (frequency : ℝ) : ℝ :=
  if frequency - (round frequency : ℝ) = 0 then (length : ℝ)
  else min (length : ℝ)
    (1 / (2 * |frequency - (round frequency : ℝ)|))

/-- The genuine interval sum at EVERY integral frequency obeys the imported
sharp geometric cap; in particular all nonzero affine resonances remain. -/
theorem actualMajorArcTail_interval_exponential_cap
    (lower upper : ℕ) (frequency : ℤ) (β : ℝ) :
    ‖ternaryExponentialSum (Finset.Ico lower upper)
      (fun _ => 1) frequency β‖ ≤
        actualMajorArcTailIntervalCap (upper - lower)
          ((frequency : ℝ) * β) := by
  have hcap := GoldbachChain.MinSum.exp_sum_Ico_min_bound
    ((frequency : ℝ) * β) lower upper
  unfold ternaryExponentialSum actualMajorArcTailIntervalCap
  simpa only [one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hcap

/-- Inside the genuine middle circle `[δ,1-δ]`, distance to the NEAREST
integer is at least `δ`; both principal endpoints are removed. -/
theorem actualMajorArcTail_middle_distance_lower
    (δ β : ℝ) (hδ : 0 < δ)
    (hlower : δ ≤ β) (hupper : β ≤ 1 - δ) :
    δ ≤ |β - (round β : ℝ)| := by
  by_cases hround : round β ≤ (0 : ℤ)
  · have hcast : (round β : ℝ) ≤ 0 := by exact_mod_cast hround
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hround' : (1 : ℤ) ≤ round β := by omega
    have hcast : (1 : ℝ) ≤ (round β : ℝ) := by
      exact_mod_cast hround'
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- On the whole true middle circle the ACTUAL arbitrary-real-strip label
interval has the uniform Dirichlet bound `1/(2δ)`. -/
theorem actualMajorArcTail_label_middle_sup
    (n : ℕ) (τ ell δ β : ℝ) (hδ : 0 < δ)
    (hβ : β ∈ Set.Icc δ (1 - δ)) :
    ‖ternaryExponentialSum
      (actualMajorArcArchimedeanLabelWindow τ ell n)
      (fun _ => 1) 1 β‖ ≤ 1 / (2 * δ) := by
  have hdistance := actualMajorArcTail_middle_distance_lower
    δ β hδ hβ.1 hβ.2
  have hnonzero : β - (round β : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hdistance
    linarith
  have hcap := actualMajorArcTail_interval_exponential_cap
    (manuscriptRealLabelLower τ n)
    (manuscriptRealLabelUpper τ ell n) 1 β
  change
    ‖ternaryExponentialSum
      (Finset.Ico (manuscriptRealLabelLower τ n)
        (manuscriptRealLabelUpper τ ell n))
      (fun _ => 1) 1 β‖ ≤ _
  rw [actualMajorArcTailIntervalCap, Int.cast_one, one_mul,
    if_neg hnonzero] at hcap
  calc
    _ ≤ 1 / (2 * |β - (round β : ℝ)|) :=
      hcap.trans (min_le_right _ _)
    _ ≤ 1 / (2 * δ) := by
      gcongr

/-- True three-frequency full middle-tail estimate.  The `a` and `-2d`
factors retain EVERY resonance through their exact dilated Parseval
identities.  The real strip and BOTH original edge endpoints are exact. -/
theorem actualMajorArcTail_smooth_middle_integral_le
    (a d n : ℕ) (τ ell δ : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hδ : 0 < δ) :
    ‖∫ β in Set.Icc δ (1 - δ),
      actualMajorArcArchimedeanSmoothCubic a d n τ ell β‖ ≤
        (1 / (2 * δ)) / 2 *
          (((actualMajorArcArchimedeanLeftWindow a n).card : ℝ) +
            ((actualMajorArcArchimedeanCenterWindow d n).card : ℝ)) := by
  let first : ℝ → ℂ := fun β =>
    ternaryExponentialSum
      (actualMajorArcArchimedeanLabelWindow τ ell n)
      (fun _ => 1) 1 β
  let second : ℝ → ℂ := fun β =>
    ternaryExponentialSum
      (actualMajorArcArchimedeanLeftWindow a n)
      (fun _ => 1) (a : ℤ) β
  let third : ℝ → ℂ := fun β =>
    ternaryExponentialSum
      (actualMajorArcArchimedeanCenterWindow d n)
      (fun _ => 1) (-2 * (d : ℤ)) β
  have hfirst : Continuous first := by
    dsimp [first]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hsecond : Continuous second := by
    dsimp [second]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hthird : Continuous third := by
    dsimp [third]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hsubset : Set.Icc δ (1 - δ) ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro β hβ
    constructor <;> linarith [hβ.1, hβ.2]
  have hquadratic := ternary_minor_integral_le_quadratic_energy
    first second third hfirst hsecond hthird
    (Set.Icc δ (1 - δ)) measurableSet_Icc hsubset
    (1 / (2 * δ)) (by positivity)
    (fun β hβ => actualMajorArcTail_label_middle_sup
      n τ ell δ β hδ hβ)
  have hleftFrequency : (a : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha)
  have hrightFrequency : (-2 * (d : ℤ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by
      exact_mod_cast (Nat.ne_of_gt hd))
  have hleftEnergy :
      (∫ β in (0 : ℝ)..1, ‖second β‖ ^ 2) =
        ((actualMajorArcArchimedeanLeftWindow a n).card : ℝ) := by
    dsimp [second]
    rw [ternary_window_dilated_parseval _ _ _ hleftFrequency]
    simp
  have hrightEnergy :
      (∫ β in (0 : ℝ)..1, ‖third β‖ ^ 2) =
        ((actualMajorArcArchimedeanCenterWindow d n).card : ℝ) := by
    dsimp [third]
    rw [ternary_window_dilated_parseval _ _ _ hrightFrequency]
    simp
  rw [hleftEnergy, hrightEnergy] at hquadratic
  exact hquadratic

/-- Simplified genuine tail estimate with no hidden coefficient loss:
both actual edge-window cardinalities are at most the ambient scale. -/
theorem actualMajorArcTail_smooth_middle_integral_le_scale
    (a d n : ℕ) (τ ell δ : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hδ : 0 < δ) :
    ‖∫ β in Set.Icc δ (1 - δ),
      actualMajorArcArchimedeanSmoothCubic a d n τ ell β‖ ≤
        (n : ℝ) / (2 * δ) := by
  have htail := actualMajorArcTail_smooth_middle_integral_le
    a d n τ ell δ ha hd hδ
  have hleft : (actualMajorArcArchimedeanLeftWindow a n).card ≤ n := by
    simpa [actualMajorArcArchimedeanLeftWindow] using
      (Nat.div_le_self n (2 * a))
  have hright :
      (actualMajorArcArchimedeanCenterWindow d n).card ≤ n := by
    simpa [actualMajorArcArchimedeanCenterWindow] using
      (Nat.div_le_self n (4 * d))
  have hleftReal :
      ((actualMajorArcArchimedeanLeftWindow a n).card : ℝ) ≤ n := by
    exact_mod_cast hleft
  have hrightReal :
      ((actualMajorArcArchimedeanCenterWindow d n).card : ℝ) ≤ n := by
    exact_mod_cast hright
  calc
    _ ≤ (1 / (2 * δ)) / 2 *
        (((actualMajorArcArchimedeanLeftWindow a n).card : ℝ) +
          ((actualMajorArcArchimedeanCenterWindow d n).card : ℝ)) := htail
    _ ≤ (1 / (2 * δ)) / 2 * ((n : ℝ) + n) := by gcongr
    _ = (n : ℝ) / (2 * δ) := by ring

/-- The ORIGINAL, unreduced Farey radius of a shifted anchor.  In
particular this retains the original denominator even at duplicate centers. -/
noncomputable def actualMajorArcTailFareyRadius
    (lower : ℕ → ℕ) (n denominator : ℕ) : ℝ :=
  1 / ((denominator : ℝ) *
    ((fullyCompatibleFareyCutoff lower n : ℝ) + 1))

/-- If the actual moving endpoint is at most its ambient scale, the true
cutoffs satisfy `P*(Q+1) ≤ 2n`. -/
theorem actualMajorArcTail_farey_cutoff_product_le_two_scale
    (lower : ℕ → ℕ) (n : ℕ)
    (hendpoint : lower n ≤ n)
    (hcutoff : compatibleLogMinorCutoff n ≤ n) :
    compatibleLogMinorCutoff n *
        (fullyCompatibleFareyCutoff lower n + 1) ≤ 2 * n := by
  calc
    compatibleLogMinorCutoff n *
        (fullyCompatibleFareyCutoff lower n + 1) =
      compatibleLogMinorCutoff n * fullyCompatibleFareyCutoff lower n +
        compatibleLogMinorCutoff n := by ring
    _ ≤ lower n + compatibleLogMinorCutoff n :=
      Nat.add_le_add_right
        (fullyCompatibleFareyCutoff_product_le lower n) _
    _ ≤ n + n := Nat.add_le_add hendpoint hcutoff
    _ = 2 * n := by ring

/-- The entire TRUE smooth circle tail outside the original two-sided
Farey radius is bounded by `q/P` after division by `n²`.  All affine
resonances, arbitrary-real strip endpoints, and original edge bounds are
retained; no sign or positivity assumption appears. -/
theorem actualMajorArcTail_true_farey_normalized_le
    (lower : ℕ → ℕ) (a d n denominator : ℕ) (τ ell : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hn : 0 < n) (hdenominator : 0 < denominator)
    (hcutoffPositive : 0 < compatibleLogMinorCutoff n)
    (hcutoffScale : compatibleLogMinorCutoff n ≤ n)
    (hendpoint : lower n ≤ n) :
    ‖∫ β in Set.Icc
        (actualMajorArcTailFareyRadius lower n denominator)
        (1 - actualMajorArcTailFareyRadius lower n denominator),
      actualMajorArcArchimedeanSmoothCubic a d n τ ell β‖ /
        (n : ℝ) ^ 2 ≤
      (denominator : ℝ) / (compatibleLogMinorCutoff n : ℝ) := by
  let δ := actualMajorArcTailFareyRadius lower n denominator
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hdenominatorReal : (0 : ℝ) < denominator := by
    exact_mod_cast hdenominator
  have hcutoffReal : (0 : ℝ) < compatibleLogMinorCutoff n := by
    exact_mod_cast hcutoffPositive
  have hfareyReal :
      (0 : ℝ) < (fullyCompatibleFareyCutoff lower n : ℝ) + 1 := by
    positivity
  have hδ : 0 < δ := by
    dsimp [δ, actualMajorArcTailFareyRadius]
    positivity
  have htail := actualMajorArcTail_smooth_middle_integral_le_scale
    a d n τ ell δ ha hd hδ
  have hcutoffNat := actualMajorArcTail_farey_cutoff_product_le_two_scale
    lower n hendpoint hcutoffScale
  have hcutoffBound :
      (compatibleLogMinorCutoff n : ℝ) *
          ((fullyCompatibleFareyCutoff lower n : ℝ) + 1) ≤
        2 * (n : ℝ) := by
    exact_mod_cast hcutoffNat
  change
    ‖∫ β in Set.Icc δ (1 - δ),
      actualMajorArcArchimedeanSmoothCubic a d n τ ell β‖ /
        (n : ℝ) ^ 2 ≤ _
  calc
    _ ≤ ((n : ℝ) / (2 * δ)) / (n : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right htail (by positivity)
    _ = ((denominator : ℝ) *
        ((fullyCompatibleFareyCutoff lower n : ℝ) + 1)) /
          (2 * n) := by
      dsimp [δ, actualMajorArcTailFareyRadius]
      field_simp
    _ ≤ (denominator : ℝ) / (compatibleLogMinorCutoff n : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) hcutoffReal).mpr
      nlinarith [mul_le_mul_of_nonneg_left hcutoffBound
        (le_of_lt hdenominatorReal)]

/-- The genuine logarithmic cutoff is eventually below its ambient natural
scale. -/
theorem actualMajorArcTail_log_cutoff_le_scale_eventually :
    ∀ᶠ n : ℕ in atTop, compatibleLogMinorCutoff n ≤ n := by
  have hlinear :
      ∀ᶠ n : ℕ in atTop, (1 : ℝ) * n ≤ ((fun m : ℕ => m) n : ℝ) :=
    Eventually.of_forall (fun _ => by simp)
  have hcube :=
    compatibleLogMinorCutoff_fixed_cube_le_linear_label_eventually
      (fun n : ℕ => n) 1 (by norm_num) hlinear 1 (by norm_num)
  filter_upwards [hcube] with n hn
  have hpower : compatibleLogMinorCutoff n ≤
      compatibleLogMinorCutoff n ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  exact hpower.trans (by simpa using hn)

/-- Uniform genuine small-denominator tail: for every original denominator
`q≤sqrt(P)=floor(log n)^6`, the whole signed three-window tail is at most
`floor(log n)^(-6)` after quadratic normalization. -/
theorem actualMajorArcTail_small_denominator_normalized_eventually
    (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ denominator : ℕ,
        0 < denominator → denominator ≤ compatibleLogBase n ^ 6 →
          ‖∫ β in Set.Icc
              (actualMajorArcTailFareyRadius lower n denominator)
              (1 - actualMajorArcTailFareyRadius lower n denominator),
            actualMajorArcArchimedeanSmoothCubic a d n τ ell β‖ /
              (n : ℝ) ^ 2 ≤
            1 / (compatibleLogBase n : ℝ) ^ 6 := by
  filter_upwards
    [eventually_gt_atTop (0 : ℕ),
      (tendsto_atTop.1 compatibleLogBase_tendsto_atTop 1),
      actualMajorArcTail_log_cutoff_le_scale_eventually,
      hendpoint] with n hn hbase hscale hupper
  intro denominator hdenominator hsmall
  have hbaseReal : (0 : ℝ) < compatibleLogBase n := by
    exact_mod_cast hbase
  have hcutoff : 0 < compatibleLogMinorCutoff n := by
    unfold compatibleLogMinorCutoff
    positivity
  have hmain := actualMajorArcTail_true_farey_normalized_le
    lower a d n denominator τ ell ha hd hn hdenominator
    hcutoff hscale hupper
  have hsmallReal : (denominator : ℝ) ≤
      (compatibleLogBase n : ℝ) ^ 6 := by
    exact_mod_cast hsmall
  calc
    _ ≤ (denominator : ℝ) / (compatibleLogMinorCutoff n : ℝ) := hmain
    _ ≤ (compatibleLogBase n : ℝ) ^ 6 /
        (compatibleLogMinorCutoff n : ℝ) := by
      exact div_le_div_of_nonneg_right hsmallReal (by positivity)
    _ = 1 / (compatibleLogBase n : ℝ) ^ 6 := by
      unfold compatibleLogMinorCutoff
      push_cast
      field_simp

/-- The exact small-denominator Farey-tail rate tends to zero. -/
theorem actualMajorArcTail_small_denominator_rate_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (compatibleLogBase n : ℝ) ^ 6)
      atTop (nhds 0) := by
  have hbase :
      Tendsto (fun n : ℕ => (compatibleLogBase n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      compatibleLogBase_tendsto_atTop
  simpa [one_div, inv_pow] using hbase.inv_tendsto_atTop.pow 6

/-- The exact signed, support-restricted small-denominator archimedean
tail, using the actual coefficient `μ(q)/φ(q)²` and the TRUE original
denominator-dependent Farey radius in each summand. -/
noncomputable def actualMajorArcTailSmallSignedSum
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ denominator ∈ Finset.Icc 1 (compatibleLogBase n ^ 6),
    ((actualMajorArcRestrictedSignedCoefficient excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n denominator)
          (1 - actualMajorArcTailFareyRadius lower n denominator),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β

/-- Absolute convergence bounds the complete genuinely signed generic
small-denominator Farey-tail sum, without replacing or deleting any sign. -/
theorem actualMajorArcTail_small_signed_normalized_eventually
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ‖actualMajorArcTailSmallSignedSum
        excluded lower a d n τ ell‖ / (n : ℝ) ^ 2 ≤
        (1 / (compatibleLogBase n : ℝ) ^ 6) *
          ∑' denominator : ℕ,
            ‖actualMajorArcRestrictedSignedCoefficient
              excluded denominator‖ := by
  have hsummable :=
    actualMajorArcRestrictedSignedCoefficient_norm_summable excluded
  filter_upwards
    [actualMajorArcTail_small_denominator_normalized_eventually
      lower hendpoint a d ha hd τ ell] with n hsmall
  let F := Finset.Icc 1 (compatibleLogBase n ^ 6)
  let rate : ℝ := 1 / (compatibleLogBase n : ℝ) ^ 6
  let term : ℕ → ℂ := fun denominator =>
    ((actualMajorArcRestrictedSignedCoefficient excluded denominator : ℝ) : ℂ) *
      ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n denominator)
          (1 - actualMajorArcTailFareyRadius lower n denominator),
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β
  have hterm : ∀ denominator ∈ F,
      ‖term denominator‖ / (n : ℝ) ^ 2 ≤
        rate * ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := by
    intro denominator hdenominator
    have hmem : 1 ≤ denominator ∧
        denominator ≤ compatibleLogBase n ^ 6 :=
      Finset.mem_Icc.mp hdenominator
    have htail := hsmall denominator (by omega) hmem.2
    dsimp [term, rate]
    rw [norm_mul, Complex.norm_real]
    calc
      ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
          ‖∫ β in Set.Icc
              (actualMajorArcTailFareyRadius lower n denominator)
              (1 - actualMajorArcTailFareyRadius lower n denominator),
            actualMajorArcArchimedeanSmoothCubic
              a d n τ ell β‖ / (n : ℝ) ^ 2 =
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
          (‖∫ β in Set.Icc
              (actualMajorArcTailFareyRadius lower n denominator)
              (1 - actualMajorArcTailFareyRadius lower n denominator),
            actualMajorArcArchimedeanSmoothCubic
              a d n τ ell β‖ / (n : ℝ) ^ 2) := by ring
      _ ≤ ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ *
            (1 / (compatibleLogBase n : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_left htail (norm_nonneg _)
      _ = _ := by
        rw [Real.norm_eq_abs]
        ring
  have hmass :
      (∑ denominator ∈ F,
        ‖actualMajorArcRestrictedSignedCoefficient excluded denominator‖) ≤
        ∑' denominator : ℕ,
          ‖actualMajorArcRestrictedSignedCoefficient
            excluded denominator‖ :=
    hsummable.sum_le_tsum F (fun _ _ => norm_nonneg _)
  change ‖∑ denominator ∈ F, term denominator‖ / (n : ℝ) ^ 2 ≤
    rate * _
  calc
    _ ≤ (∑ denominator ∈ F, ‖term denominator‖) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ denominator ∈ F,
        (‖term denominator‖ / (n : ℝ) ^ 2) := by
      rw [Finset.sum_div]
    _ ≤ ∑ denominator ∈ F,
        rate * ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := Finset.sum_le_sum hterm
    _ = rate * ∑ denominator ∈ F,
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ := by
      rw [Finset.mul_sum]
    _ ≤ rate * ∑' denominator : ℕ,
        ‖actualMajorArcRestrictedSignedCoefficient
          excluded denominator‖ :=
      mul_le_mul_of_nonneg_left hmass (by dsimp [rate]; positivity)

/-- The COMPLETE signed generic small-denominator actual Farey-tail sum is
`o(n²)`, uniformly over the actual original windows and their resonances. -/
theorem actualMajorArcTail_small_signed_normalized_tendsto_zero
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖actualMajorArcTailSmallSignedSum
          excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hmajor :
      Tendsto
        (fun n : ℕ =>
          (1 / (compatibleLogBase n : ℝ) ^ 6) *
            ∑' denominator : ℕ,
              ‖actualMajorArcRestrictedSignedCoefficient
                excluded denominator‖)
        atTop (nhds 0) := by
    simpa using
      actualMajorArcTail_small_denominator_rate_tendsto_zero.mul_const
        (∑' denominator : ℕ,
          ‖actualMajorArcRestrictedSignedCoefficient
            excluded denominator‖)
  exact squeeze_zero'
    (Eventually.of_forall (fun n => by positivity))
    (actualMajorArcTail_small_signed_normalized_eventually
      excluded lower hendpoint a d ha hd τ ell)
    hmajor

/-- The discarded LARGE generic denominators have absolutely summable true
signed coefficients: the exact shell `[sqrt(P),P)` tends to zero. This is an
arithmetic tail only; it does NOT assert that the support-sharing actual
major centers equal this generic shell. -/
theorem actualMajorArcTail_restricted_large_denominator_mass_tendsto_zero
    (excluded : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ∑ denominator ∈ Finset.Ico (compatibleLogBase n ^ 6)
          (compatibleLogMinorCutoff n),
            ‖actualMajorArcRestrictedSignedCoefficient
              excluded denominator‖)
      atTop (nhds 0) := by
  have hsummable :=
    actualMajorArcRestrictedSignedCoefficient_norm_summable excluded
  have hsmallTop :
      Tendsto (fun n : ℕ => compatibleLogBase n ^ 6) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)).comp
      compatibleLogBase_tendsto_atTop
  have hupper := hsummable.hasSum.tendsto_sum_nat.comp
    compatibleLogMinorCutoff_tendsto_atTop
  have hlower := hsummable.hasSum.tendsto_sum_nat.comp hsmallTop
  have hdifference :
      Tendsto
        (fun n : ℕ =>
          (∑ denominator ∈ Finset.range (compatibleLogMinorCutoff n),
            ‖actualMajorArcRestrictedSignedCoefficient
              excluded denominator‖) -
          (∑ denominator ∈ Finset.range (compatibleLogBase n ^ 6),
            ‖actualMajorArcRestrictedSignedCoefficient
              excluded denominator‖))
        atTop (nhds 0) := by
    simpa using hupper.sub hlower
  refine Filter.Tendsto.congr' ?_ hdifference
  filter_upwards
    [(tendsto_atTop.1 compatibleLogBase_tendsto_atTop 1)] with n hbase
  have hcutoff : compatibleLogBase n ^ 6 ≤
      compatibleLogMinorCutoff n := by
    unfold compatibleLogMinorCutoff
    exact Nat.pow_le_pow_right hbase (by norm_num)
  exact (Finset.sum_Ico_eq_sub
    (fun denominator : ℕ =>
      ‖actualMajorArcRestrictedSignedCoefficient excluded denominator‖)
    hcutoff).symm


end Erdos689
