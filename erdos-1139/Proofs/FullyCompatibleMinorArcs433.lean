module

public import CompatibleLogMinorArcs433

@[expose] public section


/-!
# Major-width-compatible shifted circle-method cutoffs for Erdős #689

The smaller cutoff `Q = 3 * P ^ 2` gives a genuine minor-arc theorem but its
major arcs are too wide for the available Siegel--Walfisz/Abel error.  For an
actual label endpoint `lower n`, take `P = floor(log n) ^ 12` and
`Q = lower n / P`.  This preserves every minor hypothesis while controlling
the Abel factor and separating all anchors after multiplication by any fixed
support modulus.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The Farey-width cutoff determined by the actual moving label endpoint. -/
noncomputable def fullyCompatibleFareyCutoff (lower : ℕ → ℕ) (n : ℕ) : ℕ :=
  lower n / compatibleLogMinorCutoff n

/-- The corrected cutoff automatically satisfies the *actual* label endpoint,
not merely the global Fourier scale. -/
theorem fullyCompatibleFareyCutoff_product_le
    (lower : ℕ → ℕ) (n : ℕ) :
    compatibleLogMinorCutoff n * fullyCompatibleFareyCutoff lower n ≤
      lower n := by
  unfold fullyCompatibleFareyCutoff
  exact Nat.mul_div_le _ _

/-- Every fixed multiple of the logarithmic denominator cube is eventually
below any genuinely positive-linear manuscript label endpoint. -/
theorem compatibleLogMinorCutoff_fixed_cube_le_linear_label_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (K : ℕ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop,
      K * compatibleLogMinorCutoff n ^ 3 ≤ lower n := by
  obtain ⟨N₀, hpoly⟩ :=
    GoldbachChain.polylog_le_self 36 ((K : ℝ) / κ) (by positivity)
  filter_upwards [eventually_ge_atTop N₀, hlinear] with n hn hlabel
  let L := compatibleLogBase n
  have hfloor : (L : ℝ) ≤ Real.log (n : ℝ) :=
    Nat.floor_le (Real.log_natCast_nonneg n)
  have hpow : (L : ℝ) ^ 36 ≤ Real.log (n : ℝ) ^ 36 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 36
  have hpoly' := hpoly n hn
  have hscale :
      (K : ℝ) * Real.log (n : ℝ) ^ 36 ≤ κ * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hpoly' hκ.le
    field_simp at h
    nlinarith
  have hbound : (K : ℝ) * (L : ℝ) ^ 36 ≤ (lower n : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg K)).trans
      (hscale.trans hlabel)
  have hcast :
      ((K * compatibleLogMinorCutoff n ^ 3 : ℕ) : ℝ) =
        (K : ℝ) * (L : ℝ) ^ 36 := by
    dsimp [compatibleLogMinorCutoff]
    push_cast
    ring
  exact_mod_cast hcast.symm ▸ hbound

/-- Unlike the old `Q = 3 * P ^ 2`, the corrected cutoff separates even the
merged shifted-anchor denominator family `q ≤ M * P`, for every fixed `M`.
-/
theorem fullyCompatibleFareyCutoff_merged_disjoint_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (M : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      2 * (M * compatibleLogMinorCutoff n) ^ 2 <
        fullyCompatibleFareyCutoff lower n + 1 := by
  filter_upwards
    [(tendsto_atTop.1 compatibleLogMinorCutoff_tendsto_atTop 1),
      compatibleLogMinorCutoff_fixed_cube_le_linear_label_eventually
        lower κ hκ hlinear (2 * (M + 1) ^ 2) (by positivity)]
    with n hP hcube
  let P := compatibleLogMinorCutoff n
  have hPpos : 0 < P := hP
  have hM : M ^ 2 ≤ (M + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_succ M) 2
  have htarget : 2 * (M * P) ^ 2 * P ≤ lower n := by
    have hfactor : 2 * (M * P) ^ 2 * P ≤
        (2 * (M + 1) ^ 2) * P ^ 3 := by
      calc
        2 * (M * P) ^ 2 * P = (2 * M ^ 2) * P ^ 3 := by ring
        _ ≤ (2 * (M + 1) ^ 2) * P ^ 3 :=
          Nat.mul_le_mul_right (P ^ 3) (Nat.mul_le_mul_left 2 hM)
    exact hfactor.trans hcube
  have hdiv : 2 * (M * P) ^ 2 ≤ lower n / P :=
    (Nat.le_div_iff_mul_le hPpos).mpr htarget
  change 2 * (M * P) ^ 2 < lower n / P + 1
  omega

/-- The exact available major-arc width has the essential Abel scale
`n / (Q + 1) ≤ P / κ`; the smaller old cutoff did not have this property. -/
theorem fullyCompatibleFareyCutoff_abel_scale_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (fullyCompatibleFareyCutoff lower n + 1 : ℕ) ≤
        (compatibleLogMinorCutoff n : ℝ) / κ := by
  filter_upwards
    [(tendsto_atTop.1 compatibleLogMinorCutoff_tendsto_atTop 1), hlinear]
    with n hP hlabel
  let P := compatibleLogMinorCutoff n
  let Q := fullyCompatibleFareyCutoff lower n
  have hPpos : 0 < P := hP
  have hlower : lower n < (Q + 1) * P := by
    have h := (Nat.div_lt_iff_lt_mul hPpos).mp
      (Nat.lt_succ_self (lower n / P))
    simpa [Q, fullyCompatibleFareyCutoff, P] using h
  have hlowerreal : (lower n : ℝ) <
      ((Q + 1 : ℕ) : ℝ) * (P : ℝ) := by
    exact_mod_cast hlower
  have hQ : 0 < ((Q + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_div_iff₀ hQ hκ).mpr
  nlinarith

/-- On every true Farey arc, including denominator `q = 1`, the available
Siegel--Walfisz/Abel oscillation factor is only logarithmic. -/
theorem fullyCompatibleFareyCutoff_major_beta_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, 0 < q → ∀ β : ℝ,
      |β| ≤ 1 / ((q : ℝ) *
          (fullyCompatibleFareyCutoff lower n + 1 : ℕ)) →
        (n : ℝ) * |β| ≤
          (compatibleLogMinorCutoff n : ℝ) / (κ * (q : ℝ)) := by
  filter_upwards
    [fullyCompatibleFareyCutoff_abel_scale_eventually
      lower κ hκ hlinear] with n hscale
  intro q hq β hβ
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    (n : ℝ) * |β| ≤
        (n : ℝ) * (1 /
          ((q : ℝ) * (fullyCompatibleFareyCutoff lower n + 1 : ℕ))) := by
      gcongr
    _ = ((n : ℝ) /
          (fullyCompatibleFareyCutoff lower n + 1 : ℕ)) / (q : ℝ) := by
      ring
    _ ≤ ((compatibleLogMinorCutoff n : ℝ) / κ) / (q : ℝ) := by
      exact div_le_div_of_nonneg_right hscale hqreal.le
    _ = (compatibleLogMinorCutoff n : ℝ) / (κ * (q : ℝ)) := by
      ring

/-- The corrected same-partition result: the actual residue-filtered,
archimedean-localized, coefficient-dilated cubic shifted-minor integral is
`o(n²)` at every original natural endpoint, with genuinely effective
major-arc widths and merged fixed-modulus Farey separation. -/
theorem ternary_shifted_minor_fully_compatible_all_scales_tendsto_zero
    (modulus residue : ℕ) (hmodulus : 0 < modulus)
    (lower : ℕ → ℕ) (hupper : ∀ n, lower n ≤ n)
    (κ : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (left center : ℕ → Finset ℕ)
    (hleft : ∀ n, left n ⊆ Finset.range n)
    (hcenter : ∀ n, center n ⊆ Finset.range n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    Tendsto
      (fun n : ℕ =>
        ‖∫ α in ternaryShiftedMinorArcs modulus
              (compatibleLogMinorCutoff n)
              (fullyCompatibleFareyCutoff lower n),
          ternaryExponentialSum
            ((Finset.Ioc (lower n) n).filter
              fun m => m % modulus = residue % modulus)
            (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
            1 α *
          ternaryExponentialSum (left n)
            (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
            (a : ℤ) α *
          ternaryExponentialSum (center n)
            (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
            (-2 * (d : ℤ)) α‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by positivity))
    _ compatible_log_shifted_minor_error_rate_tendsto_zero
  filter_upwards [eventually_ge_atTop 1,
      (tendsto_atTop.1 compatibleLogMinorCutoff_tendsto_atTop 2),
      compatibleLogMinorCutoff_fixed_cube_le_linear_label_eventually
        lower κ hκ hlower 1 (by norm_num)] with n hn hP hcube
  let P := compatibleLogMinorCutoff n
  let Q := fullyCompatibleFareyCutoff lower n
  have hPpos : 0 < P := by omega
  have hcube' : P ^ 3 ≤ lower n := by simpa [P] using hcube
  have hPQcut : P ≤ Q := by
    apply (Nat.le_div_iff_mul_le hPpos).mpr
    have hPpower : P * P ≤ P ^ 3 := by
      nlinarith [sq_nonneg (P : ℤ)]
    exact hPpower.trans hcube'
  have hproduct : P * Q ≤ lower n :=
    fullyCompatibleFareyCutoff_product_le lower n
  have hminor :=
    ternary_shifted_minor_residue_interval_dilated_window_integral_bound
      (lower n) n P Q modulus residue
      hP hcube' hPQcut hproduct (hupper n) hmodulus
      (left n) (center n) (hleft n) (hcenter n)
      (a : ℤ) (-2 * (d : ℤ))
      (by exact_mod_cast ha.ne') (by
        have : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
        exact mul_ne_zero (by norm_num) this)
  have hnreal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  calc
    _ ≤ (600 * (n : ℝ) ^ 2 * (Real.log n + 2) ^ 3 *
          Real.log n ^ 2 / Real.sqrt (P : ℝ)) / (n : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hminor (sq_nonneg _)
    _ = 600 * (Real.log n + 2) ^ 3 * Real.log n ^ 2 /
          Real.sqrt (P : ℝ) := by
      field_simp

end Erdos689

