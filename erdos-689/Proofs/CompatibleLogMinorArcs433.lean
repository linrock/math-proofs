module

public import ShiftedMajorArcAssembly433

@[expose] public section


/-!
# Simultaneously compatible logarithmic major/minor cutoffs for Erdős #689

The explicit cutoffs `L=floor(log n)`, `P=L^12`, `Q=3P^2` simultaneously
give negligible cubic shifted minor arcs, Siegel--Walfisz-sized major-arc
denominators, and pairwise disjoint Farey anchor arcs.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The genuine floored natural logarithm, including every small endpoint. -/
noncomputable def compatibleLogBase (n : ℕ) : ℕ :=
  Nat.floor (Real.log (n : ℝ))

/-- The compatible logarithmic major-arc denominator cutoff. -/
noncomputable def compatibleLogMinorCutoff (n : ℕ) : ℕ :=
  compatibleLogBase n ^ 12

/-- A Farey denominator cutoff large enough for genuine anchor disjointness. -/
noncomputable def compatibleLogFareyCutoff (n : ℕ) : ℕ :=
  3 * compatibleLogMinorCutoff n ^ 2

/-- The exact floored logarithm tends to infinity at every natural endpoint. -/
theorem compatibleLogBase_tendsto_atTop :
    Tendsto compatibleLogBase atTop atTop := by
  unfold compatibleLogBase
  exact tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The genuine logarithmic major denominator cutoff tends to infinity. -/
theorem compatibleLogMinorCutoff_tendsto_atTop :
    Tendsto compatibleLogMinorCutoff atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 compatibleLogBase_tendsto_atTop
      (max b 1))] with n hn
  have hbase : b ≤ compatibleLogBase n := le_trans (le_max_left _ _) hn
  have hone : 1 ≤ compatibleLogBase n := le_trans (le_max_right _ _) hn
  unfold compatibleLogMinorCutoff
  exact hbase.trans (Nat.le_self_pow (by norm_num) _)

/-- The actual major-arc denominator is bounded by the twelfth logarithmic
power, exactly the range required by Siegel--Walfisz. -/
theorem compatibleLogMinorCutoff_le_log_pow_twelve (n : ℕ) :
    (compatibleLogMinorCutoff n : ℝ) ≤ Real.log (n : ℝ) ^ 12 := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hfloor : (compatibleLogBase n : ℝ) ≤ Real.log (n : ℝ) :=
    Nat.floor_le hlog
  unfold compatibleLogMinorCutoff
  push_cast
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 12

/-- After multiplication by any fixed support modulus, the true common
major-arc denominator remains in the fixed Siegel--Walfisz range
`(log n)^13`. -/
theorem compatibleLogMinorCutoff_fixed_modulus_le_log_pow_thirteen
    (M : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (M : ℝ) * (compatibleLogMinorCutoff n : ℝ) ≤
        Real.log (n : ℝ) ^ 13 := by
  have hlogtop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [(tendsto_atTop.1 hlogtop (M : ℝ))] with n hn
  calc
    (M : ℝ) * (compatibleLogMinorCutoff n : ℝ) ≤
      Real.log (n : ℝ) * Real.log (n : ℝ) ^ 12 := by
        exact mul_le_mul hn
          (compatibleLogMinorCutoff_le_log_pow_twelve n)
          (Nat.cast_nonneg _)
          (Real.log_natCast_nonneg n)
    _ = Real.log (n : ℝ) ^ 13 := by ring

/-- The exact real square root of the compatible denominator is the sixth
power of the genuine floored logarithm. -/
theorem compatibleLogMinorCutoff_real_sqrt (n : ℕ) :
    Real.sqrt (compatibleLogMinorCutoff n : ℝ) =
      (compatibleLogBase n : ℝ) ^ 6 := by
  unfold compatibleLogMinorCutoff
  push_cast
  rw [show (compatibleLogBase n : ℝ) ^ 12 =
    ((compatibleLogBase n : ℝ) ^ 6) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- The chosen Farey cutoff satisfies the actual strict pairwise-disjointness
condition used by the imported Goldbach major-arc assembly. -/
theorem compatibleLogFareyCutoff_disjoint (n : ℕ) :
    2 * compatibleLogMinorCutoff n ^ 2 <
      compatibleLogFareyCutoff n + 1 := by
  unfold compatibleLogFareyCutoff
  nlinarith [sq_nonneg (compatibleLogMinorCutoff n : ℤ)]

/-- The exact cubic shifted-minor rate tends to zero with the SAME
logarithmic cutoff that remains admissible for Siegel--Walfisz. -/
theorem compatible_log_shifted_minor_error_rate_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        600 * (Real.log (n : ℝ) + 2) ^ 3 * Real.log (n : ℝ) ^ 2 /
          Real.sqrt (compatibleLogMinorCutoff n : ℝ))
      atTop (nhds 0) := by
  let K : ℝ := 600 * 4 ^ (3 : ℕ) * 2 ^ (2 : ℕ)
  have hbaseReal :
      Tendsto (fun n : ℕ => (compatibleLogBase n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      compatibleLogBase_tendsto_atTop
  have hmajor :
      Tendsto
        (fun n : ℕ => K * (compatibleLogBase n : ℝ)⁻¹)
        atTop (nhds 0) := by
    simpa using hbaseReal.inv_tendsto_atTop.const_mul K
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by positivity)) _ hmajor
  filter_upwards
    [(tendsto_atTop.1 compatibleLogBase_tendsto_atTop 1)] with n hL
  let L := compatibleLogBase n
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hfloor : Real.log (n : ℝ) < (L : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.log (n : ℝ))
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hlogbound : Real.log (n : ℝ) ≤ 2 * (L : ℝ) := by
    have hLone : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hplusbound : Real.log (n : ℝ) + 2 ≤ 4 * (L : ℝ) := by
    have hLone : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  rw [compatibleLogMinorCutoff_real_sqrt]
  change
    600 * (Real.log (n : ℝ) + 2) ^ 3 * Real.log (n : ℝ) ^ 2 /
        (L : ℝ) ^ 6 ≤ K * (L : ℝ)⁻¹
  calc
    600 * (Real.log (n : ℝ) + 2) ^ 3 * Real.log (n : ℝ) ^ 2 /
        (L : ℝ) ^ 6 ≤
      600 * (4 * (L : ℝ)) ^ 3 * (2 * (L : ℝ)) ^ 2 /
        (L : ℝ) ^ 6 := by
      gcongr
    _ = K * (L : ℝ)⁻¹ := by
      dsimp [K]
      field_simp

/-- Any positive-linear genuine label lower endpoint eventually dominates
the full Farey product `P*Q=3P³`.  This simultaneously discharges BOTH
Goldbach minor-arc eligibility conditions. -/
theorem compatibleLogFareyCutoff_product_le_linear_label_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      compatibleLogMinorCutoff n * compatibleLogFareyCutoff n ≤ lower n := by
  obtain ⟨N₀, hpoly⟩ :=
    GoldbachChain.polylog_le_self 36 (3 / κ) (by positivity)
  filter_upwards [eventually_ge_atTop N₀, hlinear] with n hn hlabel
  let L := compatibleLogBase n
  let P := compatibleLogMinorCutoff n
  have hfloor : (L : ℝ) ≤ Real.log (n : ℝ) :=
    Nat.floor_le (Real.log_natCast_nonneg n)
  have hpow : (L : ℝ) ^ 36 ≤ Real.log (n : ℝ) ^ 36 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 36
  have hpoly' := hpoly n hn
  have hthree : 3 * (L : ℝ) ^ 36 ≤ κ * (n : ℝ) := by
    have hscale : 3 * Real.log (n : ℝ) ^ 36 ≤ κ * (n : ℝ) := by
      have := (mul_le_mul_of_nonneg_left hpoly' hκ.le)
      field_simp at this
      nlinarith
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3 by norm_num)
      (sub_nonneg.mpr hpow)]
  have hproduct :
      ((compatibleLogMinorCutoff n * compatibleLogFareyCutoff n : ℕ) : ℝ) =
        3 * (L : ℝ) ^ 36 := by
    dsimp [compatibleLogFareyCutoff, compatibleLogMinorCutoff]
    push_cast
    ring
  have hresult :
      ((compatibleLogMinorCutoff n * compatibleLogFareyCutoff n : ℕ) : ℝ) ≤
        (lower n : ℝ) := by
    rw [hproduct]
    exact hthree.trans hlabel
  exact_mod_cast hresult

/-- The ACTUAL residue-filtered moving-label affine cubic has negligible
shifted-minor contribution at EVERY original endpoint on the SAME partition
that admits both Siegel--Walfisz major-arc evaluation and pairwise-disjoint
Farey anchors.  No cutoff-growth, denominator-compatibility, or analytic
minor-arc hypothesis is assumed. -/
theorem ternary_shifted_minor_compatible_log_all_scales_tendsto_zero
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
              (compatibleLogFareyCutoff n),
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
      compatibleLogFareyCutoff_product_le_linear_label_eventually
        lower κ hκ hlower] with n hn hP hproduct
  let P := compatibleLogMinorCutoff n
  let Q := compatibleLogFareyCutoff n
  have hPQcut : P ≤ Q := by
    dsimp [Q, compatibleLogFareyCutoff]
    nlinarith
  have hcube : P ^ 3 ≤ lower n := by
    calc
      P ^ 3 ≤ 3 * P ^ 3 := by omega
      _ = P * Q := by
        dsimp [Q, compatibleLogFareyCutoff]
        ring
      _ ≤ lower n := hproduct
  have hminor :=
    ternary_shifted_minor_residue_interval_dilated_window_integral_bound
      (lower n) n P Q modulus residue
      hP hcube hPQcut hproduct (hupper n) hmodulus
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

#print axioms Erdos689.compatibleLogBase_tendsto_atTop
#print axioms Erdos689.compatibleLogMinorCutoff_tendsto_atTop
#print axioms Erdos689.compatibleLogMinorCutoff_le_log_pow_twelve
#print axioms Erdos689.compatibleLogMinorCutoff_fixed_modulus_le_log_pow_thirteen
#print axioms Erdos689.compatibleLogMinorCutoff_real_sqrt
#print axioms Erdos689.compatibleLogFareyCutoff_disjoint
#print axioms Erdos689.compatible_log_shifted_minor_error_rate_tendsto_zero
#print axioms Erdos689.compatibleLogFareyCutoff_product_le_linear_label_eventually
#print axioms Erdos689.ternary_shifted_minor_compatible_log_all_scales_tendsto_zero
