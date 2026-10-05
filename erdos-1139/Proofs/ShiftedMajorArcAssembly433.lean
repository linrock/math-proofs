module

public import ThreePrimeMajorArcClosure433
public import ThreePrimeMajorArcError433
public import ThreePrimeLatticeLower433

@[expose] public section


/-!
# Exact shifted major/minor-arc assembly for Erdős #689

The already proved shifted-minor bound transfers to the actual affine
von-Mangoldt triple count.  Only the total real mass on the complementary
finite union of shifted major arcs remains to be controlled; positivity of a
single principal arc cannot be substituted for that missing control.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Exact partition of the fundamental Fourier circle into the simultaneous
shifted minor region and its finite union of shifted major regions.  The
major region is the actual set-theoretic complement, avoiding any overlap
or double-counting assumption about Farey arcs. -/
theorem ternary_shifted_major_minor_integral_partition
    (modulus P Q : ℕ) (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ α in Set.Ioc (0 : ℝ) 1, f α) =
      (∫ α in Set.Ioc (0 : ℝ) 1 \
        ternaryShiftedMinorArcs modulus P Q, f α) +
      (∫ α in ternaryShiftedMinorArcs modulus P Q, f α) := by
  have hminor : MeasurableSet (ternaryShiftedMinorArcs modulus P Q) :=
    ternaryShiftedMinorArcs_measurable modulus P Q
  have hsubset :
      ternaryShiftedMinorArcs modulus P Q ⊆ Set.Ioc (0 : ℝ) 1 :=
    Set.inter_subset_left
  have hintegrable : IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume :=
    hf.integrableOn_Ioc
  have hdiff := setIntegral_sdiff hminor hintegrable hsubset
  exact (eq_sub_iff_add_eq.mp hdiff).symm

/-- The actual von-Mangoldt weighted affine count is bounded below by the
real mass of the *entire* shifted major region, minus the independently
proved shifted-minor error.  All residue and archimedean filters, nonzero
manuscript coefficients, and the exact numerical constant are retained. -/
theorem ternary_shifted_major_arc_lower_for_actual_affine_vonMangoldt_count
    (lower N P Q modulus residue : ℕ)
    (hP : 2 ≤ P)
    (hPlower : P ^ 3 ≤ lower)
    (hPQcut : P ≤ Q)
    (hPQlower : P * Q ≤ lower)
    (hlower : lower ≤ N)
    (hmodulus : 0 < modulus)
    (left center : Finset ℕ)
    (hleft : left ⊆ Finset.range N)
    (hcenter : center ⊆ Finset.range N)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \
        ternaryShiftedMinorArcs modulus P Q,
      ternaryExponentialSum
        ((Finset.Ioc lower N).filter
          fun n => n % modulus = residue % modulus)
        (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        1 α *
      ternaryExponentialSum left
        (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        (a : ℤ) α *
      ternaryExponentialSum center
        (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        (-2 * (d : ℤ)) α).re -
        600 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
          Real.log N ^ 2 / Real.sqrt P ≤
      ∑ v ∈ ternaryAffineTriples left center
          ((Finset.Ioc lower N).filter
            fun n => n % modulus = residue % modulus)
          a (2 * d),
        ArithmeticFunction.vonMangoldt v.1 *
          ArithmeticFunction.vonMangoldt v.2.1 *
          ArithmeticFunction.vonMangoldt v.2.2 := by
  let labels : Finset ℕ :=
    (Finset.Ioc lower N).filter
      fun n => n % modulus = residue % modulus
  let weight : ℕ → ℂ :=
    fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  let f : ℝ → ℂ := fun α =>
    ternaryExponentialSum labels weight 1 α *
      ternaryExponentialSum left weight (a : ℤ) α *
      ternaryExponentialSum center weight (-2 * (d : ℤ)) α
  have hf : Continuous f := by
    dsimp [f, ternaryExponentialSum, weight]
    unfold GoldbachChain.e
    fun_prop
  have hminor :=
    ternary_shifted_minor_residue_interval_dilated_window_integral_bound
      lower N P Q modulus residue hP hPlower hPQcut hPQlower hlower
      hmodulus left center hleft hcenter (a : ℤ) (-2 * (d : ℤ))
      (by exact_mod_cast ha.ne') (by
        have : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
        exact mul_ne_zero (by norm_num) this)
  change
    ‖∫ α in ternaryShiftedMinorArcs modulus P Q, f α‖ ≤
      600 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
        Real.log N ^ 2 / Real.sqrt P at hminor
  have hpartition :=
    ternary_shifted_major_minor_integral_partition modulus P Q f hf
  have hreal :=
    (Complex.abs_re_le_norm
      (∫ α in ternaryShiftedMinorArcs modulus P Q, f α)).trans hminor
  have hlower := neg_le_of_abs_le hreal
  have hfourier := ternary_affine_nat_fourier_identity
    left center labels weight weight weight a (2 * d)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    at hfourier
  have hfrequency : (-(2 * d : ℕ) : ℤ) = -2 * (d : ℤ) := by
    push_cast
    ring
  rw [hfrequency] at hfourier
  have hfull :
      (∫ α in Set.Ioc (0 : ℝ) 1, f α) =
        ∑ v ∈ ternaryAffineTriples left center labels a (2 * d),
          weight v.1 * weight v.2.1 * weight v.2.2 := by
    rw [← hfourier]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro α hα
    dsimp [f]
    ring
  change
    (∫ α in Set.Ioc (0 : ℝ) 1 \
          ternaryShiftedMinorArcs modulus P Q, f α).re -
        600 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
          Real.log N ^ 2 / Real.sqrt P ≤ _
  have hsumreal :
      (∑ v ∈ ternaryAffineTriples left center labels a (2 * d),
        weight v.1 * weight v.2.1 * weight v.2.2).re =
      ∑ v ∈ ternaryAffineTriples left center labels a (2 * d),
        ArithmeticFunction.vonMangoldt v.1 *
          ArithmeticFunction.vonMangoldt v.2.1 *
          ArithmeticFunction.vonMangoldt v.2.2 := by
    simp [weight, Complex.mul_re]
  rw [← hsumreal, ← hfull]
  rw [hpartition, Complex.add_re]
  linarith

/-- A precise adversarial obstruction: a genuine three-window affine Fourier
cubic can have a strictly positive principal-arc integral while its entire
complement has strictly negative real mass.  Thus dropping or declaring
nonnegative the complementary shifted major arcs would be mathematically
false, even with positive unit weights and nonzero manuscript coefficients. -/
theorem ternary_principal_arc_complement_can_be_strictly_negative :
    (∫ β in Set.Ioc (0 : ℝ) 1 \
        Set.Ioc (0 : ℝ) (1 / (4 * Real.pi)),
      ternaryExponentialSum {1} (fun _ => 1) 1 β *
        ternaryExponentialSum {1} (fun _ => 1) (-1) β *
        ternaryExponentialSum {1} (fun _ => 1) 1 β).re ≤
      -(1 / (8 * Real.pi)) := by
  let f : ℝ → ℂ := fun β =>
    ternaryExponentialSum {1} (fun _ => 1) 1 β *
      ternaryExponentialSum {1} (fun _ => 1) (-1) β *
      ternaryExponentialSum {1} (fun _ => 1) 1 β
  let δ : ℝ := 1 / (4 * Real.pi)
  have hf : Continuous f := by
    dsimp [f, ternaryExponentialSum]
    unfold GoldbachChain.e
    fun_prop
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  have hsubset : Set.Ioc (0 : ℝ) δ ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro β hβ
    exact ⟨hβ.1, hβ.2.trans hδone⟩
  have hfull : (∫ β in Set.Ioc (0 : ℝ) 1, f β) = 0 := by
    have hempty :
        ternaryAffineTriples
          ({1} : Finset ℕ) ({1} : Finset ℕ) ({1} : Finset ℕ) 1 1 = ∅ := by
      ext ⟨x, y, z⟩
      simp [ternaryAffineTriples]
      omega
    have hfourier := ternary_affine_count_fourier_identity
      ({1} : Finset ℕ) ({1} : Finset ℕ) ({1} : Finset ℕ) 1 1
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      at hfourier
    rw [hempty] at hfourier
    simpa [f] using hfourier
  have hprincipal := ternary_unweighted_cubic_principal_arc_integral_lower
    ({1} : Finset ℕ) ({1} : Finset ℕ) ({1} : Finset ℕ)
    1 1 1 (by norm_num) (by
      intro x hx y hy z hz
      simp only [Finset.mem_singleton] at hx hy hz
      subst x
      subst y
      subst z
      norm_num)
  have hprincipal' :
      1 / (8 * Real.pi) ≤
        (∫ β in Set.Ioc (0 : ℝ) δ, f β).re := by
    simpa [f, δ] using hprincipal
  have hdiff := setIntegral_sdiff measurableSet_Ioc
    (show IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume from
      hf.integrableOn_Ioc) hsubset
  rw [hfull, zero_sub] at hdiff
  change (∫ β in Set.Ioc (0 : ℝ) 1 \ Set.Ioc (0 : ℝ) δ,
    f β).re ≤ -(1 / (8 * Real.pi))
  rw [hdiff, Complex.neg_re]
  linarith

/-- The complementary major-region negativity in the preceding concrete
example is strict, not a harmless zero-measure or endpoint artifact. -/
theorem ternary_principal_arc_complement_negative :
    (∫ β in Set.Ioc (0 : ℝ) 1 \
        Set.Ioc (0 : ℝ) (1 / (4 * Real.pi)),
      ternaryExponentialSum {1} (fun _ => 1) 1 β *
        ternaryExponentialSum {1} (fun _ => 1) (-1) β *
        ternaryExponentialSum {1} (fun _ => 1) 1 β).re < 0 := by
  calc
    _ ≤ -(1 / (8 * Real.pi)) :=
      ternary_principal_arc_complement_can_be_strictly_negative
    _ < 0 := neg_lt_zero.mpr (by positivity)

/-- The explicit Goldbach minor-arc rate is genuinely negligible at the
valid polynomial cutoff `N = m⁴`, `P = m`, `Q = m²`.  This is a proved
scalar limit, not a conjectural prime-distribution assumption. -/
theorem ternary_quartic_shifted_minor_error_rate_tendsto_zero :
    Tendsto
      (fun m : ℕ =>
        600 * (Real.log ((m ^ 4 : ℕ) : ℝ) + 2) ^ 3 *
          Real.log ((m ^ 4 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ))
      atTop (nhds 0) := by
  have hpower (k : ℕ) :
      Tendsto
        (fun m : ℕ =>
          Real.log (m : ℝ) ^ k / Real.sqrt (m : ℝ))
        atTop (nhds 0) := by
    have h :=
      (isLittleO_log_rpow_rpow_atTop (k : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have hnat := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, Real.sqrt_eq_rpow, Real.rpow_natCast]
      using hnat
  have hsum :=
    (((hpower 5).const_mul (600 * 1024 : ℝ)).add
      ((hpower 4).const_mul (600 * 1536 : ℝ))).add
      (((hpower 3).const_mul (600 * 768 : ℝ)).add
        ((hpower 2).const_mul (600 * 128 : ℝ)))
  convert hsum using 1
  · funext m
    push_cast
    rw [Real.log_pow]
    ring
  · norm_num

/-- On a valid explicit Goldbach cutoff, the *actual* residue-filtered,
archimedean-localized manuscript cubic has shifted-minor contribution
`o(N²)`.  The label lower endpoint may move arbitrarily between `m³` and
`N=m⁴`, and both other prime windows and their nonzero affine coefficients
are retained exactly. -/
theorem ternary_shifted_minor_quartic_scale_normalized_tendsto_zero
    (modulus residue : ℕ) (hmodulus : 0 < modulus)
    (lower : ℕ → ℕ)
    (hlower : ∀ m, m ^ 3 ≤ lower m)
    (hupper : ∀ m, lower m ≤ m ^ 4)
    (left center : ℕ → Finset ℕ)
    (hleft : ∀ m, left m ⊆ Finset.range (m ^ 4))
    (hcenter : ∀ m, center m ⊆ Finset.range (m ^ 4))
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    Tendsto
      (fun m : ℕ =>
        ‖∫ α in ternaryShiftedMinorArcs modulus m (m ^ 2),
          ternaryExponentialSum
            ((Finset.Ioc (lower m) (m ^ 4)).filter
              fun n => n % modulus = residue % modulus)
            (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            1 α *
          ternaryExponentialSum (left m)
            (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            (a : ℤ) α *
          ternaryExponentialSum (center m)
            (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            (-2 * (d : ℤ)) α‖ /
          (((m ^ 4 : ℕ) : ℝ) ^ 2))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun m => by positivity))
    _ ternary_quartic_shifted_minor_error_rate_tendsto_zero
  filter_upwards [eventually_ge_atTop 2] with m hm
  have hmzero : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  have hP : 2 ≤ m := hm
  have hPQcut : m ≤ m ^ 2 := by nlinarith
  have hPQlower : m * m ^ 2 ≤ lower m := by
    simpa [pow_succ, mul_assoc] using hlower m
  have hminor :=
    ternary_shifted_minor_residue_interval_dilated_window_integral_bound
      (lower m) (m ^ 4) m (m ^ 2) modulus residue
      hP (hlower m) hPQcut hPQlower (hupper m) hmodulus
      (left m) (center m) (hleft m) (hcenter m)
      (a : ℤ) (-2 * (d : ℤ))
      (by exact_mod_cast ha.ne') (by
        have : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
        exact mul_ne_zero (by norm_num) this)
  calc
    _ ≤ (600 * (((m ^ 4 : ℕ) : ℝ) ^ 2) *
          (Real.log ((m ^ 4 : ℕ) : ℝ) + 2) ^ 3 *
          Real.log ((m ^ 4 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ)) /
            (((m ^ 4 : ℕ) : ℝ) ^ 2) := by
      apply div_le_div_of_nonneg_right hminor
      positivity
    _ = 600 * (Real.log ((m ^ 4 : ℕ) : ℝ) + 2) ^ 3 *
          Real.log ((m ^ 4 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ) := by
      push_cast
      field_simp

end Erdos689

