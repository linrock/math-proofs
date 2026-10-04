module

public import ShiftedFareyDisjoint433

@[expose] public section


/-!
# Exact two-sided manuscript-strip minor arcs for Erdős #689

Earlier all-scale minor theorems use the upper-tail label window `(lower,n]`.
The actual manuscript window is `(lower,upper]`, with `upper < n/10` while
the other two prime windows still live at the global scale `n`.  This module
decouples the label upper endpoint from the Parseval/global endpoint and
proves the same `o(n²)` estimate on the fully compatible shifted partition.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Exact residue-filtered decomposition of a true two-sided label strip as
the difference of its two upper tails at any common ambient endpoint. -/
theorem ternary_filtered_Ioc_exponentialSum_eq_tail_sub
    (lower upper N modulus residue : ℕ)
    (hlower : lower ≤ upper) (hupper : upper ≤ N)
    (weight : ℕ → ℂ) (frequency : ℤ) (α : ℝ) :
    ternaryExponentialSum
        ((Finset.Ioc lower upper).filter
          fun m => m % modulus = residue)
        weight frequency α =
      ternaryExponentialSum
          ((Finset.Ioc lower N).filter
            fun m => m % modulus = residue)
          weight frequency α -
        ternaryExponentialSum
          ((Finset.Ioc upper N).filter
            fun m => m % modulus = residue)
          weight frequency α := by
  have hdisjoint : Disjoint
      (Finset.Ioc lower upper) (Finset.Ioc upper N) :=
    Finset.Ioc_disjoint_Ioc_of_le (le_refl upper)
  have hunion :
      Finset.Ioc lower upper ∪ Finset.Ioc upper N =
        Finset.Ioc lower N :=
    Finset.Ioc_union_Ioc_eq_Ioc hlower hupper
  unfold ternaryExponentialSum
  simp_rw [Finset.sum_filter]
  apply (eq_sub_iff_add_eq).mpr
  rw [← Finset.sum_union hdisjoint, hunion]

/-- Actual two-sided residue-strip minor bound with genuinely independent
label upper endpoint and global Fourier/Parseval endpoint.  The numerical
constant remains `600`; no two-tail factor is lost. -/
theorem ternary_shifted_minor_exact_strip_dilated_window_integral_bound
    (lower upper N P Q modulus residue : ℕ)
    (hP : 2 ≤ P)
    (hPlower : P ^ 3 ≤ lower)
    (hPQcut : P ≤ Q)
    (hPQlower : P * Q ≤ lower)
    (hlower : lower ≤ upper)
    (hupper : upper ≤ N)
    (hmodulus : 0 < modulus)
    (left right : Finset ℕ)
    (hleft : left ⊆ Finset.range N)
    (hright : right ⊆ Finset.range N)
    (leftFrequency rightFrequency : ℤ)
    (hleftFrequency : leftFrequency ≠ 0)
    (hrightFrequency : rightFrequency ≠ 0) :
    ‖∫ α in ternaryShiftedMinorArcs modulus P Q,
      ternaryExponentialSum
        ((Finset.Ioc lower upper).filter
          fun n => n % modulus = residue % modulus)
        (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        1 α *
      ternaryExponentialSum left
        (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        leftFrequency α *
      ternaryExponentialSum right
        (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        rightFrequency α‖ ≤
      600 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
        Real.log N ^ 2 / Real.sqrt P := by
  let first : ℝ → ℂ := fun α =>
    ternaryExponentialSum
      ((Finset.Ioc lower upper).filter
        fun n => n % modulus = residue % modulus)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      1 α
  let second : ℝ → ℂ := fun α =>
    ternaryExponentialSum left
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      leftFrequency α
  let third : ℝ → ℂ := fun α =>
    ternaryExponentialSum right
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      rightFrequency α
  let minor : Set ℝ := ternaryShiftedMinorArcs modulus P Q
  let bound : ℝ :=
    600 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P
  have hPone : 1 ≤ P := by omega
  have hupperone : 1 ≤ upper := by
    have : 1 ≤ P ^ 3 := one_le_pow₀ hPone
    omega
  have hNone : 1 ≤ N := hupperone.trans hupper
  have hlog : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast hNone)
  have hbound : 0 ≤ bound := by
    dsimp [bound]
    positivity
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
  have hminor : MeasurableSet minor :=
    ternaryShiftedMinorArcs_measurable modulus P Q
  have hsubset : minor ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_left
  have hsup : ∀ α ∈ minor, ‖first α‖ ≤ bound := by
    intro α hα
    have hexact := ternary_shifted_minor_residue_interval_vonMangoldt_sup
      lower upper P Q modulus residue hP hPlower hPQcut hPQlower
      hlower hmodulus α hα
    have hmono := ternary_minor_prefix_bound_mono upper N P hupperone hupper
    change ‖first α‖ ≤ bound
    calc
      ‖first α‖ ≤
          600 * (upper : ℝ) * (Real.log upper + 2) ^ 3 /
            Real.sqrt P := hexact
      _ = 2 * (300 * (upper : ℝ) * (Real.log upper + 2) ^ 3 /
          Real.sqrt P) := by ring
      _ ≤ 2 * (300 * (N : ℝ) * (Real.log N + 2) ^ 3 /
          Real.sqrt P) := by gcongr
      _ = bound := by dsimp [bound]; ring
  have hquadratic := ternary_minor_integral_le_quadratic_energy
    first second third hfirst hsecond hthird minor hminor hsubset
    bound hbound hsup
  have hleftEnergy :
      (∫ α in (0 : ℝ)..1, ‖second α‖ ^ 2) ≤
        (N : ℝ) * Real.log N ^ 2 :=
    ternary_vonMangoldt_dilated_window_parseval_le
      left N hleft leftFrequency hleftFrequency
  have hrightEnergy :
      (∫ α in (0 : ℝ)..1, ‖third α‖ ^ 2) ≤
        (N : ℝ) * Real.log N ^ 2 :=
    ternary_vonMangoldt_dilated_window_parseval_le
      right N hright rightFrequency hrightFrequency
  change
    ‖∫ α in minor, first α * second α * third α‖ ≤
      600 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
        Real.log N ^ 2 / Real.sqrt P
  calc
    ‖∫ α in minor, first α * second α * third α‖ ≤
        bound / 2 *
          ((∫ α in (0 : ℝ)..1, ‖second α‖ ^ 2) +
            (∫ α in (0 : ℝ)..1, ‖third α‖ ^ 2)) := hquadratic
    _ ≤ bound / 2 *
          ((N : ℝ) * Real.log N ^ 2 +
            (N : ℝ) * Real.log N ^ 2) := by
      apply mul_le_mul_of_nonneg_left
        (add_le_add hleftEnergy hrightEnergy)
      positivity
    _ = 600 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
          Real.log N ^ 2 / Real.sqrt P := by
      dsimp [bound]
      ring

/-- The exact original two-sided manuscript label strip, with both moving
endpoints and both independent global prime windows, has negligible actual
shifted-minor contribution on the fully major-compatible partition at every
original integer endpoint. -/
theorem ternary_shifted_minor_exact_strip_fully_compatible_tendsto_zero
    (modulus residue : ℕ) (hmodulus : 0 < modulus)
    (lower upper : ℕ → ℕ)
    (horder : ∀ n, lower n ≤ upper n)
    (hupper : ∀ n, upper n ≤ n)
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
            ((Finset.Ioc (lower n) (upper n)).filter
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
    ternary_shifted_minor_exact_strip_dilated_window_integral_bound
      (lower n) (upper n) n P Q modulus residue
      hP hcube' hPQcut hproduct (horder n) (hupper n) hmodulus
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

#print axioms Erdos689.ternary_filtered_Ioc_exponentialSum_eq_tail_sub
#print axioms Erdos689.ternary_shifted_minor_exact_strip_dilated_window_integral_bound
#print axioms Erdos689.ternary_shifted_minor_exact_strip_fully_compatible_tendsto_zero
