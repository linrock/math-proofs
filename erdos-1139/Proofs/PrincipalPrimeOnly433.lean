module

public import PrincipalArcPositivity433

@[expose] public section


/-!
# Removing proper prime powers inside the actual #689 principal arc

The positive principal-arc theorem concerns von-Mangoldt exponential sums.
This module controls their exact prime-filtered counterparts without
introducing an unproved three-prime counting assumption.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Every genuinely bounded von-Mangoldt window, with any integral affine
frequency, has the elementary uniform exponential-sum bound `n log n`. -/
theorem ternary_vonMangoldt_window_exponential_norm_le
    (window : Finset ℕ) (n : ℕ)
    (hwindow : window ⊆ Finset.Ioc 0 n)
    (frequency : ℤ) (α : ℝ) :
    ‖ternaryExponentialSum window
      (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      frequency α‖ ≤ (n : ℝ) * Real.log n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  unfold ternaryExponentialSum
  calc
    ‖∑ k ∈ window,
        ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) *
          GoldbachChain.e ((frequency : ℝ) * k * α)‖ ≤
        ∑ k ∈ window,
          ‖((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) *
            GoldbachChain.e ((frequency : ℝ) * k * α)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ window, Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn := Finset.mem_Ioc.mp (hwindow hk)
      rw [norm_mul, GoldbachChain.e_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hkn.1)
          (by exact_mod_cast hkn.2))
    _ = (window.card : ℝ) * Real.log (n : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * Real.log (n : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hlog
      have hcard := Finset.card_le_card hwindow
      have hcard' : window.card ≤ n := by simpa using hcard
      exact_mod_cast hcard'

/-- Filtering an arbitrary bounded affine exponential window down to actual
primes changes it by at most the complete proper-prime-power mass.  The
bound is uniform in the coefficient, rational center, and residue filter. -/
theorem ternary_vonMangoldt_prime_filtered_exponential_error
    (window : Finset ℕ) (n : ℕ)
    (hwindow : window ⊆ Finset.Ioc 0 n)
    (frequency : ℤ) (α : ℝ) :
    ‖ternaryExponentialSum window
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          frequency α -
        ternaryExponentialSum (window.filter Nat.Prime)
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          frequency α‖ ≤
      (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n := by
  let weight : ℕ → ℂ := fun k =>
    ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) *
      GoldbachChain.e ((frequency : ℝ) * k * α)
  let bad : Finset ℕ :=
    (window.filter fun k => ¬ k.Prime).filter
      fun k => ArithmeticFunction.vonMangoldt k ≠ 0
  have hsplit :
      ternaryExponentialSum window
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          frequency α -
        ternaryExponentialSum (window.filter Nat.Prime)
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          frequency α =
        ∑ k ∈ window.filter (fun k => ¬ k.Prime), weight k := by
    unfold ternaryExponentialSum
    dsimp [weight]
    rw [← Finset.sum_filter_add_sum_filter_not window Nat.Prime]
    ring
  have hremove :
      (∑ k ∈ window.filter (fun k => ¬ k.Prime), weight k) =
        ∑ k ∈ bad, weight k := by
    dsimp [bad]
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    split <;> rename_i h
    · rfl
    · dsimp [weight]
      have hzero : ArithmeticFunction.vonMangoldt k = 0 :=
        Classical.byContradiction h
      simp [hzero]
  have hbad : bad ⊆ ternaryProperPrimePowers n := by
    intro k hk
    obtain ⟨hkbad, hkweight⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkw, hkprime⟩ := Finset.mem_filter.mp hkbad
    apply Finset.mem_filter.mpr
    exact ⟨hwindow hkw, hkprime, hkweight⟩
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  rw [hsplit, hremove]
  calc
    ‖∑ k ∈ bad, weight k‖ ≤ ∑ k ∈ bad, ‖weight k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ bad, Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn := Finset.mem_Ioc.mp
        (Finset.mem_filter.mp (hbad hk)).1
      dsimp [weight]
      rw [norm_mul, GoldbachChain.e_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hkn.1)
          (by exact_mod_cast hkn.2))
    _ = (bad.card : ℝ) * Real.log (n : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((ternaryProperPrimePowers n).card : ℝ) *
          Real.log (n : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast Finset.card_le_card hbad
    _ ≤ (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n :=
      mul_le_mul_of_nonneg_right
        (ternaryProperPrimePowers_card_le n) hlog

/-- Exact three-factor removal of proper prime powers, uniformly for three
arbitrary actual windows and all three integer affine frequencies. -/
theorem ternary_vonMangoldt_prime_filtered_cubic_error
    (labels left center : Finset ℕ) (n : ℕ)
    (hlabels : labels ⊆ Finset.Ioc 0 n)
    (hleft : left ⊆ Finset.Ioc 0 n)
    (hcenter : center ⊆ Finset.Ioc 0 n)
    (labelFrequency leftFrequency centerFrequency : ℤ) (α : ℝ) :
    ‖ternaryExponentialSum labels
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          labelFrequency α *
        ternaryExponentialSum left
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          leftFrequency α *
        ternaryExponentialSum center
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          centerFrequency α -
      ternaryExponentialSum (labels.filter Nat.Prime)
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          labelFrequency α *
        ternaryExponentialSum (left.filter Nat.Prime)
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          leftFrequency α *
        ternaryExponentialSum (center.filter Nat.Prime)
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          centerFrequency α‖ ≤
      3 * ((n : ℝ) * Real.log n) ^ 2 *
        ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n) := by
  let weight : ℕ → ℂ :=
    fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)
  let X := ternaryExponentialSum labels weight labelFrequency α
  let Y := ternaryExponentialSum left weight leftFrequency α
  let Z := ternaryExponentialSum center weight centerFrequency α
  let x := ternaryExponentialSum (labels.filter Nat.Prime)
    weight labelFrequency α
  let y := ternaryExponentialSum (left.filter Nat.Prime)
    weight leftFrequency α
  let z := ternaryExponentialSum (center.filter Nat.Prime)
    weight centerFrequency α
  let B : ℝ := (n : ℝ) * Real.log n
  let E : ℝ :=
    (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hX : ‖X - x‖ ≤ E :=
    ternary_vonMangoldt_prime_filtered_exponential_error
      labels n hlabels labelFrequency α
  have hY : ‖Y - y‖ ≤ E :=
    ternary_vonMangoldt_prime_filtered_exponential_error
      left n hleft leftFrequency α
  have hZ : ‖Z - z‖ ≤ E :=
    ternary_vonMangoldt_prime_filtered_exponential_error
      center n hcenter centerFrequency α
  have hYbound : ‖Y‖ ≤ B :=
    ternary_vonMangoldt_window_exponential_norm_le
      left n hleft leftFrequency α
  have hZbound : ‖Z‖ ≤ B :=
    ternary_vonMangoldt_window_exponential_norm_le
      center n hcenter centerFrequency α
  have hxbound : ‖x‖ ≤ B :=
    ternary_vonMangoldt_window_exponential_norm_le
      (labels.filter Nat.Prime) n
      (fun k hk => hlabels (Finset.mem_of_mem_filter k hk))
      labelFrequency α
  have hybound : ‖y‖ ≤ B :=
    ternary_vonMangoldt_window_exponential_norm_le
      (left.filter Nat.Prime) n
      (fun k hk => hleft (Finset.mem_of_mem_filter k hk))
      leftFrequency α
  change ‖X * Y * Z - x * y * z‖ ≤ 3 * B ^ 2 * E
  have htel :
      X * Y * Z - x * y * z =
        (X - x) * Y * Z + x * (Y - y) * Z + x * y * (Z - z) := by
    ring
  rw [htel]
  calc
    ‖(X - x) * Y * Z + x * (Y - y) * Z + x * y * (Z - z)‖ ≤
        ‖(X - x) * Y * Z‖ + ‖x * (Y - y) * Z‖ +
          ‖x * y * (Z - z)‖ := by
      calc
        _ ≤ ‖(X - x) * Y * Z + x * (Y - y) * Z‖ +
              ‖x * y * (Z - z)‖ := norm_add_le _ _
        _ ≤ (‖(X - x) * Y * Z‖ + ‖x * (Y - y) * Z‖) +
              ‖x * y * (Z - z)‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ E * B * B + B * E * B + B * B * E := by
      simp only [norm_mul]
      gcongr
    _ = 3 * B ^ 2 * E := by ring

/-- Zero can be removed from any von-Mangoldt Fourier window exactly; this
lets the principal-arc result allow manuscript intervals starting at zero. -/
theorem ternary_vonMangoldt_exponentialSum_filter_positive
    (window : Finset ℕ) (frequency : ℤ) (α : ℝ) :
    ternaryExponentialSum window
        (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
        frequency α =
      ternaryExponentialSum (window.filter fun k => 0 < k)
        (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
        frequency α := by
  unfold ternaryExponentialSum
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  split <;> rename_i h
  · rfl
  · have hkzero : k = 0 := by omega
    subst k
    simp

/-- Positive filtering does not change a genuine prime window. -/
theorem ternary_filter_positive_filter_prime
    (window : Finset ℕ) :
    (window.filter fun k => 0 < k).filter Nat.Prime =
      window.filter Nat.Prime := by
  ext k
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hk, hpos⟩, hprime⟩
    exact ⟨hk, hprime⟩
  · rintro ⟨hk, hprime⟩
    exact ⟨⟨hk, hprime.pos⟩, hprime⟩

/-- The actual prime-only residue-cell cubic retains the genuine
von-Mangoldt prime weights (`log p`), all residue selectors, all three
independent intervals, and the rational major-arc center. -/
noncomputable def ternaryManuscriptResidueCubicPrimeOnly
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) (β : ℝ) : ℂ :=
  ternaryExponentialSum
      (((Finset.Ico labelLower labelUpper).filter
        fun n => n % modulus = labelResidue).filter Nat.Prime)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      1 ((numerator : ℝ) / modulus + β) *
    ternaryExponentialSum
      (((Finset.Ico leftLower leftUpper).filter
        fun n => n % modulus = leftResidue).filter Nat.Prime)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      (a : ℤ) ((numerator : ℝ) / modulus + β) *
    ternaryExponentialSum
      (((Finset.Ico rightLower rightUpper).filter
        fun n => n % modulus = rightResidue).filter Nat.Prime)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      (-2 * (d : ℤ)) ((numerator : ℝ) / modulus + β)

/-- Pointwise prime-power removal for the actual manuscript residue cubic,
without requiring any lower endpoint to be positive. -/
theorem ternaryManuscriptResidueCubicPrimeOnly_error
    (modulus labelResidue leftResidue rightResidue a d n : ℕ)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (hlabelUpper : labelUpper ≤ n)
    (hleftUpper : leftUpper ≤ n)
    (hrightUpper : rightUpper ≤ n)
    (numerator : ℤ) (β : ℝ) :
    ‖ternaryManuscriptResidueCubicVonMangoldt
          modulus labelResidue leftResidue rightResidue a d
          labelLower labelUpper leftLower leftUpper
          rightLower rightUpper numerator β -
      ternaryManuscriptResidueCubicPrimeOnly
          modulus labelResidue leftResidue rightResidue a d
          labelLower labelUpper leftLower leftUpper
          rightLower rightUpper numerator β‖ ≤
      3 * ((n : ℝ) * Real.log n) ^ 2 *
        ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n) := by
  let labels := (Finset.Ico labelLower labelUpper).filter
    fun k => k % modulus = labelResidue
  let left := (Finset.Ico leftLower leftUpper).filter
    fun k => k % modulus = leftResidue
  let center := (Finset.Ico rightLower rightUpper).filter
    fun k => k % modulus = rightResidue
  let α : ℝ := (numerator : ℝ) / modulus + β
  have hlabels :
      (labels.filter fun k => 0 < k) ⊆ Finset.Ioc 0 n := by
    intro k hk
    obtain ⟨hklabels, hkpositive⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkinterval, hkresidue⟩ := Finset.mem_filter.mp hklabels
    exact Finset.mem_Ioc.mpr
      ⟨hkpositive, (Nat.le_of_lt (Finset.mem_Ico.mp hkinterval).2).trans
        hlabelUpper⟩
  have hleft :
      (left.filter fun k => 0 < k) ⊆ Finset.Ioc 0 n := by
    intro k hk
    obtain ⟨hkleft, hkpositive⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkinterval, hkresidue⟩ := Finset.mem_filter.mp hkleft
    exact Finset.mem_Ioc.mpr
      ⟨hkpositive, (Nat.le_of_lt (Finset.mem_Ico.mp hkinterval).2).trans
        hleftUpper⟩
  have hcenter :
      (center.filter fun k => 0 < k) ⊆ Finset.Ioc 0 n := by
    intro k hk
    obtain ⟨hkcenter, hkpositive⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkinterval, hkresidue⟩ := Finset.mem_filter.mp hkcenter
    exact Finset.mem_Ioc.mpr
      ⟨hkpositive, (Nat.le_of_lt (Finset.mem_Ico.mp hkinterval).2).trans
        hrightUpper⟩
  have hcubic := ternary_vonMangoldt_prime_filtered_cubic_error
    (labels.filter fun k => 0 < k)
    (left.filter fun k => 0 < k)
    (center.filter fun k => 0 < k)
    n hlabels hleft hcenter 1 (a : ℤ) (-2 * (d : ℤ)) α
  rw [ternary_filter_positive_filter_prime,
    ternary_filter_positive_filter_prime,
    ternary_filter_positive_filter_prime] at hcubic
  rw [← ternary_vonMangoldt_exponentialSum_filter_positive labels 1 α,
    ← ternary_vonMangoldt_exponentialSum_filter_positive left (a : ℤ) α,
    ← ternary_vonMangoldt_exponentialSum_filter_positive
      center (-2 * (d : ℤ)) α] at hcubic
  exact hcubic

/-- On the true coefficient-sensitive principal arc, replacing all three
von-Mangoldt windows by actual prime-filtered windows costs at most the
already-proved global `O(n^(3/2) log^4 n)` error. -/
theorem ternaryManuscriptResidueCubicPrimeOnly_principal_integral_error_le
    (modulus labelResidue leftResidue rightResidue a d n : ℕ)
    (hn : 0 < n)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (hlabelUpper : labelUpper ≤ n)
    (hleftUpper : leftUpper ≤ n)
    (hrightUpper : rightUpper ≤ n)
    (numerator : ℤ) :
    ‖(∫ β in Set.Ioc (0 : ℝ)
          (1 / (4 * Real.pi *
            ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
        ternaryManuscriptResidueCubicVonMangoldt
          modulus labelResidue leftResidue rightResidue a d
          labelLower labelUpper leftLower leftUpper
          rightLower rightUpper numerator β) -
      (∫ β in Set.Ioc (0 : ℝ)
          (1 / (4 * Real.pi *
            ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
        ternaryManuscriptResidueCubicPrimeOnly
          modulus labelResidue leftResidue rightResidue a d
          labelLower labelUpper leftLower leftUpper
          rightLower rightUpper numerator β)‖ ≤
      ternaryPrimePowerErrorBound n := by
  let δ : ℝ := 1 / (4 * Real.pi *
    ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))
  let actual : ℝ → ℂ := fun β =>
    ternaryManuscriptResidueCubicVonMangoldt
      modulus labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator β
  let prime : ℝ → ℂ := fun β =>
    ternaryManuscriptResidueCubicPrimeOnly
      modulus labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator β
  let bound : ℝ :=
    3 * ((n : ℝ) * Real.log n) ^ 2 *
      ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hcentral : δ ≤ 1 / (n : ℝ) :=
    ternary_manuscript_principal_arc_le_central a d n hn
  have hone : 1 / (n : ℝ) ≤ 1 :=
    (div_le_iff₀ hnreal).mpr (by
      have : 1 ≤ n := hn
      have hreal : (1 : ℝ) ≤ n := by exact_mod_cast this
      simpa using hreal)
  have hsubset : Set.Ioc (0 : ℝ) δ ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro β hβ
    exact ⟨hβ.1, (hβ.2.trans hcentral).trans hone⟩
  have hactual : Continuous actual := by
    dsimp [actual, ternaryManuscriptResidueCubicVonMangoldt,
      ternaryExponentialSum]
    unfold GoldbachChain.e
    fun_prop
  have hprime : Continuous prime := by
    dsimp [prime, ternaryManuscriptResidueCubicPrimeOnly,
      ternaryExponentialSum]
    unfold GoldbachChain.e
    fun_prop
  have hpoint : ∀ β ∈ Set.Ioc (0 : ℝ) δ,
      ‖actual β - prime β‖ ≤ bound := by
    intro β hβ
    exact ternaryManuscriptResidueCubicPrimeOnly_error
      modulus labelResidue leftResidue rightResidue a d n
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper hlabelUpper hleftUpper hrightUpper
      numerator β
  have hintegrated := ternary_major_arc_integrated_constant_error
    (Set.Ioc (0 : ℝ) δ) measurableSet_Ioc hsubset actual prime
    hactual.integrableOn_Ioc hprime.integrableOn_Ioc bound hpoint
  rw [Real.volume_real_Ioc_of_le hδ.le, sub_zero] at hintegrated
  change
    ‖(∫ β in Set.Ioc (0 : ℝ) δ, actual β) -
      (∫ β in Set.Ioc (0 : ℝ) δ, prime β)‖ ≤
      ternaryPrimePowerErrorBound n
  calc
    _ ≤ bound * δ := hintegrated
    _ ≤ bound * (1 / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hcentral
      dsimp [bound]
      positivity
    _ = ternaryPrimePowerErrorBound n := by
      dsimp [bound, ternaryPrimePowerErrorBound]
      field_simp

/-- Proper prime powers are negligible inside the *actual truncated
principal-arc integral*, uniformly for all moving true manuscript windows. -/
theorem ternaryManuscriptResidueCubicPrimeOnly_principal_normalized_tendsto_zero
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (labelLower labelUpper leftLower leftUpper
      rightLower rightUpper : ℕ → ℕ)
    (hlabelUpper : ∀ n, labelUpper n ≤ n)
    (hleftUpper : ∀ n, leftUpper n ≤ n)
    (hrightUpper : ∀ n, rightUpper n ≤ n)
    (numerator : ℤ) :
    Tendsto
      (fun n : ℕ =>
        ‖(∫ β in Set.Ioc (0 : ℝ)
              (1 / (4 * Real.pi *
                ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
            ternaryManuscriptResidueCubicVonMangoldt
              modulus labelResidue leftResidue rightResidue a d
              (labelLower n) (labelUpper n)
              (leftLower n) (leftUpper n)
              (rightLower n) (rightUpper n) numerator β) -
          (∫ β in Set.Ioc (0 : ℝ)
              (1 / (4 * Real.pi *
                ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
            ternaryManuscriptResidueCubicPrimeOnly
              modulus labelResidue leftResidue rightResidue a d
              (labelLower n) (labelUpper n)
              (leftLower n) (leftUpper n)
              (rightLower n) (rightUpper n) numerator β)‖ /
          (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by positivity))
    _ ternaryPrimePowerErrorBound_normalized_tendsto_zero
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact ternaryManuscriptResidueCubicPrimeOnly_principal_integral_error_le
    modulus labelResidue leftResidue rightResidue a d n hn
    (labelLower n) (labelUpper n)
    (leftLower n) (leftUpper n)
    (rightLower n) (rightUpper n)
    (hlabelUpper n) (hleftUpper n) (hrightUpper n) numerator

/-- The genuinely PRIME-ONLY, residue-restricted, coefficient-sensitive
manuscript principal arc has an unconditional strictly positive quadratic
lower bound.  Every prime-power contribution has been removed inside the
actual Fourier integral; no global major-arc or prime-pattern hypothesis is
assumed.  Complementary shifted major arcs remain a separate issue. -/
theorem ternary_prime_only_principal_arc_eventually_quadratic_positive
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hlabelResidue : labelResidue < modulus)
    (hleftResidue : leftResidue < modulus)
    (hrightResidue : rightResidue < modulus)
    (hlabelUnit : Nat.gcd labelResidue modulus = 1)
    (hleftUnit : Nat.gcd leftResidue modulus = 1)
    (hrightUnit : Nat.gcd rightResidue modulus = 1)
    (hadmissible : (a * leftResidue + labelResidue) % modulus =
      (2 * d * rightResidue) % modulus)
    (labelLower labelUpper leftLower leftUpper
      rightLower rightUpper : ℕ → ℕ)
    (hlabelLower : ∀ n, labelLower n ≤ labelUpper n)
    (hlabelUpper : ∀ n, labelUpper n ≤ n)
    (hleftLower : ∀ n, leftLower n ≤ leftUpper n)
    (hleftUpper : ∀ n, leftUpper n ≤ n)
    (hrightLower : ∀ n, rightLower n ≤ rightUpper n)
    (hrightUpper : ∀ n, rightUpper n ≤ n)
    (κlabel κleft κright : ℝ)
    (hκlabel : 0 < κlabel)
    (hκleft : 0 < κleft)
    (hκright : 0 < κright)
    (hlabelWidth : ∀ᶠ n : ℕ in atTop,
      κlabel * (n : ℝ) ≤
        ((Finset.Ico (labelLower n) (labelUpper n)).card : ℝ))
    (hleftWidth : ∀ᶠ n : ℕ in atTop,
      κleft * (n : ℝ) ≤
        ((Finset.Ico (leftLower n) (leftUpper n)).card : ℝ))
    (hrightWidth : ∀ᶠ n : ℕ in atTop,
      κright * (n : ℝ) ≤
        ((Finset.Ico (rightLower n) (rightUpper n)).card : ℝ))
    (numerator : ℤ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ^ 2 ≤
        (∫ β in Set.Ioc (0 : ℝ)
          (1 / (4 * Real.pi *
            ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
          ternaryManuscriptResidueCubicPrimeOnly
            modulus labelResidue leftResidue rightResidue a d
            (labelLower n) (labelUpper n)
            (leftLower n) (leftUpper n)
            (rightLower n) (rightUpper n) numerator β).re := by
  obtain ⟨κ, hκ, hactual⟩ :=
    ternary_actual_principal_arc_eventually_quadratic_positive
      modulus labelResidue leftResidue rightResidue a d hmodulus
      hlabelResidue hleftResidue hrightResidue
      hlabelUnit hleftUnit hrightUnit hadmissible
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper hlabelLower hlabelUpper
      hleftLower hleftUpper hrightLower hrightUpper
      κlabel κleft κright hκlabel hκleft hκright
      hlabelWidth hleftWidth hrightWidth numerator
  refine ⟨κ / 2, by positivity, ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2 < κ / 2 :=
    (tendsto_order.1 ternaryPrimePowerErrorBound_normalized_tendsto_zero).2
      (κ / 2) (by positivity)
  filter_upwards [hactual, hsmall, eventually_ge_atTop 1] with
    n hactualn hsmalln hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have herror :=
    ternaryManuscriptResidueCubicPrimeOnly_principal_integral_error_le
      modulus labelResidue leftResidue rightResidue a d n hn
      (labelLower n) (labelUpper n)
      (leftLower n) (leftUpper n)
      (rightLower n) (rightUpper n)
      (hlabelUpper n) (hleftUpper n) (hrightUpper n) numerator
  have hreal :=
    (Complex.abs_re_le_norm
      ((∫ β in Set.Ioc (0 : ℝ)
            (1 / (4 * Real.pi *
              ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
          ternaryManuscriptResidueCubicVonMangoldt
            modulus labelResidue leftResidue rightResidue a d
            (labelLower n) (labelUpper n)
            (leftLower n) (leftUpper n)
            (rightLower n) (rightUpper n) numerator β) -
        (∫ β in Set.Ioc (0 : ℝ)
            (1 / (4 * Real.pi *
              ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
          ternaryManuscriptResidueCubicPrimeOnly
            modulus labelResidue leftResidue rightResidue a d
            (labelLower n) (labelUpper n)
            (leftLower n) (leftUpper n)
            (rightLower n) (rightUpper n) numerator β))).trans herror
  have hdiff := le_of_abs_le hreal
  have hquadratic : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnreal
  have hsmall' : ternaryPrimePowerErrorBound n < κ / 2 * (n : ℝ) ^ 2 :=
    (div_lt_iff₀ hquadratic).mp hsmalln
  change
    ((∫ β in Set.Ioc (0 : ℝ)
          (1 / (4 * Real.pi *
            ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
        ternaryManuscriptResidueCubicVonMangoldt
          modulus labelResidue leftResidue rightResidue a d
          (labelLower n) (labelUpper n)
          (leftLower n) (leftUpper n)
          (rightLower n) (rightUpper n) numerator β).re -
      (∫ β in Set.Ioc (0 : ℝ)
          (1 / (4 * Real.pi *
            ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
        ternaryManuscriptResidueCubicPrimeOnly
          modulus labelResidue leftResidue rightResidue a d
          (labelLower n) (labelUpper n)
          (leftLower n) (leftUpper n)
          (rightLower n) (rightUpper n) numerator β).re) ≤
      ternaryPrimePowerErrorBound n at hdiff
  linarith

end Erdos689

