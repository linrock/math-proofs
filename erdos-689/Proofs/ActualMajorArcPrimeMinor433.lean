import ActualMajorArcWeightedBridge433
import PrincipalPrimeOnly433

/-!
# Actual prime-only shifted minor arcs for the original manuscript patterns

The exact weighted bridge uses genuine-prime label windows, whereas the
existing Vaughan bound applies to von-Mangoldt windows containing proper
prime powers.  A supremum prime-power error combined with the two actual
quadratic energies gives the correct `o(n²)` transfer on the full minor
region, without pretending that pointwise cubic errors integrate cheaply.

Global major-arc positivity and singular-series evaluation remain open.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Filtering only the label window to actual primes changes any shifted
minor-region cubic by at most the already-audited coefficient-uniform
three-prime prime-power error.  The key is `L∞ × L² × L²`, not a false
pointwise-cubic-times-unit-measure estimate. -/
theorem ternary_prime_filtered_label_minor_integral_error_le
    (labels left center : Finset ℕ) (n : ℕ)
    (hlabels : labels ⊆ Finset.Ioc 0 n)
    (hleft : left ⊆ Finset.range n)
    (hcenter : center ⊆ Finset.range n)
    (leftFrequency centerFrequency : ℤ)
    (hleftFrequency : leftFrequency ≠ 0)
    (hcenterFrequency : centerFrequency ≠ 0)
    (minor : Set ℝ)
    (hminor : MeasurableSet minor)
    (hsubset : minor ⊆ Set.Ioc (0 : ℝ) 1) :
    ‖(∫ α in minor,
        ternaryExponentialSum labels
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          1 α *
        ternaryExponentialSum left
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          leftFrequency α *
        ternaryExponentialSum center
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          centerFrequency α) -
      (∫ α in minor,
        ternaryExponentialSum (labels.filter Nat.Prime)
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          1 α *
        ternaryExponentialSum left
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          leftFrequency α *
        ternaryExponentialSum center
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          centerFrequency α)‖ ≤
      ternaryPrimePowerErrorBound n := by
  let weight : ℕ → ℂ :=
    fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)
  let first : ℝ → ℂ := fun α =>
    ternaryExponentialSum labels weight 1 α -
      ternaryExponentialSum (labels.filter Nat.Prime) weight 1 α
  let second : ℝ → ℂ := fun α =>
    ternaryExponentialSum left weight leftFrequency α
  let third : ℝ → ℂ := fun α =>
    ternaryExponentialSum center weight centerFrequency α
  let bound : ℝ :=
    (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) * Real.log n
  have hfirst : Continuous first := by
    dsimp [first, ternaryExponentialSum, weight]
    unfold GoldbachChain.e
    fun_prop
  have hsecond : Continuous second := by
    dsimp [second, ternaryExponentialSum, weight]
    unfold GoldbachChain.e
    fun_prop
  have hthird : Continuous third := by
    dsimp [third, ternaryExponentialSum, weight]
    unfold GoldbachChain.e
    fun_prop
  have hbound : 0 ≤ bound := by
    dsimp [bound]
    exact mul_nonneg
      (mul_nonneg (by positivity) (by positivity))
      (Real.log_natCast_nonneg n)
  have hsup : ∀ α ∈ minor, ‖first α‖ ≤ bound := by
    intro α hα
    exact ternary_vonMangoldt_prime_filtered_exponential_error
      labels n hlabels 1 α
  have hquadratic := ternary_minor_integral_le_quadratic_energy
    first second third hfirst hsecond hthird minor hminor hsubset
    bound hbound hsup
  have hleftEnergy :
      (∫ α in (0 : ℝ)..1, ‖second α‖ ^ 2) ≤
        (n : ℝ) * Real.log n ^ 2 :=
    ternary_vonMangoldt_dilated_window_parseval_le
      left n hleft leftFrequency hleftFrequency
  have hcenterEnergy :
      (∫ α in (0 : ℝ)..1, ‖third α‖ ^ 2) ≤
        (n : ℝ) * Real.log n ^ 2 :=
    ternary_vonMangoldt_dilated_window_parseval_le
      center n hcenter centerFrequency hcenterFrequency
  have hfull : Continuous (fun α =>
      ternaryExponentialSum labels weight 1 α *
        second α * third α) := by
    dsimp [second, third, ternaryExponentialSum, weight]
    unfold GoldbachChain.e
    fun_prop
  have hprime : Continuous (fun α =>
      ternaryExponentialSum (labels.filter Nat.Prime) weight 1 α *
        second α * third α) := by
    dsimp [second, third, ternaryExponentialSum, weight]
    unfold GoldbachChain.e
    fun_prop
  have hintegral :
      (∫ α in minor,
        ternaryExponentialSum labels weight 1 α *
          second α * third α) -
      (∫ α in minor,
        ternaryExponentialSum (labels.filter Nat.Prime) weight 1 α *
          second α * third α) =
        ∫ α in minor, first α * second α * third α := by
    rw [← MeasureTheory.integral_sub
      (hfull.integrableOn_Ioc.mono_set hsubset)
      (hprime.integrableOn_Ioc.mono_set hsubset)]
    apply setIntegral_congr_fun hminor
    intro α hα
    dsimp [first]
    ring
  change
    ‖(∫ α in minor,
        ternaryExponentialSum labels weight 1 α *
          second α * third α) -
      (∫ α in minor,
        ternaryExponentialSum (labels.filter Nat.Prime) weight 1 α *
          second α * third α)‖ ≤ _
  rw [hintegral]
  calc
    ‖∫ α in minor, first α * second α * third α‖ ≤
        bound / 2 *
          ((∫ α in (0 : ℝ)..1, ‖second α‖ ^ 2) +
            (∫ α in (0 : ℝ)..1, ‖third α‖ ^ 2)) := hquadratic
    _ ≤ bound / 2 *
          ((n : ℝ) * Real.log n ^ 2 +
            (n : ℝ) * Real.log n ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hleftEnergy hcenterEnergy) (by positivity)
    _ ≤ ternaryPrimePowerErrorBound n := by
      dsimp [bound, ternaryPrimePowerErrorBound]
      have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)
        (mul_nonneg (show (0 : ℝ) ≤ (Nat.sqrt n : ℝ) by positivity)
          (mul_nonneg (show (0 : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 by positivity)
            (show (0 : ℝ) ≤ Real.log (n : ℝ) ^ 3 by positivity)))]

/-- For arbitrary moving genuine windows and arbitrary measurable moving
minor subsets of the fundamental circle, replacing the label window by
its actual prime filter costs `o(n²)`. -/
theorem ternary_prime_filtered_label_minor_error_normalized_tendsto_zero
    (labels left center : ℕ → Finset ℕ)
    (hlabels : ∀ n, labels n ⊆ Finset.Ioc 0 n)
    (hleft : ∀ n, left n ⊆ Finset.range n)
    (hcenter : ∀ n, center n ⊆ Finset.range n)
    (leftFrequency centerFrequency : ℤ)
    (hleftFrequency : leftFrequency ≠ 0)
    (hcenterFrequency : centerFrequency ≠ 0)
    (minor : ℕ → Set ℝ)
    (hminor : ∀ n, MeasurableSet (minor n))
    (hsubset : ∀ n, minor n ⊆ Set.Ioc (0 : ℝ) 1) :
    Tendsto
      (fun n : ℕ =>
        ‖(∫ α in minor n,
            ternaryExponentialSum (labels n)
              (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
              1 α *
            ternaryExponentialSum (left n)
              (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
              leftFrequency α *
            ternaryExponentialSum (center n)
              (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
              centerFrequency α) -
          (∫ α in minor n,
            ternaryExponentialSum ((labels n).filter Nat.Prime)
              (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
              1 α *
            ternaryExponentialSum (left n)
              (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
              leftFrequency α *
            ternaryExponentialSum (center n)
              (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
              centerFrequency α)‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by positivity))
    _ ternaryPrimePowerErrorBound_normalized_tendsto_zero
  exact Eventually.of_forall fun n =>
    div_le_div_of_nonneg_right
      (ternary_prime_filtered_label_minor_integral_error_le
        (labels n) (left n) (center n) n
        (hlabels n) (hleft n) (hcenter n)
        leftFrequency centerFrequency
        hleftFrequency hcenterFrequency
        (minor n) (hminor n) (hsubset n))
      (sq_nonneg _)

/-- The true two-sided residue-strip minor theorem remains valid after
restricting the label coordinate to *actual primes*.  Both other windows
remain arbitrary, the affine frequencies are the original `a,-2d`, and
the Farey cutoffs are the fully major-compatible endpoint-dependent ones. -/
theorem ternary_shifted_minor_exact_strip_prime_only_fully_compatible_tendsto_zero
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
            (((Finset.Ioc (lower n) (upper n)).filter
              fun m => m % modulus = residue % modulus).filter Nat.Prime)
            (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
            1 α *
          ternaryExponentialSum (left n)
            (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
            (a : ℤ) α *
          ternaryExponentialSum (center n)
            (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
            (-2 * (d : ℤ)) α‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  let labels : ℕ → Finset ℕ := fun n =>
    (Finset.Ioc (lower n) (upper n)).filter
      fun m => m % modulus = residue % modulus
  let minor : ℕ → Set ℝ := fun n =>
    ternaryShiftedMinorArcs modulus
      (compatibleLogMinorCutoff n)
      (fullyCompatibleFareyCutoff lower n)
  let weight : ℕ → ℂ :=
    fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)
  have hlabels : ∀ n, labels n ⊆ Finset.Ioc 0 n := by
    intro n m hm
    obtain ⟨hmstrip, _⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmlower, hmupper⟩ := Finset.mem_Ioc.mp hmstrip
    exact Finset.mem_Ioc.mpr ⟨by omega, hmupper.trans (hupper n)⟩
  have haminus : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hdminus : (-2 * (d : ℤ)) ≠ 0 := by
    have : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
    exact mul_ne_zero (by norm_num) this
  have hfull :=
    ternary_shifted_minor_exact_strip_fully_compatible_tendsto_zero
      modulus residue hmodulus lower upper horder hupper
      κ hκ hlower left center hleft hcenter a d ha hd
  have herror :=
    ternary_prime_filtered_label_minor_error_normalized_tendsto_zero
      labels left center hlabels hleft hcenter
      (a : ℤ) (-2 * (d : ℤ)) haminus hdminus minor
      (fun n => ternaryShiftedMinorArcs_measurable
        modulus (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff lower n))
      (fun n => Set.inter_subset_left)
  have hsum : Tendsto
      (fun n : ℕ =>
        ‖∫ α in minor n,
            ternaryExponentialSum (labels n) weight 1 α *
              ternaryExponentialSum (left n) weight (a : ℤ) α *
              ternaryExponentialSum (center n) weight
                (-2 * (d : ℤ)) α‖ / (n : ℝ) ^ 2 +
        ‖(∫ α in minor n,
            ternaryExponentialSum (labels n) weight 1 α *
              ternaryExponentialSum (left n) weight (a : ℤ) α *
              ternaryExponentialSum (center n) weight
                (-2 * (d : ℤ)) α) -
          (∫ α in minor n,
            ternaryExponentialSum ((labels n).filter Nat.Prime)
              weight 1 α *
              ternaryExponentialSum (left n) weight (a : ℤ) α *
              ternaryExponentialSum (center n) weight
                (-2 * (d : ℤ)) α)‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
    simpa [labels, minor, weight] using hfull.add herror
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by positivity)) _ hsum
  exact Eventually.of_forall fun n => by
    let full : ℂ := ∫ α in minor n,
      ternaryExponentialSum (labels n) weight 1 α *
        ternaryExponentialSum (left n) weight (a : ℤ) α *
        ternaryExponentialSum (center n) weight (-2 * (d : ℤ)) α
    let prime : ℂ := ∫ α in minor n,
      ternaryExponentialSum ((labels n).filter Nat.Prime) weight 1 α *
        ternaryExponentialSum (left n) weight (a : ℤ) α *
        ternaryExponentialSum (center n) weight (-2 * (d : ℤ)) α
    have htriangle : ‖prime‖ ≤ ‖full‖ + ‖full - prime‖ := by
      calc
        ‖prime‖ = ‖full - (full - prime)‖ := by ring_nf
        _ ≤ ‖full‖ + ‖full - prime‖ := norm_sub_le _ _
    change ‖prime‖ / (n : ℝ) ^ 2 ≤
      ‖full‖ / (n : ℝ) ^ 2 + ‖full - prime‖ / (n : ℝ) ^ 2
    rw [← add_div]
    exact div_le_div_of_nonneg_right htriangle (sq_nonneg _)

/-- The genuine left prime window, including its actual edge cutoff, lies
strictly below the original global endpoint. -/
theorem actualMajorArcLeftPrimeWindow_subset_range
    (S : Finset ℕ) (b : ℕ → ℕ) (n a : ℕ) (ha : 0 < a) :
    actualMajorArcLeftPrimeWindow S b n a ⊆ Finset.range n := by
  intro q hq
  obtain ⟨_, hprime, _, hbound, _⟩ := Finset.mem_filter.mp hq
  have hqle : q ≤ a * q := Nat.le_mul_of_pos_left q ha
  have hproduct : 0 < a * q := Nat.mul_pos ha hprime.pos
  exact Finset.mem_range.mpr (by omega)

/-- The genuine center prime window likewise lies strictly below the
endpoint because its retained graph cutoff is `4*d*q ≤ n`. -/
theorem actualMajorArcCenterPrimeWindow_subset_range
    (S : Finset ℕ) (b : ℕ → ℕ) (n d : ℕ) (hd : 0 < d) :
    actualMajorArcCenterPrimeWindow S b n d ⊆ Finset.range n := by
  intro q hq
  obtain ⟨_, hprime, _, hbound, _⟩ := Finset.mem_filter.mp hq
  have hcoefficient : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
  have hqle : q ≤ (2 * d) * q :=
    Nat.le_mul_of_pos_left q hcoefficient
  have hproduct : 0 < (2 * d) * q :=
    Nat.mul_pos hcoefficient hprime.pos
  exact Finset.mem_range.mpr (by omega)

/-- The true upper manuscript label floor never exceeds the global endpoint
for an admissible arbitrary-real strip. -/
theorem actualMajorArc_real_strip_upper_floor_le
    (τ ell : ℝ) (n : ℕ)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell)
    (hstrip : τ + ell < (1 : ℝ)) :
    Nat.floor ((τ + ell) * (n : ℝ)) ≤ n := by
  have hnonnegative : 0 ≤ (τ + ell) * (n : ℝ) := by positivity
  have hfloor := Nat.floor_le hnonnegative
  have hupper : (τ + ell) * (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  exact_mod_cast hfloor.trans hupper

/-- Every positive real manuscript lower endpoint has genuine fixed linear
growth at all sufficiently large original integer scales. -/
theorem actualMajorArc_real_lower_floor_eventually_linear
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop,
      (τ / 2) * (n : ℝ) ≤ (Nat.floor (τ * (n : ℝ)) : ℝ) := by
  filter_upwards
    [(tendsto_atTop.1 (tendsto_natCast_atTop_atTop (R := ℝ))
      (2 / τ))] with n hn
  have hlarge : 2 ≤ τ * (n : ℝ) := by
    have h := (div_le_iff₀ hτ).mp hn
    nlinarith
  have hfloor := Nat.lt_floor_add_one (τ * (n : ℝ))
  nlinarith

/-- The actual original coefficient-specific manuscript cubic has negligible
shifted-minor contribution.  Its windows retain BOTH true edge cutoffs,
both switched-support exclusions, both outside-prime exclusions, the genuine
prime-only robust residue label, arbitrary real `τ,ell`, and the fully
major-compatible Farey cutoff at EVERY original endpoint. -/
theorem actualMajorArcPrimeCubic_shifted_minor_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (J residue a d : ℕ) (τ ell : ℝ)
    (hresidue : residue ∈ robustResidues S b J)
    (ha : 0 < a) (hd : 0 < d)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    Tendsto
      (fun n : ℕ =>
        ‖∫ α in ternaryShiftedMinorArcs (∏ s ∈ S, s)
              (compatibleLogMinorCutoff n)
              (fullyCompatibleFareyCutoff
                (fun m => Nat.floor (τ * (m : ℝ))) n),
          actualMajorArcPrimeCubic
            S b n J residue a d τ ell α‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  classical
  let W := ∏ s ∈ S, s
  let lower : ℕ → ℕ := fun n => Nat.floor (τ * (n : ℝ))
  let upper : ℕ → ℕ := fun n => Nat.floor ((τ + ell) * (n : ℝ))
  let left : ℕ → Finset ℕ := fun n =>
    actualMajorArcLeftPrimeWindow S b n a
  let center : ℕ → Finset ℕ := fun n =>
    actualMajorArcCenterPrimeWindow S b n d
  have hresidueRange : residue < W :=
    Finset.mem_range.mp (Finset.mem_filter.mp hresidue).1
  have hW : 0 < W := by omega
  have horder : ∀ n, lower n ≤ upper n := by
    intro n
    apply Nat.floor_mono
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hupper : ∀ n, upper n ≤ n := by
    intro n
    exact actualMajorArc_real_strip_upper_floor_le
      τ ell n hτ.le hell.le (by nlinarith)
  have hleft : ∀ n, left n ⊆ Finset.range n :=
    fun n => actualMajorArcLeftPrimeWindow_subset_range S b n a ha
  have hcenter : ∀ n, center n ⊆ Finset.range n :=
    fun n => actualMajorArcCenterPrimeWindow_subset_range S b n d hd
  have hminor :=
    ternary_shifted_minor_exact_strip_prime_only_fully_compatible_tendsto_zero
      W residue hW lower upper horder hupper
      (τ / 2) (by positivity)
      (actualMajorArc_real_lower_floor_eventually_linear τ hτ)
      left center hleft hcenter a d ha hd
  have hwindow (n : ℕ) :=
    actualMajorArcLabelPrimeWindow_eq_exact_Ioc_prime_filter
      S b n J residue τ ell hresidue
  simpa only [W, lower, upper, left, center,
    Nat.mod_eq_of_lt hresidueRange,
    actualMajorArcPrimeCubic, hwindow] using hminor

/-- The genuine fully compatible shifted minor region at the original
integer endpoint, using the actual real-strip lower label floor. -/
noncomputable def actualMajorArcShiftedMinor
    (S : Finset ℕ) (τ : ℝ) (n : ℕ) : Set ℝ :=
  ternaryShiftedMinorArcs (∏ s ∈ S, s)
    (compatibleLogMinorCutoff n)
    (fullyCompatibleFareyCutoff
      (fun m => Nat.floor (τ * (m : ℝ))) n)

/-- The exact coefficient-summed *real* minor contribution occurring in
the original weighted robust-residue manuscript count. -/
noncomputable def actualMajorArcCoefficientMinorIntegral
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ s ∈ S, s).divisors,
    ∑ d ∈ (∏ s ∈ S, s).divisors,
      (∫ α in actualMajorArcShiftedMinor S τ n,
        actualMajorArcPrimeCubic S b n J residue a d τ ell α).re

/-- The COMPLETE actual support-divisor-summed minor contribution is `o(n²)`
for every genuine robust residue.  Every coefficient branch uses the actual
prime-only graph windows and both exact edge endpoints. -/
theorem actualMajorArcCoefficientMinorIntegral_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (J residue : ℕ) (τ ell : ℝ)
    (hresidue : residue ∈ robustResidues S b J)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    Tendsto
      (fun n : ℕ =>
        |actualMajorArcCoefficientMinorIntegral
          S b n J residue τ ell| / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  classical
  let W := ∏ s ∈ S, s
  have hW : 0 < W := by
    have hrange := Finset.mem_range.mp
      (Finset.mem_filter.mp hresidue).1
    omega
  have hpositive (a : ℕ) (ha : a ∈ W.divisors) : 0 < a :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hW
  let I : ℕ → ℕ → ℕ → ℂ := fun n a d =>
    ∫ α in actualMajorArcShiftedMinor S τ n,
      actualMajorArcPrimeCubic S b n J residue a d τ ell α
  have hterm (a : ℕ) (ha : a ∈ W.divisors)
      (d : ℕ) (hd : d ∈ W.divisors) :
      Tendsto (fun n : ℕ => ‖I n a d‖ / (n : ℝ) ^ 2)
        atTop (nhds 0) := by
    exact actualMajorArcPrimeCubic_shifted_minor_normalized_tendsto_zero
      S b J residue a d τ ell hresidue
      (hpositive a ha) (hpositive d hd) hτ hell hstrip
  have hinner (a : ℕ) (ha : a ∈ W.divisors) :
      Tendsto
        (fun n : ℕ =>
          ∑ d ∈ W.divisors, ‖I n a d‖ / (n : ℝ) ^ 2)
        atTop (nhds 0) := by
    simpa using tendsto_finsetSum
      (f := fun d n => ‖I n a d‖ / (n : ℝ) ^ 2)
      (a := fun _ => (0 : ℝ)) W.divisors (hterm a ha)
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
            ‖I n a d‖ / (n : ℝ) ^ 2)
        atTop (nhds 0) := by
    simpa using tendsto_finsetSum
      (f := fun a n =>
        ∑ d ∈ W.divisors, ‖I n a d‖ / (n : ℝ) ^ 2)
      (a := fun _ => (0 : ℝ)) W.divisors hinner
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by positivity)) _ hsum
  exact Eventually.of_forall fun n => by
    have hfirst :
        |∑ a ∈ W.divisors, ∑ d ∈ W.divisors, (I n a d).re| ≤
          ∑ a ∈ W.divisors, |∑ d ∈ W.divisors, (I n a d).re| :=
      Finset.abs_sum_le_sum_abs
        (fun a => ∑ d ∈ W.divisors, (I n a d).re) W.divisors
    have hsecond :
        (∑ a ∈ W.divisors, |∑ d ∈ W.divisors, (I n a d).re|) ≤
          ∑ a ∈ W.divisors, ∑ d ∈ W.divisors, |(I n a d).re| := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs
        (fun d => (I n a d).re) W.divisors
    have hthird :
        (∑ a ∈ W.divisors, ∑ d ∈ W.divisors, |(I n a d).re|) ≤
          ∑ a ∈ W.divisors, ∑ d ∈ W.divisors, ‖I n a d‖ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro d hd
      exact Complex.abs_re_le_norm (I n a d)
    have htotal := hfirst.trans (hsecond.trans hthird)
    change
      |∑ a ∈ W.divisors, ∑ d ∈ W.divisors, (I n a d).re| /
          (n : ℝ) ^ 2 ≤
        ∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
          ‖I n a d‖ / (n : ℝ) ^ 2
    calc
      _ ≤ (∑ a ∈ W.divisors, ∑ d ∈ W.divisors, ‖I n a d‖) /
            (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right htotal (sq_nonneg _)
      _ = _ := by
        simp_rw [Finset.sum_div]

/-- The exact coefficient-summed real integral on the *entire* genuinely
shifted major region complementary to the fully compatible minor region. -/
noncomputable def actualMajorArcCoefficientMajorIntegral
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ s ∈ S, s).divisors,
    ∑ d ∈ (∏ s ∈ S, s).divisors,
      (∫ α in Set.Ioc (0 : ℝ) 1 \
          actualMajorArcShiftedMinor S τ n,
        actualMajorArcPrimeCubic S b n J residue a d τ ell α).re

/-- The original weighted robust residue count is exactly the sum of its
actual coefficient-summed full-major and actual coefficient-summed minor
contributions at the fully compatible original endpoint. -/
theorem manuscriptWeightedResidueCount_eq_actualMajorArc_major_add_minor
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue : ℕ) (τ ell : ℝ)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell) :
    manuscriptWeightedResidueCount S b n J τ ell residue =
      actualMajorArcCoefficientMajorIntegral
        S b n J residue τ ell +
      actualMajorArcCoefficientMinorIntegral
        S b n J residue τ ell := by
  exact manuscriptWeightedResidueCount_eq_actual_shifted_major_minor_sum
    S b n J residue
    (compatibleLogMinorCutoff n)
    (fullyCompatibleFareyCutoff
      (fun m => Nat.floor (τ * (m : ℝ))) n)
    τ ell hτ hell

/-- The sole remaining actual three-prime analytic goal after all exact
prime-only Fourier assembly and all full coefficient-summed minor errors
have been unconditionally discharged.  The constant is chosen before the
support; positivity concerns the ENTIRE shifted major union. -/
def UniformActualCoefficientSummedMajorArcPositivity : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ),
      (∀ s ∈ S, s.Prime ∧ 3 < s ∧ J < s ∧ b s % s ≠ 0) →
      0 < τ → 0 < ell → τ + ell < 1 / 10 →
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ residue ∈ robustResidues S b J,
            c * manuscriptLocalSingularFactor S b residue *
                ell * (n : ℝ) ^ 2 ≤
              actualMajorArcCoefficientMajorIntegral
                S b n J residue τ ell

/-- Positive quadratic mass on the COMPLETE actual shifted major region
implies the original residue-localized three-prime major-arc lower bound.
All actual prime-only minors, divisor sums, switched selectors, endpoint
constraints, robust residue classes, and arbitrary-real strips are already
proved; no additional minor estimate or prime-pattern input is assumed. -/
theorem uniformLocalizedThreePrimeMajorArcLowerBound_of_actual_summed_major_positivity
    (hmajor : UniformActualCoefficientSummedMajorArcPositivity) :
    UniformLocalizedThreePrimeMajorArcLowerBound := by
  classical
  obtain ⟨c, hc, hmajor⟩ := hmajor
  refine ⟨c / 2, by positivity, ?_⟩
  intro S b J τ ell hsupport hτ hell hstrip
  have hminor :
      ∀ᶠ n : ℕ in atTop,
        ∀ residue ∈ robustResidues S b J,
          |actualMajorArcCoefficientMinorIntegral
            S b n J residue τ ell| / (n : ℝ) ^ 2 <
            (c / 2) * manuscriptLocalSingularFactor S b residue * ell := by
    apply (Filter.eventually_all_finset
      (robustResidues S b J)).mpr
    intro residue hresidue
    apply (tendsto_order.1
      (actualMajorArcCoefficientMinorIntegral_normalized_tendsto_zero
        S b J residue τ ell hresidue hτ hell hstrip)).2
    have hlocal : 0 < manuscriptLocalSingularFactor S b residue :=
      manuscriptLocalSingularFactor_pos S b residue
        (fun s hs => (hsupport s hs).2.1)
    positivity
  filter_upwards
    [hmajor S b J τ ell hsupport hτ hell hstrip,
      hminor, eventually_ge_atTop 1] with n hmajorN hminorN hn
  intro residue hresidue
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have herror := hminorN residue hresidue
  have herror' :
      |actualMajorArcCoefficientMinorIntegral
        S b n J residue τ ell| <
          ((c / 2) * manuscriptLocalSingularFactor
            S b residue * ell) * (n : ℝ) ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hnreal)).mp herror
  rw [manuscriptWeightedResidueCount_eq_actualMajorArc_major_add_minor
    S b n J residue τ ell hτ.le hell.le]
  have hmain := hmajorN residue hresidue
  have hnegative :=
    neg_abs_le (actualMajorArcCoefficientMinorIntegral
      S b n J residue τ ell)
  nlinarith

#print axioms Erdos689.ternary_prime_filtered_label_minor_integral_error_le
#print axioms Erdos689.ternary_prime_filtered_label_minor_error_normalized_tendsto_zero
#print axioms Erdos689.ternary_shifted_minor_exact_strip_prime_only_fully_compatible_tendsto_zero
#print axioms Erdos689.actualMajorArcLeftPrimeWindow_subset_range
#print axioms Erdos689.actualMajorArcCenterPrimeWindow_subset_range
#print axioms Erdos689.actualMajorArc_real_strip_upper_floor_le
#print axioms Erdos689.actualMajorArc_real_lower_floor_eventually_linear
#print axioms Erdos689.actualMajorArcPrimeCubic_shifted_minor_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcCoefficientMinorIntegral_normalized_tendsto_zero
#print axioms Erdos689.manuscriptWeightedResidueCount_eq_actualMajorArc_major_add_minor
#print axioms Erdos689.uniformLocalizedThreePrimeMajorArcLowerBound_of_actual_summed_major_positivity

end Erdos689
