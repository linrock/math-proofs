module

public import GoldbachChainMaster

@[expose] public section


/-!
# Ternary affine Fourier identities for Erdős problem 689

The Goldbach master supplies binary Fourier extraction and quantitative
minor-arc bounds.  The manuscript edges for problem 689 instead require three
simultaneously prime affine forms.  This file proves the missing finite cubic
Fourier identity with completely arbitrary finite windows, complex weights,
and integral coefficients.  Residue and primality restrictions may therefore
be imposed directly on the three windows.

These identities are exact finite statements.  They do not assert the
unproved major-arc asymptotic, a three-prime lower bound, or a solution to the
original Erdős problem.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Erdos689

/-- A finite weighted prime/exponential window with an arbitrary integral
frequency.  The finset can encode primality, a residue class, and a prescribed
archimedean interval simultaneously. -/
noncomputable def ternaryExponentialSum
    (window : Finset ℕ) (weight : ℕ → ℂ) (frequency : ℤ)
    (α : ℝ) : ℂ :=
  ∑ n ∈ window,
    weight n * GoldbachChain.e (((frequency : ℝ) * n) * α)

/-- Additive characters recover an exact natural-number congruence indicator.
Unlike a density approximation, this identity holds for every positive
modulus and every pair of natural numbers. -/
theorem ternary_residue_character_orthogonality
    (modulus n residue : ℕ) (hmodulus : 0 < modulus) :
    (∑ j ∈ Finset.range modulus,
      GoldbachChain.e
        (((n : ℝ) - (residue : ℝ)) * j / modulus)) =
      if n % modulus = residue % modulus
      then (modulus : ℂ)
      else 0 := by
  have hdivisibility :
      ((modulus : ℤ) ∣ (n : ℤ) - (residue : ℤ)) ↔
        n % modulus = residue % modulus := by
    constructor
    · intro h
      exact (Nat.modEq_iff_dvd.mpr h).symm
    · intro h
      exact Nat.modEq_iff_dvd.mp h.symm
  have horthogonality :=
    GoldbachChain.MinorArc.char_orthogonality
      ((n : ℤ) - (residue : ℤ)) modulus hmodulus.ne'
  simpa only [Int.cast_sub, Int.cast_natCast, hdivisibility]
    using horthogonality

/-- Exact additive-character localization of an arbitrarily weighted finite
exponential sum to one prescribed residue class.  This is the precise
`(1 / M) * Σⱼ e(-jr/M) S(α+j/M)` decomposition needed to transport
unrestricted minor-arc estimates to fixed manuscript residue classes. -/
theorem ternary_residue_filtered_exponential_sum
    (window : Finset ℕ) (weight : ℕ → ℂ)
    (modulus residue : ℕ) (hmodulus : 0 < modulus) (α : ℝ) :
    ternaryExponentialSum
      (window.filter fun n => n % modulus = residue % modulus)
      weight 1 α =
        (modulus : ℂ)⁻¹ *
          ∑ j ∈ Finset.range modulus,
            GoldbachChain.e
                (-((residue : ℝ) * j / modulus)) *
              ternaryExponentialSum window weight 1
                (α + (j : ℝ) / modulus) := by
  classical
  have hmodulusComplex : (modulus : ℂ) ≠ 0 := by
    exact_mod_cast hmodulus.ne'
  unfold ternaryExponentialSum
  simp only [Int.cast_one, one_mul]
  rw [Finset.sum_filter, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  have hcharacter :=
    ternary_residue_character_orthogonality modulus n residue hmodulus
  have hphase : ∀ j : ℕ,
      GoldbachChain.e (-((residue : ℝ) * j / modulus)) *
          GoldbachChain.e ((n : ℝ) * (α + (j : ℝ) / modulus)) =
        GoldbachChain.e ((n : ℝ) * α) *
          GoldbachChain.e
            (((n : ℝ) - (residue : ℝ)) * j / modulus) := by
    intro j
    rw [GoldbachChain.e_add, GoldbachChain.e_add]
    congr 1
    ring
  calc
    (if n % modulus = residue % modulus
      then weight n * GoldbachChain.e ((n : ℝ) * α)
      else 0) =
        weight n * GoldbachChain.e ((n : ℝ) * α) *
          ((modulus : ℂ)⁻¹ *
            if n % modulus = residue % modulus
            then (modulus : ℂ)
            else 0) := by
      split <;> simp [hmodulusComplex]
    _ = weight n * GoldbachChain.e ((n : ℝ) * α) *
          ((modulus : ℂ)⁻¹ *
            ∑ j ∈ Finset.range modulus,
              GoldbachChain.e
                (((n : ℝ) - (residue : ℝ)) * j / modulus)) := by
      rw [hcharacter]
    _ = ∑ j ∈ Finset.range modulus,
          (modulus : ℂ)⁻¹ *
            (GoldbachChain.e (-((residue : ℝ) * j / modulus)) *
              (weight n *
                GoldbachChain.e
                  ((n : ℝ) * (α + (j : ℝ) / modulus)))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      calc
        weight n * GoldbachChain.e ((n : ℝ) * α) *
            ((modulus : ℂ)⁻¹ *
              GoldbachChain.e
                (((n : ℝ) - (residue : ℝ)) * j / modulus)) =
            ((modulus : ℂ)⁻¹ * weight n) *
              (GoldbachChain.e ((n : ℝ) * α) *
                GoldbachChain.e
                  (((n : ℝ) - (residue : ℝ)) * j / modulus)) := by
          ring
        _ = ((modulus : ℂ)⁻¹ * weight n) *
              (GoldbachChain.e (-((residue : ℝ) * j / modulus)) *
                GoldbachChain.e
                  ((n : ℝ) * (α + (j : ℝ) / modulus))) := by
          rw [← hphase j]
        _ = (modulus : ℂ)⁻¹ *
              (GoldbachChain.e (-((residue : ℝ) * j / modulus)) *
                (weight n *
                  GoldbachChain.e
                    ((n : ℝ) * (α + (j : ℝ) / modulus)))) := by
          ring

/-- A residue-filtered exponential sum inherits any common bound on the finitely
many unrestricted shifted sums.  The averaging factor cancels the exact number
of additive characters, so no modulus-dependent multiplicative loss occurs. -/
theorem ternary_residue_filtered_exponential_sum_norm_le
    (window : Finset ℕ) (weight : ℕ → ℂ)
    (modulus residue : ℕ) (hmodulus : 0 < modulus)
    (α bound : ℝ)
    (hshift : ∀ j ∈ Finset.range modulus,
      ‖ternaryExponentialSum window weight 1
        (α + (j : ℝ) / modulus)‖ ≤ bound) :
    ‖ternaryExponentialSum
      (window.filter fun n => n % modulus = residue % modulus)
      weight 1 α‖ ≤ bound := by
  have hmodulusReal : (0 : ℝ) < (modulus : ℝ) := by
    exact_mod_cast hmodulus
  have hbound : 0 ≤ bound := by
    have hzero : 0 ∈ Finset.range modulus := Finset.mem_range.mpr hmodulus
    exact (norm_nonneg _).trans (hshift 0 hzero)
  rw [ternary_residue_filtered_exponential_sum
    window weight modulus residue hmodulus α]
  calc
    ‖(modulus : ℂ)⁻¹ *
        ∑ j ∈ Finset.range modulus,
          GoldbachChain.e (-((residue : ℝ) * j / modulus)) *
            ternaryExponentialSum window weight 1
              (α + (j : ℝ) / modulus)‖ =
        (modulus : ℝ)⁻¹ *
          ‖∑ j ∈ Finset.range modulus,
            GoldbachChain.e (-((residue : ℝ) * j / modulus)) *
              ternaryExponentialSum window weight 1
                (α + (j : ℝ) / modulus)‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (modulus : ℝ)⁻¹ *
          ∑ j ∈ Finset.range modulus,
            ‖GoldbachChain.e (-((residue : ℝ) * j / modulus)) *
              ternaryExponentialSum window weight 1
                (α + (j : ℝ) / modulus)‖ := by
      apply mul_le_mul_of_nonneg_left (norm_sum_le _ _)
      positivity
    _ ≤ (modulus : ℝ)⁻¹ *
          ∑ _j ∈ Finset.range modulus, bound := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, GoldbachChain.e_norm, one_mul]
      exact hshift j hj
    _ = bound := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- Exact integral orthogonality for three independent weighted windows and an
arbitrary integral affine relation.  This is the cubic counterpart of the
Goldbach master's binary `fourier_coeff_sq` identity. -/
theorem ternary_affine_fourier_identity
    (left center right : Finset ℕ)
    (leftWeight centerWeight rightWeight : ℕ → ℂ)
    (leftFrequency centerFrequency rightFrequency : ℤ) :
    (∫ α in (0 : ℝ)..1,
      ternaryExponentialSum left leftWeight leftFrequency α *
        ternaryExponentialSum center centerWeight centerFrequency α *
          ternaryExponentialSum right rightWeight rightFrequency α) =
      ∑ x ∈ left, ∑ y ∈ center, ∑ z ∈ right,
        if leftFrequency * (x : ℤ) + centerFrequency * (y : ℤ) +
              rightFrequency * (z : ℤ) = 0
        then leftWeight x * centerWeight y * rightWeight z
        else 0 := by
  classical
  have hterm : ∀ x y z : ℕ,
      IntervalIntegrable
        (fun α : ℝ =>
          (leftWeight x * centerWeight y * rightWeight z) *
            GoldbachChain.e
              (((leftFrequency * (x : ℤ) + centerFrequency * (y : ℤ) +
                rightFrequency * (z : ℤ) : ℤ) : ℝ) * α))
        volume 0 1 := by
    intro x y z
    apply Continuous.intervalIntegrable
    unfold GoldbachChain.e
    fun_prop
  have hinner : ∀ x y : ℕ,
      IntervalIntegrable
        (fun α : ℝ =>
          ∑ z ∈ right,
            (leftWeight x * centerWeight y * rightWeight z) *
              GoldbachChain.e
                (((leftFrequency * (x : ℤ) + centerFrequency * (y : ℤ) +
                  rightFrequency * (z : ℤ) : ℤ) : ℝ) * α))
        volume 0 1 := by
    intro x y
    apply Continuous.intervalIntegrable
    unfold GoldbachChain.e
    fun_prop
  have hmiddle : ∀ x : ℕ,
      IntervalIntegrable
        (fun α : ℝ =>
          ∑ y ∈ center, ∑ z ∈ right,
            (leftWeight x * centerWeight y * rightWeight z) *
              GoldbachChain.e
                (((leftFrequency * (x : ℤ) + centerFrequency * (y : ℤ) +
                  rightFrequency * (z : ℤ) : ℤ) : ℝ) * α))
        volume 0 1 := by
    intro x
    apply Continuous.intervalIntegrable
    unfold GoldbachChain.e
    fun_prop
  have hpointwise : ∀ α ∈ Set.uIcc (0 : ℝ) 1,
      ternaryExponentialSum left leftWeight leftFrequency α *
        ternaryExponentialSum center centerWeight centerFrequency α *
          ternaryExponentialSum right rightWeight rightFrequency α =
        ∑ x ∈ left, ∑ y ∈ center, ∑ z ∈ right,
          (leftWeight x * centerWeight y * rightWeight z) *
            GoldbachChain.e
              (((leftFrequency * (x : ℤ) + centerFrequency * (y : ℤ) +
                rightFrequency * (z : ℤ) : ℤ) : ℝ) * α) := by
    intro α _
    unfold ternaryExponentialSum
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    have hphase :
        (((leftFrequency * (x : ℤ) + centerFrequency * (y : ℤ) +
          rightFrequency * (z : ℤ) : ℤ) : ℝ) * α) =
          ((leftFrequency : ℝ) * x) * α +
            ((centerFrequency : ℝ) * y) * α +
              ((rightFrequency : ℝ) * z) * α := by
      push_cast
      ring
    rw [hphase, ← GoldbachChain.e_add, ← GoldbachChain.e_add]
    ring
  rw [intervalIntegral.integral_congr hpointwise]
  rw [intervalIntegral.integral_finsetSum (fun x _ => hmiddle x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [intervalIntegral.integral_finsetSum (fun y _ => hinner x y)]
  apply Finset.sum_congr rfl
  intro y _
  rw [intervalIntegral.integral_finsetSum (fun z _ => hterm x y z)]
  apply Finset.sum_congr rfl
  intro z _
  rw [intervalIntegral.integral_const_mul,
    GoldbachChain.MinorArc.integral_e]
  split <;> simp_all

/-- The actual finite affine triples underlying the manuscript patterns.  The
windows themselves may already contain arbitrary primality, residue, and
interval filters. -/
def ternaryAffineTriples
    (left center right : Finset ℕ) (leftCoefficient centerCoefficient : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (left.product (center.product right)).filter fun triple =>
    leftCoefficient * triple.1 + triple.2.2 =
      centerCoefficient * triple.2.1

/-- The cubic Fourier identity expressed with the nonnegative affine equation
`a * x + z = b * y`, exactly the three-prime equation occurring in #689. -/
theorem ternary_affine_nat_fourier_identity
    (left center right : Finset ℕ)
    (leftWeight centerWeight rightWeight : ℕ → ℂ)
    (leftCoefficient centerCoefficient : ℕ) :
    (∫ α in (0 : ℝ)..1,
      ternaryExponentialSum left leftWeight (leftCoefficient : ℤ) α *
        ternaryExponentialSum center centerWeight
          (-(centerCoefficient : ℤ)) α *
          ternaryExponentialSum right rightWeight 1 α) =
      ∑ triple ∈
          ternaryAffineTriples left center right
            leftCoefficient centerCoefficient,
        leftWeight triple.1 * centerWeight triple.2.1 *
          rightWeight triple.2.2 := by
  classical
  rw [ternary_affine_fourier_identity]
  unfold ternaryAffineTriples
  rw [Finset.sum_filter]
  change
    (∑ x ∈ left, ∑ y ∈ center, ∑ z ∈ right,
      if (leftCoefficient : ℤ) * (x : ℤ) +
          (-(centerCoefficient : ℤ)) * (y : ℤ) +
            (1 : ℤ) * (z : ℤ) = 0
      then leftWeight x * centerWeight y * rightWeight z
      else 0) =
      ∑ triple ∈ left ×ˢ (center ×ˢ right),
        if leftCoefficient * triple.1 + triple.2.2 =
            centerCoefficient * triple.2.1
        then leftWeight triple.1 * centerWeight triple.2.1 *
          rightWeight triple.2.2
        else 0
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  have hequation :
      (leftCoefficient : ℤ) * (x : ℤ) +
          (-(centerCoefficient : ℤ)) * (y : ℤ) +
            (1 : ℤ) * (z : ℤ) = 0 ↔
        leftCoefficient * x + z = centerCoefficient * y := by
    constructor
    · intro h
      have hcast :
          ((leftCoefficient * x + z : ℕ) : ℤ) =
            ((centerCoefficient * y : ℕ) : ℤ) := by
        push_cast
        nlinarith [h]
      exact_mod_cast hcast
    · intro h
      have hcast :
          ((leftCoefficient * x + z : ℕ) : ℤ) =
            ((centerCoefficient * y : ℕ) : ℤ) := by
        exact_mod_cast h
      push_cast at hcast
      nlinarith [hcast]
  split <;> rename_i h
  · rw [if_pos (hequation.mp h)]
  · rw [if_neg (fun h' => h (hequation.mpr h'))]

/-- With unit weights, cubic Fourier extraction counts actual finite affine
triples without a representation-multiplicity hypothesis. -/
theorem ternary_affine_count_fourier_identity
    (left center right : Finset ℕ)
    (leftCoefficient centerCoefficient : ℕ) :
    (∫ α in (0 : ℝ)..1,
      ternaryExponentialSum left (fun _ => 1) (leftCoefficient : ℤ) α *
        ternaryExponentialSum center (fun _ => 1)
          (-(centerCoefficient : ℤ)) α *
          ternaryExponentialSum right (fun _ => 1) 1 α) =
      ((ternaryAffineTriples left center right
        leftCoefficient centerCoefficient).card : ℂ) := by
  rw [ternary_affine_nat_fourier_identity]
  simp

/-- Exact three-prime Fourier extraction for the manuscript's coefficients:
`a * q + P = 2 * d * q'`.  Each window can additionally encode its prescribed
residue class and archimedean strip before the explicit prime filter. -/
theorem manuscript_three_prime_fourier_identity
    (left center labels : Finset ℕ) (a d : ℕ) :
    (∫ α in (0 : ℝ)..1,
      ternaryExponentialSum (left.filter Nat.Prime)
          (fun _ => 1) (a : ℤ) α *
        ternaryExponentialSum (center.filter Nat.Prime)
          (fun _ => 1) (-(2 * d : ℕ) : ℤ) α *
          ternaryExponentialSum (labels.filter Nat.Prime)
            (fun _ => 1) 1 α) =
      ((ternaryAffineTriples
        (left.filter Nat.Prime)
        (center.filter Nat.Prime)
        (labels.filter Nat.Prime)
        a (2 * d)).card : ℂ) := by
  exact ternary_affine_count_fourier_identity
    (left.filter Nat.Prime)
    (center.filter Nat.Prime)
    (labels.filter Nat.Prime)
    a (2 * d)

/-- Complex conjugation reverses the integral frequency of a finite weighted
exponential window and conjugates its coefficients. -/
theorem ternaryExponentialSum_conj
    (window : Finset ℕ) (weight : ℕ → ℂ)
    (frequency : ℤ) (α : ℝ) :
    (starRingEnd ℂ) (ternaryExponentialSum window weight frequency α) =
      ternaryExponentialSum window
        (fun n => (starRingEnd ℂ) (weight n)) (-frequency) α := by
  unfold ternaryExponentialSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul, GoldbachChain.e_conj]
  congr 1
  push_cast
  ring

/-- Complex Parseval for any nonzero integral dilation and any finite window.
The proof extracts the diagonal from the newly proved cubic identity, taking
its third window to be the singleton `{0}`. -/
theorem ternary_window_dilated_parseval_aux
    (window : Finset ℕ) (weight : ℕ → ℂ)
    (frequency : ℤ) (hfrequency : frequency ≠ 0) :
    (∫ α in (0 : ℝ)..1,
      ternaryExponentialSum window weight frequency α *
        (starRingEnd ℂ)
          (ternaryExponentialSum window weight frequency α)) =
      ∑ n ∈ window,
        weight n * (starRingEnd ℂ) (weight n) := by
  classical
  have hzeroWindow : ∀ α : ℝ,
      ternaryExponentialSum {0} (fun _ => (1 : ℂ)) 0 α = 1 := by
    intro α
    simp [ternaryExponentialSum, GoldbachChain.e]
  have hcondition : ∀ x y : ℕ,
      frequency * (x : ℤ) + (-frequency) * (y : ℤ) = 0 ↔ x = y := by
    intro x y
    have hfactor :
        frequency * (x : ℤ) + (-frequency) * (y : ℤ) =
          frequency * ((x : ℤ) - (y : ℤ)) := by ring
    rw [hfactor]
    constructor
    · intro h
      have hzero : (x : ℤ) - (y : ℤ) = 0 :=
        (mul_eq_zero.mp h).resolve_left hfrequency
      exact_mod_cast sub_eq_zero.mp hzero
    · intro h
      subst y
      simp
  have hcubic := ternary_affine_fourier_identity
    window window {0}
    weight
    (fun n => (starRingEnd ℂ) (weight n))
    (fun _ => (1 : ℂ))
    frequency (-frequency) 0
  simp only [Finset.sum_singleton, zero_mul, add_zero, mul_one] at hcubic
  simp_rw [hzeroWindow, mul_one, ← ternaryExponentialSum_conj] at hcubic
  rw [hcubic]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single x]
  · rw [if_pos ((hcondition x x).mpr rfl)]
  · intro y _ hy
    rw [if_neg]
    exact fun h => hy ((hcondition x y).mp h).symm
  · intro h
    exact (h hx).elim

/-- Parseval is invariant under every nonzero integral coefficient.  This
covers the manuscript's frequencies `a`, `-2d`, and `1` directly, without
losing a coefficient-dependent factor. -/
theorem ternary_window_dilated_parseval
    (window : Finset ℕ) (weight : ℕ → ℂ)
    (frequency : ℤ) (hfrequency : frequency ≠ 0) :
    (∫ α in (0 : ℝ)..1,
      ‖ternaryExponentialSum window weight frequency α‖ ^ 2) =
      ∑ n ∈ window, ‖weight n‖ ^ 2 := by
  have hcomplex :=
    ternary_window_dilated_parseval_aux window weight frequency hfrequency
  have hnorm : ∀ z : ℂ,
      z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hintegral :
      (∫ α in (0 : ℝ)..1,
        ternaryExponentialSum window weight frequency α *
          (starRingEnd ℂ)
            (ternaryExponentialSum window weight frequency α)) =
        ((∫ α in (0 : ℝ)..1,
          ‖ternaryExponentialSum window weight frequency α‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro α _
    exact hnorm _
  have hsum :
      (∑ n ∈ window, weight n * (starRingEnd ℂ) (weight n)) =
        ((∑ n ∈ window, ‖weight n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun n _ => hnorm (weight n))
  rw [hintegral, hsum] at hcomplex
  exact_mod_cast hcomplex

/-- Parseval remains exact after imposing an arbitrary finite window, including
simultaneous prime, residue-class, and interval restrictions. -/
theorem ternary_window_parseval
    (window : Finset ℕ) (weight : ℕ → ℂ) (N : ℕ)
    (hwindow : window ⊆ Finset.range N) :
    (∫ α in (0 : ℝ)..1,
      ‖ternaryExponentialSum window weight 1 α‖ ^ 2) =
        ∑ n ∈ window, ‖weight n‖ ^ 2 := by
  classical
  let padded : ℕ → ℂ := fun n => if n ∈ window then weight n else 0
  have hexponential : ∀ α : ℝ,
      ternaryExponentialSum window weight 1 α =
        ∑ n ∈ Finset.range N,
          padded n * GoldbachChain.e ((n : ℝ) * α) := by
    intro α
    calc
      ternaryExponentialSum window weight 1 α =
          ∑ n ∈ window,
            padded n * GoldbachChain.e ((n : ℝ) * α) := by
        unfold ternaryExponentialSum
        apply Finset.sum_congr rfl
        intro n hn
        simp [padded, hn]
      _ = ∑ n ∈ Finset.range N,
          padded n * GoldbachChain.e ((n : ℝ) * α) := by
        apply Finset.sum_subset hwindow
        intro n _ hn
        simp [padded, hn]
  have henergy :
      (∑ n ∈ window, ‖weight n‖ ^ 2) =
        ∑ n ∈ Finset.range N, ‖padded n‖ ^ 2 := by
    calc
      (∑ n ∈ window, ‖weight n‖ ^ 2) =
          ∑ n ∈ window, ‖padded n‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [padded, hn]
      _ = ∑ n ∈ Finset.range N, ‖padded n‖ ^ 2 := by
        apply Finset.sum_subset hwindow
        intro n _ hn
        simp [padded, hn]
  calc
    (∫ α in (0 : ℝ)..1,
      ‖ternaryExponentialSum window weight 1 α‖ ^ 2) =
        ∫ α in (0 : ℝ)..1,
          ‖∑ n ∈ Finset.range N,
            padded n * GoldbachChain.e ((n : ℝ) * α)‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro α _
      dsimp only
      rw [hexponential α]
    _ = ∑ n ∈ Finset.range N, ‖padded n‖ ^ 2 :=
      GoldbachChain.MinorArc.parseval padded N
    _ = ∑ n ∈ window, ‖weight n‖ ^ 2 := henergy.symm

/-- Every restricted von-Mangoldt window has the same uniform `L²` bound as
the unrestricted prime exponential sum. -/
theorem ternary_vonMangoldt_window_parseval_le
    (window : Finset ℕ) (N : ℕ)
    (hwindow : window ⊆ Finset.range N) :
    (∫ α in (0 : ℝ)..1,
      ‖ternaryExponentialSum window
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 α‖ ^ 2) ≤
      (N : ℝ) * Real.log N ^ 2 := by
  rw [ternary_window_parseval window _ N hwindow]
  calc
    (∑ n ∈ window,
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ ^ 2) =
        ∑ n ∈ window, ArithmeticFunction.vonMangoldt n ^ 2 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ n ∈ Finset.range N,
          ArithmeticFunction.vonMangoldt n ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hwindow
      intro n _ _
      positivity
    _ ≤ (N : ℝ) * Real.log N ^ 2 :=
      GoldbachChain.MinorArc.sum_vonMangoldt_sq_range_le N

/-- The same restricted von-Mangoldt `L²` estimate holds at every nonzero
integral frequency, including both nontrivial manuscript coefficients. -/
theorem ternary_vonMangoldt_dilated_window_parseval_le
    (window : Finset ℕ) (N : ℕ)
    (hwindow : window ⊆ Finset.range N)
    (frequency : ℤ) (hfrequency : frequency ≠ 0) :
    (∫ α in (0 : ℝ)..1,
      ‖ternaryExponentialSum window
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          frequency α‖ ^ 2) ≤
      (N : ℝ) * Real.log N ^ 2 := by
  rw [ternary_window_dilated_parseval window _ frequency hfrequency]
  calc
    (∑ n ∈ window,
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ ^ 2) =
        ∑ n ∈ window, ArithmeticFunction.vonMangoldt n ^ 2 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ n ∈ Finset.range N,
          ArithmeticFunction.vonMangoldt n ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hwindow
      intro n _ _
      positivity
    _ ≤ (N : ℝ) * Real.log N ^ 2 :=
      GoldbachChain.MinorArc.sum_vonMangoldt_sq_range_le N

/-- A cubic minor-arc integral is controlled by one supremum and the two
full-circle quadratic energies.  The elementary inequality
`2 * u * v ≤ u² + v²` avoids any extra measure-space hypotheses while giving
the standard `L∞ × L² × L²` mechanism needed for ternary prime patterns. -/
theorem ternary_minor_integral_le_quadratic_energy
    (first second third : ℝ → ℂ)
    (hfirst : Continuous first)
    (hsecond : Continuous second)
    (hthird : Continuous third)
    (minor : Set ℝ)
    (hminor : MeasurableSet minor)
    (hsubset : minor ⊆ Set.Ioc (0 : ℝ) 1)
    (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hsup : ∀ α ∈ minor, ‖first α‖ ≤ bound) :
    ‖∫ α in minor, first α * second α * third α‖ ≤
      bound / 2 *
        ((∫ α in (0 : ℝ)..1, ‖second α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖third α‖ ^ 2)) := by
  have hfirstIntegrable :
      IntegrableOn (fun α => ‖first α * second α * third α‖)
        minor volume :=
    (((hfirst.mul hsecond).mul hthird).norm.integrableOn_Ioc).mono_set hsubset
  have hsecondIntegrable :
      IntegrableOn (fun α => ‖second α‖ ^ 2) minor volume :=
    ((hsecond.norm.pow 2).integrableOn_Ioc).mono_set hsubset
  have hthirdIntegrable :
      IntegrableOn (fun α => ‖third α‖ ^ 2) minor volume :=
    ((hthird.norm.pow 2).integrableOn_Ioc).mono_set hsubset
  have hmajorIntegrable :
      IntegrableOn
        (fun α => bound / 2 * (‖second α‖ ^ 2 + ‖third α‖ ^ 2))
        minor volume :=
    (hsecondIntegrable.add hthirdIntegrable).const_mul (bound / 2)
  have hpointwise : ∀ α ∈ minor,
      ‖first α * second α * third α‖ ≤
        bound / 2 * (‖second α‖ ^ 2 + ‖third α‖ ^ 2) := by
    intro α hα
    have hproduct :
        ‖second α‖ * ‖third α‖ ≤
          (‖second α‖ ^ 2 + ‖third α‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖second α‖ - ‖third α‖)]
    calc
      ‖first α * second α * third α‖ =
          ‖first α‖ * (‖second α‖ * ‖third α‖) := by
        rw [norm_mul, norm_mul]
        ring
      _ ≤ bound * (‖second α‖ * ‖third α‖) :=
        mul_le_mul_of_nonneg_right (hsup α hα)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ bound *
          ((‖second α‖ ^ 2 + ‖third α‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hproduct hbound
      _ = bound / 2 * (‖second α‖ ^ 2 + ‖third α‖ ^ 2) := by ring
  calc
    ‖∫ α in minor, first α * second α * third α‖ ≤
        ∫ α in minor, ‖first α * second α * third α‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ α in minor,
          bound / 2 * (‖second α‖ ^ 2 + ‖third α‖ ^ 2) :=
      MeasureTheory.setIntegral_mono_on hfirstIntegrable
        hmajorIntegrable hminor hpointwise
    _ = bound / 2 *
          ((∫ α in minor, ‖second α‖ ^ 2) +
            (∫ α in minor, ‖third α‖ ^ 2)) := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add hsecondIntegrable hthirdIntegrable]
    _ ≤ bound / 2 *
          ((∫ α in (0 : ℝ)..1, ‖second α‖ ^ 2) +
            (∫ α in (0 : ℝ)..1, ‖third α‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (GoldbachChain.MinorArc.setL2_le_circle
          second hsecond minor hsubset)
        (GoldbachChain.MinorArc.setL2_le_circle
          third hthird minor hsubset)

/-- The already-proved Vaughan/Vinogradov estimates imply an explicit
unconditional prime-exponential-sum supremum on the minor arcs.  The cutoff
`P` is arbitrary rather than the binary Goldbach pipeline's fixed
`(log N)^9`; this is the quantitative input needed by a future ternary
`L² × L² × L∞` argument. -/
theorem ternary_minor_arc_vonMangoldt_sup
    (N P Q : ℕ)
    (hP : 2 ≤ P)
    (hPN : P ^ 3 ≤ N)
    (hPQcut : P ≤ Q)
    (hPQ : P * Q ≤ N)
    (α : ℝ)
    (hα : α ∈ Set.Ioc (0 : ℝ) 1 \ GoldbachChain.MajorArcs P Q) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          GoldbachChain.e ((n : ℝ) * α)‖ ≤
      300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P := by
  have hPone : 1 ≤ P := by omega
  have hNone : 1 ≤ N := by
    have : 1 ≤ P ^ 3 := one_le_pow₀ hPone
    omega
  have hPbound : P ≤ N := by
    calc
      P ≤ P ^ 3 := Nat.le_self_pow (by omega) P
      _ ≤ N := hPN
  have hPPbound : P * P ≤ N := by
    calc
      P * P = P ^ 2 := by ring
      _ ≤ P ^ 3 := Nat.pow_le_pow_right hPone (by omega)
      _ ≤ N := hPN
  have hPPone : 1 ≤ P * P := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsup := GoldbachChain.MinorArc.minor_sup_uniform
    N P Q P P (by omega) hPQcut hPbound hPPbound
    hPPone
    (GoldbachChain.minorCsup N P P P Q)
    (fun q hPq hqQ =>
      GoldbachChain.MinorArc.tightSupRHS_le
        N P P P Q q hNone hPone hPone hPone hPq hqQ)
    α hα
  exact hsup.trans
    (GoldbachChain.MinorArc.minorCsup_bound N P Q hP hPN hPQ)

/-- Explicit cubic minor-arc control for one unrestricted prime sum and two
arbitrarily restricted finite von-Mangoldt windows.  The bound is

`300 * N² * (log N + 2)³ * (log N)² / sqrt P`.

In particular, any cutoff `P` exceeding a sufficiently high power of `log N`
makes this contribution lower order than the natural weighted ternary main
term.  The unrestricted supremum is deliberately visible: transporting it to
shifted residue-class phases requires a separate localization lemma. -/
theorem ternary_minor_arc_window_integral_bound
    (N P Q : ℕ)
    (hP : 2 ≤ P)
    (hPN : P ^ 3 ≤ N)
    (hPQcut : P ≤ Q)
    (hPQ : P * Q ≤ N)
    (left right : Finset ℕ)
    (hleft : left ⊆ Finset.range N)
    (hright : right ⊆ Finset.range N) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ GoldbachChain.MajorArcs P Q,
      (∑ n ∈ Finset.Ioc 0 N,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          GoldbachChain.e ((n : ℝ) * α)) *
        ternaryExponentialSum left
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 α *
        ternaryExponentialSum right
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 α‖ ≤
      300 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
        Real.log N ^ 2 / Real.sqrt P := by
  let first : ℝ → ℂ := fun α =>
    ∑ n ∈ Finset.Ioc 0 N,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        GoldbachChain.e ((n : ℝ) * α)
  let second : ℝ → ℂ := fun α =>
    ternaryExponentialSum left
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) 1 α
  let third : ℝ → ℂ := fun α =>
    ternaryExponentialSum right
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) 1 α
  let minor : Set ℝ := Set.Ioc (0 : ℝ) 1 \ GoldbachChain.MajorArcs P Q
  let bound : ℝ :=
    300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P
  have hPone : 1 ≤ P := by omega
  have hNone : 1 ≤ N := by
    have : 1 ≤ P ^ 3 := one_le_pow₀ hPone
    omega
  have hlog : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast hNone)
  have hbound : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have hfirst : Continuous first := by
    dsimp [first]
    unfold GoldbachChain.e
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
    measurableSet_Ioc.diff
      (GoldbachChain.MinorArc.measurableSet_majorArcs P Q)
  have hsubset : minor ⊆ Set.Ioc (0 : ℝ) 1 := Set.sdiff_subset
  have hsup : ∀ α ∈ minor, ‖first α‖ ≤ bound := by
    intro α hα
    exact ternary_minor_arc_vonMangoldt_sup
      N P Q hP hPN hPQcut hPQ α hα
  have hquadratic := ternary_minor_integral_le_quadratic_energy
    first second third hfirst hsecond hthird minor hminor hsubset
    bound hbound hsup
  have hleftEnergy :
      (∫ α in (0 : ℝ)..1, ‖second α‖ ^ 2) ≤
        (N : ℝ) * Real.log N ^ 2 :=
    ternary_vonMangoldt_window_parseval_le left N hleft
  have hrightEnergy :
      (∫ α in (0 : ℝ)..1, ‖third α‖ ^ 2) ≤
        (N : ℝ) * Real.log N ^ 2 :=
    ternary_vonMangoldt_window_parseval_le right N hright
  change
    ‖∫ α in minor, first α * second α * third α‖ ≤
      300 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
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
    _ = 300 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
          Real.log N ^ 2 / Real.sqrt P := by
      dsimp [bound]
      ring

/-- The explicit cubic minor-arc estimate with two arbitrary nonzero integral
dilations.  In particular `leftFrequency = a` and
`rightFrequency = -2 * d` give the exact nontrivial manuscript frequencies;
the third factor remains the explicitly unrestricted label sum. -/
theorem ternary_minor_arc_dilated_window_integral_bound
    (N P Q : ℕ)
    (hP : 2 ≤ P)
    (hPN : P ^ 3 ≤ N)
    (hPQcut : P ≤ Q)
    (hPQ : P * Q ≤ N)
    (left right : Finset ℕ)
    (hleft : left ⊆ Finset.range N)
    (hright : right ⊆ Finset.range N)
    (leftFrequency rightFrequency : ℤ)
    (hleftFrequency : leftFrequency ≠ 0)
    (hrightFrequency : rightFrequency ≠ 0) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ GoldbachChain.MajorArcs P Q,
      (∑ n ∈ Finset.Ioc 0 N,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          GoldbachChain.e ((n : ℝ) * α)) *
        ternaryExponentialSum left
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          leftFrequency α *
        ternaryExponentialSum right
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          rightFrequency α‖ ≤
      300 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
        Real.log N ^ 2 / Real.sqrt P := by
  let first : ℝ → ℂ := fun α =>
    ∑ n ∈ Finset.Ioc 0 N,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        GoldbachChain.e ((n : ℝ) * α)
  let second : ℝ → ℂ := fun α =>
    ternaryExponentialSum left
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      leftFrequency α
  let third : ℝ → ℂ := fun α =>
    ternaryExponentialSum right
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      rightFrequency α
  let minor : Set ℝ := Set.Ioc (0 : ℝ) 1 \ GoldbachChain.MajorArcs P Q
  let bound : ℝ :=
    300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P
  have hPone : 1 ≤ P := by omega
  have hNone : 1 ≤ N := by
    have : 1 ≤ P ^ 3 := one_le_pow₀ hPone
    omega
  have hlog : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast hNone)
  have hbound : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have hfirst : Continuous first := by
    dsimp [first]
    unfold GoldbachChain.e
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
    measurableSet_Ioc.diff
      (GoldbachChain.MinorArc.measurableSet_majorArcs P Q)
  have hsubset : minor ⊆ Set.Ioc (0 : ℝ) 1 := Set.sdiff_subset
  have hsup : ∀ α ∈ minor, ‖first α‖ ≤ bound := by
    intro α hα
    exact ternary_minor_arc_vonMangoldt_sup
      N P Q hP hPN hPQcut hPQ α hα
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
      300 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
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
    _ = 300 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
          Real.log N ^ 2 / Real.sqrt P := by
      dsimp [bound]
      ring

/-- The integer-periodic lift of the Goldbach minor arcs.  The shift is
recorded existentially, so no discontinuous choice of a representative is
needed. -/
def ternaryPeriodicMinorArcs (P Q : ℕ) : Set ℝ :=
  ⋃ k : ℤ,
    (fun α : ℝ => α - (k : ℝ)) ⁻¹'
      (Set.Ioc (0 : ℝ) 1 \ GoldbachChain.MajorArcs P Q)

/-- Frequencies whose every fixed-modulus character shift remains on a
periodic Goldbach minor arc. -/
def ternaryShiftedMinorArcs (modulus P Q : ℕ) : Set ℝ :=
  Set.Ioc (0 : ℝ) 1 ∩
    ⋂ j : Fin modulus,
      (fun α : ℝ => α + (j.val : ℝ) / modulus) ⁻¹'
        ternaryPeriodicMinorArcs P Q

/-- The complementary periodic major-arc region. -/
def ternaryPeriodicMajorArcs (P Q : ℕ) : Set ℝ :=
  (ternaryPeriodicMinorArcs P Q)ᶜ

theorem ternaryPeriodicMinorArcs_measurable (P Q : ℕ) :
    MeasurableSet (ternaryPeriodicMinorArcs P Q) := by
  unfold ternaryPeriodicMinorArcs
  apply MeasurableSet.iUnion
  intro k
  exact
    (measurableSet_Ioc.diff
      (GoldbachChain.MinorArc.measurableSet_majorArcs P Q)).preimage
      (continuous_id.sub continuous_const).measurable

theorem ternaryShiftedMinorArcs_measurable (modulus P Q : ℕ) :
    MeasurableSet (ternaryShiftedMinorArcs modulus P Q) := by
  unfold ternaryShiftedMinorArcs
  apply measurableSet_Ioc.inter
  apply MeasurableSet.iInter
  intro j
  exact
    (ternaryPeriodicMinorArcs_measurable P Q).preimage
      (continuous_id.add continuous_const).measurable

/-- Membership explicitly records one integer-period correction for each
additive-character shift. -/
theorem mem_ternaryShiftedMinorArcs_iff
    (modulus P Q : ℕ) (α : ℝ) :
    α ∈ ternaryShiftedMinorArcs modulus P Q ↔
      α ∈ Set.Ioc (0 : ℝ) 1 ∧
        ∀ j ∈ Finset.range modulus,
          ∃ k : ℤ,
            α + (j : ℝ) / modulus - (k : ℝ) ∈
              Set.Ioc (0 : ℝ) 1 \ GoldbachChain.MajorArcs P Q := by
  simp only [ternaryShiftedMinorArcs, ternaryPeriodicMinorArcs,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨hα, hshift⟩
    refine ⟨hα, ?_⟩
    intro j hj
    exact hshift ⟨j, Finset.mem_range.mp hj⟩
  · rintro ⟨hα, hshift⟩
    refine ⟨hα, ?_⟩
    intro j
    exact hshift j.val (Finset.mem_range.mpr j.isLt)

/-- Exponential sums with integral frequencies are genuinely periodic under
every integer translation. -/
theorem ternaryExponentialSum_add_int
    (window : Finset ℕ)
    (weight : ℕ → ℂ)
    (frequency : ℤ)
    (α : ℝ)
    (k : ℤ) :
    ternaryExponentialSum window weight frequency (α + (k : ℝ)) =
      ternaryExponentialSum window weight frequency α := by
  unfold ternaryExponentialSum
  apply Finset.sum_congr rfl
  intro n hn
  have hphase :
      ((frequency : ℝ) * (n : ℝ)) * (α + (k : ℝ)) =
        ((frequency : ℝ) * (n : ℝ)) * α +
          (((frequency * (n : ℤ) * k : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [hphase, ← GoldbachChain.e_add, GoldbachChain.MinorArc.e_int,
    mul_one]

/-- On the unit fundamental interval, the complement of the simultaneous
shifted minor arcs is exactly a finite union of shifted periodic major arcs.
Thus the localization cost is a geometric enlargement of the major region,
not a multiplicative loss in the minor-arc estimate. -/
theorem ternaryShiftedMinorArcs_complement_eq
    (modulus P Q : ℕ) :
    Set.Ioc (0 : ℝ) 1 \ ternaryShiftedMinorArcs modulus P Q =
      Set.Ioc (0 : ℝ) 1 ∩
        ⋃ j : Fin modulus,
          (fun α : ℝ => α + (j.val : ℝ) / modulus) ⁻¹'
            ternaryPeriodicMajorArcs P Q := by
  classical
  ext α
  simp [ternaryShiftedMinorArcs, ternaryPeriodicMajorArcs]

/-- A fixed residue class inherits the unrestricted Goldbach minor-arc
supremum on the simultaneous shifted minor region.  Integer periodicity
handles character shifts outside the fundamental interval, and averaging
keeps the numerical constant independent of the modulus. -/
theorem ternary_shifted_minor_residue_vonMangoldt_sup
    (N P Q modulus residue : ℕ)
    (hP : 2 ≤ P)
    (hPN : P ^ 3 ≤ N)
    (hPQcut : P ≤ Q)
    (hPQ : P * Q ≤ N)
    (hmodulus : 0 < modulus)
    (α : ℝ)
    (hα : α ∈ ternaryShiftedMinorArcs modulus P Q) :
    ‖ternaryExponentialSum
      ((Finset.Ioc 0 N).filter
        fun n => n % modulus = residue % modulus)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      1 α‖ ≤
      300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P := by
  apply ternary_residue_filtered_exponential_sum_norm_le
    (Finset.Ioc 0 N)
    (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
    modulus residue hmodulus α
    (300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P)
  intro j hj
  obtain ⟨k, hk⟩ :=
    ((mem_ternaryShiftedMinorArcs_iff modulus P Q α).mp hα).2 j hj
  let β : ℝ := α + (j : ℝ) / modulus - (k : ℝ)
  have hperiod :
      ternaryExponentialSum (Finset.Ioc 0 N)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 (α + (j : ℝ) / modulus) =
        ternaryExponentialSum (Finset.Ioc 0 N)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 β := by
    simpa [β] using
      ternaryExponentialSum_add_int (Finset.Ioc 0 N)
        (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        1 β k
  rw [hperiod]
  simpa [ternaryExponentialSum] using
    ternary_minor_arc_vonMangoldt_sup
      N P Q hP hPN hPQcut hPQ β hk

/-- Fully localized cubic minor-arc estimate: the first factor is restricted
to any fixed residue class, the other two have arbitrary finite windows and
arbitrary nonzero integral dilations, and the minor region is the exact
intersection on which all additive-character shifts remain minor.  There is
no modulus-dependent loss in the bound. -/
theorem ternary_shifted_minor_residue_dilated_window_integral_bound
    (N P Q modulus residue : ℕ)
    (hP : 2 ≤ P)
    (hPN : P ^ 3 ≤ N)
    (hPQcut : P ≤ Q)
    (hPQ : P * Q ≤ N)
    (hmodulus : 0 < modulus)
    (left right : Finset ℕ)
    (hleft : left ⊆ Finset.range N)
    (hright : right ⊆ Finset.range N)
    (leftFrequency rightFrequency : ℤ)
    (hleftFrequency : leftFrequency ≠ 0)
    (hrightFrequency : rightFrequency ≠ 0) :
    ‖∫ α in ternaryShiftedMinorArcs modulus P Q,
      ternaryExponentialSum
        ((Finset.Ioc 0 N).filter
          fun n => n % modulus = residue % modulus)
        (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        1 α *
        ternaryExponentialSum left
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          leftFrequency α *
        ternaryExponentialSum right
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          rightFrequency α‖ ≤
      300 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
        Real.log N ^ 2 / Real.sqrt P := by
  let first : ℝ → ℂ := fun α =>
    ternaryExponentialSum
      ((Finset.Ioc 0 N).filter
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
    300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P
  have hPone : 1 ≤ P := by omega
  have hNone : 1 ≤ N := by
    have : 1 ≤ P ^ 3 := one_le_pow₀ hPone
    omega
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
    exact ternary_shifted_minor_residue_vonMangoldt_sup
      N P Q modulus residue hP hPN hPQcut hPQ hmodulus α hα
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
      300 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
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
    _ = 300 * (N : ℝ) ^ 2 * (Real.log N + 2) ^ 3 *
          Real.log N ^ 2 / Real.sqrt P := by
      dsimp [bound]
      ring

/-- Every archimedean interval exponential sum is exactly the difference of
its two prefix exponential sums, with no endpoint or residue convention lost. -/
theorem ternary_interval_exponentialSum_eq_sub
    (lower upper : ℕ)
    (hlower : lower ≤ upper)
    (weight : ℕ → ℂ)
    (frequency : ℤ)
    (α : ℝ) :
    ternaryExponentialSum (Finset.Ioc lower upper) weight frequency α =
      ternaryExponentialSum (Finset.Ioc 0 upper) weight frequency α -
        ternaryExponentialSum (Finset.Ioc 0 lower) weight frequency α := by
  have hdisjoint :
      Disjoint (Finset.Ioc 0 lower) (Finset.Ioc lower upper) :=
    Finset.Ioc_disjoint_Ioc_of_le (le_refl lower)
  have hunion :
      Finset.Ioc 0 lower ∪ Finset.Ioc lower upper =
        Finset.Ioc 0 upper :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le lower) hlower
  have hsplit :
      ternaryExponentialSum (Finset.Ioc 0 lower) weight frequency α +
        ternaryExponentialSum (Finset.Ioc lower upper) weight frequency α =
          ternaryExponentialSum (Finset.Ioc 0 upper) weight frequency α := by
    unfold ternaryExponentialSum
    rw [← Finset.sum_union hdisjoint, hunion]
  apply (eq_sub_iff_add_eq).2
  simpa [add_comm] using hsplit

/-- The explicit Goldbach prefix majorant increases with the prefix endpoint
once that endpoint is positive. -/
theorem ternary_minor_prefix_bound_mono
    (lower upper P : ℕ)
    (hpositive : 1 ≤ lower)
    (hlower : lower ≤ upper) :
    300 * (lower : ℝ) * (Real.log lower + 2) ^ 3 / Real.sqrt P ≤
      300 * (upper : ℝ) * (Real.log upper + 2) ^ 3 / Real.sqrt P := by
  have hlowerReal : (lower : ℝ) ≤ (upper : ℝ) := by
    exact_mod_cast hlower
  have hpositiveReal : (0 : ℝ) < lower := by
    exact_mod_cast hpositive
  have hloglower : 0 ≤ Real.log lower :=
    Real.log_nonneg (by exact_mod_cast hpositive)
  have hlogmono : Real.log (lower : ℝ) ≤ Real.log (upper : ℝ) :=
    Real.log_le_log hpositiveReal hlowerReal
  gcongr

/-- The actual finite label band in a fixed residue class has a shifted
minor-arc supremum bounded by twice the unrestricted prefix bound.  Both
endpoints satisfy the same minor-arc eligibility conditions; no modulus
factor appears. -/
theorem ternary_shifted_minor_residue_interval_vonMangoldt_sup
    (lower N P Q modulus residue : ℕ)
    (hP : 2 ≤ P)
    (hPlower : P ^ 3 ≤ lower)
    (hPQcut : P ≤ Q)
    (hPQlower : P * Q ≤ lower)
    (hlower : lower ≤ N)
    (hmodulus : 0 < modulus)
    (α : ℝ)
    (hα : α ∈ ternaryShiftedMinorArcs modulus P Q) :
    ‖ternaryExponentialSum
      ((Finset.Ioc lower N).filter
        fun n => n % modulus = residue % modulus)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      1 α‖ ≤
      600 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P := by
  have hPN : P ^ 3 ≤ N := hPlower.trans hlower
  have hPQ : P * Q ≤ N := hPQlower.trans hlower
  have hpositive : 1 ≤ lower := by
    have hPone : 1 ≤ P := by omega
    have : 1 ≤ P ^ 3 := one_le_pow₀ hPone
    omega
  apply ternary_residue_filtered_exponential_sum_norm_le
    (Finset.Ioc lower N)
    (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
    modulus residue hmodulus α
    (600 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P)
  intro j hj
  obtain ⟨k, hk⟩ :=
    ((mem_ternaryShiftedMinorArcs_iff modulus P Q α).mp hα).2 j hj
  let β : ℝ := α + (j : ℝ) / modulus - (k : ℝ)
  have hperiod :
      ternaryExponentialSum (Finset.Ioc lower N)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 (α + (j : ℝ) / modulus) =
        ternaryExponentialSum (Finset.Ioc lower N)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 β := by
    simpa [β] using
      ternaryExponentialSum_add_int (Finset.Ioc lower N)
        (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        1 β k
  have hupperBound :
      ‖ternaryExponentialSum (Finset.Ioc 0 N)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 β‖ ≤
        300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P := by
    simpa [ternaryExponentialSum] using
      ternary_minor_arc_vonMangoldt_sup
        N P Q hP hPN hPQcut hPQ β hk
  have hlowerBound :
      ‖ternaryExponentialSum (Finset.Ioc 0 lower)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 β‖ ≤
        300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P := by
    calc
      ‖ternaryExponentialSum (Finset.Ioc 0 lower)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          1 β‖ ≤
          300 * (lower : ℝ) * (Real.log lower + 2) ^ 3 / Real.sqrt P := by
        simpa [ternaryExponentialSum] using
          ternary_minor_arc_vonMangoldt_sup
            lower P Q hP hPlower hPQcut hPQlower β hk
      _ ≤ 300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P :=
        ternary_minor_prefix_bound_mono lower N P hpositive hlower
  rw [hperiod,
    ternary_interval_exponentialSum_eq_sub lower N hlower]
  calc
    ‖ternaryExponentialSum (Finset.Ioc 0 N)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) 1 β -
        ternaryExponentialSum (Finset.Ioc 0 lower)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) 1 β‖ ≤
        ‖ternaryExponentialSum (Finset.Ioc 0 N)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) 1 β‖ +
        ‖ternaryExponentialSum (Finset.Ioc 0 lower)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) 1 β‖ :=
      norm_sub_le _ _
    _ ≤ (300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P) +
          (300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P) :=
      add_le_add hupperBound hlowerBound
    _ = 600 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P := by
      ring

/-- The actual archimedean-and-residue-localized manuscript label factor,
together with arbitrary restricted windows for the other two prime factors
and their exact nonzero integral affine coefficients.  The only localization
cost is the factor two from writing the label interval as a difference of
prefixes; in particular no fixed-modulus loss occurs. -/
theorem ternary_shifted_minor_residue_interval_dilated_window_integral_bound
    (lower N P Q modulus residue : ℕ)
    (hP : 2 ≤ P)
    (hPlower : P ^ 3 ≤ lower)
    (hPQcut : P ≤ Q)
    (hPQlower : P * Q ≤ lower)
    (hlower : lower ≤ N)
    (hmodulus : 0 < modulus)
    (left right : Finset ℕ)
    (hleft : left ⊆ Finset.range N)
    (hright : right ⊆ Finset.range N)
    (leftFrequency rightFrequency : ℤ)
    (hleftFrequency : leftFrequency ≠ 0)
    (hrightFrequency : rightFrequency ≠ 0) :
    ‖∫ α in ternaryShiftedMinorArcs modulus P Q,
      ternaryExponentialSum
        ((Finset.Ioc lower N).filter
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
      ((Finset.Ioc lower N).filter
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
  have hNone : 1 ≤ N := by
    have : 1 ≤ P ^ 3 := one_le_pow₀ hPone
    omega
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
    exact ternary_shifted_minor_residue_interval_vonMangoldt_sup
      lower N P Q modulus residue hP hPlower hPQcut hPQlower
      hlower hmodulus α hα
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

/-- The exact telescoping estimate transferring three separate major-arc
approximations to their cubic product.  Each input is allowed its own error;
no symmetry or shared coefficient is assumed. -/
theorem ternary_major_arc_product_error
    (first second third firstModel secondModel thirdModel : ℂ)
    (firstError secondError thirdError : ℝ)
    (hfirst : ‖first - firstModel‖ ≤ firstError)
    (hsecond : ‖second - secondModel‖ ≤ secondError)
    (hthird : ‖third - thirdModel‖ ≤ thirdError) :
    ‖first * second * third - firstModel * secondModel * thirdModel‖ ≤
      firstError * (‖secondModel‖ + secondError) *
          (‖thirdModel‖ + thirdError) +
        ‖firstModel‖ * secondError * (‖thirdModel‖ + thirdError) +
        ‖firstModel‖ * ‖secondModel‖ * thirdError := by
  have hfirstError : 0 ≤ firstError := (norm_nonneg _).trans hfirst
  have hsecondError : 0 ≤ secondError := (norm_nonneg _).trans hsecond
  have hthirdError : 0 ≤ thirdError := (norm_nonneg _).trans hthird
  have hsecondNorm : ‖second‖ ≤ ‖secondModel‖ + secondError := by
    calc
      ‖second‖ = ‖secondModel + (second - secondModel)‖ := by
        congr 1
        ring
      _ ≤ ‖secondModel‖ + ‖second - secondModel‖ :=
        norm_add_le _ _
      _ ≤ ‖secondModel‖ + secondError := by gcongr
  have hthirdNorm : ‖third‖ ≤ ‖thirdModel‖ + thirdError := by
    calc
      ‖third‖ = ‖thirdModel + (third - thirdModel)‖ := by
        congr 1
        ring
      _ ≤ ‖thirdModel‖ + ‖third - thirdModel‖ :=
        norm_add_le _ _
      _ ≤ ‖thirdModel‖ + thirdError := by gcongr
  have htelescope :
      first * second * third - firstModel * secondModel * thirdModel =
        (first - firstModel) * second * third +
          firstModel * (second - secondModel) * third +
          firstModel * secondModel * (third - thirdModel) := by
    ring
  rw [htelescope]
  calc
    ‖(first - firstModel) * second * third +
        firstModel * (second - secondModel) * third +
        firstModel * secondModel * (third - thirdModel)‖ ≤
        ‖(first - firstModel) * second * third‖ +
          ‖firstModel * (second - secondModel) * third‖ +
          ‖firstModel * secondModel * (third - thirdModel)‖ := by
      calc
        ‖(first - firstModel) * second * third +
            firstModel * (second - secondModel) * third +
            firstModel * secondModel * (third - thirdModel)‖ ≤
            ‖(first - firstModel) * second * third +
              firstModel * (second - secondModel) * third‖ +
              ‖firstModel * secondModel * (third - thirdModel)‖ :=
          norm_add_le _ _
        _ ≤ ‖(first - firstModel) * second * third‖ +
              ‖firstModel * (second - secondModel) * third‖ +
              ‖firstModel * secondModel * (third - thirdModel)‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ firstError * (‖secondModel‖ + secondError) *
            (‖thirdModel‖ + thirdError) +
          ‖firstModel‖ * secondError * (‖thirdModel‖ + thirdError) +
          ‖firstModel‖ * ‖secondModel‖ * thirdError := by
      simp only [norm_mul]
      gcongr

/-- On one residue class, the rational part of a major-arc frequency factors
out exactly, for every integral affine coefficient and every finite window. -/
theorem ternary_progression_major_arc_phase
    (window : Finset ℕ)
    (weight : ℕ → ℂ)
    (frequency numerator : ℤ)
    (modulus residue : ℕ)
    (hmodulus : 0 < modulus)
    (β : ℝ) :
    ternaryExponentialSum
      (window.filter fun n => n % modulus = residue)
      weight frequency ((numerator : ℝ) / modulus + β) =
        GoldbachChain.e
          (((frequency : ℝ) * residue) * numerator / modulus) *
          ternaryExponentialSum
            (window.filter fun n => n % modulus = residue)
            weight frequency β := by
  unfold ternaryExponentialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hresidue : n % modulus = residue :=
    (Finset.mem_filter.mp hn).2
  have hn_nat : modulus * (n / modulus) + residue = n := by
    rw [← hresidue]
    exact Nat.div_add_mod n modulus
  have hn_real :
      (n : ℝ) = (modulus : ℝ) * ((n / modulus : ℕ) : ℝ) +
        (residue : ℝ) := by
    exact_mod_cast hn_nat.symm
  have hmodulusReal : (modulus : ℝ) ≠ 0 := by
    exact_mod_cast hmodulus.ne'
  have hphase :
      ((frequency : ℝ) * n) * ((numerator : ℝ) / modulus + β) =
        (((frequency * numerator * (n / modulus : ℕ) : ℤ) : ℝ)) +
          (((frequency : ℝ) * residue) * numerator / modulus +
            ((frequency : ℝ) * n) * β) := by
    rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, hn_real]
    field_simp
    ring
  rw [hphase, ← GoldbachChain.e_add, GoldbachChain.MinorArc.e_int,
    one_mul, ← GoldbachChain.e_add]
  ring

/-- Unconditional, exponentially rated Siegel--Walfisz control of a twisted
prime sum in any reduced residue class.  Unlike the Goldbach master's
unrestricted rated window, this keeps the individual residue cell visible
for subsequent ternary major-arc products. -/
theorem ternary_rated_unit_progression_twisted_model
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N →
        ∀ modulus : ℕ, 0 < modulus →
          (modulus : ℝ) ≤ Real.log N ^ B →
          ∀ residue : ℕ, residue < modulus →
            Nat.gcd residue modulus = 1 →
            ∀ β : ℝ,
              ‖(∑ n ∈ (Finset.range N).filter
                    (fun n => n % modulus = residue),
                  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                    GoldbachChain.e ((n : ℝ) * β)) -
                (1 / (modulus.totient : ℂ)) *
                  ∑ n ∈ Finset.range N,
                    GoldbachChain.e ((n : ℝ) * β)‖ ≤
                C * N * Real.exp
                    (-c * Real.log N ^ ((1 : ℝ) / 10)) *
                  (1 + 2 * Real.pi * N * |β|) := by
  obtain ⟨c, C, hc, hC, N₀, hprogression⟩ :=
    GoldbachChain.rated_progression_bound B hB
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hN modulus hmodulus hsize residue hresidue hunit β
  apply GoldbachChain.MinorArc.ap_twisted_model
    (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
    (1 / (modulus.totient : ℂ)) modulus residue N β
    (C * N * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 10)))
  intro t ht
  exact hprogression N hN modulus hmodulus hsize
    residue hresidue hunit t ht

/-- The explicit major-arc model in one reduced residue cell: its rational
phase, the local factor `1 / φ(modulus)`, and its coefficient-dilated smooth
archimedean exponential sum remain separate. -/
noncomputable def ternaryMajorArcProgressionModel
    (N modulus residue : ℕ)
    (frequency numerator : ℤ)
    (β : ℝ) : ℂ :=
  GoldbachChain.e
      (((frequency : ℝ) * residue) * numerator / modulus) *
    ((1 / (modulus.totient : ℂ)) *
      ternaryExponentialSum (Finset.range N) (fun _ => 1) frequency β)

/-- The proven Siegel--Walfisz/Abel major-arc error for an integer-dilated
frequency. -/
noncomputable def ternaryMajorArcProgressionError
    (c C : ℝ) (N : ℕ) (frequency : ℤ) (β : ℝ) : ℝ :=
  C * N * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 10)) *
    (1 + 2 * Real.pi * N * |(frequency : ℝ) * β|)

/-- Unconditional per-rational major-arc evaluation for a genuinely
residue-restricted prime sum with any integral affine coefficient.  An anchor
of denominator `q` together with a prescribed modulus `M` is represented by
the common modulus `lcm q M` and the corresponding rescaled numerator. -/
theorem ternary_rated_progression_major_arc_model
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N →
        ∀ modulus : ℕ, 0 < modulus →
          (modulus : ℝ) ≤ Real.log N ^ B →
          ∀ residue : ℕ, residue < modulus →
            Nat.gcd residue modulus = 1 →
            ∀ frequency numerator : ℤ, ∀ β : ℝ,
              ‖ternaryExponentialSum
                  ((Finset.range N).filter
                    fun n => n % modulus = residue)
                  (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                  frequency ((numerator : ℝ) / modulus + β) -
                ternaryMajorArcProgressionModel
                  N modulus residue frequency numerator β‖ ≤
                ternaryMajorArcProgressionError c C N frequency β := by
  obtain ⟨c, C, hc, hC, N₀, htwisted⟩ :=
    ternary_rated_unit_progression_twisted_model B hB
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hN modulus hmodulus hsize residue hresidue hunit
    frequency numerator β
  let phase : ℂ :=
    GoldbachChain.e
      (((frequency : ℝ) * residue) * numerator / modulus)
  let prime : ℂ :=
    ternaryExponentialSum
      ((Finset.range N).filter fun n => n % modulus = residue)
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      frequency β
  let smooth : ℂ :=
    ternaryExponentialSum (Finset.range N) (fun _ => 1) frequency β
  have hphase := ternary_progression_major_arc_phase
    (Finset.range N)
    (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
    frequency numerator modulus residue hmodulus β
  have hprime :
      prime = ∑ n ∈ (Finset.range N).filter
          (fun n => n % modulus = residue),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          GoldbachChain.e ((n : ℝ) * ((frequency : ℝ) * β)) := by
    dsimp [prime]
    unfold ternaryExponentialSum
    apply Finset.sum_congr rfl
    intro n hn
    congr 2
    ring
  have hsmooth :
      smooth = ∑ n ∈ Finset.range N,
        GoldbachChain.e ((n : ℝ) * ((frequency : ℝ) * β)) := by
    dsimp [smooth]
    unfold ternaryExponentialSum
    simp only [one_mul]
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    ring
  have hmodel := htwisted N hN modulus hmodulus hsize
    residue hresidue hunit ((frequency : ℝ) * β)
  rw [hphase]
  change
    ‖phase * prime - phase * ((1 / (modulus.totient : ℂ)) * smooth)‖ ≤
      ternaryMajorArcProgressionError c C N frequency β
  calc
    ‖phase * prime - phase * ((1 / (modulus.totient : ℂ)) * smooth)‖ =
        ‖phase * (prime - (1 / (modulus.totient : ℂ)) * smooth)‖ := by
      congr 1
      ring
    _ = ‖prime - (1 / (modulus.totient : ℂ)) * smooth‖ := by
      rw [norm_mul]
      change ‖GoldbachChain.e _‖ * _ = _
      rw [GoldbachChain.e_norm, one_mul]
    _ ≤ ternaryMajorArcProgressionError c C N frequency β := by
      rw [hprime, hsmooth]
      exact hmodel

/-- The complete per-rational cubic major-arc product approximation for the
manuscript's exact three coefficients `1`, `a`, and `-2d`, in arbitrary
reduced residue cells of a shared effective modulus.  Every one-factor error
has the proven Siegel--Walfisz exponential rate; the displayed bound is the
rigorous telescoping transfer to the ternary product. -/
theorem ternary_rated_manuscript_major_arc_product_model
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N →
        ∀ modulus : ℕ, 0 < modulus →
          (modulus : ℝ) ≤ Real.log N ^ B →
          ∀ labelResidue leftResidue rightResidue : ℕ,
            labelResidue < modulus →
            leftResidue < modulus →
            rightResidue < modulus →
            Nat.gcd labelResidue modulus = 1 →
            Nat.gcd leftResidue modulus = 1 →
            Nat.gcd rightResidue modulus = 1 →
            ∀ a d : ℕ, ∀ numerator : ℤ, ∀ β : ℝ,
              let label := ternaryExponentialSum
                ((Finset.range N).filter
                  fun n => n % modulus = labelResidue)
                (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                1 ((numerator : ℝ) / modulus + β)
              let left := ternaryExponentialSum
                ((Finset.range N).filter
                  fun n => n % modulus = leftResidue)
                (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                (a : ℤ) ((numerator : ℝ) / modulus + β)
              let right := ternaryExponentialSum
                ((Finset.range N).filter
                  fun n => n % modulus = rightResidue)
                (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                (-2 * (d : ℤ)) ((numerator : ℝ) / modulus + β)
              let labelModel := ternaryMajorArcProgressionModel
                N modulus labelResidue 1 numerator β
              let leftModel := ternaryMajorArcProgressionModel
                N modulus leftResidue (a : ℤ) numerator β
              let rightModel := ternaryMajorArcProgressionModel
                N modulus rightResidue (-2 * (d : ℤ)) numerator β
              let labelError :=
                ternaryMajorArcProgressionError c C N 1 β
              let leftError :=
                ternaryMajorArcProgressionError c C N (a : ℤ) β
              let rightError :=
                ternaryMajorArcProgressionError c C N (-2 * (d : ℤ)) β
              ‖label * left * right - labelModel * leftModel * rightModel‖ ≤
                labelError * (‖leftModel‖ + leftError) *
                    (‖rightModel‖ + rightError) +
                  ‖labelModel‖ * leftError *
                    (‖rightModel‖ + rightError) +
                  ‖labelModel‖ * ‖leftModel‖ * rightError := by
  obtain ⟨c, C, hc, hC, N₀, hmodel⟩ :=
    ternary_rated_progression_major_arc_model B hB
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hN modulus hmodulus hsize
    labelResidue leftResidue rightResidue
    hlabelResidue hleftResidue hrightResidue
    hlabelUnit hleftUnit hrightUnit a d numerator β
  apply ternary_major_arc_product_error
  · exact hmodel N hN modulus hmodulus hsize
      labelResidue hlabelResidue hlabelUnit 1 numerator β
  · exact hmodel N hN modulus hmodulus hsize
      leftResidue hleftResidue hleftUnit (a : ℤ) numerator β
  · exact hmodel N hN modulus hmodulus hsize
      rightResidue hrightResidue hrightUnit (-2 * (d : ℤ)) numerator β

/-- Prefix subtraction for half-open archimedean windows, matching the
`range` convention used by the upstream Siegel--Walfisz theorem. -/
theorem ternary_Ico_exponentialSum_eq_sub
    (lower upper : ℕ)
    (hlower : lower ≤ upper)
    (weight : ℕ → ℂ)
    (frequency : ℤ)
    (α : ℝ) :
    ternaryExponentialSum (Finset.Ico lower upper) weight frequency α =
      ternaryExponentialSum (Finset.range upper) weight frequency α -
        ternaryExponentialSum (Finset.range lower) weight frequency α := by
  unfold ternaryExponentialSum
  exact Finset.sum_Ico_eq_sub _ hlower

/-- Prefix subtraction remains exact after imposing one fixed residue class. -/
theorem ternary_filtered_Ico_exponentialSum_eq_sub
    (lower upper : ℕ)
    (hlower : lower ≤ upper)
    (modulus residue : ℕ)
    (weight : ℕ → ℂ)
    (frequency : ℤ)
    (α : ℝ) :
    ternaryExponentialSum
      ((Finset.Ico lower upper).filter
        fun n => n % modulus = residue)
      weight frequency α =
      ternaryExponentialSum
          ((Finset.range upper).filter
            fun n => n % modulus = residue)
          weight frequency α -
        ternaryExponentialSum
          ((Finset.range lower).filter
            fun n => n % modulus = residue)
          weight frequency α := by
  unfold ternaryExponentialSum
  simp_rw [Finset.sum_filter]
  exact Finset.sum_Ico_eq_sub _ hlower

/-- The actual interval major-arc model, keeping the rational phase, local
unit-residue density, coefficient, and independent archimedean endpoints. -/
noncomputable def ternaryMajorArcIntervalModel
    (lower upper modulus residue : ℕ)
    (frequency numerator : ℤ)
    (β : ℝ) : ℂ :=
  GoldbachChain.e
      (((frequency : ℝ) * residue) * numerator / modulus) *
    ((1 / (modulus.totient : ℂ)) *
      ternaryExponentialSum
        (Finset.Ico lower upper) (fun _ => 1) frequency β)

/-- Unconditional rated major-arc evaluation on any actual archimedean
interval and reduced residue class, for every integral affine coefficient.
The two prefix endpoints are both controlled at the common scale `N`, so
neither endpoint needs its own Siegel--Walfisz threshold; their subtraction
costs exactly a factor of two. -/
theorem ternary_rated_interval_progression_major_arc_model
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N →
        ∀ lower upper : ℕ, lower ≤ upper → upper ≤ N →
          ∀ modulus : ℕ, 0 < modulus →
            (modulus : ℝ) ≤ Real.log N ^ B →
            ∀ residue : ℕ, residue < modulus →
              Nat.gcd residue modulus = 1 →
              ∀ frequency numerator : ℤ, ∀ β : ℝ,
                ‖ternaryExponentialSum
                    ((Finset.Ico lower upper).filter
                      fun n => n % modulus = residue)
                    (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                    frequency ((numerator : ℝ) / modulus + β) -
                  ternaryMajorArcIntervalModel
                    lower upper modulus residue frequency numerator β‖ ≤
                  2 * ternaryMajorArcProgressionError c C N frequency β := by
  obtain ⟨c, C, hc, hC, N₀, hprogression⟩ :=
    GoldbachChain.rated_progression_bound B hB
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hN lower upper hlower hupper modulus hmodulus hsize
    residue hresidue hunit frequency numerator β
  let phase : ℂ :=
    GoldbachChain.e
      (((frequency : ℝ) * residue) * numerator / modulus)
  let κ : ℂ := 1 / (modulus.totient : ℂ)
  let error : ℝ :=
    C * N * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 10))
  have herror : 0 ≤ error := by
    dsimp [error]
    positivity
  have hprefix : ∀ T : ℕ, T ≤ N →
      ‖ternaryExponentialSum
            ((Finset.range T).filter
              fun n => n % modulus = residue)
            (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            frequency β -
          κ * ternaryExponentialSum
            (Finset.range T) (fun _ => 1) frequency β‖ ≤
        ternaryMajorArcProgressionError c C N frequency β := by
    intro T hT
    have habel := GoldbachChain.MinorArc.ap_twisted_model
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      κ modulus residue T ((frequency : ℝ) * β) error
      (fun t ht =>
        hprogression N hN modulus hmodulus hsize residue hresidue hunit
          t (ht.trans hT))
    have hprime :
        ternaryExponentialSum
            ((Finset.range T).filter
              fun n => n % modulus = residue)
            (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            frequency β =
          ∑ n ∈ (Finset.range T).filter
              (fun n => n % modulus = residue),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              GoldbachChain.e ((n : ℝ) * ((frequency : ℝ) * β)) := by
      unfold ternaryExponentialSum
      apply Finset.sum_congr rfl
      intro n hn
      congr 2
      ring
    have hsmooth :
        ternaryExponentialSum (Finset.range T) (fun _ => 1)
            frequency β =
          ∑ n ∈ Finset.range T,
            GoldbachChain.e ((n : ℝ) * ((frequency : ℝ) * β)) := by
      unfold ternaryExponentialSum
      simp only [one_mul]
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      ring
    rw [hprime, hsmooth]
    calc
      ‖(∑ n ∈ (Finset.range T).filter
            (fun n => n % modulus = residue),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            GoldbachChain.e ((n : ℝ) * ((frequency : ℝ) * β))) -
          κ * ∑ n ∈ Finset.range T,
            GoldbachChain.e ((n : ℝ) * ((frequency : ℝ) * β))‖ ≤
          error * (1 + 2 * Real.pi * T * |(frequency : ℝ) * β|) :=
        habel
      _ ≤ error * (1 + 2 * Real.pi * N * |(frequency : ℝ) * β|) := by
        gcongr
      _ = ternaryMajorArcProgressionError c C N frequency β := rfl
  have hphase := ternary_progression_major_arc_phase
    (Finset.Ico lower upper)
    (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
    frequency numerator modulus residue hmodulus β
  rw [hphase]
  change
    ‖phase * ternaryExponentialSum
          ((Finset.Ico lower upper).filter
            fun n => n % modulus = residue)
          (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          frequency β -
        phase * (κ * ternaryExponentialSum
          (Finset.Ico lower upper) (fun _ => 1) frequency β)‖ ≤
      2 * ternaryMajorArcProgressionError c C N frequency β
  rw [ternary_filtered_Ico_exponentialSum_eq_sub
    lower upper hlower modulus residue,
    ternary_Ico_exponentialSum_eq_sub lower upper hlower]
  have hupperPrefix := hprefix upper hupper
  have hlowerPrefix := hprefix lower (hlower.trans hupper)
  calc
    ‖phase *
          (ternaryExponentialSum
            ((Finset.range upper).filter
              fun n => n % modulus = residue)
            (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            frequency β -
          ternaryExponentialSum
            ((Finset.range lower).filter
              fun n => n % modulus = residue)
            (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            frequency β) -
        phase *
          (κ * (ternaryExponentialSum (Finset.range upper)
              (fun _ => 1) frequency β -
            ternaryExponentialSum (Finset.range lower)
              (fun _ => 1) frequency β))‖ =
        ‖phase *
          ((ternaryExponentialSum
              ((Finset.range upper).filter
                fun n => n % modulus = residue)
              (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
              frequency β -
            κ * ternaryExponentialSum (Finset.range upper)
              (fun _ => 1) frequency β) -
          (ternaryExponentialSum
              ((Finset.range lower).filter
                fun n => n % modulus = residue)
              (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
              frequency β -
            κ * ternaryExponentialSum (Finset.range lower)
              (fun _ => 1) frequency β))‖ := by
      congr 1
      ring
    _ = ‖(ternaryExponentialSum
              ((Finset.range upper).filter
                fun n => n % modulus = residue)
              (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
              frequency β -
            κ * ternaryExponentialSum (Finset.range upper)
              (fun _ => 1) frequency β) -
          (ternaryExponentialSum
              ((Finset.range lower).filter
                fun n => n % modulus = residue)
              (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
              frequency β -
            κ * ternaryExponentialSum (Finset.range lower)
              (fun _ => 1) frequency β)‖ := by
      rw [norm_mul]
      change ‖GoldbachChain.e _‖ * _ = _
      rw [GoldbachChain.e_norm, one_mul]
    _ ≤ ‖ternaryExponentialSum
              ((Finset.range upper).filter
                fun n => n % modulus = residue)
              (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
              frequency β -
            κ * ternaryExponentialSum (Finset.range upper)
              (fun _ => 1) frequency β‖ +
          ‖ternaryExponentialSum
              ((Finset.range lower).filter
                fun n => n % modulus = residue)
              (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
              frequency β -
            κ * ternaryExponentialSum (Finset.range lower)
              (fun _ => 1) frequency β‖ :=
      norm_sub_le _ _
    _ ≤ ternaryMajorArcProgressionError c C N frequency β +
          ternaryMajorArcProgressionError c C N frequency β :=
      add_le_add hupperPrefix hlowerPrefix
    _ = 2 * ternaryMajorArcProgressionError c C N frequency β := by ring

/-- The fully archimedean-localized per-rational cubic major-arc model for
the actual manuscript coefficients `1`, `a`, and `-2d`.  All three finite
intervals and all three reduced residue classes are independent, while the
Siegel--Walfisz error is controlled uniformly at the common scale `N`. -/
theorem ternary_rated_manuscript_interval_major_arc_product_model
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N →
        ∀ labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ,
          labelLower ≤ labelUpper → labelUpper ≤ N →
          leftLower ≤ leftUpper → leftUpper ≤ N →
          rightLower ≤ rightUpper → rightUpper ≤ N →
          ∀ modulus : ℕ, 0 < modulus →
            (modulus : ℝ) ≤ Real.log N ^ B →
            ∀ labelResidue leftResidue rightResidue : ℕ,
              labelResidue < modulus →
              leftResidue < modulus →
              rightResidue < modulus →
              Nat.gcd labelResidue modulus = 1 →
              Nat.gcd leftResidue modulus = 1 →
              Nat.gcd rightResidue modulus = 1 →
              ∀ a d : ℕ, ∀ numerator : ℤ, ∀ β : ℝ,
                let label := ternaryExponentialSum
                  ((Finset.Ico labelLower labelUpper).filter
                    fun n => n % modulus = labelResidue)
                  (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                  1 ((numerator : ℝ) / modulus + β)
                let left := ternaryExponentialSum
                  ((Finset.Ico leftLower leftUpper).filter
                    fun n => n % modulus = leftResidue)
                  (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                  (a : ℤ) ((numerator : ℝ) / modulus + β)
                let right := ternaryExponentialSum
                  ((Finset.Ico rightLower rightUpper).filter
                    fun n => n % modulus = rightResidue)
                  (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                  (-2 * (d : ℤ)) ((numerator : ℝ) / modulus + β)
                let labelModel := ternaryMajorArcIntervalModel
                  labelLower labelUpper modulus labelResidue 1 numerator β
                let leftModel := ternaryMajorArcIntervalModel
                  leftLower leftUpper modulus leftResidue
                  (a : ℤ) numerator β
                let rightModel := ternaryMajorArcIntervalModel
                  rightLower rightUpper modulus rightResidue
                  (-2 * (d : ℤ)) numerator β
                let labelError :=
                  2 * ternaryMajorArcProgressionError c C N 1 β
                let leftError :=
                  2 * ternaryMajorArcProgressionError c C N (a : ℤ) β
                let rightError :=
                  2 * ternaryMajorArcProgressionError
                    c C N (-2 * (d : ℤ)) β
                ‖label * left * right -
                    labelModel * leftModel * rightModel‖ ≤
                  labelError * (‖leftModel‖ + leftError) *
                      (‖rightModel‖ + rightError) +
                    ‖labelModel‖ * leftError *
                      (‖rightModel‖ + rightError) +
                    ‖labelModel‖ * ‖leftModel‖ * rightError := by
  obtain ⟨c, C, hc, hC, N₀, hmodel⟩ :=
    ternary_rated_interval_progression_major_arc_model B hB
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hN labelLower labelUpper leftLower leftUpper rightLower rightUpper
    hlabelLower hlabelUpper hleftLower hleftUpper hrightLower hrightUpper
    modulus hmodulus hsize labelResidue leftResidue rightResidue
    hlabelResidue hleftResidue hrightResidue
    hlabelUnit hleftUnit hrightUnit a d numerator β
  apply ternary_major_arc_product_error
  · exact hmodel N hN labelLower labelUpper hlabelLower hlabelUpper
      modulus hmodulus hsize labelResidue hlabelResidue hlabelUnit
      1 numerator β
  · exact hmodel N hN leftLower leftUpper hleftLower hleftUpper
      modulus hmodulus hsize leftResidue hleftResidue hleftUnit
      (a : ℤ) numerator β
  · exact hmodel N hN rightLower rightUpper hrightLower hrightUpper
      modulus hmodulus hsize rightResidue hrightResidue hrightUnit
      (-2 * (d : ℤ)) numerator β

/-- Pointwise complex major-arc model errors integrate without cancellation
assumptions: the norm of the difference of integrals is bounded by the
integral of any pointwise real error majorant. -/
theorem ternary_major_arc_integrated_error
    (arc : Set ℝ)
    (harc : MeasurableSet arc)
    (actual model : ℝ → ℂ)
    (error : ℝ → ℝ)
    (hactual : IntegrableOn actual arc volume)
    (hmodel : IntegrableOn model arc volume)
    (herror : IntegrableOn error arc volume)
    (hpoint : ∀ α ∈ arc, ‖actual α - model α‖ ≤ error α) :
    ‖(∫ α in arc, actual α) - (∫ α in arc, model α)‖ ≤
      ∫ α in arc, error α := by
  rw [← MeasureTheory.integral_sub hactual hmodel]
  calc
    ‖∫ α in arc, actual α - model α‖ ≤
        ∫ α in arc, ‖actual α - model α‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ α in arc, error α :=
      MeasureTheory.setIntegral_mono_on
        (hactual.sub hmodel).norm herror harc hpoint

/-- On a measurable subset of the fundamental circle, a constant pointwise
major-arc error costs exactly `error × measure(arc)`. -/
theorem ternary_major_arc_integrated_constant_error
    (arc : Set ℝ)
    (harc : MeasurableSet arc)
    (hsubset : arc ⊆ Set.Ioc (0 : ℝ) 1)
    (actual model : ℝ → ℂ)
    (hactual : IntegrableOn actual arc volume)
    (hmodel : IntegrableOn model arc volume)
    (bound : ℝ)
    (hpoint : ∀ α ∈ arc, ‖actual α - model α‖ ≤ bound) :
    ‖(∫ α in arc, actual α) - (∫ α in arc, model α)‖ ≤
      bound * volume.real arc := by
  have hfinite : volume arc < ⊤ :=
    (measure_mono hsubset).trans_lt measure_Ioc_lt_top
  have hconstant : IntegrableOn (fun _ : ℝ => bound) arc volume :=
    integrableOn_const hfinite.ne
  have hmajor := ternary_major_arc_integrated_error
    arc harc actual model (fun _ : ℝ => bound)
    hactual hmodel hconstant hpoint
  simpa [mul_comm] using hmajor

/-- A positive real lower bound for the integrated major-arc model transfers
to the real part of the actual cubic correlation, losing only the integrated
pointwise error.  No singular-series evaluation is assumed here. -/
theorem ternary_major_arc_real_lower_of_model
    (arc : Set ℝ)
    (harc : MeasurableSet arc)
    (hsubset : arc ⊆ Set.Ioc (0 : ℝ) 1)
    (actual model : ℝ → ℂ)
    (hactual : IntegrableOn actual arc volume)
    (hmodel : IntegrableOn model arc volume)
    (bound main : ℝ)
    (hpoint : ∀ α ∈ arc, ‖actual α - model α‖ ≤ bound)
    (hmain : main ≤ (∫ α in arc, model α).re) :
    main - bound * volume.real arc ≤
      (∫ α in arc, actual α).re := by
  have hnorm := ternary_major_arc_integrated_constant_error
    arc harc hsubset actual model hactual hmodel bound hpoint
  have hreal :=
    (Complex.abs_re_le_norm
      ((∫ α in arc, actual α) - (∫ α in arc, model α))).trans hnorm
  have hlower := (neg_le_of_abs_le hreal)
  change -(bound * volume.real arc) ≤
    (∫ α in arc, actual α).re - (∫ α in arc, model α).re at hlower
  linarith

/-- For an admissible residue triple, the three rational major-arc phases
for `P + a*q - 2*d*q'` cancel exactly.  This is the arithmetic reason the
individual local model carries a real nonnegative coefficient rather than an
uncontrolled complex oscillation. -/
theorem ternary_manuscript_major_arc_phase_cancel
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus)
    (numerator : ℤ) :
    GoldbachChain.e
          ((labelResidue : ℝ) * numerator / modulus) *
        GoldbachChain.e
          (((a : ℝ) * leftResidue) * numerator / modulus) *
        GoldbachChain.e
          ((((-2 * (d : ℤ) : ℤ) : ℝ) * rightResidue) *
            numerator / modulus) = 1 := by
  have hdivisibility :
      (modulus : ℤ) ∣
        ((a * leftResidue + labelResidue : ℕ) : ℤ) -
          ((2 * d * rightResidue : ℕ) : ℤ) :=
    Nat.modEq_iff_dvd.mp hadmissible.symm
  obtain ⟨k, hk⟩ := hdivisibility
  have hbalance := congrArg (fun z : ℤ => (z : ℝ)) hk
  push_cast at hbalance
  have hmodulusReal : (modulus : ℝ) ≠ 0 := by
    exact_mod_cast hmodulus.ne'
  rw [GoldbachChain.e_add, GoldbachChain.e_add]
  have hphase :
      (labelResidue : ℝ) * numerator / modulus +
          (((a : ℝ) * leftResidue) * numerator / modulus) +
          ((((-2 * (d : ℤ) : ℤ) : ℝ) * rightResidue) *
            numerator / modulus) =
        ((k * numerator : ℤ) : ℝ) := by
    push_cast
    field_simp
    linear_combination (numerator : ℝ) * hbalance
  rw [hphase, GoldbachChain.MinorArc.e_int]

/-- After admissible-residue phase cancellation, the cubic major-arc model is
exactly the positive local coefficient `φ(modulus)⁻³` times the three smooth
archimedean interval sums. -/
theorem ternary_manuscript_interval_model_product_eq
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ)
    (β : ℝ) :
    ternaryMajorArcIntervalModel
          labelLower labelUpper modulus labelResidue 1 numerator β *
        ternaryMajorArcIntervalModel
          leftLower leftUpper modulus leftResidue (a : ℤ) numerator β *
        ternaryMajorArcIntervalModel
          rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β =
      (1 / (modulus.totient : ℂ)) ^ 3 *
        (ternaryExponentialSum (Finset.Ico labelLower labelUpper)
          (fun _ => 1) 1 β *
          ternaryExponentialSum (Finset.Ico leftLower leftUpper)
            (fun _ => 1) (a : ℤ) β *
          ternaryExponentialSum (Finset.Ico rightLower rightUpper)
            (fun _ => 1) (-2 * (d : ℤ)) β) := by
  have hphase := ternary_manuscript_major_arc_phase_cancel
    modulus labelResidue leftResidue rightResidue a d
    hmodulus hadmissible numerator
  unfold ternaryMajorArcIntervalModel
  simp only [Int.cast_one, one_mul, Int.cast_natCast]
  calc
    GoldbachChain.e ((labelResidue : ℝ) * numerator / modulus) *
            ((1 / (modulus.totient : ℂ)) *
              ternaryExponentialSum
                (Finset.Ico labelLower labelUpper) (fun _ => 1) 1 β) *
          (GoldbachChain.e
              (((a : ℝ) * leftResidue) * numerator / modulus) *
            ((1 / (modulus.totient : ℂ)) *
              ternaryExponentialSum
                (Finset.Ico leftLower leftUpper) (fun _ => 1) (a : ℤ) β)) *
          (GoldbachChain.e
              ((((-2 * (d : ℤ) : ℤ) : ℝ) * rightResidue) *
                numerator / modulus) *
            ((1 / (modulus.totient : ℂ)) *
              ternaryExponentialSum
                (Finset.Ico rightLower rightUpper) (fun _ => 1)
                (-2 * (d : ℤ)) β)) =
        (GoldbachChain.e ((labelResidue : ℝ) * numerator / modulus) *
          GoldbachChain.e
            (((a : ℝ) * leftResidue) * numerator / modulus) *
          GoldbachChain.e
            ((((-2 * (d : ℤ) : ℤ) : ℝ) * rightResidue) *
              numerator / modulus)) *
          ((1 / (modulus.totient : ℂ)) ^ 3 *
            (ternaryExponentialSum (Finset.Ico labelLower labelUpper)
              (fun _ => 1) 1 β *
              ternaryExponentialSum (Finset.Ico leftLower leftUpper)
                (fun _ => 1) (a : ℤ) β *
              ternaryExponentialSum (Finset.Ico rightLower rightUpper)
                (fun _ => 1) (-2 * (d : ℤ)) β)) := by
      ring
    _ = _ := by rw [hphase, one_mul]

/-- On the whole circle (not on a truncated major arc), the smooth ternary
archimedean singular integral is exactly the nonnegative finite count of
lattice solutions `a*q + P = 2*d*q'` in the three independent intervals. -/
theorem ternary_archimedean_interval_singular_integral
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (a d : ℕ) :
    (∫ β in (0 : ℝ)..1,
      ternaryExponentialSum (Finset.Ico labelLower labelUpper)
          (fun _ => 1) 1 β *
        ternaryExponentialSum (Finset.Ico leftLower leftUpper)
          (fun _ => 1) (a : ℤ) β *
        ternaryExponentialSum (Finset.Ico rightLower rightUpper)
          (fun _ => 1) (-2 * (d : ℤ)) β) =
      ((ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico rightLower rightUpper)
        (Finset.Ico labelLower labelUpper)
        a (2 * d)).card : ℂ) := by
  have hfrequency : (-2 * (d : ℤ)) = (-(2 * d : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hfrequency]
  calc
    (∫ β in (0 : ℝ)..1,
      ternaryExponentialSum (Finset.Ico labelLower labelUpper)
          (fun _ => 1) 1 β *
        ternaryExponentialSum (Finset.Ico leftLower leftUpper)
          (fun _ => 1) (a : ℤ) β *
        ternaryExponentialSum (Finset.Ico rightLower rightUpper)
          (fun _ => 1) (-(2 * d : ℕ) : ℤ) β) =
      (∫ β in (0 : ℝ)..1,
        ternaryExponentialSum (Finset.Ico leftLower leftUpper)
            (fun _ => 1) (a : ℤ) β *
          ternaryExponentialSum (Finset.Ico rightLower rightUpper)
            (fun _ => 1) (-(2 * d : ℕ) : ℤ) β *
          ternaryExponentialSum (Finset.Ico labelLower labelUpper)
            (fun _ => 1) 1 β) := by
      apply intervalIntegral.integral_congr
      intro β hβ
      ring
    _ = _ := ternary_affine_count_fourier_identity
      (Finset.Ico leftLower leftUpper)
      (Finset.Ico rightLower rightUpper)
      (Finset.Ico labelLower labelUpper)
      a (2 * d)

/-- The full-circle integral of one admissible residue-cell major-arc model
is exactly `φ(modulus)⁻³` times its nonnegative affine lattice count.  This
identity concerns the whole archimedean circle; it makes no claim that a
truncated Farey arc already captures that mass. -/
theorem ternary_manuscript_interval_model_singular_integral
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) :
    (∫ β in (0 : ℝ)..1,
      ternaryMajorArcIntervalModel
          labelLower labelUpper modulus labelResidue 1 numerator β *
        ternaryMajorArcIntervalModel
          leftLower leftUpper modulus leftResidue (a : ℤ) numerator β *
        ternaryMajorArcIntervalModel
          rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β) =
      (1 / (modulus.totient : ℂ)) ^ 3 *
        ((ternaryAffineTriples
          (Finset.Ico leftLower leftUpper)
          (Finset.Ico rightLower rightUpper)
          (Finset.Ico labelLower labelUpper)
          a (2 * d)).card : ℂ) := by
  calc
    (∫ β in (0 : ℝ)..1,
      ternaryMajorArcIntervalModel
          labelLower labelUpper modulus labelResidue 1 numerator β *
        ternaryMajorArcIntervalModel
          leftLower leftUpper modulus leftResidue (a : ℤ) numerator β *
        ternaryMajorArcIntervalModel
          rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β) =
      (∫ β in (0 : ℝ)..1,
        (1 / (modulus.totient : ℂ)) ^ 3 *
          (ternaryExponentialSum (Finset.Ico labelLower labelUpper)
              (fun _ => 1) 1 β *
            ternaryExponentialSum (Finset.Ico leftLower leftUpper)
              (fun _ => 1) (a : ℤ) β *
            ternaryExponentialSum (Finset.Ico rightLower rightUpper)
              (fun _ => 1) (-2 * (d : ℤ)) β)) := by
      apply intervalIntegral.integral_congr
      intro β hβ
      exact ternary_manuscript_interval_model_product_eq
        modulus labelResidue leftResidue rightResidue a d
        hmodulus hadmissible labelLower labelUpper leftLower leftUpper
        rightLower rightUpper numerator β
    _ = (1 / (modulus.totient : ℂ)) ^ 3 *
        (∫ β in (0 : ℝ)..1,
          ternaryExponentialSum (Finset.Ico labelLower labelUpper)
              (fun _ => 1) 1 β *
            ternaryExponentialSum (Finset.Ico leftLower leftUpper)
              (fun _ => 1) (a : ℤ) β *
            ternaryExponentialSum (Finset.Ico rightLower rightUpper)
              (fun _ => 1) (-2 * (d : ℤ)) β) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [ternary_archimedean_interval_singular_integral
        labelLower labelUpper leftLower leftUpper rightLower rightUpper a d]

/-- Every admissible residue-cell whole-circle model has nonnegative real
mass; this is exact finite positivity, not an asserted truncated-arc bound. -/
theorem ternary_manuscript_interval_model_singular_integral_nonneg
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) :
    0 ≤ (∫ β in (0 : ℝ)..1,
      ternaryMajorArcIntervalModel
          labelLower labelUpper modulus labelResidue 1 numerator β *
        ternaryMajorArcIntervalModel
          leftLower leftUpper modulus leftResidue (a : ℤ) numerator β *
        ternaryMajorArcIntervalModel
          rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β).re := by
  rw [ternary_manuscript_interval_model_singular_integral
    modulus labelResidue leftResidue rightResidue a d hmodulus hadmissible
    labelLower labelUpper leftLower leftUpper rightLower rightUpper numerator]
  have hcast :
      (1 / (modulus.totient : ℂ)) ^ 3 *
          ((ternaryAffineTriples
            (Finset.Ico leftLower leftUpper)
            (Finset.Ico rightLower rightUpper)
            (Finset.Ico labelLower labelUpper)
            a (2 * d)).card : ℂ) =
        (((1 / (modulus.totient : ℝ)) ^ 3 *
          ((ternaryAffineTriples
            (Finset.Ico leftLower leftUpper)
            (Finset.Ico rightLower rightUpper)
            (Finset.Ico labelLower labelUpper)
            a (2 * d)).card : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re]
  positivity

/-- An explicit affine lattice witness makes the admissible residue-cell
whole-circle model strictly positive.  This proves qualitative positivity
only; obtaining a uniform quadratic lattice lower bound is separate. -/
theorem ternary_manuscript_interval_model_singular_integral_pos_of_witness
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ)
    (left right label : ℕ)
    (hleft : left ∈ Finset.Ico leftLower leftUpper)
    (hright : right ∈ Finset.Ico rightLower rightUpper)
    (hlabel : label ∈ Finset.Ico labelLower labelUpper)
    (hequation : a * left + label = 2 * d * right) :
    0 < (∫ β in (0 : ℝ)..1,
      ternaryMajorArcIntervalModel
          labelLower labelUpper modulus labelResidue 1 numerator β *
        ternaryMajorArcIntervalModel
          leftLower leftUpper modulus leftResidue (a : ℤ) numerator β *
        ternaryMajorArcIntervalModel
          rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β).re := by
  have hwitness :
      (left, (right, label)) ∈ ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico rightLower rightUpper)
        (Finset.Ico labelLower labelUpper)
        a (2 * d) := by
    unfold ternaryAffineTriples
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨hleft, Finset.mem_product.mpr ⟨hright, hlabel⟩⟩,
        hequation⟩
  have hcard :
      0 < (ternaryAffineTriples
        (Finset.Ico leftLower leftUpper)
        (Finset.Ico rightLower rightUpper)
        (Finset.Ico labelLower labelUpper)
        a (2 * d)).card := Finset.card_pos.mpr ⟨_, hwitness⟩
  have htotient : 0 < modulus.totient := Nat.totient_pos.mpr hmodulus
  rw [ternary_manuscript_interval_model_singular_integral
    modulus labelResidue leftResidue rightResidue a d hmodulus hadmissible
    labelLower labelUpper leftLower leftUpper rightLower rightUpper numerator]
  have hcast :
      (1 / (modulus.totient : ℂ)) ^ 3 *
          ((ternaryAffineTriples
            (Finset.Ico leftLower leftUpper)
            (Finset.Ico rightLower rightUpper)
            (Finset.Ico labelLower labelUpper)
            a (2 * d)).card : ℂ) =
        (((1 / (modulus.totient : ℝ)) ^ 3 *
          ((ternaryAffineTriples
            (Finset.Ico leftLower leftUpper)
            (Finset.Ico rightLower rightUpper)
            (Finset.Ico labelLower labelUpper)
            a (2 * d)).card : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re]
  positivity

end Erdos689

