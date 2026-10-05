module

public import AdaptiveMixedSharedTargetPrimePowerFibers1139

@[expose] public section


/-!
# Actual proper-prime-power removal in all three mixed-pattern families

The physical #1139 parameter is the dyadic prime-label scale `N`, whereas
the natural upper bound on all actual prime-form values is a FIXED multiple
`K * N`.  Identifying those two parameters would be false: the genuine label
itself lies in `(N, 2 * N]`.

This file keeps the source-faithful scaled cutoff and proves proper-prime-
power removal on the ACTUAL original two-dimensional signed box and both
ACTUAL three-dimensional paired lattices.  Every affine fiber is supplied by
previously proved exact physical-coordinate injection theorems.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1139

/-- The audited fixed-rank prime-power error still tends to zero when the
actual dyadic scale is `N` and the prime-form cutoff is any fixed `K * N`. -/
theorem adaptiveMixedProperPrimePowerScaledError_tendsto_zero
    (rank multiplier : ℕ) (multiplier_positive : 0 < multiplier) :
    Tendsto
      (fun N : ℕ =>
        (Nat.sqrt (multiplier * N) : ℝ) *
          ((Nat.log 2 (multiplier * N) : ℝ) + 1) *
            Real.log ((multiplier * N : ℕ) : ℝ) ^ rank / (N : ℝ))
      atTop (nhds 0) := by
  have scaled_top : Tendsto (fun N : ℕ => multiplier * N) atTop atTop :=
    Filter.tendsto_atTop_mono
      (fun N => Nat.le_mul_of_pos_left N multiplier_positive) tendsto_id
  have composed :=
    (adaptiveMixedProperPrimePowerScaleError_tendsto_zero rank).comp scaled_top
  have scaled_limit := composed.const_mul (multiplier : ℝ)
  convert scaled_limit using 1
  · funext N
    simp only [Function.comp_apply]
    by_cases zero : N = 0
    · simp [zero]
    · have multiplier_nonzero : (multiplier : ℝ) ≠ 0 := by
        exact_mod_cast multiplier_positive.ne'
      have N_nonzero : (N : ℝ) ≠ 0 := by
        exact_mod_cast zero
      push_cast
      field_simp
  · simp

/-- Arbitrary fixed-rank, arbitrary positive-dimensional removal with the
TRUE two-parameter scaling: forms are bounded by `K * N`, fibers are
`O(N^(dimension-1))`, and the proper-prime-power contribution is
`o(N^dimension)`. -/
theorem adaptiveMixedVonMangoldtPrimePowerExceptions_scaled_normalized_tendsto_zero
    {ι α : Type*} (forms : Finset ι) (points : ℕ → Finset α)
    (value : ι → ℕ → α → ℕ)
    (dimension coefficient multiplier : ℕ)
    (dimension_positive : 0 < dimension)
    (multiplier_positive : 0 < multiplier)
    (bounded : ∀ N : ℕ, ∀ point ∈ points N,
      ∀ index ∈ forms, value index N point ∈ Finset.Ioc 0 (multiplier * N))
    (fibers : ∀ N : ℕ, ∀ index ∈ forms,
      ∀ power ∈ Erdos689.ternaryProperPrimePowers (multiplier * N),
        ((points N).filter
          fun point => value index N point = power).card ≤
            coefficient * N ^ (dimension - 1)) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
          (points N) forms (fun index point => value index N point),
            adaptiveMixedVonMangoldtProduct forms
              (fun index point => value index N point) point) /
                (N : ℝ) ^ dimension)
      atTop (nhds 0) := by
  have upper_limit :
      Tendsto
        (fun N : ℕ =>
          ((forms.card : ℝ) * (coefficient : ℝ)) *
            ((Nat.sqrt (multiplier * N) : ℝ) *
              ((Nat.log 2 (multiplier * N) : ℝ) + 1) *
                Real.log ((multiplier * N : ℕ) : ℝ) ^ forms.card / (N : ℝ)))
        atTop (nhds 0) := by
    simpa using
      (adaptiveMixedProperPrimePowerScaledError_tendsto_zero
        forms.card multiplier multiplier_positive).const_mul
          ((forms.card : ℝ) * (coefficient : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds upper_limit ?_ ?_
  · exact Eventually.of_forall fun N =>
      div_nonneg (Finset.sum_nonneg fun point _ =>
        adaptiveMixedVonMangoldtProduct_nonneg forms
          (fun index point => value index N point) point) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with N at_least_one
    have positive : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast at_least_one
    have power_positive : (0 : ℝ) < (N : ℝ) ^ dimension := by
      positivity
    have exception_bound :=
      adaptiveMixedVonMangoldtPrimePowerExceptions_weight_le
        (points N) forms (fun index point => value index N point)
        (multiplier * N) (coefficient * N ^ (dimension - 1))
        (bounded N) (fibers N)
    calc
      (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
          (points N) forms (fun index point => value index N point),
            adaptiveMixedVonMangoldtProduct forms
              (fun index point => value index N point) point) /
                (N : ℝ) ^ dimension ≤
          ((forms.card : ℝ) *
            ((coefficient * N ^ (dimension - 1) : ℕ) : ℝ) *
              (Nat.sqrt (multiplier * N) : ℝ) *
                ((Nat.log 2 (multiplier * N) : ℝ) + 1) *
                  Real.log ((multiplier * N : ℕ) : ℝ) ^ forms.card) /
                    (N : ℝ) ^ dimension := by
          exact (div_le_div_iff_of_pos_right power_positive).mpr exception_bound
      _ = ((forms.card : ℝ) * (coefficient : ℝ)) *
            ((Nat.sqrt (multiplier * N) : ℝ) *
              ((Nat.log 2 (multiplier * N) : ℝ) + 1) *
                Real.log ((multiplier * N : ℕ) : ℝ) ^ forms.card / (N : ℝ)) := by
          simp only [Nat.cast_mul, Nat.cast_pow]
          have power_identity :
              (N : ℝ) ^ dimension =
                (N : ℝ) ^ (dimension - 1) * (N : ℝ) := by
            rw [← pow_succ]
            congr 1
            omega
          rw [power_identity]
          field_simp

/-- Exact genuine signed-center-window size has a fixed linear coefficient
for every positive dyadic scale; its additive endpoint is retained. -/
theorem adaptiveMixedSignedSearchCenterWindow_linear_bound
    (base N : ℕ) (positive : 0 < N) :
    2 * (base + 1) * N + 1 ≤ (2 * (base + 1) + 1) * N := by
  calc
    2 * (base + 1) * N + 1 ≤ 2 * (base + 1) * N + N :=
      Nat.add_le_add_left positive _
    _ = (2 * (base + 1) + 1) * N := by ring

/-- The TWO actual signed-center windows have an explicit fixed quadratic
bound, without discarding either endpoint contribution. -/
theorem adaptiveMixedSignedPairedSearchWindows_quadratic_bound
    (firstBase secondBase N : ℕ) (positive : 0 < N) :
    (2 * (firstBase + 1) * N + 1) *
      (2 * (secondBase + 1) * N + 1) ≤
        ((2 * (firstBase + 1) + 1) *
          (2 * (secondBase + 1) + 1)) * N ^ 2 := by
  calc
    (2 * (firstBase + 1) * N + 1) *
        (2 * (secondBase + 1) * N + 1) ≤
      ((2 * (firstBase + 1) + 1) * N) *
        ((2 * (secondBase + 1) + 1) * N) :=
          Nat.mul_le_mul
            (adaptiveMixedSignedSearchCenterWindow_linear_bound
              firstBase N positive)
            (adaptiveMixedSignedSearchCenterWindow_linear_bound
              secondBase N positive)
    _ = ((2 * (firstBase + 1) + 1) *
          (2 * (secondBase + 1) + 1)) * N ^ 2 := by ring

/-- TRUE original signed physical-system prime-power removal at EVERY fixed
mixed rank and EVERY fixed positive form cutoff multiplier.  Its actual
dyadic-label/signed-center proper-prime-power error is `o(N²)`. -/
theorem adaptiveMixedSignedOriginalPrimePowerExceptions_normalized_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (multiplier : ℕ) (multiplier_positive : 0 < multiplier)
    (primes : ∀ prime ∈ support, prime.Prime)
    (points : ℕ → Finset (ℕ × ℤ))
    (boxed : ∀ N : ℕ,
      points N ⊆ (Finset.Ioc N (2 * N)).product
        (adaptiveMixedSignedSearchCenterWindow outcome.1 N))
    (bounded : ∀ N : ℕ, ∀ point ∈ points N,
      ∀ index ∈ adaptiveMixedActualFormIndices support scale outcome,
        adaptiveMixedActualSignedPrimeFormValue
          support outcome.1 index point ∈ Finset.Ioc 0 (multiplier * N)) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
          (points N) (adaptiveMixedActualFormIndices support scale outcome)
          (adaptiveMixedActualSignedPrimeFormValue support outcome.1),
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedActualFormIndices support scale outcome)
              (adaptiveMixedActualSignedPrimeFormValue support outcome.1)
                point) / (N : ℝ) ^ 2)
      atTop (nhds 0) := by
  apply adaptiveMixedVonMangoldtPrimePowerExceptions_scaled_normalized_tendsto_zero
    (adaptiveMixedActualFormIndices support scale outcome) points
      (fun index _N point =>
        adaptiveMixedActualSignedPrimeFormValue support outcome.1 index point)
        2 (2 * (outcome.1 + 1) + 1) multiplier
          (by norm_num) multiplier_positive bounded
  intro N index selected power selected_power
  by_cases zero : N = 0
  · subst N
    have empty : points 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro point in_points
      have impossible := boxed 0 in_points
      simp at impossible
    simp [empty]
  · have positive : 0 < N := Nat.pos_of_ne_zero zero
    have power_positive :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp selected_power).1).1
    calc
      ((points N).filter fun point =>
        adaptiveMixedActualSignedPrimeFormValue
          support outcome.1 index point = power).card ≤
          2 * (outcome.1 + 1) * N + 1 :=
        adaptiveMixedSignedOriginalActualFormFiber_card_le_window
          support scale outcome N (points N) (boxed N) primes
            index selected power power_positive
      _ ≤ (2 * (outcome.1 + 1) + 1) * N :=
        adaptiveMixedSignedSearchCenterWindow_linear_bound
          outcome.1 N positive
      _ = (2 * (outcome.1 + 1) + 1) * N ^ (2 - 1) := by simp

/-- TRUE shared-label signed three-coordinate prime-power removal at EVERY
fixed combined mixed rank.  One genuine prime label and BOTH full signed
target branches are retained, and their proper-prime-power error is `o(N³)`. -/
theorem adaptiveMixedSignedSharedLabelPrimePowerExceptions_normalized_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (multiplier : ℕ) (multiplier_positive : 0 < multiplier)
    (primes : ∀ prime ∈ support, prime.Prime)
    (points : ℕ → Finset (ℕ × ℤ × ℤ))
    (boxed : ∀ N : ℕ,
      points N ⊆ (Finset.Ioc N (2 * N)).product
        ((adaptiveMixedSignedSearchCenterWindow first.1 N).product
          (adaptiveMixedSignedSearchCenterWindow second.1 N)))
    (bounded : ∀ N : ℕ, ∀ point ∈ points N,
      ∀ index ∈ adaptiveMixedSharedLabelFormIndices support scale first second,
        adaptiveMixedSharedLabelSignedPrimeFormValue
          support first.1 second.1 index point ∈
            Finset.Ioc 0 (multiplier * N)) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
          (points N) (adaptiveMixedSharedLabelFormIndices
            support scale first second)
          (adaptiveMixedSharedLabelSignedPrimeFormValue
            support first.1 second.1),
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedSharedLabelFormIndices support scale first second)
              (adaptiveMixedSharedLabelSignedPrimeFormValue
                support first.1 second.1) point) / (N : ℝ) ^ 3)
      atTop (nhds 0) := by
  apply adaptiveMixedVonMangoldtPrimePowerExceptions_scaled_normalized_tendsto_zero
    (adaptiveMixedSharedLabelFormIndices support scale first second) points
      (fun index _N point =>
        adaptiveMixedSharedLabelSignedPrimeFormValue
          support first.1 second.1 index point)
        3 ((2 * (first.1 + 1) + 1) * (2 * (second.1 + 1) + 1))
          multiplier (by norm_num) multiplier_positive bounded
  intro N index selected power selected_power
  by_cases zero : N = 0
  · subst N
    have empty : points 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro point in_points
      have impossible := boxed 0 in_points
      simp at impossible
    simp [empty]
  · have positive : 0 < N := Nat.pos_of_ne_zero zero
    have power_positive :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp selected_power).1).1
    calc
      ((points N).filter fun point =>
        adaptiveMixedSharedLabelSignedPrimeFormValue
          support first.1 second.1 index point = power).card ≤
        (2 * (first.1 + 1) * N + 1) *
          (2 * (second.1 + 1) * N + 1) :=
        adaptiveMixedSignedSharedLabelActualFormFiber_card_le_windows
          support scale first second N (points N) (boxed N) primes
            index selected power power_positive
      _ ≤ ((2 * (first.1 + 1) + 1) *
          (2 * (second.1 + 1) + 1)) * N ^ 2 :=
        adaptiveMixedSignedPairedSearchWindows_quadratic_bound
          first.1 second.1 N positive
      _ = ((2 * (first.1 + 1) + 1) *
          (2 * (second.1 + 1) + 1)) * N ^ (3 - 1) := by norm_num

/-- TRUE full-lattice shared-target prime-power removal at EVERY fixed
combined rank.  BOTH labels, BOTH signed centers, their exact physical
target equality, and the single counted distinguished shared target are all
retained.  The unrestricted lattice proper-prime-power error is `o(N³)`. -/
theorem adaptiveMixedSignedSharedTargetPrimePowerExceptions_normalized_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex multiplier : ℕ)
    (multiplier_positive : 0 < multiplier)
    (primes : ∀ prime ∈ support, prime.Prime)
    (points : ℕ → Finset ((ℕ × ℤ) × (ℕ × ℤ)))
    (boxed : ∀ N : ℕ,
      points N ⊆
        ((Finset.Ioc N (2 * N)).product
          (adaptiveMixedSignedSearchCenterWindow first.1 N)).product
        ((Finset.Ioc N (2 * N)).product
          (adaptiveMixedSignedSearchCenterWindow second.1 N)))
    (shared : ∀ N : ℕ, ∀ point ∈ points N,
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support first.1 firstIndex point.1.1 point.1.2 =
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support second.1 secondIndex point.2.1 point.2.2)
    (bounded : ∀ N : ℕ, ∀ point ∈ points N,
      ∀ index ∈ adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex,
          adaptiveMixedSharedTargetSignedPrimeFormValue
            support first.1 second.1 index point ∈
              Finset.Ioc 0 (multiplier * N)) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
          (points N) (adaptiveMixedSharedTargetFormIndices
            support scale first second secondIndex)
          (adaptiveMixedSharedTargetSignedPrimeFormValue
            support first.1 second.1),
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedSharedTargetFormIndices
                support scale first second secondIndex)
              (adaptiveMixedSharedTargetSignedPrimeFormValue
                support first.1 second.1) point) / (N : ℝ) ^ 3)
      atTop (nhds 0) := by
  apply adaptiveMixedVonMangoldtPrimePowerExceptions_scaled_normalized_tendsto_zero
    (adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex) points
      (fun index _N point =>
        adaptiveMixedSharedTargetSignedPrimeFormValue
          support first.1 second.1 index point)
        3 ((2 * (first.1 + 1) + 1) * (2 * (second.1 + 1) + 1))
          multiplier (by norm_num) multiplier_positive bounded
  intro N index selected power selected_power
  by_cases zero : N = 0
  · subst N
    have empty : points 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro point in_points
      have impossible := boxed 0 in_points
      simp at impossible
    simp [empty]
  · have positive : 0 < N := Nat.pos_of_ne_zero zero
    have power_positive :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp selected_power).1).1
    calc
      ((points N).filter fun point =>
        adaptiveMixedSharedTargetSignedPrimeFormValue
          support first.1 second.1 index point = power).card ≤
        (2 * (first.1 + 1) * N + 1) *
          (2 * (second.1 + 1) * N + 1) :=
        adaptiveMixedSignedSharedTargetActualFormFiber_card_le_windows
          support scale first second firstIndex secondIndex N
            (points N) (boxed N) (shared N) primes
              index selected power power_positive
      _ ≤ ((2 * (first.1 + 1) + 1) *
          (2 * (second.1 + 1) + 1)) * N ^ 2 :=
        adaptiveMixedSignedPairedSearchWindows_quadratic_bound
          first.1 second.1 N positive
      _ = ((2 * (first.1 + 1) + 1) *
          (2 * (second.1 + 1) + 1)) * N ^ (3 - 1) := by norm_num

end Erdos1139

