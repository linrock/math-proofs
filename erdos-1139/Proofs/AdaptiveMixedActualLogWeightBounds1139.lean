module

public import AdaptiveMixedAffinePrimePowerFibers1139
public import AdaptiveMixedLogWeightNormalization1139
public import ScaleAdaptiveGlobalMomentConstruction1139

@[expose] public section


/-!
# Actual signed mixed-prime affine forms have uniformly linear log weights

Every genuine original-family prime form, including its indispensable prime
label and every retained prime/semiprime quotient, lies between fixed
positive multiples of the dyadic scale.  The bounds use the TRUE signed
fundamental residue and positive gcd type; no positive-center substitute or
extra prime-pattern hypothesis is introduced.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1139

/-- On a genuine signed prime edge, each active physical target quotient `q`
satisfies the exact uniform inequalities `label ≤ W*q` and
`q < (scale+1)*label`.  The fixed square-core modulus `W` is retained. -/
theorem adaptiveMixedSignedActualTargetPrimeForm_natural_bounds
    {support : Finset ℕ} {scale index label : ℕ}
    {outcome : ℕ × ℕ} {centers : Finset ℤ} {center : ℤ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (edge : center ∈ weightedPrimePatternEdges
      support scale outcome centers label)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome) :
    label ≤ adaptiveMixedTypeModulus support *
      (weightedPrimePatternIntegerForm
        support outcome.1 index label center).toNat ∧
    (weightedPrimePatternIntegerForm
      support outcome.1 index label center).toNat <
        (scale + 1) * label := by
  obtain ⟨_label_prime, _in_centers, residue_nonnegative,
    residue_upper, certificates⟩ :=
    weightedPrimePatternEdges_prime_certificate
      support scale outcome centers label center edge
  obtain ⟨index_bounds, form_positive, _prime⟩ := certificates index active
  have index_range : 1 ≤ index ∧ index ≤ scale :=
    Finset.mem_Icc.mp index_bounds
  let form := weightedPrimePatternIntegerForm
    support outcome.1 index label center
  let target := form.toNat
  let target_type := adaptiveMixedActualIndexType support outcome.1 index
  have target_int : (target : ℤ) = form := by
    dsimp [target]
    exact Int.toNat_of_nonneg form_positive.le
  have physical :
      (target_type : ℤ) * (target : ℤ) =
        weightedPrimePatternSignedResidue
          support outcome.1 label center +
          (index : ℤ) * (label : ℤ) := by
    rw [target_int]
    exact scaleAdaptiveSignedPhysicalTarget_eq_residue_add_index
      center primes active
  have type_positive : 0 < target_type :=
    adaptiveMixedActualIndexType_pos_of_active primes active
  have type_le_modulus : target_type ≤ adaptiveMixedTypeModulus support :=
    Nat.le_of_dvd (adaptiveMixedTypeModulus_pos support primes)
      (adaptiveMixedOutcomeActiveIndex_type_dvd_modulus primes active)
  have index_label_lower : label ≤ index * label := by
    have bound := Nat.mul_le_mul_right label index_range.1
    simpa using bound
  have type_target_lower : label ≤ target_type * target := by
    have lower_integer : (label : ℤ) ≤ (target_type : ℤ) * (target : ℤ) := by
      have index_integer :
          (label : ℤ) ≤ (index : ℤ) * (label : ℤ) := by
        exact_mod_cast index_label_lower
      omega
    exact_mod_cast lower_integer
  have type_target_upper : target_type * target < (index + 1) * label := by
    have upper_integer :
        (target_type : ℤ) * (target : ℤ) <
          ((index + 1) * label : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast upper_integer
  constructor
  · exact type_target_lower.trans
      (Nat.mul_le_mul_right target type_le_modulus)
  · have target_le_type_target : target ≤ target_type * target := by
      have bound := Nat.mul_le_mul_right target type_positive
      simpa using bound
    exact (target_le_type_target.trans_lt type_target_upper).trans_le
      (Nat.mul_le_mul_right label (by omega : index + 1 ≤ scale + 1))

/-- EVERY actual original-system prime form, including the genuine prime
label, has fixed positive linear bounds on the TRUE signed realization set.
The lower coefficient is the inverse genuine squared support modulus. -/
theorem adaptiveMixedSignedOriginalActualPrimeForm_linear_bounds
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    {point : ℕ × ℤ}
    (selected : point ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N)
    {index : Option ℕ}
    (active : index ∈ adaptiveMixedActualFormIndices
      support scale outcome) :
    ((adaptiveMixedTypeModulus support : ℝ)⁻¹) * (N : ℝ) ≤
        (adaptiveMixedActualSignedPrimeFormValue
          support outcome.1 index point : ℝ) ∧
      (adaptiveMixedActualSignedPrimeFormValue
        support outcome.1 index point : ℝ) ≤
          ((2 * (scale + 1) : ℕ) : ℝ) * (N : ℝ) := by
  classical
  obtain ⟨boxed, edge, _in_domain⟩ := Finset.mem_filter.mp selected
  have label_window := (Finset.mem_product.mp boxed).1
  obtain ⟨label_lower, label_upper⟩ := Finset.mem_Ioc.mp label_window
  have modulus_positive := adaptiveMixedTypeModulus_pos support primes
  have modulus_real_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast modulus_positive
  have lower_nat :
      N ≤ adaptiveMixedTypeModulus support *
        adaptiveMixedActualSignedPrimeFormValue
          support outcome.1 index point := by
    cases index with
    | none =>
        change N ≤ adaptiveMixedTypeModulus support * point.1
        exact (Nat.le_of_lt label_lower).trans
          (by
            have bound := Nat.mul_le_mul_right point.1 modulus_positive
            simpa using bound)
    | some physical =>
        have physical_active :=
          (adaptiveMixedActualFormIndices_target_mem_iff
            support scale physical outcome).mp active
        have actual :=
          adaptiveMixedSignedActualTargetPrimeForm_natural_bounds
            primes edge physical_active
        exact (Nat.le_of_lt label_lower).trans actual.1
  have upper_nat :
      adaptiveMixedActualSignedPrimeFormValue
          support outcome.1 index point ≤
        (2 * (scale + 1)) * N := by
    cases index with
    | none =>
        change point.1 ≤ (2 * (scale + 1)) * N
        calc
          point.1 ≤ 2 * N := label_upper
          _ ≤ (2 * (scale + 1)) * N := by
            apply Nat.mul_le_mul_right N
            omega
    | some physical =>
        have physical_active :=
          (adaptiveMixedActualFormIndices_target_mem_iff
            support scale physical outcome).mp active
        have actual :=
          adaptiveMixedSignedActualTargetPrimeForm_natural_bounds
            primes edge physical_active
        change
          (weightedPrimePatternIntegerForm
            support outcome.1 physical point.1 point.2).toNat ≤
              (2 * (scale + 1)) * N
        calc
          _ ≤ (scale + 1) * point.1 := actual.2.le
          _ ≤ (scale + 1) * (2 * N) :=
            Nat.mul_le_mul_left (scale + 1) label_upper
          _ = (2 * (scale + 1)) * N := by ring
  constructor
  · have real_lower :
        (N : ℝ) ≤
          (adaptiveMixedTypeModulus support : ℝ) *
            (adaptiveMixedActualSignedPrimeFormValue
              support outcome.1 index point : ℝ) := by
      exact_mod_cast lower_nat
    calc
      ((adaptiveMixedTypeModulus support : ℝ)⁻¹) * (N : ℝ) =
          (N : ℝ) / (adaptiveMixedTypeModulus support : ℝ) := by
            rw [div_eq_mul_inv, mul_comm]
      _ ≤ (adaptiveMixedActualSignedPrimeFormValue
          support outcome.1 index point : ℝ) := by
        apply (div_le_iff₀ modulus_real_positive).mpr
        simpa [mul_comm] using real_lower
  · exact_mod_cast upper_nat

/-- EVERY indexed actual form at a genuine signed original realization is
prime, including the indispensable label and all true mixed target quotients. -/
theorem adaptiveMixedSignedOriginalActualPrimeForm_prime
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ)
    {point : ℕ × ℤ}
    (selected : point ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N)
    {index : Option ℕ}
    (active : index ∈ adaptiveMixedActualFormIndices
      support scale outcome) :
    (adaptiveMixedActualSignedPrimeFormValue
      support outcome.1 index point).Prime := by
  classical
  obtain ⟨_boxed, edge, _in_domain⟩ := Finset.mem_filter.mp selected
  obtain ⟨label_prime, _in_centers, _residue_nonnegative,
    _residue_upper, certificates⟩ :=
      weightedPrimePatternEdges_prime_certificate
        support scale outcome
          (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
          point.1 point.2 edge
  cases index with
  | none => exact label_prime
  | some physical =>
      have physical_active :=
        (adaptiveMixedActualFormIndices_target_mem_iff
          support scale physical outcome).mp active
      exact (certificates physical physical_active).2.2

/-- On the actual prime realization family, the full arbitrary-rank von
Mangoldt product equals the product of the TRUE affine-prime logarithms. -/
theorem adaptiveMixedSignedOriginalActualVonMangoldtProduct_eq_logs
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ)
    {point : ℕ × ℤ}
    (selected : point ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N) :
    adaptiveMixedVonMangoldtProduct
        (adaptiveMixedActualFormIndices support scale outcome)
        (adaptiveMixedActualSignedPrimeFormValue support outcome.1) point =
      ∏ index ∈ adaptiveMixedActualFormIndices support scale outcome,
        Real.log
          (adaptiveMixedActualSignedPrimeFormValue
            support outcome.1 index point : ℝ) := by
  unfold adaptiveMixedVonMangoldtProduct
  apply Finset.prod_congr rfl
  intro index active
  exact ArithmeticFunction.vonMangoldt_apply_prime
    (adaptiveMixedSignedOriginalActualPrimeForm_prime
      support scale outcome domain N selected active)

/-- Source-faithful exact ORIGINAL-SYSTEM weighted/unweighted equivalence
at every fixed genuine mixed rank.  The point family is the ACTUAL signed
physical prime-realization set and the logarithmic exponent includes its
indispensable prime label. -/
theorem adaptiveMixedSignedOriginalActualLogWeighted_asymptotic_iff
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N,
          ∏ index ∈ adaptiveMixedActualFormIndices support scale outcome,
            Real.log (adaptiveMixedActualSignedPrimeFormValue
              support outcome.1 index point : ℝ)) / (N : ℝ) ^ 2)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices
              support scale outcome).card + 1) /
          (N : ℝ) ^ 2)
      atTop (nhds limit) := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have lower_positive :
      0 < (adaptiveMixedTypeModulus support : ℝ)⁻¹ :=
    inv_pos.mpr modulus_positive
  have upper_positive : (0 : ℝ) < ((2 * (scale + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by positivity : 0 < 2 * (scale + 1))
  have bounds : ∀ᶠ N : ℕ in atTop,
      ∀ point ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N,
        ∀ index ∈ adaptiveMixedActualFormIndices support scale outcome,
          ((adaptiveMixedTypeModulus support : ℝ)⁻¹) * (N : ℝ) ≤
              (adaptiveMixedActualSignedPrimeFormValue
                support outcome.1 index point : ℝ) ∧
            (adaptiveMixedActualSignedPrimeFormValue
              support outcome.1 index point : ℝ) ≤
                ((2 * (scale + 1) : ℕ) : ℝ) * (N : ℝ) := by
    exact Eventually.of_forall fun N point selected index active =>
      adaptiveMixedSignedOriginalActualPrimeForm_linear_bounds
        support scale outcome domain N primes selected active
  have transfer := adaptiveMixedFixedLinearLogWeighted_asymptotic_iff
    (adaptiveMixedActualFormIndices support scale outcome)
    (fun N => adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N)
    (adaptiveMixedActualSignedPrimeFormValue support outcome.1)
    ((adaptiveMixedTypeModulus support : ℝ)⁻¹)
    ((2 * (scale + 1) : ℕ) : ℝ) 2 limit
    lower_positive upper_positive bounds
  simpa [adaptiveMixedActualFormIndices_card] using transfer

/-- The literal published von-Mangoldt-weighted ORIGINAL prime-only sum
is EQUIVALENT to the exact required source-faithful unweighted fixed-system
prime count, with every actual signed form and the correct rank retained. -/
theorem adaptiveMixedSignedOriginalActualVonMangoldt_asymptotic_iff
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N,
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedActualFormIndices support scale outcome)
              (adaptiveMixedActualSignedPrimeFormValue
                support outcome.1) point) / (N : ℝ) ^ 2)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices
              support scale outcome).card + 1) /
          (N : ℝ) ^ 2)
      atTop (nhds limit) := by
  have weighted_same :
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N,
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedActualFormIndices support scale outcome)
              (adaptiveMixedActualSignedPrimeFormValue
                support outcome.1) point) / (N : ℝ) ^ 2) =
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N,
          ∏ index ∈ adaptiveMixedActualFormIndices support scale outcome,
            Real.log (adaptiveMixedActualSignedPrimeFormValue
              support outcome.1 index point : ℝ)) / (N : ℝ) ^ 2) := by
    funext N
    congr 1
    apply Finset.sum_congr rfl
    intro point selected
    exact adaptiveMixedSignedOriginalActualVonMangoldtProduct_eq_logs
      support scale outcome domain N selected
  rw [weighted_same]
  exact adaptiveMixedSignedOriginalActualLogWeighted_asymptotic_iff
    support scale outcome domain limit primes


end Erdos1139
