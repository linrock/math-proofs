module

public import AdaptiveMixedSharedTargetPrimePowerFibers1139
public import AdaptiveMixedActualLogWeightBounds1139

@[expose] public section


/-!
# Log-weight normalization on the actual paired mixed-prime systems

The genuine shared-label and shared-target correlations retain their actual
signed physical coordinates, their true affine prime forms, and exactly the
deduplicated prime-form index sets.  Every form has fixed positive linear
bounds, so the published von-Mangoldt-weighted prime-only asymptotics are
equivalent to the exact unweighted realization asymptotics at every fixed
mixed rank.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1139

/-- Every genuine shared-label realization projects to BOTH true signed
original prime realizations; no restriction on the independent centers is
discarded. -/
theorem adaptiveMixedSignedSharedLabelPrimeRealizations_original_branches
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    {point : ℕ × ℤ × ℤ}
    (selected : point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
      support scale first second domain N) :
    (point.1, point.2.1) ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale first Set.univ N ∧
    (point.1, point.2.2) ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale second Set.univ N := by
  classical
  simp only [adaptiveMixedSignedSharedLabelPrimeRealizations,
    Finset.mem_filter] at selected
  obtain ⟨boxed, first_edge, second_edge, _physical⟩ := selected
  have label := (Finset.mem_product.mp boxed).1
  have centers := Finset.mem_product.mp (Finset.mem_product.mp boxed).2
  constructor
  · simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter, Set.mem_univ, and_true]
    exact ⟨Finset.mem_product.mpr ⟨label, centers.1⟩, first_edge⟩
  · simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter, Set.mem_univ, and_true]
    exact ⟨Finset.mem_product.mpr ⟨label, centers.2⟩, second_edge⟩

/-- EVERY actual shared-label prime form, including the one common prime
label and both full signed target branches, has the same genuine fixed
positive linear bounds as an original mixed system. -/
theorem adaptiveMixedSignedSharedLabelActualPrimeForm_linear_bounds
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    {point : ℕ × ℤ × ℤ}
    (selected : point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
      support scale first second domain N)
    {index : Option ℕ ⊕ ℕ}
    (active : index ∈ adaptiveMixedSharedLabelFormIndices
      support scale first second) :
    ((adaptiveMixedTypeModulus support : ℝ)⁻¹) * (N : ℝ) ≤
        (adaptiveMixedSharedLabelSignedPrimeFormValue
          support first.1 second.1 index point : ℝ) ∧
      (adaptiveMixedSharedLabelSignedPrimeFormValue
        support first.1 second.1 index point : ℝ) ≤
          ((2 * (scale + 1) : ℕ) : ℝ) * (N : ℝ) := by
  obtain ⟨first_selected, second_selected⟩ :=
    adaptiveMixedSignedSharedLabelPrimeRealizations_original_branches
      support scale first second domain N selected
  cases index with
  | inl branch =>
      have branch_active :=
        (adaptiveMixedSharedLabelFormIndices_inl_mem_iff
          support scale first second branch).mp active
      have bound := adaptiveMixedSignedOriginalActualPrimeForm_linear_bounds
        support scale first Set.univ N primes first_selected branch_active
      cases branch <;> exact bound
  | inr physical =>
      have branch_active :=
        (adaptiveMixedSharedLabelFormIndices_inr_mem_iff
          support scale first second physical).mp active
      have actual_active :=
        (adaptiveMixedActualFormIndices_target_mem_iff
          support scale physical second).mpr branch_active
      exact adaptiveMixedSignedOriginalActualPrimeForm_linear_bounds
        support scale second Set.univ N primes second_selected actual_active

/-- Every form in the true deduplicated shared-label system is prime on the
actual signed prime-realization family. -/
theorem adaptiveMixedSignedSharedLabelActualPrimeForm_prime
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    {point : ℕ × ℤ × ℤ}
    (selected : point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
      support scale first second domain N)
    {index : Option ℕ ⊕ ℕ}
    (active : index ∈ adaptiveMixedSharedLabelFormIndices
      support scale first second) :
    (adaptiveMixedSharedLabelSignedPrimeFormValue
      support first.1 second.1 index point).Prime := by
  obtain ⟨first_selected, second_selected⟩ :=
    adaptiveMixedSignedSharedLabelPrimeRealizations_original_branches
      support scale first second domain N selected
  cases index with
  | inl branch =>
      have branch_active :=
        (adaptiveMixedSharedLabelFormIndices_inl_mem_iff
          support scale first second branch).mp active
      have prime := adaptiveMixedSignedOriginalActualPrimeForm_prime
        support scale first Set.univ N first_selected branch_active
      cases branch <;> exact prime
  | inr physical =>
      have branch_active :=
        (adaptiveMixedSharedLabelFormIndices_inr_mem_iff
          support scale first second physical).mp active
      have actual_active :=
        (adaptiveMixedActualFormIndices_target_mem_iff
          support scale physical second).mpr branch_active
      exact adaptiveMixedSignedOriginalActualPrimeForm_prime
        support scale second Set.univ N second_selected actual_active

/-- The exact arbitrary-rank shared-label von Mangoldt product is the product
of the logarithms of its true affine prime values. -/
theorem adaptiveMixedSignedSharedLabelActualVonMangoldtProduct_eq_logs
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    {point : ℕ × ℤ × ℤ}
    (selected : point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
      support scale first second domain N) :
    adaptiveMixedVonMangoldtProduct
        (adaptiveMixedSharedLabelFormIndices support scale first second)
        (adaptiveMixedSharedLabelSignedPrimeFormValue
          support first.1 second.1) point =
      ∏ index ∈ adaptiveMixedSharedLabelFormIndices
        support scale first second,
          Real.log (adaptiveMixedSharedLabelSignedPrimeFormValue
            support first.1 second.1 index point : ℝ) := by
  unfold adaptiveMixedVonMangoldtProduct
  apply Finset.prod_congr rfl
  intro index active
  exact ArithmeticFunction.vonMangoldt_apply_prime
    (adaptiveMixedSignedSharedLabelActualPrimeForm_prime
      support scale first second domain N selected active)

/-- Source-faithful exact SHARED-LABEL weighted/unweighted equivalence at
every fixed genuine combined rank.  The common prime label is counted once,
and BOTH signed target branches are counted in full. -/
theorem adaptiveMixedSignedSharedLabelActualLogWeighted_asymptotic_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
          support scale first second domain N,
          ∏ index ∈ adaptiveMixedSharedLabelFormIndices
            support scale first second,
            Real.log (adaptiveMixedSharedLabelSignedPrimeFormValue
              support first.1 second.1 index point : ℝ)) / (N : ℝ) ^ 3)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedLabelPrimeRealizations
          support scale first second domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices support scale first).card +
              (adaptiveMixedOutcomeActiveIndices support scale second).card +
                1) / (N : ℝ) ^ 3)
      atTop (nhds limit) := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have lower_positive :
      0 < (adaptiveMixedTypeModulus support : ℝ)⁻¹ :=
    inv_pos.mpr modulus_positive
  have upper_positive : (0 : ℝ) < ((2 * (scale + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by positivity : 0 < 2 * (scale + 1))
  have bounds : ∀ᶠ N : ℕ in atTop,
      ∀ point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
          support scale first second domain N,
        ∀ index ∈ adaptiveMixedSharedLabelFormIndices
          support scale first second,
          ((adaptiveMixedTypeModulus support : ℝ)⁻¹) * (N : ℝ) ≤
              (adaptiveMixedSharedLabelSignedPrimeFormValue
                support first.1 second.1 index point : ℝ) ∧
            (adaptiveMixedSharedLabelSignedPrimeFormValue
              support first.1 second.1 index point : ℝ) ≤
                ((2 * (scale + 1) : ℕ) : ℝ) * (N : ℝ) := by
    exact Eventually.of_forall fun N point selected index active =>
      adaptiveMixedSignedSharedLabelActualPrimeForm_linear_bounds
        support scale first second domain N primes selected active
  have transfer := adaptiveMixedFixedLinearLogWeighted_asymptotic_iff
    (adaptiveMixedSharedLabelFormIndices support scale first second)
    (fun N => adaptiveMixedSignedSharedLabelPrimeRealizations
      support scale first second domain N)
    (adaptiveMixedSharedLabelSignedPrimeFormValue support first.1 second.1)
    ((adaptiveMixedTypeModulus support : ℝ)⁻¹)
    ((2 * (scale + 1) : ℕ) : ℝ) 3 limit
    lower_positive upper_positive bounds
  simpa [adaptiveMixedSharedLabelFormIndices_card] using transfer

/-- The literal published von-Mangoldt-weighted SHARED-LABEL prime-only sum
is EQUIVALENT to its exact required source-faithful unweighted fixed-system
count at EVERY combined rank. -/
theorem adaptiveMixedSignedSharedLabelActualVonMangoldt_asymptotic_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
          support scale first second domain N,
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedSharedLabelFormIndices support scale first second)
              (adaptiveMixedSharedLabelSignedPrimeFormValue
                support first.1 second.1) point) / (N : ℝ) ^ 3)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedLabelPrimeRealizations
          support scale first second domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices support scale first).card +
              (adaptiveMixedOutcomeActiveIndices support scale second).card +
                1) / (N : ℝ) ^ 3)
      atTop (nhds limit) := by
  have weighted_same :
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
          support scale first second domain N,
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedSharedLabelFormIndices support scale first second)
              (adaptiveMixedSharedLabelSignedPrimeFormValue
                support first.1 second.1) point) / (N : ℝ) ^ 3) =
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
          support scale first second domain N,
          ∏ index ∈ adaptiveMixedSharedLabelFormIndices
            support scale first second,
            Real.log (adaptiveMixedSharedLabelSignedPrimeFormValue
              support first.1 second.1 index point : ℝ)) / (N : ℝ) ^ 3) := by
    funext N
    congr 1
    apply Finset.sum_congr rfl
    intro point selected
    exact adaptiveMixedSignedSharedLabelActualVonMangoldtProduct_eq_logs
      support scale first second domain N selected
  rw [weighted_same]
  exact adaptiveMixedSignedSharedLabelActualLogWeighted_asymptotic_iff
    support scale first second domain limit primes

/-- Every genuine unrestricted shared-target realization projects to BOTH
true signed original prime realizations.  The full target-equality lattice,
including globally equal prime labels, is retained. -/
theorem adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations_original_branches
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    {point : (ℕ × ℤ) × (ℕ × ℤ)}
    (selected : point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N) :
    point.1 ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale first Set.univ N ∧
    point.2 ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale second Set.univ N := by
  classical
  obtain ⟨first_boxed, second_boxed, first_edge, second_edge,
    _shared, _physical⟩ :=
      (mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
        support scale first second firstIndex secondIndex domain N point).mp selected
  constructor
  · simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter, Set.mem_univ, and_true]
    exact ⟨first_boxed, first_edge⟩
  · simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter, Set.mem_univ, and_true]
    exact ⟨second_boxed, second_edge⟩

/-- EVERY deduplicated shared-target prime form has genuine positive linear
bounds on the FULL signed target-equality lattice.  BOTH prime labels remain
present; only the distinguished duplicated target is removed. -/
theorem adaptiveMixedSignedSharedTargetUnrestrictedActualPrimeForm_linear_bounds
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    {point : (ℕ × ℤ) × (ℕ × ℤ)}
    (selected : point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N)
    {index : Option ℕ ⊕ Option ℕ}
    (active : index ∈ adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex) :
    ((adaptiveMixedTypeModulus support : ℝ)⁻¹) * (N : ℝ) ≤
        (adaptiveMixedSharedTargetSignedPrimeFormValue
          support first.1 second.1 index point : ℝ) ∧
      (adaptiveMixedSharedTargetSignedPrimeFormValue
        support first.1 second.1 index point : ℝ) ≤
          ((2 * (scale + 1) : ℕ) : ℝ) * (N : ℝ) := by
  obtain ⟨first_selected, second_selected⟩ :=
    adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations_original_branches
      support scale first second firstIndex secondIndex domain N selected
  cases index with
  | inl branch =>
      have branch_active :=
        (adaptiveMixedSharedTargetFormIndices_inl_mem_iff
          support scale first second secondIndex branch).mp active
      exact adaptiveMixedSignedOriginalActualPrimeForm_linear_bounds
        support scale first Set.univ N primes first_selected branch_active
  | inr branch =>
      have branch_active :=
        (adaptiveMixedSharedTargetFormIndices_inr_mem_iff
          support scale first second secondIndex branch).mp active
      exact adaptiveMixedSignedOriginalActualPrimeForm_linear_bounds
        support scale second Set.univ N primes second_selected branch_active.2

/-- Every indexed genuine shared-target affine form is prime on the actual
FULL target-equality prime-realization lattice. -/
theorem adaptiveMixedSignedSharedTargetUnrestrictedActualPrimeForm_prime
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    {point : (ℕ × ℤ) × (ℕ × ℤ)}
    (selected : point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N)
    {index : Option ℕ ⊕ Option ℕ}
    (active : index ∈ adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex) :
    (adaptiveMixedSharedTargetSignedPrimeFormValue
      support first.1 second.1 index point).Prime := by
  obtain ⟨first_selected, second_selected⟩ :=
    adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations_original_branches
      support scale first second firstIndex secondIndex domain N selected
  cases index with
  | inl branch =>
      have branch_active :=
        (adaptiveMixedSharedTargetFormIndices_inl_mem_iff
          support scale first second secondIndex branch).mp active
      exact adaptiveMixedSignedOriginalActualPrimeForm_prime
        support scale first Set.univ N first_selected branch_active
  | inr branch =>
      have branch_active :=
        (adaptiveMixedSharedTargetFormIndices_inr_mem_iff
          support scale first second secondIndex branch).mp active
      exact adaptiveMixedSignedOriginalActualPrimeForm_prime
        support scale second Set.univ N second_selected branch_active.2

/-- On the FULL genuine shared-target lattice, the deduplicated von Mangoldt
product equals the true product of all affine-prime logarithms. -/
theorem adaptiveMixedSignedSharedTargetUnrestrictedActualVonMangoldtProduct_eq_logs
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    {point : (ℕ × ℤ) × (ℕ × ℤ)}
    (selected : point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N) :
    adaptiveMixedVonMangoldtProduct
        (adaptiveMixedSharedTargetFormIndices
          support scale first second secondIndex)
        (adaptiveMixedSharedTargetSignedPrimeFormValue
          support first.1 second.1) point =
      ∏ index ∈ adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex,
          Real.log (adaptiveMixedSharedTargetSignedPrimeFormValue
            support first.1 second.1 index point : ℝ) := by
  unfold adaptiveMixedVonMangoldtProduct
  apply Finset.prod_congr rfl
  intro index active
  exact ArithmeticFunction.vonMangoldt_apply_prime
    (adaptiveMixedSignedSharedTargetUnrestrictedActualPrimeForm_prime
      support scale first second firstIndex secondIndex domain N selected active)

/-- Source-faithful exact FULL-LATTICE SHARED-TARGET logarithmic weighted /
unweighted equivalence at every fixed rank.  The actual globally equal-label
diagonal is allowed, as required by the published fixed-system theorem. -/
theorem adaptiveMixedSignedSharedTargetUnrestrictedActualLogWeighted_asymptotic_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N,
          ∏ index ∈ adaptiveMixedSharedTargetFormIndices
            support scale first second secondIndex,
            Real.log (adaptiveMixedSharedTargetSignedPrimeFormValue
              support first.1 second.1 index point : ℝ)) / (N : ℝ) ^ 3)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices support scale first).card +
              (adaptiveMixedOutcomeActiveIndices support scale second).card +
                1) / (N : ℝ) ^ 3)
      atTop (nhds limit) := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have lower_positive :
      0 < (adaptiveMixedTypeModulus support : ℝ)⁻¹ :=
    inv_pos.mpr modulus_positive
  have upper_positive : (0 : ℝ) < ((2 * (scale + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by positivity : 0 < 2 * (scale + 1))
  have bounds : ∀ᶠ N : ℕ in atTop,
      ∀ point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N,
        ∀ index ∈ adaptiveMixedSharedTargetFormIndices
          support scale first second secondIndex,
          ((adaptiveMixedTypeModulus support : ℝ)⁻¹) * (N : ℝ) ≤
              (adaptiveMixedSharedTargetSignedPrimeFormValue
                support first.1 second.1 index point : ℝ) ∧
            (adaptiveMixedSharedTargetSignedPrimeFormValue
              support first.1 second.1 index point : ℝ) ≤
                ((2 * (scale + 1) : ℕ) : ℝ) * (N : ℝ) := by
    exact Eventually.of_forall fun N point selected index active =>
      adaptiveMixedSignedSharedTargetUnrestrictedActualPrimeForm_linear_bounds
        support scale first second firstIndex secondIndex domain N
          primes selected active
  have transfer := adaptiveMixedFixedLinearLogWeighted_asymptotic_iff
    (adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex)
    (fun N => adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N)
    (adaptiveMixedSharedTargetSignedPrimeFormValue support first.1 second.1)
    ((adaptiveMixedTypeModulus support : ℝ)⁻¹)
    ((2 * (scale + 1) : ℕ) : ℝ) 3 limit
    lower_positive upper_positive bounds
  rw [adaptiveMixedSharedTargetFormIndices_card second_active] at transfer
  exact transfer

/-- The literal published von-Mangoldt-weighted FULL-LATTICE SHARED-TARGET
prime-only sum is EQUIVALENT to its exact required source-faithful
unweighted fixed-system prime count, at EVERY combined fixed rank. -/
theorem adaptiveMixedSignedSharedTargetUnrestrictedActualVonMangoldt_asymptotic_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N,
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedSharedTargetFormIndices
                support scale first second secondIndex)
              (adaptiveMixedSharedTargetSignedPrimeFormValue
                support first.1 second.1) point) / (N : ℝ) ^ 3)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices support scale first).card +
              (adaptiveMixedOutcomeActiveIndices support scale second).card +
                1) / (N : ℝ) ^ 3)
      atTop (nhds limit) := by
  have weighted_same :
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N,
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedSharedTargetFormIndices
                support scale first second secondIndex)
              (adaptiveMixedSharedTargetSignedPrimeFormValue
                support first.1 second.1) point) / (N : ℝ) ^ 3) =
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N,
          ∏ index ∈ adaptiveMixedSharedTargetFormIndices
            support scale first second secondIndex,
            Real.log (adaptiveMixedSharedTargetSignedPrimeFormValue
              support first.1 second.1 index point : ℝ)) / (N : ℝ) ^ 3) := by
    funext N
    congr 1
    apply Finset.sum_congr rfl
    intro point selected
    exact adaptiveMixedSignedSharedTargetUnrestrictedActualVonMangoldtProduct_eq_logs
      support scale first second firstIndex secondIndex domain N selected
  rw [weighted_same]
  exact adaptiveMixedSignedSharedTargetUnrestrictedActualLogWeighted_asymptotic_iff
    support scale first second firstIndex secondIndex domain limit
      primes second_active

end Erdos1139

