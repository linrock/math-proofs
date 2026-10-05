module

public import ScaleAdaptiveConstantBandTargetMoments1139
public import ScaleAdaptivePrimeSliceVariance1139

@[expose] public section


/-!
# Genuine target-truncated first prime moment on a constant-residue band

For a genuine signed-center pattern `(p,C)` with `r=b*p+W*C`, retain

    1 < p < 2,  u < r < v,  L < i*p+r < U.

If `i+v ≤ L < U ≤ 2*i+u`, neither endpoint clips the actual prime-label
fiber.  The true `(p,C)` area is exactly

    (U-L) * (v-u) / (i*W).

The factor `1/W` is the REAL signed-center Jacobian: it is obtained using
translation invariance and one-dimensional scaling of Lebesgue measure,
not assumed from a rectangular artificial center box.  The resulting
actual prime-pattern first moment comes directly from the explicit signed
Green--Tao input.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos1139

/-- The genuine signed-center constant band further restricted to an ACTUAL
moving physical target window. -/
def scaleAdaptiveTruncatedBandSignedDomain
    (support : Finset ℕ) (base index : ℕ)
    (lower upper targetLower targetUpper : ℝ) : Set (ℝ × ℝ) :=
  {point |
    1 < point.1 ∧ point.1 < 2 ∧
      lower < (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 ∧
      (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 < upper ∧
      targetLower < (index : ℝ) * point.1 +
        ((base : ℝ) * point.1 +
          (adaptiveMixedTypeModulus support : ℝ) * point.2) ∧
      (index : ℝ) * point.1 +
        ((base : ℝ) * point.1 +
          (adaptiveMixedTypeModulus support : ℝ) * point.2) < targetUpper}

/-- The true label/residue-coordinate region before the signed-center
Jacobian is applied. -/
def scaleAdaptiveTruncatedBandResidueRegion
    (index : ℕ) (lower upper targetLower targetUpper : ℝ) : Set (ℝ × ℝ) :=
  {point |
    lower < point.2 ∧ point.2 < upper ∧
      targetLower < (index : ℝ) * point.1 + point.2 ∧
      (index : ℝ) * point.1 + point.2 < targetUpper}

/-- The target-truncated actual signed domain is OPEN. -/
theorem scaleAdaptiveTruncatedBandSignedDomain_isOpen
    (support : Finset ℕ) (base index : ℕ)
    (lower upper targetLower targetUpper : ℝ) :
    IsOpen (scaleAdaptiveTruncatedBandSignedDomain
      support base index lower upper targetLower targetUpper) := by
  let target : (ℝ × ℝ) → ℝ := fun point =>
    (index : ℝ) * point.1 +
      ((base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2)
  have continuous_target : Continuous target :=
    (continuous_const.mul continuous_fst).add
      ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd))
  have equal :
      scaleAdaptiveTruncatedBandSignedDomain
        support base index lower upper targetLower targetUpper =
        scaleAdaptiveSignedConstantResidueBand
          support base lower upper ∩
          target ⁻¹' Set.Ioo targetLower targetUpper := by
    ext point
    simp [scaleAdaptiveTruncatedBandSignedDomain,
      scaleAdaptiveSignedConstantResidueBand, target]
    tauto
  rw [equal]
  exact (scaleAdaptiveSignedConstantResidueBand_isOpen
    support base lower upper).inter
      (isOpen_Ioo.preimage continuous_target)

/-- The target-truncated actual signed domain is CONVEX: both the retained
residue and the physical target are genuine affine forms. -/
theorem scaleAdaptiveTruncatedBandSignedDomain_convex
    (support : Finset ℕ) (base index : ℕ)
    (lower upper targetLower targetUpper : ℝ) :
    Convex ℝ (scaleAdaptiveTruncatedBandSignedDomain
      support base index lower upper targetLower targetUpper) := by
  intro first first_selected second second_selected a b
    a_nonnegative b_nonnegative normalized
  have first_band :
      first ∈ scaleAdaptiveSignedConstantResidueBand
        support base lower upper :=
    ⟨first_selected.1, first_selected.2.1,
      first_selected.2.2.1, first_selected.2.2.2.1⟩
  have second_band :
      second ∈ scaleAdaptiveSignedConstantResidueBand
        support base lower upper :=
    ⟨second_selected.1, second_selected.2.1,
      second_selected.2.2.1, second_selected.2.2.2.1⟩
  have band := scaleAdaptiveSignedConstantResidueBand_convex
    support base lower upper first_band second_band
      a_nonnegative b_nonnegative normalized
  have targets := (convex_Ioo (𝕜 := ℝ) targetLower targetUpper)
    ⟨first_selected.2.2.2.2.1, first_selected.2.2.2.2.2⟩
    ⟨second_selected.2.2.2.2.1, second_selected.2.2.2.2.2⟩
    a_nonnegative b_nonnegative normalized
  change
    1 < a * first.1 + b * second.1 ∧
      a * first.1 + b * second.1 < 2 ∧
      lower < (base : ℝ) * (a * first.1 + b * second.1) +
        (adaptiveMixedTypeModulus support : ℝ) *
          (a * first.2 + b * second.2) ∧
      (base : ℝ) * (a * first.1 + b * second.1) +
        (adaptiveMixedTypeModulus support : ℝ) *
          (a * first.2 + b * second.2) < upper ∧
      targetLower < (index : ℝ) *
        (a * first.1 + b * second.1) +
        ((base : ℝ) * (a * first.1 + b * second.1) +
          (adaptiveMixedTypeModulus support : ℝ) *
            (a * first.2 + b * second.2)) ∧
      (index : ℝ) * (a * first.1 + b * second.1) +
        ((base : ℝ) * (a * first.1 + b * second.1) +
          (adaptiveMixedTypeModulus support : ℝ) *
            (a * first.2 + b * second.2)) < targetUpper
  refine ⟨band.1, band.2.1, band.2.2.1, band.2.2.2, ?_, ?_⟩
  · calc
      targetLower <
          a * ((index : ℝ) * first.1 +
            ((base : ℝ) * first.1 +
              (adaptiveMixedTypeModulus support : ℝ) * first.2)) +
          b * ((index : ℝ) * second.1 +
            ((base : ℝ) * second.1 +
              (adaptiveMixedTypeModulus support : ℝ) * second.2)) :=
        targets.1
      _ = _ := by ring
  · calc
      _ = a * ((index : ℝ) * first.1 +
            ((base : ℝ) * first.1 +
              (adaptiveMixedTypeModulus support : ℝ) * first.2)) +
          b * ((index : ℝ) * second.1 +
            ((base : ℝ) * second.1 +
              (adaptiveMixedTypeModulus support : ℝ) * second.2)) := by ring
      _ < targetUpper := targets.2

/-- The genuine `(p,r)` residue/target region is OPEN and thus measurable. -/
theorem scaleAdaptiveTruncatedBandResidueRegion_isOpen
    (index : ℕ) (lower upper targetLower targetUpper : ℝ) :
    IsOpen (scaleAdaptiveTruncatedBandResidueRegion
      index lower upper targetLower targetUpper) := by
  let target : (ℝ × ℝ) → ℝ := fun point =>
    (index : ℝ) * point.1 + point.2
  have continuous_target : Continuous target :=
    (continuous_const.mul continuous_fst).add continuous_snd
  have equal :
      scaleAdaptiveTruncatedBandResidueRegion
        index lower upper targetLower targetUpper =
        (fun point : ℝ × ℝ => point.2) ⁻¹' Set.Ioo lower upper ∩
          target ⁻¹' Set.Ioo targetLower targetUpper := by
    ext point
    simp [scaleAdaptiveTruncatedBandResidueRegion, target]
    tauto
  rw [equal]
  exact (isOpen_Ioo.preimage continuous_snd).inter
    (isOpen_Ioo.preimage continuous_target)

/-- EXACT two-dimensional label/residue volume before the `1/W`
signed-center Jacobian.  Fubini in the TRUE residue coordinate gives a
constant target-selected label width `(targetUpper-targetLower)/index`. -/
theorem scaleAdaptiveTruncatedBandResidueRegion_volume
    {index : ℕ} {lower upper targetLower targetUpper : ℝ}
    (index_positive : 0 < index)
    (band_ordered : lower ≤ upper)
    (target_ordered : targetLower ≤ targetUpper) :
    (volume (scaleAdaptiveTruncatedBandResidueRegion
      index lower upper targetLower targetUpper)).toReal =
        (upper - lower) *
          ((targetUpper - targetLower) / (index : ℝ)) := by
  classical
  have index_real : (0 : ℝ) < index := by
    exact_mod_cast index_positive
  have width_nonnegative :
      0 ≤ (targetUpper - targetLower) / (index : ℝ) :=
    div_nonneg (sub_nonneg.mpr target_ordered) index_real.le
  let region := scaleAdaptiveTruncatedBandResidueRegion
    index lower upper targetLower targetUpper
  have measurable : MeasurableSet region :=
    (scaleAdaptiveTruncatedBandResidueRegion_isOpen
      index lower upper targetLower targetUpper).measurableSet
  change (volume region).toReal = _
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.Measure.prod_apply_symm measurable]
  have fibers :
      (fun residue : ℝ =>
        (volume : Measure ℝ)
          ((fun label : ℝ => (label, residue)) ⁻¹' region)) =
        (Set.Ioo lower upper).indicator fun _ : ℝ =>
          ENNReal.ofReal
            ((targetUpper - targetLower) / (index : ℝ)) := by
    funext residue
    by_cases selected : residue ∈ Set.Ioo lower upper
    · rw [Set.indicator_of_mem selected]
      have equal :
          ((fun label : ℝ => (label, residue)) ⁻¹' region) =
            Set.Ioo
              ((targetLower - residue) / (index : ℝ))
              ((targetUpper - residue) / (index : ℝ)) := by
        ext label
        change
          (lower < residue ∧ residue < upper ∧
            targetLower < (index : ℝ) * label + residue ∧
            (index : ℝ) * label + residue < targetUpper) ↔
              ((targetLower - residue) / (index : ℝ) < label ∧
                label < (targetUpper - residue) / (index : ℝ))
        constructor
        · rintro ⟨_, _, left, right⟩
          constructor
          · apply (div_lt_iff₀ index_real).mpr
            linarith
          · apply (lt_div_iff₀ index_real).mpr
            linarith
        · rintro ⟨left, right⟩
          have left' := (div_lt_iff₀ index_real).mp left
          have right' := (lt_div_iff₀ index_real).mp right
          exact ⟨selected.1, selected.2, by linarith, by linarith⟩
      rw [equal, Real.volume_Ioo]
      congr 1
      ring
    · rw [Set.indicator_of_notMem selected]
      have empty :
          ((fun label : ℝ => (label, residue)) ⁻¹' region) = ∅ := by
        ext label
        constructor
        · intro belongs
          exact (selected ⟨belongs.1, belongs.2.1⟩).elim
        · intro belongs
          simp at belongs
      rw [empty, measure_empty]
  rw [fibers, lintegral_indicator measurableSet_Ioo,
    MeasureTheory.setLIntegral_const, Real.volume_Ioo]
  norm_num [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr band_ordered),
    ENNReal.toReal_ofReal width_nonnegative]
  ring

/-- On the true UNCLIPPED target interval, the actual label is automatically
in the full dyadic prime-label shell; neither endpoint may be ignored. -/
theorem scaleAdaptiveTruncatedBandResidueRegion_label
    {index : ℕ} {lower upper targetLower targetUpper : ℝ}
    (index_positive : 0 < index)
    (interior_lower : (index : ℝ) + upper ≤ targetLower)
    (interior_upper : targetUpper ≤ 2 * (index : ℝ) + lower)
    {point : ℝ × ℝ}
    (selected : point ∈ scaleAdaptiveTruncatedBandResidueRegion
      index lower upper targetLower targetUpper) :
    (1 : ℝ) < point.1 ∧ point.1 < 2 := by
  have index_real : (0 : ℝ) < index := by
    exact_mod_cast index_positive
  constructor
  · by_contra failed
    have bounded : point.1 ≤ 1 := le_of_not_gt failed
    have multiplied := mul_le_mul_of_nonneg_left bounded index_real.le
    nlinarith [selected.2.1, selected.2.2.1]
  · by_contra failed
    have bounded : (2 : ℝ) ≤ point.1 := le_of_not_gt failed
    have multiplied := mul_le_mul_of_nonneg_left bounded index_real.le
    nlinarith [selected.1, selected.2.2.2]

/-- EXACT genuine signed-center change of variables.  Translation by the
moving `base*p` and scaling by the true modulus `W` give precisely the
Lebesgue Jacobian `|W⁻¹|`, with the actual target strip and label bounds
retained. -/
theorem scaleAdaptiveTruncatedBandSignedDomain_volume_jacobian
    {support : Finset ℕ} {base index : ℕ}
    {lower upper targetLower targetUpper : ℝ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (index_positive : 0 < index)
    (interior_lower : (index : ℝ) + upper ≤ targetLower)
    (interior_upper : targetUpper ≤ 2 * (index : ℝ) + lower) :
    volume (scaleAdaptiveTruncatedBandSignedDomain
      support base index lower upper targetLower targetUpper) =
        ENNReal.ofReal
          |(adaptiveMixedTypeModulus support : ℝ)⁻¹| *
          volume (scaleAdaptiveTruncatedBandResidueRegion
            index lower upper targetLower targetUpper) := by
  classical
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  let signed := scaleAdaptiveTruncatedBandSignedDomain
    support base index lower upper targetLower targetUpper
  let region := scaleAdaptiveTruncatedBandResidueRegion
    index lower upper targetLower targetUpper
  have signed_measurable : MeasurableSet signed :=
    (scaleAdaptiveTruncatedBandSignedDomain_isOpen
      support base index lower upper targetLower targetUpper).measurableSet
  have region_measurable : MeasurableSet region :=
    (scaleAdaptiveTruncatedBandResidueRegion_isOpen
      index lower upper targetLower targetUpper).measurableSet
  have fibers : ∀ label : ℝ,
      (volume : Measure ℝ) (Prod.mk label ⁻¹' signed) =
        ENNReal.ofReal |(adaptiveMixedTypeModulus support : ℝ)⁻¹| *
          (volume : Measure ℝ) (Prod.mk label ⁻¹' region) := by
    intro label
    have equal :
        (Prod.mk label ⁻¹' signed) =
          (fun center : ℝ =>
            (adaptiveMixedTypeModulus support : ℝ) * center) ⁻¹'
            ((fun residue : ℝ => (base : ℝ) * label + residue) ⁻¹'
              (Prod.mk label ⁻¹' region)) := by
      ext center
      change
        (1 < label ∧ label < 2 ∧
          lower < (base : ℝ) * label +
            (adaptiveMixedTypeModulus support : ℝ) * center ∧
          (base : ℝ) * label +
            (adaptiveMixedTypeModulus support : ℝ) * center < upper ∧
          targetLower < (index : ℝ) * label +
            ((base : ℝ) * label +
              (adaptiveMixedTypeModulus support : ℝ) * center) ∧
          (index : ℝ) * label +
            ((base : ℝ) * label +
              (adaptiveMixedTypeModulus support : ℝ) * center) < targetUpper) ↔
            (lower < (base : ℝ) * label +
              (adaptiveMixedTypeModulus support : ℝ) * center ∧
             (base : ℝ) * label +
              (adaptiveMixedTypeModulus support : ℝ) * center < upper ∧
             targetLower < (index : ℝ) * label +
              ((base : ℝ) * label +
                (adaptiveMixedTypeModulus support : ℝ) * center) ∧
             (index : ℝ) * label +
              ((base : ℝ) * label +
                (adaptiveMixedTypeModulus support : ℝ) * center) < targetUpper)
      constructor
      · rintro ⟨_, _, residue_lower, residue_upper,
          target_lower, target_upper⟩
        exact ⟨residue_lower, residue_upper, target_lower, target_upper⟩
      · rintro ⟨residue_lower, residue_upper, target_lower, target_upper⟩
        have label_bounds := scaleAdaptiveTruncatedBandResidueRegion_label
          index_positive interior_lower interior_upper
            (point := (label,
              (base : ℝ) * label +
                (adaptiveMixedTypeModulus support : ℝ) * center))
            ⟨residue_lower, residue_upper, target_lower, target_upper⟩
        exact ⟨label_bounds.1, label_bounds.2,
          residue_lower, residue_upper, target_lower, target_upper⟩
    rw [equal, Real.volume_preimage_mul_left modulus_positive.ne',
      measure_preimage_add]
  change volume signed =
    ENNReal.ofReal |(adaptiveMixedTypeModulus support : ℝ)⁻¹| *
      volume region
  calc
    volume signed =
        ∫⁻ label : ℝ,
          (volume : Measure ℝ) (Prod.mk label ⁻¹' signed) := by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
        MeasureTheory.Measure.prod_apply signed_measurable]
    _ = ∫⁻ label : ℝ,
          ENNReal.ofReal |(adaptiveMixedTypeModulus support : ℝ)⁻¹| *
            (volume : Measure ℝ) (Prod.mk label ⁻¹' region) := by
      congr 1
      funext label
      exact fibers label
    _ = ENNReal.ofReal |(adaptiveMixedTypeModulus support : ℝ)⁻¹| *
          ∫⁻ label : ℝ,
            (volume : Measure ℝ) (Prod.mk label ⁻¹' region) := by
      rw [lintegral_const_mul _
        (measurable_measure_prodMk_left region_measurable)]
    _ = ENNReal.ofReal |(adaptiveMixedTypeModulus support : ℝ)⁻¹| *
          volume region := by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
        MeasureTheory.Measure.prod_apply region_measurable]

/-- EXACT true target-truncated signed-center physical volume.  Both the
moving prime-label width and the true `1/W` affine-center Jacobian are
proved, with no rectangular-center approximation. -/
theorem scaleAdaptiveTruncatedBandSignedDomain_volume
    {support : Finset ℕ} {base index : ℕ}
    {lower upper targetLower targetUpper : ℝ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (index_positive : 0 < index)
    (band_ordered : lower ≤ upper)
    (target_ordered : targetLower ≤ targetUpper)
    (interior_lower : (index : ℝ) + upper ≤ targetLower)
    (interior_upper : targetUpper ≤ 2 * (index : ℝ) + lower) :
    (volume (scaleAdaptiveTruncatedBandSignedDomain
      support base index lower upper targetLower targetUpper)).toReal =
      (targetUpper - targetLower) * (upper - lower) /
        ((index : ℝ) * (adaptiveMixedTypeModulus support : ℝ)) := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  rw [scaleAdaptiveTruncatedBandSignedDomain_volume_jacobian
    primes index_positive interior_lower interior_upper,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (inv_pos.mpr modulus_positive),
    scaleAdaptiveTruncatedBandResidueRegion_volume
      index_positive band_ordered target_ordered]
  ring

/-- A positive-width target/residue cell really contains a TRUE signed-center
physical point.  Its center may be negative; no prime realization is claimed
until the explicit Green--Tao input is applied. -/
theorem scaleAdaptiveTruncatedBandSignedDomain_nonempty
    {support : Finset ℕ} {base index : ℕ}
    {lower upper targetLower targetUpper : ℝ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (index_positive : 0 < index)
    (band_nonempty : lower < upper)
    (target_nonempty : targetLower < targetUpper)
    (interior_lower : (index : ℝ) + upper ≤ targetLower)
    (interior_upper : targetUpper ≤ 2 * (index : ℝ) + lower) :
    (scaleAdaptiveTruncatedBandSignedDomain
      support base index lower upper targetLower targetUpper).Nonempty := by
  have index_real : (0 : ℝ) < index := by
    exact_mod_cast index_positive
  have modulus_real : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  let target := (targetLower + targetUpper) / 2
  let residue := (lower + upper) / 2
  let label := (target - residue) / (index : ℝ)
  let center :=
    (residue - (base : ℝ) * label) /
      (adaptiveMixedTypeModulus support : ℝ)
  have target_cancellation :
      (index : ℝ) * label + residue = target := by
    dsimp [label]
    field_simp [index_real.ne']
    ring
  have residue_cancellation :
      (base : ℝ) * label +
        (adaptiveMixedTypeModulus support : ℝ) * center = residue := by
    dsimp [center]
    field_simp [modulus_real.ne']
    ring
  have residue_lower : lower < residue := by
    dsimp [residue]
    linarith
  have residue_upper : residue < upper := by
    dsimp [residue]
    linarith
  have target_lower : targetLower < target := by
    dsimp [target]
    linarith
  have target_upper : target < targetUpper := by
    dsimp [target]
    linarith
  have region :
      (label, residue) ∈ scaleAdaptiveTruncatedBandResidueRegion
        index lower upper targetLower targetUpper := by
    exact ⟨residue_lower, residue_upper,
      target_cancellation.symm ▸ target_lower,
      target_cancellation.symm ▸ target_upper⟩
  have labels := scaleAdaptiveTruncatedBandResidueRegion_label
    index_positive interior_lower interior_upper region
  refine ⟨(label, center), ?_⟩
  change
    1 < label ∧ label < 2 ∧
      lower < (base : ℝ) * label +
        (adaptiveMixedTypeModulus support : ℝ) * center ∧
      (base : ℝ) * label +
        (adaptiveMixedTypeModulus support : ℝ) * center < upper ∧
      targetLower < (index : ℝ) * label +
        ((base : ℝ) * label +
          (adaptiveMixedTypeModulus support : ℝ) * center) ∧
      (index : ℝ) * label +
        ((base : ℝ) * label +
          (adaptiveMixedTypeModulus support : ℝ) * center) < targetUpper
  rw [residue_cancellation, target_cancellation]
  exact ⟨labels.1, labels.2, residue_lower, residue_upper,
    target_lower, target_upper⟩

/-- The target-truncated signed domain remains inside the TRUE original
mixed prime-pattern fundamental strip for its actual varying label. -/
theorem scaleAdaptiveTruncatedBandSignedDomain_subset_physical
    (support : Finset ℕ) (base index : ℕ)
    (lower upper targetLower targetUpper : ℝ)
    (lower_nonnegative : 0 ≤ lower)
    (upper_bounded : upper ≤ 1) :
    scaleAdaptiveTruncatedBandSignedDomain
      support base index lower upper targetLower targetUpper ⊆
        adaptiveMixedSignedOriginalPhysicalDomain support base := by
  intro point selected
  have band :
      point ∈ scaleAdaptiveSignedConstantResidueBand
        support base lower upper :=
    ⟨selected.1, selected.2.1,
      selected.2.2.1, selected.2.2.2.1⟩
  exact scaleAdaptiveSignedConstantResidueBand_subset_physical
    support base lower upper lower_nonnegative upper_bounded band

/-- DIRECT genuine target-TRUNCATED first prime-incidence asymptotic from
the explicit signed Green--Tao input.  Its actual coefficient is exactly
`(targetUpper-targetLower)*(upper-lower)*singular/(index*W)`, retaining the
true moving target window, signed center, prime label, and physical Jacobian.

No first moment, prime witness, target uniformity, or variance is assumed. -/
theorem scaleAdaptiveTruncatedBandIndexedTarget_firstMoment_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index : ℕ) (lower upper targetLower targetUpper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (index_positive : 0 < index)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (target_nonempty : targetLower < targetUpper)
    (interior_lower : (index : ℝ) + upper ≤ targetLower)
    (interior_upper : targetUpper ≤ 2 * (index : ℝ) + lower) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale outcome)
          atTop (nhds singular) ∧
      Tendsto
        (fun N : ℕ =>
          (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
            ((scaleAdaptiveGTZIndexedTargetFiber support scale outcome
              (scaleAdaptiveTruncatedBandSignedDomain
                support outcome.1 index
                  lower upper targetLower targetUpper)
              index N target).card : ℝ)) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 2)
        atTop (nhds
          ((targetUpper - targetLower) * (upper - lower) /
            ((index : ℝ) * (adaptiveMixedTypeModulus support : ℝ)) *
            singular)) := by
  let domain := scaleAdaptiveTruncatedBandSignedDomain
    support outcome.1 index lower upper targetLower targetUpper
  obtain ⟨singular, positive, converges, asymptotic⟩ :=
    scaleAdaptiveGTZIndexedTarget_firstMoment_positive_asymptotic
      green_tao support scale outcome domain index primes
      (scaleAdaptiveTruncatedBandSignedDomain_convex
        support outcome.1 index lower upper targetLower targetUpper)
      (scaleAdaptiveTruncatedBandSignedDomain_isOpen
        support outcome.1 index lower upper targetLower targetUpper)
      (scaleAdaptiveTruncatedBandSignedDomain_nonempty
        primes index_positive band_nonempty target_nonempty
          interior_lower interior_upper)
      (scaleAdaptiveTruncatedBandSignedDomain_subset_physical
        support outcome.1 index lower upper targetLower targetUpper
          lower_nonnegative upper_bounded)
  refine ⟨singular, positive, converges, ?_⟩
  change Tendsto _ atTop (nhds ((volume domain).toReal * singular))
    at asymptotic
  rw [scaleAdaptiveTruncatedBandSignedDomain_volume
    primes index_positive band_nonempty.le target_nonempty.le
      interior_lower interior_upper] at asymptotic
  exact asymptotic

end Erdos1139

