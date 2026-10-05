module

public import ShiftedFareyDisjoint433

@[expose] public section


/-!
# Exact finite deduplication of translated major arcs

Distinct shifted Farey anchors can have exactly the same rational center.
Consequently, summing the integrals over all anchor/shift triples would
double-count genuine major-arc mass. This module groups the actual closed
intervals by their exact real center, proves different groups disjoint at the
fully compatible cutoff, and splits their circle-restricted integral exactly.
No sign or singular-series estimate is presumed.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Goldbach's complete Farey major region is exactly invariant under every
integer translation; its anchor numerator changes by `k*q`. -/
theorem goldbachMajorArcs_add_int_iff
    (P Q : ℕ) (α : ℝ) (k : ℤ) :
    α + (k : ℝ) ∈ GoldbachChain.MajorArcs P Q ↔
      α ∈ GoldbachChain.MajorArcs P Q := by
  unfold GoldbachChain.MajorArcs
  simp only [Set.mem_iUnion, Set.mem_Icc, Metric.mem_closedBall]
  constructor
  · rintro ⟨q, hq, a, hball⟩
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq.1
    refine ⟨q, hq, a - k * (q : ℤ), ?_⟩
    have hcenter :
        (((a - k * (q : ℤ) : ℤ) : ℝ) / q) =
          (a : ℝ) / q - k := by
      push_cast
      field_simp
    rw [hcenter, Real.dist_eq]
    rw [Real.dist_eq] at hball
    convert hball using 1
    congr 1
    ring
  · rintro ⟨q, hq, a, hball⟩
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq.1
    refine ⟨q, hq, a + k * (q : ℤ), ?_⟩
    have hcenter :
        (((a + k * (q : ℤ) : ℤ) : ℝ) / q) =
          (a : ℝ) / q + k := by
      push_cast
      field_simp
    rw [hcenter, Real.dist_eq]
    rw [Real.dist_eq] at hball
    convert hball using 1
    congr 1
    ring

/-- The periodic-major definition in the genuine shifted-minor decomposition
is not a larger auxiliary set: it equals Goldbach's actual complete Farey
major region on the whole real line. -/
theorem ternaryPeriodicMajorArcs_eq_goldbachMajorArcs
    (P Q : ℕ) :
    ternaryPeriodicMajorArcs P Q = GoldbachChain.MajorArcs P Q := by
  classical
  ext α
  simp only [ternaryPeriodicMajorArcs, ternaryPeriodicMinorArcs,
    Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage,
    Set.mem_sdiff, Set.mem_Ioc, not_exists, not_and]
  constructor
  · intro h
    let k : ℤ := ⌈α⌉ - 1
    have hceil : α ≤ (⌈α⌉ : ℝ) := Int.le_ceil α
    have hstrict : (⌈α⌉ : ℝ) < α + 1 := Int.ceil_lt_add_one α
    have hwindow : 0 < α - (k : ℝ) ∧ α - (k : ℝ) ≤ 1 := by
      dsimp [k]
      push_cast
      constructor <;> linarith
    have hshift : α - (k : ℝ) ∈ GoldbachChain.MajorArcs P Q :=
      Classical.byContradiction (h k hwindow)
    have htranslate :=
      (goldbachMajorArcs_add_int_iff P Q (α - (k : ℝ)) k).mpr hshift
    simpa using htranslate
  · intro h k _hwindow hnot
    apply hnot
    have htranslate :=
      (goldbachMajorArcs_add_int_iff P Q (α - (k : ℝ)) k).mp
        (by simpa using h)
    exact htranslate

/-- The exact shifted-major complement is a finite union of *actual*
Goldbach Farey major regions, not an unidentified periodic enlargement. -/
theorem ternaryShiftedMinorArcs_complement_eq_actual_major_shifts
    (M P Q : ℕ) :
    Set.Ioc (0 : ℝ) 1 \ ternaryShiftedMinorArcs M P Q =
      Set.Ioc (0 : ℝ) 1 ∩
        ⋃ j : Fin M,
          (fun α : ℝ => α + (j.val : ℝ) / M) ⁻¹'
            GoldbachChain.MajorArcs P Q := by
  rw [ternaryShiftedMinorArcs_complement_eq,
    ternaryPeriodicMajorArcs_eq_goldbachMajorArcs]

/-- A translated anchor records its original denominator, numerator, and
integer additive-character shift. -/
abbrev ShiftedFareyAnchor := ℕ × ℤ × ℤ

/-- The genuine finite translated-anchor family for the whole shifted-major
union. A character shift in `[0,1)` needs only the two integer periodic
lifts `k = 0,1`; the original reduced Farey denominator is unchanged. -/
noncomputable def actualShiftedFareyAnchors
    (M P : ℕ) : Finset ShiftedFareyAnchor :=
  (((GoldbachChain.anchors P).product (Finset.range M)).product
    (Finset.Icc (0 : ℤ) 1)).image fun t =>
      (t.1.1.1,
        t.1.1.2 + t.2 * (t.1.1.1 : ℤ),
        (t.1.2 : ℤ))

/-- Every member of the actual finite shifted family has its genuine positive
original Farey denominator at most `P`. -/
theorem actualShiftedFareyAnchors_denominator_bounds
    (M P : ℕ) (t : ShiftedFareyAnchor)
    (ht : t ∈ actualShiftedFareyAnchors M P) :
    0 < t.1 ∧ t.1 ≤ P := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hu, _⟩ := Finset.mem_product.mp hu
  obtain ⟨hanchor, _⟩ := Finset.mem_product.mp hu
  obtain ⟨hbase, _⟩ := Finset.mem_filter.mp hanchor
  obtain ⟨hq, _⟩ := Finset.mem_product.mp hbase
  exact Finset.mem_Icc.mp hq

/-- An actual translated interval is exactly the pullback of its unshifted
original-denominator Farey interval after the integer periodic correction. -/
theorem shiftedFareyAnchorArc_mem_iff_periodic_anchor
    (M Q q : ℕ) (a k : ℤ) (j : ℕ) (α : ℝ)
    (hM : 0 < M) (hq : 0 < q) :
    α ∈ shiftedFareyAnchorArc M Q q
        (a + k * (q : ℤ)) (j : ℤ) ↔
      α + (j : ℝ) / M - (k : ℝ) ∈
        Metric.closedBall ((a : ℝ) / q)
          (1 / ((q : ℝ) * (Q + 1))) := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  unfold shiftedFareyAnchorArc shiftedFareyAnchorCenter
  rw [Metric.mem_closedBall, Metric.mem_closedBall,
    Real.dist_eq, Real.dist_eq]
  have hcenter :
      ((((a + k * (q : ℤ) : ℤ) : ℝ) / q) - (j : ℝ) / M) =
        (a : ℝ) / q + k - (j : ℝ) / M := by
    push_cast
    field_simp
  simp only [Int.cast_natCast]
  rw [hcenter]
  ring_nf

/-- The *entire actual shifted-major complement* is exactly the finite union
of translated genuine Farey intervals. The construction retains both needed
periodic lifts, all character shifts, and original denominator radii. -/
theorem ternaryShiftedMinorArcs_complement_eq_finite_anchor_union
    (M P Q : ℕ) (hM : 0 < M) (hP : 0 < P) :
    Set.Ioc (0 : ℝ) 1 \ ternaryShiftedMinorArcs M P Q =
      Set.Ioc (0 : ℝ) 1 ∩
        ⋃ t ∈ actualShiftedFareyAnchors M P,
          shiftedFareyAnchorArc M Q t.1 t.2.1 t.2.2 := by
  classical
  rw [ternaryShiftedMinorArcs_complement_eq_actual_major_shifts]
  ext α
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨hα, j, hmajor⟩
    let β : ℝ := α + (j.val : ℝ) / M
    let k : ℤ := ⌈β⌉ - 1
    have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
    have hjnonneg : (0 : ℝ) ≤ (j.val : ℝ) / M := by positivity
    have hjlt : (j.val : ℝ) / M < 1 := by
      apply (div_lt_one hMreal).mpr
      exact_mod_cast j.isLt
    have hβpos : 0 < β := by
      dsimp [β]
      linarith [hα.1]
    have hβlt : β < 2 := by
      dsimp [β]
      linarith [hα.2]
    have hceil : β ≤ (⌈β⌉ : ℝ) := Int.le_ceil β
    have hstrict : (⌈β⌉ : ℝ) < β + 1 := Int.ceil_lt_add_one β
    have hkIoc : β - (k : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
      dsimp [k]
      push_cast
      constructor <;> linarith
    have hkzero : 0 ≤ k := by
      have hceilpos : (0 : ℤ) < ⌈β⌉ :=
        (Int.ceil_pos).mpr hβpos
      dsimp [k]
      omega
    have hkone : k ≤ 1 := by
      have hceille : ⌈β⌉ ≤ (2 : ℤ) :=
        (Int.ceil_le).mpr hβlt.le
      dsimp [k]
      omega
    have hshiftmajor : β - (k : ℝ) ∈ GoldbachChain.MajorArcs P Q :=
      (goldbachMajorArcs_add_int_iff P Q (β - (k : ℝ)) k).mp
        (by simpa [β] using hmajor)
    have hreduced : β - (k : ℝ) ∈
        (⋃ pq ∈ GoldbachChain.anchors P,
          Metric.closedBall ((pq.2 : ℝ) / pq.1)
            (1 / ((pq.1 : ℝ) * (Q + 1)))) := by
      have hintersection : β - (k : ℝ) ∈
          GoldbachChain.MajorArcs P Q ∩ Set.Ioc (0 : ℝ) 1 :=
        ⟨hshiftmajor, hkIoc⟩
      rw [GoldbachChain.majorArcs_inter_eq_anchors P Q hP] at hintersection
      exact hintersection.1
    simp only [Set.mem_iUnion] at hreduced
    obtain ⟨pq, hpq, hball⟩ := hreduced
    have hq : 0 < pq.1 := by
      obtain ⟨hbase, _⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hq, _⟩ := Finset.mem_product.mp hbase
      exact (Finset.mem_Icc.mp hq).1
    refine ⟨hα, (pq.1, pq.2 + k * (pq.1 : ℤ), (j.val : ℤ)), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨((pq, j.val), k), ?_, rfl⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hpq, Finset.mem_range.mpr j.isLt⟩,
          Finset.mem_Icc.mpr ⟨hkzero, hkone⟩⟩
    · exact (shiftedFareyAnchorArc_mem_iff_periodic_anchor
        M Q pq.1 pq.2 k j.val α hM hq).mpr (by simpa [β] using hball)
  · rintro ⟨hα, t, ht, hball⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hpair, _hk⟩ := Finset.mem_product.mp hu
    obtain ⟨hpq, hj⟩ := Finset.mem_product.mp hpair
    have hjlt : u.1.2 < M := Finset.mem_range.mp hj
    have hq : 0 < u.1.1.1 := by
      obtain ⟨hbase, _⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hq, _⟩ := Finset.mem_product.mp hbase
      exact (Finset.mem_Icc.mp hq).1
    have hraw := (shiftedFareyAnchorArc_mem_iff_periodic_anchor
      M Q u.1.1.1 u.1.1.2 u.2 u.1.2 α hM hq).mp hball
    have hanchor_major :
        α + (u.1.2 : ℝ) / M - (u.2 : ℝ) ∈
          GoldbachChain.MajorArcs P Q := by
      apply GoldbachChain.anchors_subset_majorArcs P Q
      simp only [Set.mem_iUnion]
      exact ⟨u.1.1, hpq, hraw⟩
    have hmajor := (goldbachMajorArcs_add_int_iff
      P Q (α + (u.1.2 : ℝ) / M - (u.2 : ℝ)) u.2).mpr
        hanchor_major
    refine ⟨hα, ⟨u.1.2, hjlt⟩, ?_⟩
    simpa using hmajor

/-- The finite set of *distinct actual centers*, not anchor indices. -/
noncomputable def shiftedFareyCenterClasses
    (M : ℕ) (A : Finset ShiftedFareyAnchor) : Finset ℝ :=
  A.image fun t => shiftedFareyAnchorCenter M t.1 t.2.1 t.2.2

/-- The full closed-interval union attached to one exact translated center.
Duplicate anchors retain their original denominator-dependent radii. -/
noncomputable def shiftedFareyCenterRegion
    (M Q : ℕ) (A : Finset ShiftedFareyAnchor) (c : ℝ) : Set ℝ :=
  ⋃ t ∈ A.filter (fun t =>
      shiftedFareyAnchorCenter M t.1 t.2.1 t.2.2 = c),
    shiftedFareyAnchorArc M Q t.1 t.2.1 t.2.2

/-- Grouping equal centers neither drops nor duplicates any actual major-arc
point: the full indexed union equals the union over distinct centers. -/
theorem shiftedFareyAnchorUnion_eq_center_union
    (M Q : ℕ) (A : Finset ShiftedFareyAnchor) :
    (⋃ t ∈ A, shiftedFareyAnchorArc M Q t.1 t.2.1 t.2.2) =
      ⋃ c ∈ shiftedFareyCenterClasses M A,
        shiftedFareyCenterRegion M Q A c := by
  classical
  ext α
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hα⟩
    refine ⟨shiftedFareyAnchorCenter M t.1 t.2.1 t.2.2, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    · simp only [shiftedFareyCenterRegion, Set.mem_iUnion]
      exact ⟨t, Finset.mem_filter.mpr ⟨ht, rfl⟩, hα⟩
  · rintro ⟨c, _hc, hα⟩
    change α ∈ shiftedFareyCenterRegion M Q A c at hα
    simp only [shiftedFareyCenterRegion, Set.mem_iUnion] at hα
    obtain ⟨t, ht, hα⟩ := hα
    exact ⟨t, (Finset.mem_filter.mp ht).1, hα⟩

/-- Every exact center class is a measurable finite union of genuine closed
intervals, even when several original Farey denominators share its center. -/
theorem shiftedFareyCenterRegion_measurable
    (M Q : ℕ) (A : Finset ShiftedFareyAnchor) (c : ℝ) :
    MeasurableSet (shiftedFareyCenterRegion M Q A c) := by
  classical
  unfold shiftedFareyCenterRegion
  apply Finset.measurableSet_biUnion
  intro t _
  exact Metric.isClosed_closedBall.measurableSet

/-- Each nonempty duplicate-center group is exactly one of its original
Farey intervals: choosing the smallest genuine denominator gives the widest
radius. Thus the center integral is a single actual rational-window integral,
not an unresolved overlapping-union expression. -/
theorem shiftedFareyCenterRegion_eq_widest_anchor
    (M Q : ℕ) (A : Finset ShiftedFareyAnchor) (c : ℝ)
    (hc : c ∈ shiftedFareyCenterClasses M A)
    (hpositive : ∀ t ∈ A, 0 < t.1) :
    ∃ t ∈ A,
      shiftedFareyAnchorCenter M t.1 t.2.1 t.2.2 = c ∧
        shiftedFareyCenterRegion M Q A c =
          shiftedFareyAnchorArc M Q t.1 t.2.1 t.2.2 := by
  classical
  let group := A.filter fun t =>
    shiftedFareyAnchorCenter M t.1 t.2.1 t.2.2 = c
  obtain ⟨u, huA, huc⟩ := Finset.mem_image.mp hc
  have hugroup : u ∈ group := Finset.mem_filter.mpr ⟨huA, huc⟩
  let denominators := group.image fun t => t.1
  have hdenominators : denominators.Nonempty :=
    ⟨u.1, Finset.mem_image.mpr ⟨u, hugroup, rfl⟩⟩
  let q := denominators.min' hdenominators
  have hqmem : q ∈ denominators := Finset.min'_mem denominators hdenominators
  obtain ⟨t, htgroup, htq⟩ := Finset.mem_image.mp hqmem
  obtain ⟨htA, htc⟩ := Finset.mem_filter.mp htgroup
  refine ⟨t, htA, htc, Set.Subset.antisymm ?_ ?_⟩
  · intro α hα
    simp only [shiftedFareyCenterRegion, Set.mem_iUnion] at hα
    obtain ⟨v, hvgroup, hαv⟩ := hα
    obtain ⟨hvA, hvc⟩ := Finset.mem_filter.mp hvgroup
    have hvden : v.1 ∈ denominators :=
      Finset.mem_image.mpr ⟨v, hvgroup, rfl⟩
    have hqle : t.1 ≤ v.1 := by
      rw [htq]
      exact Finset.min'_le denominators v.1 hvden
    have htpos : (0 : ℝ) < t.1 := by
      exact_mod_cast hpositive t htA
    have hcenter :
        shiftedFareyAnchorCenter M v.1 v.2.1 v.2.2 =
          shiftedFareyAnchorCenter M t.1 t.2.1 t.2.2 :=
      hvc.trans htc.symm
    unfold shiftedFareyAnchorArc at hαv ⊢
    rw [hcenter] at hαv
    apply (Metric.closedBall_subset_closedBall ?_) hαv
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hqle) (by positivity)
  · intro α hα
    simp only [shiftedFareyCenterRegion, Set.mem_iUnion]
    exact ⟨t, Finset.mem_filter.mpr ⟨htA, htc⟩, hα⟩

/-- At the true translated-separation cutoff, complete equal-center groups
are pairwise disjoint. This does not assert the false pairwise disjointness
of all individual anchor triples. -/
theorem shiftedFareyCenterRegions_pairwise_disjoint
    (M P Q : ℕ) (A : Finset ShiftedFareyAnchor)
    (hM : 0 < M)
    (hanchors : ∀ t ∈ A, 0 < t.1 ∧ t.1 ≤ P)
    (hPQ : 2 * (M * P) ^ 2 < Q + 1) :
    Set.Pairwise (↑(shiftedFareyCenterClasses M A) : Set ℝ)
      (fun c c' => Disjoint
        (shiftedFareyCenterRegion M Q A c)
        (shiftedFareyCenterRegion M Q A c')) := by
  classical
  intro c _hc c' _hc' hne
  rw [Set.disjoint_left]
  intro α hα hα'
  simp only [shiftedFareyCenterRegion, Set.mem_iUnion] at hα hα'
  obtain ⟨t, ht, hα⟩ := hα
  obtain ⟨u, hu, hα'⟩ := hα'
  obtain ⟨htA, htcenter⟩ := Finset.mem_filter.mp ht
  obtain ⟨huA, hucenter⟩ := Finset.mem_filter.mp hu
  obtain ⟨htpos, htbound⟩ := hanchors t htA
  obtain ⟨hupos, hubound⟩ := hanchors u huA
  have hdistinct :
      shiftedFareyAnchorCenter M t.1 t.2.1 t.2.2 ≠
        shiftedFareyAnchorCenter M u.1 u.2.1 u.2.2 := by
    intro heq
    exact hne (htcenter.symm.trans (heq.trans hucenter))
  exact Set.disjoint_left.mp
    (shiftedFareyAnchorArc_disjoint_of_distinct_centers
      M P Q t.1 u.1 t.2.1 u.2.1 t.2.2 u.2.2
      hM htpos hupos htbound hubound hPQ hdistinct) hα hα'

/-- Exact additivity on the fundamental Fourier circle for any continuous
complex integrand and any genuine finite shifted-anchor family. The sum is
indexed by distinct centers, preserving duplicates with no double counting. -/
theorem shiftedFareyAnchorUnion_integral_eq_center_sum
    (M P Q : ℕ) (A : Finset ShiftedFareyAnchor)
    (hM : 0 < M)
    (hanchors : ∀ t ∈ A, 0 < t.1 ∧ t.1 ≤ P)
    (hPQ : 2 * (M * P) ^ 2 < Q + 1)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        (⋃ t ∈ A, shiftedFareyAnchorArc M Q t.1 t.2.1 t.2.2), f α) =
      ∑ c ∈ shiftedFareyCenterClasses M A,
        ∫ α in Set.Ioc (0 : ℝ) 1 ∩
          shiftedFareyCenterRegion M Q A c, f α := by
  classical
  let centers := shiftedFareyCenterClasses M A
  let regions : ℝ → Set ℝ := fun c =>
    Set.Ioc (0 : ℝ) 1 ∩ shiftedFareyCenterRegion M Q A c
  have hgroups := shiftedFareyCenterRegions_pairwise_disjoint
    M P Q A hM hanchors hPQ
  have hmeas : ∀ c ∈ centers, MeasurableSet (regions c) := by
    intro c _
    exact measurableSet_Ioc.inter
      (shiftedFareyCenterRegion_measurable M Q A c)
  have hpairwise : Set.Pairwise (↑centers : Set ℝ)
      (fun c c' => Disjoint (regions c) (regions c')) := by
    intro c hc c' hc' hne
    exact Set.disjoint_of_subset Set.inter_subset_right
      Set.inter_subset_right (hgroups hc hc' hne)
  have hint : ∀ c ∈ centers, IntegrableOn f (regions c) := by
    intro c _
    exact (hf.integrableOn_Ioc).mono_set Set.inter_subset_left
  have hunion :
      Set.Ioc (0 : ℝ) 1 ∩
          (⋃ t ∈ A, shiftedFareyAnchorArc M Q t.1 t.2.1 t.2.2) =
        ⋃ c ∈ centers, regions c := by
    rw [shiftedFareyAnchorUnion_eq_center_union]
    ext α
    simp [regions, centers]
  rw [hunion]
  exact integral_biUnion_finset centers hmeas hpairwise hint

/-- The exact deduplicated integral decomposition applies simultaneously
to every finite translated-anchor family at every sufficiently large
original endpoint under the genuine logarithmic/linear-label cutoff. -/
theorem shiftedFareyAnchorUnion_fully_compatible_integral_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (M : ℕ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ShiftedFareyAnchor),
        (∀ t ∈ A, 0 < t.1 ∧ t.1 ≤ compatibleLogMinorCutoff n) →
          ∀ (f : ℝ → ℂ), Continuous f →
            (∫ α in Set.Ioc (0 : ℝ) 1 ∩
                (⋃ t ∈ A,
                  shiftedFareyAnchorArc M
                    (fullyCompatibleFareyCutoff lower n)
                    t.1 t.2.1 t.2.2), f α) =
              ∑ c ∈ shiftedFareyCenterClasses M A,
                ∫ α in Set.Ioc (0 : ℝ) 1 ∩
                  shiftedFareyCenterRegion M
                    (fullyCompatibleFareyCutoff lower n) A c, f α := by
  filter_upwards [fullyCompatibleFareyCutoff_merged_disjoint_eventually
    lower κ hκ hlinear M] with n hseparation
  intro A hanchors f hf
  exact shiftedFareyAnchorUnion_integral_eq_center_sum
    M (compatibleLogMinorCutoff n) (fullyCompatibleFareyCutoff lower n)
    A hM hanchors hseparation f hf

/-- The actual shifted-major region in the already proved Fourier assembly,
not merely an arbitrary model family, has an exact finite integral expansion
over distinct genuine translated rational centers. -/
theorem ternaryShiftedMajorRegion_integral_eq_actual_center_sum
    (M P Q : ℕ) (hM : 0 < M) (hP : 0 < P)
    (hPQ : 2 * (M * P) ^ 2 < Q + 1)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ ternaryShiftedMinorArcs M P Q, f α) =
      ∑ c ∈ shiftedFareyCenterClasses M (actualShiftedFareyAnchors M P),
        ∫ α in Set.Ioc (0 : ℝ) 1 ∩
          shiftedFareyCenterRegion M Q (actualShiftedFareyAnchors M P) c,
            f α := by
  rw [ternaryShiftedMinorArcs_complement_eq_finite_anchor_union M P Q hM hP]
  exact shiftedFareyAnchorUnion_integral_eq_center_sum
    M P Q (actualShiftedFareyAnchors M P) hM
    (actualShiftedFareyAnchors_denominator_bounds M P) hPQ f hf

/-- At every sufficiently large original endpoint, the *entire actual*
shifted-major integral for the corrected logarithmic/linear-label cutoff is
exactly the finite sum over disjoint equal-center groups. This fully resolves
the duplicate-anchor union/integration obstruction; rational-phase evaluation
and positive singular-series control remain separate mathematical questions. -/
theorem ternaryShiftedMajorRegion_fully_compatible_center_sum_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (M : ℕ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (f : ℝ → ℂ), Continuous f →
        (∫ α in Set.Ioc (0 : ℝ) 1 \
            ternaryShiftedMinorArcs M
              (compatibleLogMinorCutoff n)
              (fullyCompatibleFareyCutoff lower n), f α) =
          ∑ c ∈ shiftedFareyCenterClasses M
              (actualShiftedFareyAnchors M (compatibleLogMinorCutoff n)),
            ∫ α in Set.Ioc (0 : ℝ) 1 ∩
              shiftedFareyCenterRegion M
                (fullyCompatibleFareyCutoff lower n)
                (actualShiftedFareyAnchors M (compatibleLogMinorCutoff n)) c,
                  f α := by
  filter_upwards
    [fullyCompatibleFareyCutoff_merged_disjoint_eventually
      lower κ hκ hlinear M,
      (tendsto_atTop.1 compatibleLogMinorCutoff_tendsto_atTop 1)]
      with n hseparation hcutoff
  intro f hf
  exact ternaryShiftedMajorRegion_integral_eq_actual_center_sum
    M (compatibleLogMinorCutoff n) (fullyCompatibleFareyCutoff lower n)
    hM hcutoff hseparation f hf

end Erdos689

