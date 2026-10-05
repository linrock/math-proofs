module

public import FullyCompatibleMinorArcs433

@[expose] public section


/-!
# Genuine translated Farey-arc geometry for Erdős #689

After a residue-character shift, an anchor `a/q` becomes `a/q - j/M`, but its
radius remains `1/(q*(Q+1))`: it is not the standard radius attached to the
possibly larger reduced denominator.  This file proves genuine set-level
disjointness for *distinct centers* and nesting for repeated centers, rather
than silently applying the unshifted Farey lemma to the wrong radius.
-/

open Filter
open scoped Topology

namespace Erdos689

/-- The actual translated anchor, allowing arbitrary periodic integer lifts. -/
noncomputable def shiftedFareyAnchorCenter
    (M q : ℕ) (a j : ℤ) : ℝ :=
  (a : ℝ) / q - (j : ℝ) / M

/-- The actual shifted major arc retains its *original* denominator `q` in
the radius, even when its reduced center has a different denominator. -/
noncomputable def shiftedFareyAnchorArc
    (M Q q : ℕ) (a j : ℤ) : Set ℝ :=
  Metric.closedBall (shiftedFareyAnchorCenter M q a j)
    (1 / ((q : ℝ) * (Q + 1)))

/-- Distinct real rationals with positive natural denominators are separated
by their exact unreduced denominator product; no coprimality is needed. -/
theorem shiftedFarey_rational_dist_lower
    (a a' : ℤ) (q q' : ℕ) (hq : 0 < q) (hq' : 0 < q')
    (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    1 / ((q : ℝ) * q') ≤ dist ((a : ℝ) / q) ((a' : ℝ) / q') := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'real : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hnum : a * (q' : ℤ) ≠ a' * (q : ℤ) := by
    intro h
    apply hne
    apply (div_eq_div_iff hqreal.ne' hq'real.ne').mpr
    exact_mod_cast h
  rw [Real.dist_eq]
  have hval :
      (a : ℝ) / q - (a' : ℝ) / q' =
        ((a * q' - a' * q : ℤ) : ℝ) / ((q : ℝ) * q') := by
    push_cast
    field_simp
  rw [hval, abs_div, abs_of_pos (by positivity : 0 < (q : ℝ) * q')]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : (1 : ℤ) ≤ |a * q' - a' * q| :=
    Int.one_le_abs (sub_ne_zero_of_ne hnum)
  exact_mod_cast
    (by exact_mod_cast h1 : (1 : ℝ) ≤ |((a * q' - a' * q : ℤ) : ℝ)|)

/-- Every actual translated anchor has an honest unreduced rational
representation with denominator `M*q`. -/
theorem shiftedFareyAnchorCenter_eq_common_fraction
    (M q : ℕ) (a j : ℤ) (hM : 0 < M) (hq : 0 < q) :
    shiftedFareyAnchorCenter M q a j =
      ((a * (M : ℤ) - j * (q : ℤ) : ℤ) : ℝ) / (q * M : ℕ) := by
  unfold shiftedFareyAnchorCenter
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  push_cast
  field_simp

/-- Actual translated Farey intervals with their *original* radii really are
disjoint whenever their centers differ.  Repeated centers are deliberately
excluded: different shift/anchor tuples can encode the same rational. -/
theorem shiftedFareyAnchorArc_disjoint_of_distinct_centers
    (M P Q q q' : ℕ) (a a' j j' : ℤ)
    (hM : 0 < M) (hq : 0 < q) (hq' : 0 < q')
    (hqP : q ≤ P) (hq'P : q' ≤ P)
    (hPQ : 2 * (M * P) ^ 2 < Q + 1)
    (hne : shiftedFareyAnchorCenter M q a j ≠
      shiftedFareyAnchorCenter M q' a' j') :
    Disjoint (shiftedFareyAnchorArc M Q q a j)
      (shiftedFareyAnchorArc M Q q' a' j') := by
  have hP : 0 < P := hq.trans_le hqP
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hPreal : (0 : ℝ) < P := by exact_mod_cast hP
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'real : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hQreal : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  let A : ℤ := a * (M : ℤ) - j * (q : ℤ)
  let A' : ℤ := a' * (M : ℤ) - j' * (q' : ℤ)
  have hcenter := shiftedFareyAnchorCenter_eq_common_fraction M q a j hM hq
  have hcenter' :=
    shiftedFareyAnchorCenter_eq_common_fraction M q' a' j' hM hq'
  have hdist :
      1 / (((q * M : ℕ) : ℝ) * (q' * M : ℕ)) ≤
        dist (shiftedFareyAnchorCenter M q a j)
          (shiftedFareyAnchorCenter M q' a' j') := by
    rw [hcenter, hcenter']
    exact shiftedFarey_rational_dist_lower A A'
      (q * M) (q' * M) (Nat.mul_pos hq hM) (Nat.mul_pos hq' hM)
      (by simpa [A, A', hcenter, hcenter'] using hne)
  unfold shiftedFareyAnchorArc
  apply Metric.closedBall_disjoint_closedBall
  calc
    1 / ((q : ℝ) * (Q + 1)) + 1 / ((q' : ℝ) * (Q + 1)) ≤
        1 / ((Q : ℝ) + 1) + 1 / ((Q : ℝ) + 1) := by
      have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hq'one : (1 : ℝ) ≤ q' := by exact_mod_cast hq'
      apply add_le_add
      · apply one_div_le_one_div_of_le hQreal
        nlinarith
      · apply one_div_le_one_div_of_le hQreal
        nlinarith
    _ = 2 / ((Q : ℝ) + 1) := by ring
    _ < 1 / ((M : ℝ) * P) ^ 2 := by
      rw [div_lt_div_iff₀ hQreal (by positivity)]
      have hreal : (2 * (M * P) ^ 2 : ℝ) < (Q : ℝ) + 1 := by
        exact_mod_cast hPQ
      nlinarith
    _ ≤ 1 / (((q * M : ℕ) : ℝ) * (q' * M : ℕ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      have hqle : (q : ℝ) ≤ P := by exact_mod_cast hqP
      have hq'le : (q' : ℝ) ≤ P := by exact_mod_cast hq'P
      calc
        ((q : ℝ) * M) * ((q' : ℝ) * M) ≤
          ((P : ℝ) * M) * ((P : ℝ) * M) := by gcongr
        _ = ((M : ℝ) * P) ^ 2 := by ring
    _ ≤ dist (shiftedFareyAnchorCenter M q a j)
      (shiftedFareyAnchorCenter M q' a' j') := hdist

/-- Duplicate shifted centers never need a disjointness claim: their actual
closed intervals are nested, so grouping each equal-center family and taking
its widest radius preserves the union. -/
theorem shiftedFareyAnchorArc_nested_of_equal_centers
    (M Q q q' : ℕ) (a a' j j' : ℤ)
    (hcenter : shiftedFareyAnchorCenter M q a j =
      shiftedFareyAnchorCenter M q' a' j') :
    shiftedFareyAnchorArc M Q q a j ⊆
        shiftedFareyAnchorArc M Q q' a' j' ∨
      shiftedFareyAnchorArc M Q q' a' j' ⊆
        shiftedFareyAnchorArc M Q q a j := by
  unfold shiftedFareyAnchorArc
  rw [hcenter]
  exact (le_total
    (1 / ((q : ℝ) * (Q + 1)))
    (1 / ((q' : ℝ) * (Q + 1)))).imp
      Metric.closedBall_subset_closedBall
      Metric.closedBall_subset_closedBall

/-- Repeated centers occur even for the genuine odd support modulus five;
therefore pairwise disjointness for all indexed triples would be false. -/
theorem shiftedFareyAnchorCenter_actual_duplicate :
    shiftedFareyAnchorCenter 5 2 1 0 =
      shiftedFareyAnchorCenter 5 10 7 1 := by
  norm_num [shiftedFareyAnchorCenter]

/-- At every actual endpoint, all differently centered residue-shifted major
intervals are disjoint for the corrected logarithmic/label-dependent cutoff,
with original radii and arbitrary periodic integer representatives. -/
theorem shiftedFareyAnchorArc_fully_compatible_disjoint_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (M : ℕ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ q q' : ℕ, 0 < q → 0 < q' →
        q ≤ compatibleLogMinorCutoff n →
        q' ≤ compatibleLogMinorCutoff n →
        ∀ a a' j j' : ℤ,
          shiftedFareyAnchorCenter M q a j ≠
              shiftedFareyAnchorCenter M q' a' j' →
            Disjoint
              (shiftedFareyAnchorArc M (fullyCompatibleFareyCutoff lower n)
                q a j)
              (shiftedFareyAnchorArc M (fullyCompatibleFareyCutoff lower n)
                q' a' j') := by
  filter_upwards
    [fullyCompatibleFareyCutoff_merged_disjoint_eventually
      lower κ hκ hlinear M] with n hseparation
  intro q q' hq hq' hqP hq'P a a' j j' hdistinct
  exact shiftedFareyAnchorArc_disjoint_of_distinct_centers
    M (compatibleLogMinorCutoff n) (fullyCompatibleFareyCutoff lower n)
    q q' a a' j j' hM hq hq' hqP hq'P hseparation hdistinct

end Erdos689

