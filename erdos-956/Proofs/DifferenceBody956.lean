module

public import Mathlib


@[expose] public section

/-!
# Minkowski difference-body reduction for Erdős #956

Identifies the double-infimum Euclidean distance between translates of
`C = (1 / 2) • D` with point-to-body distance `Metric.infDist (y - x) D` and
proves that `y - x ∉ D` implies closed-set disjointness of `C + x` and `C + y`.
-/

open scoped Pointwise

namespace Erdos956

/-- The Euclidean minimum distance between two translates of the same set. -/
noncomputable def translateSetDistance {E : Type*} [PseudoMetricSpace E] [AddGroup E]
    (C : Set E) (x y : E) : ℝ :=
  ⨅ c : C, ⨅ d : C, dist (c.1 + x) (d.1 + y)

section Normed

variable {E : Type*} [NormedAddCommGroup E]

theorem difference_nonempty {C : Set E} (hC : C.Nonempty) : (C - C).Nonempty := by
  obtain ⟨c, hc⟩ := hC
  exact ⟨c - c, Set.sub_mem_sub hc hc⟩

theorem dist_sub_eq_dist_translate (c d x y : E) :
    dist (y - x) (c - d) = dist (c + x) (d + y) := by
  rw [dist_eq_norm, dist_eq_norm]
  have h : (y - x) - (c - d) = -((c + x) - (d + y)) := by abel
  rw [h, norm_neg]

theorem translateSetDistance_eq_infDist_sub (C : Set E) (hC : C.Nonempty) (x y : E) :
    translateSetDistance C x y = Metric.infDist (y - x) (C - C) := by
  have : Nonempty C := hC.to_subtype
  have hb_inner (c : C) :
      BddBelow (Set.range (fun d : C => dist (c.1 + x) (d.1 + y))) := by
    refine ⟨0, ?_⟩
    rintro z ⟨d, rfl⟩
    exact dist_nonneg
  have hnonneg_inner (c : C) :
      0 ≤ ⨅ d : C, dist (c.1 + x) (d.1 + y) :=
    le_ciInf fun d => dist_nonneg
  have hb_outer :
      BddBelow (Set.range (fun c : C => ⨅ d : C, dist (c.1 + x) (d.1 + y))) := by
    refine ⟨0, ?_⟩
    rintro z ⟨c, rfl⟩
    exact hnonneg_inner c
  apply le_antisymm
  · apply (Metric.le_infDist (difference_nonempty hC)).2
    intro z hz
    rcases Set.mem_sub.mp hz with ⟨c, hc, d, hd, rfl⟩
    have hle : translateSetDistance C x y ≤ dist (c + x) (d + y) := by
      unfold translateSetDistance
      exact (ciInf_le hb_outer (⟨c, hc⟩ : C)).trans
        (ciInf_le (hb_inner (⟨c, hc⟩ : C)) (⟨d, hd⟩ : C))
    rwa [dist_sub_eq_dist_translate]
  · unfold translateSetDistance
    apply le_ciInf
    intro c
    apply le_ciInf
    intro d
    have hm : (c.1 - d.1) ∈ C - C := Set.sub_mem_sub c.2 d.2
    have hle := Metric.infDist_le_dist_of_mem (x := y - x) hm
    rwa [dist_sub_eq_dist_translate] at hle

theorem translates_disjoint_iff_sub_not_mem (C : Set E) (x y : E) :
    Disjoint ((· + x) '' C) ((· + y) '' C) ↔ y - x ∉ C - C := by
  constructor
  · intro h hz
    rcases Set.mem_sub.mp hz with ⟨c, hc, d, hd, heq⟩
    have hxy : c + x = d + y := by
      apply sub_eq_zero.mp
      calc
        (c + x) - (d + y) = (c - d) - (y - x) := by abel
        _ = 0 := sub_eq_zero.mpr heq
    exact (Set.disjoint_left.mp h) ⟨c, hc, rfl⟩ ⟨d, hd, hxy.symm⟩
  · intro h
    apply Set.disjoint_left.mpr
    intro z hz1 hz2
    rcases hz1 with ⟨c, hc, rfl⟩
    rcases hz2 with ⟨d, hd, heq⟩
    apply h
    have hxy : c - d = y - x := by
      apply sub_eq_zero.mp
      calc
        (c - d) - (y - x) = (c + x) - (d + y) := by abel
        _ = 0 := sub_eq_zero.mpr heq.symm
    exact hxy ▸ Set.sub_mem_sub hc hd

end Normed

section HalfBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem half_body_difference_subset (D : Set E) (hconvex : Convex ℝ D)
    (hsymmetric : ∀ z ∈ D, -z ∈ D) :
    ((1 / 2 : ℝ) • D - (1 / 2 : ℝ) • D) ⊆ D := by
  intro z hz
  rcases Set.mem_sub.mp hz with ⟨c, hc, d, hd, rfl⟩
  rcases Set.mem_smul_set.mp hc with ⟨u, hu, rfl⟩
  rcases Set.mem_smul_set.mp hd with ⟨v, hv, rfl⟩
  have hmid : midpoint ℝ u (-v) ∈ D := hconvex.midpoint_mem hu (hsymmetric v hv)
  convert hmid using 1
  simp only [midpoint_eq_smul_add, invOf_eq_inv, one_div, smul_add,
    smul_neg, sub_eq_add_neg]

theorem mem_half_body_difference_of_mem (D : Set E) {p : E}
    (hp : p ∈ D) (hneg : -p ∈ D) :
    p ∈ (1 / 2 : ℝ) • D - (1 / 2 : ℝ) • D := by
  have hmem := Set.sub_mem_sub
    (Set.smul_mem_smul_set (a := (1 / 2 : ℝ)) hp)
    (Set.smul_mem_smul_set (a := (1 / 2 : ℝ)) hneg)
  have h : (1 / 2 : ℝ) • p - (1 / 2 : ℝ) • (-p) = p := by
    rw [smul_neg, sub_neg_eq_add, ← add_smul]
    norm_num
  exact h ▸ hmem

theorem half_body_translates_disjoint_of_diff_not_mem
    (D : Set E) (hconvex : Convex ℝ D) (hsymmetric : ∀ z ∈ D, -z ∈ D)
    {x y : E} (hxy : y - x ∉ D) :
    Disjoint ((· + x) '' ((1 / 2 : ℝ) • D))
      ((· + y) '' ((1 / 2 : ℝ) • D)) := by
  apply (translates_disjoint_iff_sub_not_mem ((1 / 2 : ℝ) • D) x y).2
  exact fun h => hxy ((half_body_difference_subset D hconvex hsymmetric) h)

theorem half_body_isCompact (D : Set E) (hD : IsCompact D) :
    IsCompact ((1 / 2 : ℝ) • D) := hD.smul _

theorem half_body_convex (D : Set E) (hD : Convex ℝ D) :
    Convex ℝ ((1 / 2 : ℝ) • D) := hD.smul _

theorem translateSetDistance_one_of_body
    (D : Set E) (hconvex : Convex ℝ D) (hsymmetric : ∀ z ∈ D, -z ∈ D)
    {p γ x y : E} (hp : p ∈ D) (hγ : y - x = γ)
    (hDist : Metric.infDist γ D = 1) (hclose : dist γ p = 1) :
    translateSetDistance ((1 / 2 : ℝ) • D) x y = 1 := by
  let C : Set E := (1 / 2 : ℝ) • D
  have hpC : ((1 / 2 : ℝ) • p) ∈ C := Set.smul_mem_smul_set hp
  have hC : C.Nonempty := ⟨_, hpC⟩
  have hsubset : C - C ⊆ D := half_body_difference_subset D hconvex hsymmetric
  have hpin : p ∈ C - C := mem_half_body_difference_of_mem D hp (hsymmetric p hp)
  have hlow : 1 ≤ Metric.infDist γ (C - C) := by
    rw [← hDist]
    exact Metric.infDist_le_infDist_of_subset hsubset ⟨p, hpin⟩
  have hupp : Metric.infDist γ (C - C) ≤ 1 := by
    exact (Metric.infDist_le_dist_of_mem hpin).trans_eq hclose
  rw [translateSetDistance_eq_infDist_sub C hC, hγ]
  exact le_antisymm hupp hlow

end HalfBody

end Erdos956
