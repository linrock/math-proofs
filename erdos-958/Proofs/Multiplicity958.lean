module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License") for the
attributed Formal Conjectures definitions, and the MIT License for the
local proof development.
-/

public import Definitions958


@[expose] public section

/-!
# Erdős Problem 958: exact distance set and multiplicity profile of `cdlSet n`

For every `n ≥ 2`, the Clemen–Dumitrescu–Liu configuration `cdlSet n` determines
exact distance set
`insert 1 ((Finset.Icc 1 (n - 2)).image (chordDist n))`
of cardinality `n - 1`, with multiplicities
* `distanceMultiplicity (cdlSet n) 1 = n - 1`, and
* `distanceMultiplicity (cdlSet n) (chordDist n s) = n - 1 - s` for `1 ≤ s ≤ n - 2`.

Consequently, `(distanceSet (cdlSet n)).image (distanceMultiplicity (cdlSet n)) = Finset.Icc 1 (n - 1)`.
It also proves the general progression multiplicity theorem `image_range_has_profile`
for any indexed family whose pairwise distances depend injectively on `Nat.dist i j`.
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace Erdos958

open Finset EuclideanGeometry

/-- Characterization of membership in `cdlSet n`. -/
lemma mem_cdlSet_iff {n : ℕ} {x : ℝ²} :
    x ∈ cdlSet n ↔ x = originPt ∨ ∃ k < n - 1, x = arcPt n k := by
  simp only [cdlSet, arcSet, mem_insert, mem_image, mem_range]
  tauto

/-- `originPt` belongs to `cdlSet n`. -/
@[simp]
lemma originPt_mem_cdlSet (n : ℕ) : originPt ∈ cdlSet n :=
  mem_insert_self originPt (arcSet n)

/-- For `k < n - 1`, `arcPt n k` belongs to `cdlSet n`. -/
lemma arcPt_mem_cdlSet {n k : ℕ} (hk : k < n - 1) : arcPt n k ∈ cdlSet n := by
  rw [mem_cdlSet_iff]
  exact Or.inr ⟨k, hk, rfl⟩

/-- For `k : ℕ`, `arcPt n k ≠ originPt`. -/
lemma arcPt_ne_originPt (n k : ℕ) : arcPt n k ≠ originPt := by
  intro h
  have hd := congrArg (dist originPt) h
  rw [dist_originPt_arcPt, dist_self] at hd
  norm_num at hd

/-- For `k : ℕ`, `originPt ≠ arcPt n k`. -/
lemma originPt_ne_arcPt (n k : ℕ) : originPt ≠ arcPt n k :=
  (arcPt_ne_originPt n k).symm

/-- Upper bound on `Nat.dist i j` for `i, j < m`. -/
lemma one_le_natDist_of_ne {i j : ℕ} (hij : i ≠ j) : 1 ≤ Nat.dist i j := by
  rcases le_total i j with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    omega

lemma natDist_le_pred {m i j : ℕ} (hi : i < m) (hj : j < m) :
    Nat.dist i j ≤ m - 1 := by
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji]
    omega

lemma natDist_le_sub_two {n i j : ℕ} (hi : i < n - 1) (hj : j < n - 1) :
    Nat.dist i j ≤ n - 2 := by
  have := natDist_le_pred hi hj
  omega

/-- Exact description of `distanceSet (cdlSet n)` for `n ≥ 2`. -/
theorem distanceSet_cdlSet {n : ℕ} (hn : 2 ≤ n) :
    distanceSet (cdlSet n) = insert (1 : ℝ) ((Finset.Icc 1 (n - 2)).image (chordDist n)) := by
  ext d
  simp only [distanceSet, mem_image, mem_offDiag, mem_insert, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨hx, hy, hxy⟩, rfl⟩
    rcases mem_cdlSet_iff.mp hx with rfl | ⟨i, hi, rfl⟩ <;>
      rcases mem_cdlSet_iff.mp hy with rfl | ⟨j, hj, rfl⟩
    · exact False.elim (hxy rfl)
    · left
      exact dist_originPt_arcPt n j
    · left
      exact dist_arcPt_originPt n i
    · right
      have hij : i ≠ j := fun h => hxy (congrArg (arcPt n) h)
      exact ⟨Nat.dist i j, ⟨one_le_natDist_of_ne hij, natDist_le_sub_two hi hj⟩,
        (dist_arcPt_arcPt n i j).symm⟩
  · rintro (rfl | ⟨s, ⟨hs1, hs2⟩, rfl⟩)
    · refine ⟨originPt, arcPt n 0, ⟨originPt_mem_cdlSet n, arcPt_mem_cdlSet (by omega),
        originPt_ne_arcPt n 0⟩, dist_originPt_arcPt n 0⟩
    · have hs_lt : s < n - 1 := by omega
      have h0_lt : 0 < n - 1 := by omega
      have hne : arcPt n 0 ≠ arcPt n s := by
        intro heq
        have h0s : (0 : ℕ) = s := arcPt_inj (by omega) (by omega) heq
        omega
      refine ⟨arcPt n 0, arcPt n s, ⟨arcPt_mem_cdlSet h0_lt, arcPt_mem_cdlSet hs_lt, hne⟩, ?_⟩
      simpa [Nat.dist_zero_left] using dist_arcPt_arcPt n 0 s

/-- `1` is not in the chord-distance image `(Finset.Icc 1 (n - 2)).image (chordDist n)`. -/
lemma one_not_mem_image_chordDist (n : ℕ) :
    (1 : ℝ) ∉ (Finset.Icc 1 (n - 2)).image (chordDist n) := by
  rw [mem_image]
  rintro ⟨s, hs, hs_eq⟩
  rw [mem_Icc] at hs
  have hlt : chordDist n s < 1 := chordDist_lt_one (by omega)
  linarith

/-- For `n ≥ 2`, `cdlSet n` determines exactly `n - 1` distinct distances. -/
theorem card_distanceSet_cdlSet {n : ℕ} (hn : 2 ≤ n) :
    #(distanceSet (cdlSet n)) = n - 1 := by
  rw [distanceSet_cdlSet hn, card_insert_of_notMem (one_not_mem_image_chordDist n)]
  rw [card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro s₁ hs₁ s₂ hs₂ heq
    rw [mem_coe, mem_Icc] at hs₁ hs₂
    exact chordDist_inj (by omega) (by omega) heq

/-- Ordered pairs of distinct points in `A` at distance `d`. -/
noncomputable def distPairs (A : Finset ℝ²) (d : ℝ) : Finset (ℝ² × ℝ²) :=
  A.offDiag.filter fun p => dist p.1 p.2 = d

lemma distanceMultiplicity_eq_card_distPairs_div_two (A : Finset ℝ²) (d : ℝ) :
    distanceMultiplicity A d = #(distPairs A d) / 2 := rfl

/-- Ordered pairs `(originPt, arcPt n k)` for `k < n - 1`. -/
noncomputable def originLeftPairs (n : ℕ) : Finset (ℝ² × ℝ²) :=
  (Finset.range (n - 1)).image fun k => (originPt, arcPt n k)

/-- Ordered pairs `(arcPt n k, originPt)` for `k < n - 1`. -/
noncomputable def originRightPairs (n : ℕ) : Finset (ℝ² × ℝ²) :=
  (Finset.range (n - 1)).image fun k => (arcPt n k, originPt)

lemma card_originLeftPairs (n : ℕ) : #(originLeftPairs n) = n - 1 := by
  rw [originLeftPairs, card_image_of_injOn, card_range]
  intro i hi j hj heq
  rw [mem_coe, mem_range] at hi hj
  exact arcPt_inj (by omega) (by omega) (Prod.ext_iff.mp heq).2

lemma card_originRightPairs (n : ℕ) : #(originRightPairs n) = n - 1 := by
  rw [originRightPairs, card_image_of_injOn, card_range]
  intro i hi j hj heq
  rw [mem_coe, mem_range] at hi hj
  exact arcPt_inj (by omega) (by omega) (Prod.ext_iff.mp heq).1

lemma disjoint_originLeftPairs_originRightPairs (n : ℕ) :
    Disjoint (originLeftPairs n) (originRightPairs n) := by
  rw [Finset.disjoint_left]
  intro p hpL hpR
  rw [originLeftPairs, mem_image] at hpL
  rw [originRightPairs, mem_image] at hpR
  obtain ⟨i, _, rfl⟩ := hpL
  obtain ⟨j, _, heq⟩ := hpR
  exact arcPt_ne_originPt n j (Prod.ext_iff.mp heq).1

/-- The ordered pairs in `cdlSet n` at distance `1` are precisely `originLeftPairs n ∪ originRightPairs n`. -/
lemma distPairs_cdlSet_one (n : ℕ) :
    distPairs (cdlSet n) 1 = originLeftPairs n ∪ originRightPairs n := by
  ext ⟨x, y⟩
  simp only [distPairs, originLeftPairs, originRightPairs, mem_filter, mem_offDiag,
    mem_union, mem_image, mem_range]
  constructor
  · rintro ⟨⟨hx, hy, hxy⟩, hdist⟩
    rcases mem_cdlSet_iff.mp hx with rfl | ⟨i, hi, rfl⟩ <;>
      rcases mem_cdlSet_iff.mp hy with rfl | ⟨j, hj, rfl⟩
    · exact False.elim (hxy rfl)
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩
    · exfalso
      rw [dist_arcPt_arcPt] at hdist
      have hlt : chordDist n (Nat.dist i j) < 1 := by
        have hdist_le := natDist_le_sub_two hi hj
        exact chordDist_lt_one (by omega)
      linarith
  · rintro (⟨k, hk, hpair⟩ | ⟨k, hk, hpair⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair.symm
      exact ⟨⟨originPt_mem_cdlSet n, arcPt_mem_cdlSet hk, originPt_ne_arcPt n k⟩,
        dist_originPt_arcPt n k⟩
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair.symm
      exact ⟨⟨arcPt_mem_cdlSet hk, originPt_mem_cdlSet n, arcPt_ne_originPt n k⟩,
        dist_arcPt_originPt n k⟩

/-- The multiplicity of distance `1` in `cdlSet n` is `n - 1`. -/
theorem distanceMultiplicity_cdlSet_one (n : ℕ) :
    distanceMultiplicity (cdlSet n) 1 = n - 1 := by
  rw [distanceMultiplicity_eq_card_distPairs_div_two, distPairs_cdlSet_one,
    card_union_of_disjoint (disjoint_originLeftPairs_originRightPairs n),
    card_originLeftPairs, card_originRightPairs]
  omega

/-- Ordered pairs `(f i, f (i + s))` for `i < m - s`. -/
noncomputable def stepLeftPairs (f : ℕ → ℝ²) (m s : ℕ) : Finset (ℝ² × ℝ²) :=
  (Finset.range (m - s)).image fun i => (f i, f (i + s))

/-- Ordered pairs `(f (i + s), f i)` for `i < m - s`. -/
noncomputable def stepRightPairs (f : ℕ → ℝ²) (m s : ℕ) : Finset (ℝ² × ℝ²) :=
  (Finset.range (m - s)).image fun i => (f (i + s), f i)

lemma card_stepLeftPairs_union_stepRightPairs_div_two {f : ℕ → ℝ²} {m s : ℕ} (hs : 1 ≤ s)
    (hfinj : ∀ ⦃i j⦄, i < m → j < m → f i = f j → i = j) :
    #(stepLeftPairs f m s ∪ stepRightPairs f m s) / 2 = m - s := by
  have hdisj : Disjoint (stepLeftPairs f m s) (stepRightPairs f m s) := by
    rw [Finset.disjoint_left]
    intro p hpL hpR
    rw [stepLeftPairs, mem_image] at hpL
    rw [stepRightPairs, mem_image] at hpR
    obtain ⟨i, hi, rfl⟩ := hpL
    obtain ⟨j, hj, heq⟩ := hpR
    rw [mem_range] at hi hj
    have h1 : j + s = i := hfinj (by omega) (by omega) (Prod.ext_iff.mp heq).1
    have h2 : j = i + s := hfinj (by omega) (by omega) (Prod.ext_iff.mp heq).2
    omega
  have hcardL : #(stepLeftPairs f m s) = m - s := by
    rw [stepLeftPairs, card_image_of_injOn, card_range]
    intro i hi j hj heq
    rw [mem_coe, mem_range] at hi hj
    exact hfinj (by omega) (by omega) (Prod.ext_iff.mp heq).1
  have hcardR : #(stepRightPairs f m s) = m - s := by
    rw [stepRightPairs, card_image_of_injOn, card_range]
    intro i hi j hj heq
    rw [mem_coe, mem_range] at hi hj
    exact hfinj (by omega) (by omega) (Prod.ext_iff.mp heq).2
  rw [card_union_of_disjoint hdisj, hcardL, hcardR]
  omega

/-- For `1 ≤ s ≤ n - 2`, the ordered pairs in `cdlSet n` at distance `chordDist n s`
are `stepLeftPairs (arcPt n) (n - 1) s ∪ stepRightPairs (arcPt n) (n - 1) s`. -/
lemma distPairs_cdlSet_chordDist {n s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ n - 2) :
    distPairs (cdlSet n) (chordDist n s) =
      stepLeftPairs (arcPt n) (n - 1) s ∪ stepRightPairs (arcPt n) (n - 1) s := by
  have hs_lt_n : s < n := by omega
  ext ⟨x, y⟩
  simp only [distPairs, stepLeftPairs, stepRightPairs, mem_filter, mem_offDiag,
    mem_union, mem_image, mem_range]
  constructor
  · rintro ⟨⟨hx, hy, hxy⟩, hdist⟩
    rcases mem_cdlSet_iff.mp hx with rfl | ⟨i, hi, rfl⟩ <;>
      rcases mem_cdlSet_iff.mp hy with rfl | ⟨j, hj, rfl⟩
    · exact False.elim (hxy rfl)
    · exfalso
      rw [dist_originPt_arcPt] at hdist
      linarith [chordDist_lt_one hs_lt_n]
    · exfalso
      rw [dist_arcPt_originPt] at hdist
      linarith [chordDist_lt_one hs_lt_n]
    · rw [dist_arcPt_arcPt] at hdist
      have hdist_le := natDist_le_sub_two hi hj
      have hnat : Nat.dist i j = s := chordDist_inj (by omega) hs_lt_n hdist
      rcases le_total i j with hij | hji
      · rw [Nat.dist_eq_sub_of_le hij] at hnat
        have hj_eq : j = i + s := by omega
        subst hj_eq
        exact Or.inl ⟨i, by omega, rfl⟩
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji] at hnat
        have hi_eq : i = j + s := by omega
        subst hi_eq
        exact Or.inr ⟨j, by omega, rfl⟩
  · rintro (⟨i, hi, hpair⟩ | ⟨i, hi, hpair⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair.symm
      have hne : arcPt n i ≠ arcPt n (i + s) := by
        intro heq
        have his : i = i + s := arcPt_inj (by omega) (by omega) heq
        omega
      refine ⟨⟨arcPt_mem_cdlSet (by omega), arcPt_mem_cdlSet (by omega), hne⟩, ?_⟩
      rw [dist_arcPt_arcPt, Nat.dist_eq_sub_of_le (Nat.le_add_right i s), Nat.add_sub_cancel_left]
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair.symm
      have hne : arcPt n (i + s) ≠ arcPt n i := by
        intro heq
        have his : i + s = i := arcPt_inj (by omega) (by omega) heq
        omega
      refine ⟨⟨arcPt_mem_cdlSet (by omega), arcPt_mem_cdlSet (by omega), hne⟩, ?_⟩
      rw [dist_arcPt_arcPt, Nat.dist_comm,
        Nat.dist_eq_sub_of_le (Nat.le_add_right i s), Nat.add_sub_cancel_left]

/-- For `1 ≤ s ≤ n - 2`, the multiplicity of `chordDist n s` in `cdlSet n` is `n - 1 - s`. -/
theorem distanceMultiplicity_cdlSet_chordDist {n s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ n - 2) :
    distanceMultiplicity (cdlSet n) (chordDist n s) = n - 1 - s := by
  rw [distanceMultiplicity_eq_card_distPairs_div_two, distPairs_cdlSet_chordDist hs1 hs2,
    card_stepLeftPairs_union_stepRightPairs_div_two hs1
      (fun i j hi hj heq => arcPt_inj (by omega) (by omega) heq)]

/-- For `n ≥ 2`, the multiplicities of the distances in `cdlSet n` are `{1, 2, ..., n - 1}`. -/
theorem image_distanceMultiplicity_cdlSet {n : ℕ} (hn : 2 ≤ n) :
    (distanceSet (cdlSet n)).image (distanceMultiplicity (cdlSet n)) = Finset.Icc 1 (n - 1) := by
  rw [distanceSet_cdlSet hn]
  ext m
  simp only [mem_image, mem_insert, mem_Icc]
  constructor
  · rintro ⟨d, rfl | ⟨s, ⟨hs1, hs2⟩, rfl⟩, rfl⟩
    · rw [distanceMultiplicity_cdlSet_one]
      omega
    · rw [distanceMultiplicity_cdlSet_chordDist hs1 hs2]
      omega
  · rintro ⟨hm1, hm2⟩
    rcases eq_or_lt_of_le hm2 with rfl | hmlt
    · exact ⟨1, Or.inl rfl, distanceMultiplicity_cdlSet_one n⟩
    · refine ⟨chordDist n (n - 1 - m), Or.inr ⟨n - 1 - m, ⟨by omega, by omega⟩, rfl⟩, ?_⟩
      rw [distanceMultiplicity_cdlSet_chordDist (by omega) (by omega)]
      omega

/-- General distance-multiplicity profile for any indexed progression `(Finset.range m).image f`
whose pairwise distances depend injectively on `Nat.dist i j`. -/
theorem image_range_has_profile {f : ℕ → ℝ²} {D : ℕ → ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hdist : ∀ i j, dist (f i) (f j) = D (Nat.dist i j))
    (hD : ∀ ⦃s₁ s₂⦄, s₁ < m → s₂ < m → D s₁ = D s₂ → s₁ = s₂) :
    #(distanceSet ((Finset.range m).image f)) = m - 1 ∧
      (distanceSet ((Finset.range m).image f)).image
        (distanceMultiplicity ((Finset.range m).image f)) = Finset.Icc 1 (m - 1) := by
  have hfinj : ∀ ⦃i j⦄, i < m → j < m → f i = f j → i = j := by
    intro i j hi hj heq
    have hd0 : D (Nat.dist i j) = D 0 := by
      have hd := congrArg (dist (f i)) heq
      rw [dist_self, hdist i j] at hd
      have h00 := hdist 0 0
      rw [dist_self, Nat.dist_self] at h00
      linarith
    have hdist_le := natDist_le_pred hi hj
    have hnat0 : Nat.dist i j = 0 := hD (by omega) (by omega) hd0
    by_contra hij
    have := one_le_natDist_of_ne hij
    omega
  have hdistSet : distanceSet ((Finset.range m).image f) = (Finset.Icc 1 (m - 1)).image D := by
    ext d
    simp only [distanceSet, mem_image, mem_offDiag, mem_range, mem_Icc, Prod.exists]
    constructor
    · rintro ⟨x, y, ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, hxy⟩, rfl⟩
      have hij : i ≠ j := fun h => hxy (congrArg f h)
      exact ⟨Nat.dist i j, ⟨one_le_natDist_of_ne hij, natDist_le_pred hi hj⟩, (hdist i j).symm⟩
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      have hne : f 0 ≠ f s := fun h => by
        have := hfinj (by omega) (by omega) h
        omega
      refine ⟨f 0, f s, ⟨⟨0, by omega, rfl⟩, ⟨s, by omega, rfl⟩, hne⟩, ?_⟩
      simpa [Nat.dist_zero_left] using hdist 0 s
  have hmult : ∀ {s : ℕ}, 1 ≤ s → s ≤ m - 1 →
      distanceMultiplicity ((Finset.range m).image f) (D s) = m - s := by
    intro s hs1 hs2
    have hpairs : distPairs ((Finset.range m).image f) (D s) =
        stepLeftPairs f m s ∪ stepRightPairs f m s := by
      ext ⟨x, y⟩
      simp only [distPairs, stepLeftPairs, stepRightPairs, mem_filter, mem_offDiag,
        mem_union, mem_image, mem_range]
      constructor
      · rintro ⟨⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, _⟩, hd⟩
        rw [hdist] at hd
        have hdist_le := natDist_le_pred hi hj
        have hnat : Nat.dist i j = s := hD (by omega) (by omega) hd
        rcases le_total i j with hij | hji
        · rw [Nat.dist_eq_sub_of_le hij] at hnat
          have hj_eq : j = i + s := by omega
          subst hj_eq
          exact Or.inl ⟨i, by omega, rfl⟩
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji] at hnat
          have hi_eq : i = j + s := by omega
          subst hi_eq
          exact Or.inr ⟨j, by omega, rfl⟩
      · rintro (⟨i, hi, hpair⟩ | ⟨i, hi, hpair⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair.symm
          have hne : f i ≠ f (i + s) := fun h => by
            have := hfinj (by omega) (by omega) h; omega
          refine ⟨⟨⟨i, by omega, rfl⟩, ⟨i + s, by omega, rfl⟩, hne⟩, ?_⟩
          rw [hdist, Nat.dist_eq_sub_of_le (Nat.le_add_right i s), Nat.add_sub_cancel_left]
        · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair.symm
          have hne : f (i + s) ≠ f i := fun h => by
            have := hfinj (by omega) (by omega) h; omega
          refine ⟨⟨⟨i + s, by omega, rfl⟩, ⟨i, by omega, rfl⟩, hne⟩, ?_⟩
          rw [hdist, Nat.dist_comm,
            Nat.dist_eq_sub_of_le (Nat.le_add_right i s), Nat.add_sub_cancel_left]
    rw [distanceMultiplicity_eq_card_distPairs_div_two, hpairs,
      card_stepLeftPairs_union_stepRightPairs_div_two hs1 hfinj]
  rw [hdistSet]
  constructor
  · rw [card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro s₁ hs₁ s₂ hs₂ heq
      rw [mem_coe, mem_Icc] at hs₁ hs₂
      exact hD (by omega) (by omega) heq
  · ext k
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨d, ⟨s, ⟨hs1, hs2⟩, rfl⟩, rfl⟩
      rw [hmult hs1 hs2]
      omega
    · rintro ⟨hk1, hk2⟩
      refine ⟨D (m - k), ⟨m - k, ⟨by omega, by omega⟩, rfl⟩, ?_⟩
      rw [hmult (by omega) (by omega)]
      omega

end Erdos958
